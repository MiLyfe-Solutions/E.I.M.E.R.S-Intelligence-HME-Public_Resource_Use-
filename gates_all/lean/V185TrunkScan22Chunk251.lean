import V185TrunkScan22Chunk250

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2239220 : List Nat := [2, 6, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_2239220 : Nat := 118140960795 + 2239220 * 2 ^ 59
def prefixEnd_2239220 : Nat := 4983230072969 + 3 ^ 40 * 2239220 * 2
def baseEnd_2239220 : Nat := 766530767440556183434681

theorem tailTrace_2239220 : CollatzResearch.WordTrace tailWord_2239220 prefixEnd_2239220 766530767440556183434681 := by
  unfold tailWord_2239220
  simp only [CollatzResearch.WordTrace]
  refine ⟨40835531473847921587217557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54447375298463895449623409 40835531473847921587217557)
  ·
    refine ⟨1914165537836621324400823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40835531473847921587217557 1914165537836621324400823)
    ·
      refine ⟨2871248306754931986601235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1914165537836621324400823 2871248306754931986601235)
      ·
        refine ⟨4306872460132397979901853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2871248306754931986601235 4306872460132397979901853)
        ·
          refine ⟨1615077172549649242463195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4306872460132397979901853 1615077172549649242463195)
          ·
            refine ⟨2422615758824473863694793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1615077172549649242463195 2422615758824473863694793)
            ·
              refine ⟨1816961819118355397771095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2422615758824473863694793 1816961819118355397771095)
              ·
                refine ⟨2725442728677533096656643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1816961819118355397771095 2725442728677533096656643)
                ·
                  refine ⟨4088164093016299644984965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2725442728677533096656643 4088164093016299644984965)
                  ·
                    refine ⟨766530767440556183434681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4088164093016299644984965 766530767440556183434681)
                    ·
                      rfl

theorem cell22_2239220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_2239220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239220 prefixEnd_2239220 := by exact prefixLift 2239220
  have htrace : WordTrace (prefixWord ++ tailWord_2239220) baseStart_2239220 baseEnd_2239220 := by
    simpa [prefixWord, tailWord_2239220, baseEnd_2239220] using wordTrace_append hprefix tailTrace_2239220
  have hstable : (prefixWord ++ tailWord_2239220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239220).length < 2 ^ (prefixWord ++ tailWord_2239220).sum := by decide
  have hdescent : baseEnd_2239220 < baseStart_2239220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239223 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 7]
def baseStart_2239223 : Nat := 118140960795 + 2239223 * 2 ^ 59
def prefixEnd_2239223 : Nat := 4983230072969 + 3 ^ 40 * 2239223 * 2
def baseEnd_2239223 : Nat := 255510598133955058536557

theorem tailTrace_2239223 : CollatzResearch.WordTrace tailWord_2239223 prefixEnd_2239223 255510598133955058536557 := by
  unfold tailWord_2239223
  simp only [CollatzResearch.WordTrace]
  refine ⟨81671172366684974686794323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54447448244456649791196215 81671172366684974686794323)
  ·
    refine ⟨122506758550027462030191485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81671172366684974686794323 122506758550027462030191485)
    ·
      refine ⟨45940034456260298261321807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122506758550027462030191485 45940034456260298261321807)
      ·
        refine ⟨68910051684390447391982711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45940034456260298261321807 68910051684390447391982711)
        ·
          refine ⟨103365077526585671087974067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68910051684390447391982711 103365077526585671087974067)
          ·
            refine ⟨155047616289878506631961101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103365077526585671087974067 155047616289878506631961101)
            ·
              refine ⟨58142856108704439986985413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155047616289878506631961101 58142856108704439986985413)
              ·
                refine ⟨10901785520382082497559765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58142856108704439986985413 10901785520382082497559765)
                ·
                  refine ⟨255510598133955058536557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10901785520382082497559765 255510598133955058536557)
                  ·
                    rfl

theorem cell22_2239223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 7].length) (baseStart_2239223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239223 prefixEnd_2239223 := by exact prefixLift 2239223
  have htrace : WordTrace (prefixWord ++ tailWord_2239223) baseStart_2239223 baseEnd_2239223 := by
    simpa [prefixWord, tailWord_2239223, baseEnd_2239223] using wordTrace_append hprefix tailTrace_2239223
  have hstable : (prefixWord ++ tailWord_2239223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239223).length < 2 ^ (prefixWord ++ tailWord_2239223).sum := by decide
  have hdescent : baseEnd_2239223 < baseStart_2239223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239240 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 7]
def baseStart_2239240 : Nat := 118140960795 + 2239240 * 2 ^ 59
def prefixEnd_2239240 : Nat := 4983230072969 + 3 ^ 40 * 2239240 * 2
def baseEnd_2239240 : Nat := 255512537949760932644873

theorem tailTrace_2239240 : CollatzResearch.WordTrace tailWord_2239240 prefixEnd_2239240 255512537949760932644873 := by
  unfold tailWord_2239240
  simp only [CollatzResearch.WordTrace]
  refine ⟨40835896203811693295081587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54447861605082257726775449 40835896203811693295081587)
  ·
    refine ⟨61253844305717539942622381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40835896203811693295081587 61253844305717539942622381)
    ·
      refine ⟨22970191614644077478483393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61253844305717539942622381 22970191614644077478483393)
      ·
        refine ⟨17227643710983058108862545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22970191614644077478483393 17227643710983058108862545)
        ·
          refine ⟨12920732783237293581646909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17227643710983058108862545 12920732783237293581646909)
          ·
            refine ⟨4845274793713985093117591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12920732783237293581646909 4845274793713985093117591)
            ·
              refine ⟨7267912190570977639676387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4845274793713985093117591 7267912190570977639676387)
              ·
                refine ⟨10901868285856466459514581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7267912190570977639676387 10901868285856466459514581)
                ·
                  refine ⟨255512537949760932644873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10901868285856466459514581 255512537949760932644873)
                  ·
                    rfl

theorem cell22_2239240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 7].length) (baseStart_2239240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239240 prefixEnd_2239240 := by exact prefixLift 2239240
  have htrace : WordTrace (prefixWord ++ tailWord_2239240) baseStart_2239240 baseEnd_2239240 := by
    simpa [prefixWord, tailWord_2239240, baseEnd_2239240] using wordTrace_append hprefix tailTrace_2239240
  have hstable : (prefixWord ++ tailWord_2239240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239240).length < 2 ^ (prefixWord ++ tailWord_2239240).sum := by decide
  have hdescent : baseEnd_2239240 < baseStart_2239240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239278 : List Nat := [4, 1, 3, 2, 1, 3, 1, 3, 1, 3]
def baseStart_2239278 : Nat := 118140960795 + 2239278 * 2 ^ 59
def prefixEnd_2239278 : Nat := 4983230072969 + 3 ^ 40 * 2239278 * 2
def baseEnd_2239278 : Nat := 766550622025863365484503

theorem tailTrace_2239278 : CollatzResearch.WordTrace tailWord_2239278 prefixEnd_2239278 766550622025863365484503 := by
  unfold tailWord_2239278
  simp only [CollatzResearch.WordTrace]
  refine ⟨10209147297685714885005811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54448785587657146053364325 10209147297685714885005811)
  ·
    refine ⟨15313720946528572327508717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10209147297685714885005811 15313720946528572327508717)
    ·
      refine ⟨5742645354948214622815769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15313720946528572327508717 5742645354948214622815769)
      ·
        refine ⟨4306984016211160967111827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5742645354948214622815769 4306984016211160967111827)
        ·
          refine ⟨6460476024316741450667741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4306984016211160967111827 6460476024316741450667741)
          ·
            refine ⟨2422678509118778044000403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6460476024316741450667741 2422678509118778044000403)
            ·
              refine ⟨3634017763678167066000605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2422678509118778044000403 3634017763678167066000605)
              ·
                refine ⟨1362756661379312649750227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3634017763678167066000605 1362756661379312649750227)
                ·
                  refine ⟨2044134992068968974625341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1362756661379312649750227 2044134992068968974625341)
                  ·
                    refine ⟨766550622025863365484503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2044134992068968974625341 766550622025863365484503)
                    ·
                      rfl

theorem cell22_2239278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_2239278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239278 prefixEnd_2239278 := by exact prefixLift 2239278
  have htrace : WordTrace (prefixWord ++ tailWord_2239278) baseStart_2239278 baseEnd_2239278 := by
    simpa [prefixWord, tailWord_2239278, baseEnd_2239278] using wordTrace_append hprefix tailTrace_2239278
  have hstable : (prefixWord ++ tailWord_2239278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239278).length < 2 ^ (prefixWord ++ tailWord_2239278).sum := by decide
  have hdescent : baseEnd_2239278 < baseStart_2239278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239332 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_2239332 : Nat := 118140960795 + 2239332 * 2 ^ 59
def prefixEnd_2239332 : Nat := 4983230072969 + 3 ^ 40 * 2239332 * 2
def baseEnd_2239332 : Nat := 766569107329425224634337

theorem tailTrace_2239332 : CollatzResearch.WordTrace tailWord_2239332 prefixEnd_2239332 766569107329425224634337 := by
  unfold tailWord_2239332
  simp only [CollatzResearch.WordTrace]
  refine ⟨40837573961645043151256125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54450098615526724201674833 40837573961645043151256125)
  ·
    refine ⟨15314090235616891181721047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40837573961645043151256125 15314090235616891181721047)
    ·
      refine ⟨22971135353425336772581571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15314090235616891181721047 22971135353425336772581571)
      ·
        refine ⟨34456703030138005158872357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22971135353425336772581571 34456703030138005158872357)
        ·
          refine ⟨6460631818150875967288567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34456703030138005158872357 6460631818150875967288567)
          ·
            refine ⟨9690947727226313950932851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6460631818150875967288567 9690947727226313950932851)
            ·
              refine ⟨14536421590839470926399277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9690947727226313950932851 14536421590839470926399277)
              ·
                refine ⟨5451158096564801597399729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14536421590839470926399277 5451158096564801597399729)
                ·
                  refine ⟨4088368572423601198049797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5451158096564801597399729 4088368572423601198049797)
                  ·
                    refine ⟨766569107329425224634337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4088368572423601198049797 766569107329425224634337)
                    ·
                      rfl

theorem cell22_2239332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_2239332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239332 prefixEnd_2239332 := by exact prefixLift 2239332
  have htrace : WordTrace (prefixWord ++ tailWord_2239332) baseStart_2239332 baseEnd_2239332 := by
    simpa [prefixWord, tailWord_2239332, baseEnd_2239332] using wordTrace_append hprefix tailTrace_2239332
  have hstable : (prefixWord ++ tailWord_2239332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239332).length < 2 ^ (prefixWord ++ tailWord_2239332).sum := by decide
  have hdescent : baseEnd_2239332 < baseStart_2239332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239396 : List Nat := [2, 3, 1, 2, 1, 2, 4, 3, 1, 3]
def baseStart_2239396 : Nat := 118140960795 + 2239396 * 2 ^ 59
def prefixEnd_2239396 : Nat := 4983230072969 + 3 ^ 40 * 2239396 * 2
def baseEnd_2239396 : Nat := 766591015837350391034141

theorem tailTrace_2239396 : CollatzResearch.WordTrace tailWord_2239396 prefixEnd_2239396 766591015837350391034141 := by
  unfold tailWord_2239396
  simp only [CollatzResearch.WordTrace]
  refine ⟨40838741097529112616421021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54451654796705483488561361 40838741097529112616421021)
  ·
    refine ⟨15314527911573417231157883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40838741097529112616421021 15314527911573417231157883)
    ·
      refine ⟨22971791867360125846736825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15314527911573417231157883 22971791867360125846736825)
      ·
        refine ⟨17228843900520094385052619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22971791867360125846736825 17228843900520094385052619)
        ·
          refine ⟨25843265850780141577578929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17228843900520094385052619 25843265850780141577578929)
          ·
            refine ⟨19382449388085106183184197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25843265850780141577578929 19382449388085106183184197)
            ·
              refine ⟨3634209260265957409347037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19382449388085106183184197 3634209260265957409347037)
              ·
                refine ⟨1362828472599734028505139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3634209260265957409347037 1362828472599734028505139)
                ·
                  refine ⟨2044242708899601042757709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1362828472599734028505139 2044242708899601042757709)
                  ·
                    refine ⟨766591015837350391034141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2044242708899601042757709 766591015837350391034141)
                    ·
                      rfl

theorem cell22_2239396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_2239396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239396 prefixEnd_2239396 := by exact prefixLift 2239396
  have htrace : WordTrace (prefixWord ++ tailWord_2239396) baseStart_2239396 baseEnd_2239396 := by
    simpa [prefixWord, tailWord_2239396, baseEnd_2239396] using wordTrace_append hprefix tailTrace_2239396
  have hstable : (prefixWord ++ tailWord_2239396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239396).length < 2 ^ (prefixWord ++ tailWord_2239396).sum := by decide
  have hdescent : baseEnd_2239396 < baseStart_2239396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239439 : List Nat := [1, 1, 2, 1, 1, 7, 2, 2, 1, 4]
def baseStart_2239439 : Nat := 118140960795 + 2239439 * 2 ^ 59
def prefixEnd_2239439 : Nat := 4983230072969 + 3 ^ 40 * 2239439 * 2
def baseEnd_2239439 : Nat := 766605735616112612209009

theorem tailTrace_2239439 : CollatzResearch.WordTrace tailWord_2239439 prefixEnd_2239439 766605735616112612209009 := by
  unfold tailWord_2239439
  simp only [CollatzResearch.WordTrace]
  refine ⟨81679050533902443576657371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54452700355934962384438247 81679050533902443576657371)
  ·
    refine ⟨122518575800853665364986057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81679050533902443576657371 122518575800853665364986057)
    ·
      refine ⟨91888931850640249023739543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122518575800853665364986057 91888931850640249023739543)
      ·
        refine ⟨137833397775960373535609315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91888931850640249023739543 137833397775960373535609315)
        ·
          refine ⟨206750096663940560303413973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137833397775960373535609315 206750096663940560303413973)
          ·
            refine ⟨4845705390561106882111265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 206750096663940560303413973 4845705390561106882111265)
            ·
              refine ⟨3634279042920830161583449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4845705390561106882111265 3634279042920830161583449)
              ·
                refine ⟨2725709282190622621187587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3634279042920830161583449 2725709282190622621187587)
                ·
                  refine ⟨4088563923285933931781381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2725709282190622621187587 4088563923285933931781381)
                  ·
                    refine ⟨766605735616112612209009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4088563923285933931781381 766605735616112612209009)
                    ·
                      rfl

theorem cell22_2239439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 4].length) (baseStart_2239439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239439 prefixEnd_2239439 := by exact prefixLift 2239439
  have htrace : WordTrace (prefixWord ++ tailWord_2239439) baseStart_2239439 baseEnd_2239439 := by
    simpa [prefixWord, tailWord_2239439, baseEnd_2239439] using wordTrace_append hprefix tailTrace_2239439
  have hstable : (prefixWord ++ tailWord_2239439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239439).length < 2 ^ (prefixWord ++ tailWord_2239439).sum := by decide
  have hdescent : baseEnd_2239439 < baseStart_2239439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239471 : List Nat := [1, 1, 2, 1, 4, 4, 3, 2, 4]
def baseStart_2239471 : Nat := 118140960795 + 2239471 * 2 ^ 59
def prefixEnd_2239471 : Nat := 4983230072969 + 3 ^ 40 * 2239471 * 2
def baseEnd_2239471 : Nat := 255538896623358398469637

theorem tailTrace_2239471 : CollatzResearch.WordTrace tailWord_2239471 prefixEnd_2239471 255538896623358398469637 := by
  unfold tailWord_2239471
  simp only [CollatzResearch.WordTrace]
  refine ⟨81680217669786513041822267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54453478446524342027881511 81680217669786513041822267)
  ·
    refine ⟨122520326504679769562733401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81680217669786513041822267 122520326504679769562733401)
    ·
      refine ⟨91890244878509827172050051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122520326504679769562733401 91890244878509827172050051)
      ·
        refine ⟨137835367317764740758075077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91890244878509827172050051 137835367317764740758075077)
        ·
          refine ⟨25844131372080888892139077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137835367317764740758075077 25844131372080888892139077)
          ·
            refine ⟨4845774632265166667276077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25844131372080888892139077 4845774632265166667276077)
            ·
              refine ⟨1817165487099437500228529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4845774632265166667276077 1817165487099437500228529)
              ·
                refine ⟨1362874115324578125171397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1817165487099437500228529 1362874115324578125171397)
                ·
                  refine ⟨255538896623358398469637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1362874115324578125171397 255538896623358398469637)
                  ·
                    rfl

theorem cell22_2239471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 4].length) (baseStart_2239471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239471 prefixEnd_2239471 := by exact prefixLift 2239471
  have htrace : WordTrace (prefixWord ++ tailWord_2239471) baseStart_2239471 baseEnd_2239471 := by
    simpa [prefixWord, tailWord_2239471, baseEnd_2239471] using wordTrace_append hprefix tailTrace_2239471
  have hstable : (prefixWord ++ tailWord_2239471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239471).length < 2 ^ (prefixWord ++ tailWord_2239471).sum := by decide
  have hdescent : baseEnd_2239471 < baseStart_2239471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239490 : List Nat := [3, 4, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_2239490 : Nat := 118140960795 + 2239490 * 2 ^ 59
def prefixEnd_2239490 : Nat := 4983230072969 + 3 ^ 40 * 2239490 * 2
def baseEnd_2239490 : Nat := 766623193958365479183853

theorem tailTrace_2239490 : CollatzResearch.WordTrace tailWord_2239490 prefixEnd_2239490 766623193958365479183853 := by
  unfold tailWord_2239490
  simp only [CollatzResearch.WordTrace]
  refine ⟨20420227664179419821690981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54453940437811786191175949 20420227664179419821690981)
  ·
    refine ⟨3828792687033641216567059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20420227664179419821690981 3828792687033641216567059)
    ·
      refine ⟨5743189030550461824850589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3828792687033641216567059 5743189030550461824850589)
      ·
        refine ⟨2153695886456423184318971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5743189030550461824850589 2153695886456423184318971)
        ·
          refine ⟨3230543829684634776478457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2153695886456423184318971 3230543829684634776478457)
          ·
            refine ⟨2422907872263476082358843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3230543829684634776478457 2422907872263476082358843)
            ·
              refine ⟨3634361808395214123538265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2422907872263476082358843 3634361808395214123538265)
              ·
                refine ⟨2725771356296410592653699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3634361808395214123538265 2725771356296410592653699)
                ·
                  refine ⟨4088657034444615888980549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2725771356296410592653699 4088657034444615888980549)
                  ·
                    refine ⟨766623193958365479183853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4088657034444615888980549 766623193958365479183853)
                    ·
                      rfl

theorem cell22_2239490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_2239490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239490 prefixEnd_2239490 := by exact prefixLift 2239490
  have htrace : WordTrace (prefixWord ++ tailWord_2239490) baseStart_2239490 baseEnd_2239490 := by
    simpa [prefixWord, tailWord_2239490, baseEnd_2239490] using wordTrace_append hprefix tailTrace_2239490
  have hstable : (prefixWord ++ tailWord_2239490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239490).length < 2 ^ (prefixWord ++ tailWord_2239490).sum := by decide
  have hdescent : baseEnd_2239490 < baseStart_2239490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239531 : List Nat := [1, 1, 1, 1, 2, 1, 7, 4, 1, 3]
def baseStart_2239531 : Nat := 118140960795 + 2239531 * 2 ^ 59
def prefixEnd_2239531 : Nat := 4983230072969 + 3 ^ 40 * 2239531 * 2
def baseEnd_2239531 : Nat := 766637229096255038908727

theorem tailTrace_2239531 : CollatzResearch.WordTrace tailWord_2239531 prefixEnd_2239531 766637229096255038908727 := by
  unfold tailWord_2239531
  simp only [CollatzResearch.WordTrace]
  refine ⟨81682406049569143289006447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54454937366379428859337631 81682406049569143289006447)
  ·
    refine ⟨122523609074353714933509671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81682406049569143289006447 122523609074353714933509671)
    ·
      refine ⟨183785413611530572400264507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122523609074353714933509671 183785413611530572400264507)
      ·
        refine ⟨275678120417295858600396761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183785413611530572400264507 275678120417295858600396761)
        ·
          refine ⟨206758590312971893950297571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275678120417295858600396761 206758590312971893950297571)
          ·
            refine ⟨310137885469457840925446357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206758590312971893950297571 310137885469457840925446357)
            ·
              refine ⟨7268856690690418146690149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 310137885469457840925446357 7268856690690418146690149)
              ·
                refine ⟨1362910629504453402504403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7268856690690418146690149 1362910629504453402504403)
                ·
                  refine ⟨2044365944256680103756605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1362910629504453402504403 2044365944256680103756605)
                  ·
                    refine ⟨766637229096255038908727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2044365944256680103756605 766637229096255038908727)
                    ·
                      rfl

theorem cell22_2239531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 1, 3].length) (baseStart_2239531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239531 prefixEnd_2239531 := by exact prefixLift 2239531
  have htrace : WordTrace (prefixWord ++ tailWord_2239531) baseStart_2239531 baseEnd_2239531 := by
    simpa [prefixWord, tailWord_2239531, baseEnd_2239531] using wordTrace_append hprefix tailTrace_2239531
  have hstable : (prefixWord ++ tailWord_2239531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239531).length < 2 ^ (prefixWord ++ tailWord_2239531).sum := by decide
  have hdescent : baseEnd_2239531 < baseStart_2239531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239544 : List Nat := [2, 1, 2, 1, 5, 1, 2, 3, 5]
def baseStart_2239544 : Nat := 118140960795 + 2239544 * 2 ^ 59
def prefixEnd_2239544 : Nat := 4983230072969 + 3 ^ 40 * 2239544 * 2
def baseEnd_2239544 : Nat := 255547226420642446111229

theorem tailTrace_2239544 : CollatzResearch.WordTrace tailWord_2239544 prefixEnd_2239544 255547226420642446111229 := by
  unfold tailWord_2239544
  simp only [CollatzResearch.WordTrace]
  refine ⟨40841440099261023254614843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54455253465681364339486457 40841440099261023254614843)
  ·
    refine ⟨61262160148891534881922265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40841440099261023254614843 61262160148891534881922265)
    ·
      refine ⟨45946620111668651161441699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61262160148891534881922265 45946620111668651161441699)
      ·
        refine ⟨68919930167502976742162549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45946620111668651161441699 68919930167502976742162549)
        ·
          refine ⟨6461243453203404069577739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68919930167502976742162549 6461243453203404069577739)
          ·
            refine ⟨9691865179805106104366609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6461243453203404069577739 9691865179805106104366609)
            ·
              refine ⟨7268898884853829578274957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9691865179805106104366609 7268898884853829578274957)
              ·
                refine ⟨2725837081820186091853109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7268898884853829578274957 2725837081820186091853109)
                ·
                  refine ⟨255547226420642446111229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2725837081820186091853109 255547226420642446111229)
                  ·
                    rfl

theorem cell22_2239544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 5].length) (baseStart_2239544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239544 prefixEnd_2239544 := by exact prefixLift 2239544
  have htrace : WordTrace (prefixWord ++ tailWord_2239544) baseStart_2239544 baseEnd_2239544 := by
    simpa [prefixWord, tailWord_2239544, baseEnd_2239544] using wordTrace_append hprefix tailTrace_2239544
  have hstable : (prefixWord ++ tailWord_2239544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239544).length < 2 ^ (prefixWord ++ tailWord_2239544).sum := by decide
  have hdescent : baseEnd_2239544 < baseStart_2239544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239565 : List Nat := [1, 6, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_2239565 : Nat := 118140960795 + 2239565 * 2 ^ 59
def prefixEnd_2239565 : Nat := 4983230072969 + 3 ^ 40 * 2239565 * 2
def baseEnd_2239565 : Nat := 766648867991090283558623

theorem tailTrace_2239565 : CollatzResearch.WordTrace tailWord_2239565 prefixEnd_2239565 766648867991090283558623 := by
  unfold tailWord_2239565
  simp only [CollatzResearch.WordTrace]
  refine ⟨81683646131445967095744149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54455764087630644730496099 81683646131445967095744149)
  ·
    refine ⟨3828920912411529707613007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81683646131445967095744149 3828920912411529707613007)
    ·
      refine ⟨5743381368617294561419511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3828920912411529707613007 5743381368617294561419511)
      ·
        refine ⟨8615072052925941842129267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5743381368617294561419511 8615072052925941842129267)
        ·
          refine ⟨12922608079388912763193901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8615072052925941842129267 12922608079388912763193901)
          ·
            refine ⟨4845978029770842286197713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12922608079388912763193901 4845978029770842286197713)
            ·
              refine ⟨3634483522328131714648285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4845978029770842286197713 3634483522328131714648285)
              ·
                refine ⟨1362931320873049392993107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3634483522328131714648285 1362931320873049392993107)
                ·
                  refine ⟨2044396981309574089489661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1362931320873049392993107 2044396981309574089489661)
                  ·
                    refine ⟨766648867991090283558623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2044396981309574089489661 766648867991090283558623)
                    ·
                      rfl

theorem cell22_2239565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_2239565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239565 prefixEnd_2239565 := by exact prefixLift 2239565
  have htrace : WordTrace (prefixWord ++ tailWord_2239565) baseStart_2239565 baseEnd_2239565 := by
    simpa [prefixWord, tailWord_2239565, baseEnd_2239565] using wordTrace_append hprefix tailTrace_2239565
  have hstable : (prefixWord ++ tailWord_2239565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239565).length < 2 ^ (prefixWord ++ tailWord_2239565).sum := by decide
  have hdescent : baseEnd_2239565 < baseStart_2239565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239582 : List Nat := [4, 4, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_2239582 : Nat := 118140960795 + 2239582 * 2 ^ 59
def prefixEnd_2239582 : Nat := 4983230072969 + 3 ^ 40 * 2239582 * 2
def baseEnd_2239582 : Nat := 766654687438507905883571

theorem tailTrace_2239582 : CollatzResearch.WordTrace tailWord_2239582 prefixEnd_2239582 766654687438507905883571 := by
  unfold tailWord_2239582
  simp only [CollatzResearch.WordTrace]
  refine ⟨10210533271548047374889125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54456177448256252666075333 10210533271548047374889125)
  ·
    refine ⟨1914474988415258882791711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10210533271548047374889125 1914474988415258882791711)
    ·
      refine ⟨2871712482622888324187567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1914474988415258882791711 2871712482622888324187567)
      ·
        refine ⟨4307568723934332486281351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2871712482622888324187567 4307568723934332486281351)
        ·
          refine ⟨6461353085901498729422027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4307568723934332486281351 6461353085901498729422027)
          ·
            refine ⟨9692029628852248094133041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6461353085901498729422027 9692029628852248094133041)
            ·
              refine ⟨7269022221639186070599781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9692029628852248094133041 7269022221639186070599781)
              ·
                refine ⟨1362941666557347388237459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7269022221639186070599781 1362941666557347388237459)
                ·
                  refine ⟨2044412499836021082356189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1362941666557347388237459 2044412499836021082356189)
                  ·
                    refine ⟨766654687438507905883571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2044412499836021082356189 766654687438507905883571)
                    ·
                      rfl

theorem cell22_2239582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_2239582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239582 prefixEnd_2239582 := by exact prefixLift 2239582
  have htrace : WordTrace (prefixWord ++ tailWord_2239582) baseStart_2239582 baseEnd_2239582 := by
    simpa [prefixWord, tailWord_2239582, baseEnd_2239582] using wordTrace_append hprefix tailTrace_2239582
  have hstable : (prefixWord ++ tailWord_2239582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239582).length < 2 ^ (prefixWord ++ tailWord_2239582).sum := by decide
  have hdescent : baseEnd_2239582 < baseStart_2239582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239589 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 6]
def baseStart_2239589 : Nat := 118140960795 + 2239589 * 2 ^ 59
def prefixEnd_2239589 : Nat := 4983230072969 + 3 ^ 40 * 2239589 * 2
def baseEnd_2239589 : Nat := 255552361227187406986183

theorem tailTrace_2239589 : CollatzResearch.WordTrace tailWord_2239589 prefixEnd_2239589 255552361227187406986183 := by
  unfold tailWord_2239589
  simp only [CollatzResearch.WordTrace]
  refine ⟨81684521483359019194617821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54456347655572679463078547 81684521483359019194617821)
  ·
    refine ⟨30631695556259632197981683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81684521483359019194617821 30631695556259632197981683)
    ·
      refine ⟨45947543334389448296972525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30631695556259632197981683 45947543334389448296972525)
      ·
        refine ⟨17230328750396043111364697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45947543334389448296972525 17230328750396043111364697)
        ·
          refine ⟨12922746562797032333523523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17230328750396043111364697 12922746562797032333523523)
          ·
            refine ⟨19384119844195548500285285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12922746562797032333523523 19384119844195548500285285)
            ·
              refine ⟨3634522470786665343803491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19384119844195548500285285 3634522470786665343803491)
              ·
                refine ⟨5451783706179998015705237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3634522470786665343803491 5451783706179998015705237)
                ·
                  refine ⟨255552361227187406986183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5451783706179998015705237 255552361227187406986183)
                  ·
                    rfl

theorem cell22_2239589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_2239589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239589 prefixEnd_2239589 := by exact prefixLift 2239589
  have htrace : WordTrace (prefixWord ++ tailWord_2239589) baseStart_2239589 baseEnd_2239589 := by
    simpa [prefixWord, tailWord_2239589, baseEnd_2239589] using wordTrace_append hprefix tailTrace_2239589
  have hstable : (prefixWord ++ tailWord_2239589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239589).length < 2 ^ (prefixWord ++ tailWord_2239589).sum := by decide
  have hdescent : baseEnd_2239589 < baseStart_2239589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239619 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 2, 4]
def baseStart_2239619 : Nat := 118140960795 + 2239619 * 2 ^ 59
def prefixEnd_2239619 : Nat := 4983230072969 + 3 ^ 40 * 2239619 * 2
def baseEnd_2239619 : Nat := 766667353294652142708457

theorem tailTrace_2239619 : CollatzResearch.WordTrace tailWord_2239619 prefixEnd_2239619 766667353294652142708457 := by
  unfold tailWord_2239619
  simp only [CollatzResearch.WordTrace]
  refine ⟨81685615673250334318209911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54457077115500222878806607 81685615673250334318209911)
  ·
    refine ⟨122528423509875501477314867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81685615673250334318209911 122528423509875501477314867)
    ·
      refine ⟨183792635264813252215972301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122528423509875501477314867 183792635264813252215972301)
      ·
        refine ⟨68922238224304969580989613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183792635264813252215972301 68922238224304969580989613)
        ·
          refine ⟨25845839334114363592871105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68922238224304969580989613 25845839334114363592871105)
          ·
            refine ⟨19384379500585772694653329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25845839334114363592871105 19384379500585772694653329)
            ·
              refine ⟨14538284625439329520989997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19384379500585772694653329 14538284625439329520989997)
              ·
                refine ⟨5451856734539748570371249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14538284625439329520989997 5451856734539748570371249)
                ·
                  refine ⟨4088892550904811427778437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5451856734539748570371249 4088892550904811427778437)
                  ·
                    refine ⟨766667353294652142708457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4088892550904811427778437 766667353294652142708457)
                    ·
                      rfl

theorem cell22_2239619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 4].length) (baseStart_2239619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239619 prefixEnd_2239619 := by exact prefixLift 2239619
  have htrace : WordTrace (prefixWord ++ tailWord_2239619) baseStart_2239619 baseEnd_2239619 := by
    simpa [prefixWord, tailWord_2239619, baseEnd_2239619] using wordTrace_append hprefix tailTrace_2239619
  have hstable : (prefixWord ++ tailWord_2239619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239619).length < 2 ^ (prefixWord ++ tailWord_2239619).sum := by decide
  have hdescent : baseEnd_2239619 < baseStart_2239619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239634 : List Nat := [3, 2, 3, 1, 1, 2, 10]
def baseStart_2239634 : Nat := 118140960795 + 2239634 * 2 ^ 59
def prefixEnd_2239634 : Nat := 4983230072969 + 3 ^ 40 * 2239634 * 2
def baseEnd_2239634 : Nat := 28395277337081374206793

theorem tailTrace_2239634 : CollatzResearch.WordTrace tailWord_2239634 prefixEnd_2239634 28395277337081374206793 := by
  unfold tailWord_2239634
  simp only [CollatzResearch.WordTrace]
  refine ⟨20421540692048997970001489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54457441845463994586670637 20421540692048997970001489)
  ·
    refine ⟨15316155519036748477501117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20421540692048997970001489 15316155519036748477501117)
    ·
      refine ⟨5743558319638780679062919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15316155519036748477501117 5743558319638780679062919)
      ·
        refine ⟨8615337479458171018594379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5743558319638780679062919 8615337479458171018594379)
        ·
          refine ⟨12923006219187256527891569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8615337479458171018594379 12923006219187256527891569)
          ·
            refine ⟨9692254664390442395918677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12923006219187256527891569 9692254664390442395918677)
            ·
              refine ⟨28395277337081374206793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9692254664390442395918677 28395277337081374206793)
              ·
                rfl

theorem cell22_2239634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 10].length) (baseStart_2239634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239634 prefixEnd_2239634 := by exact prefixLift 2239634
  have htrace : WordTrace (prefixWord ++ tailWord_2239634) baseStart_2239634 baseEnd_2239634 := by
    simpa [prefixWord, tailWord_2239634, baseEnd_2239634] using wordTrace_append hprefix tailTrace_2239634
  have hstable : (prefixWord ++ tailWord_2239634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239634).length < 2 ^ (prefixWord ++ tailWord_2239634).sum := by decide
  have hdescent : baseEnd_2239634 < baseStart_2239634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239655 : List Nat := [1, 1, 6, 2, 1, 1, 4, 1, 2, 3]
def baseStart_2239655 : Nat := 118140960795 + 2239655 * 2 ^ 59
def prefixEnd_2239655 : Nat := 4983230072969 + 3 ^ 40 * 2239655 * 2
def baseEnd_2239655 : Nat := 766679676830360048808347

theorem tailTrace_2239655 : CollatzResearch.WordTrace tailWord_2239655 prefixEnd_2239655 766679676830360048808347 := by
  unfold tailWord_2239655
  simp only [CollatzResearch.WordTrace]
  refine ⟨81686928701119912466520419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54457952467413274977680279 81686928701119912466520419)
  ·
    refine ⟨122530393051679868699780629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81686928701119912466520419 122530393051679868699780629)
    ·
      refine ⟨5743612174297493845302217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 122530393051679868699780629 5743612174297493845302217)
      ·
        refine ⟨4307709130723120383976663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5743612174297493845302217 4307709130723120383976663)
        ·
          refine ⟨6461563696084680575964995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4307709130723120383976663 6461563696084680575964995)
          ·
            refine ⟨9692345544127020863947493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6461563696084680575964995 9692345544127020863947493)
            ·
              refine ⟨1817314789523816411990155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9692345544127020863947493 1817314789523816411990155)
              ·
                refine ⟨2725972184285724617985233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1817314789523816411990155 2725972184285724617985233)
                ·
                  refine ⟨2044479138214293463488925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2725972184285724617985233 2044479138214293463488925)
                  ·
                    refine ⟨766679676830360048808347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2044479138214293463488925 766679676830360048808347)
                    ·
                      rfl

theorem cell22_2239655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_2239655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239655 prefixEnd_2239655 := by exact prefixLift 2239655
  have htrace : WordTrace (prefixWord ++ tailWord_2239655) baseStart_2239655 baseEnd_2239655 := by
    simpa [prefixWord, tailWord_2239655, baseEnd_2239655] using wordTrace_append hprefix tailTrace_2239655
  have hstable : (prefixWord ++ tailWord_2239655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239655).length < 2 ^ (prefixWord ++ tailWord_2239655).sum := by decide
  have hdescent : baseEnd_2239655 < baseStart_2239655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239724 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 8]
def baseStart_2239724 : Nat := 118140960795 + 2239724 * 2 ^ 59
def prefixEnd_2239724 : Nat := 4983230072969 + 3 ^ 40 * 2239724 * 2
def baseEnd_2239724 : Nat := 255567765646822289611045

theorem tailTrace_2239724 : CollatzResearch.WordTrace tailWord_2239724 prefixEnd_2239724 255567765646822289611045 := by
  unfold tailWord_2239724
  simp only [CollatzResearch.WordTrace]
  refine ⟨40844722668934968625391113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54459630225246624833854817 40844722668934968625391113)
  ·
    refine ⟨30633542001701226469043335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40844722668934968625391113 30633542001701226469043335)
    ·
      refine ⟨45950313002551839703565003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30633542001701226469043335 45950313002551839703565003)
      ·
        refine ⟨68925469503827759555347505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45950313002551839703565003 68925469503827759555347505)
        ·
          refine ⟨51694102127870819666510629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68925469503827759555347505 51694102127870819666510629)
          ·
            refine ⟨9692644148975778687470743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51694102127870819666510629 9692644148975778687470743)
            ·
              refine ⟨14538966223463668031206115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9692644148975778687470743 14538966223463668031206115)
              ·
                refine ⟨21808449335195502046809173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14538966223463668031206115 21808449335195502046809173)
                ·
                  refine ⟨255567765646822289611045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21808449335195502046809173 255567765646822289611045)
                  ·
                    rfl

theorem cell22_2239724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_2239724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239724 prefixEnd_2239724 := by exact prefixLift 2239724
  have htrace : WordTrace (prefixWord ++ tailWord_2239724) baseStart_2239724 baseEnd_2239724 := by
    simpa [prefixWord, tailWord_2239724, baseEnd_2239724] using wordTrace_append hprefix tailTrace_2239724
  have hstable : (prefixWord ++ tailWord_2239724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239724).length < 2 ^ (prefixWord ++ tailWord_2239724).sum := by decide
  have hdescent : baseEnd_2239724 < baseStart_2239724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239726 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2239726 : Nat := 118140960795 + 2239726 * 2 ^ 59
def prefixEnd_2239726 : Nat := 4983230072969 + 3 ^ 40 * 2239726 * 2
def baseEnd_2239726 : Nat := 766703981581339530283129

theorem tailTrace_2239726 : CollatzResearch.WordTrace tailWord_2239726 prefixEnd_2239726 766703981581339530283129 := by
  unfold tailWord_2239726
  simp only [CollatzResearch.WordTrace]
  refine ⟨10211189785482836449044379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54459678855908461061570021 10211189785482836449044379)
  ·
    refine ⟨15316784678224254673566569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10211189785482836449044379 15316784678224254673566569)
    ·
      refine ⟨11487588508668191005174927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15316784678224254673566569 11487588508668191005174927)
      ·
        refine ⟨17231382763002286507762391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11487588508668191005174927 17231382763002286507762391)
        ·
          refine ⟨25847074144503429761643587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17231382763002286507762391 25847074144503429761643587)
          ·
            refine ⟨38770611216755144642465381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25847074144503429761643587 38770611216755144642465381)
            ·
              refine ⟨7269489603141589620462259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38770611216755144642465381 7269489603141589620462259)
              ·
                refine ⟨10904234404712384430693389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7269489603141589620462259 10904234404712384430693389)
                ·
                  refine ⟨4089087901767144161510021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10904234404712384430693389 4089087901767144161510021)
                  ·
                    refine ⟨766703981581339530283129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4089087901767144161510021 766703981581339530283129)
                    ·
                      rfl

theorem cell22_2239726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2239726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239726 prefixEnd_2239726 := by exact prefixLift 2239726
  have htrace : WordTrace (prefixWord ++ tailWord_2239726) baseStart_2239726 baseEnd_2239726 := by
    simpa [prefixWord, tailWord_2239726, baseEnd_2239726] using wordTrace_append hprefix tailTrace_2239726
  have hstable : (prefixWord ++ tailWord_2239726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239726).length < 2 ^ (prefixWord ++ tailWord_2239726).sum := by decide
  have hdescent : baseEnd_2239726 < baseStart_2239726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239743 : List Nat := [1, 1, 2, 2, 1, 5, 4, 1, 1, 4]
def baseStart_2239743 : Nat := 118140960795 + 2239743 * 2 ^ 59
def prefixEnd_2239743 : Nat := 4983230072969 + 3 ^ 40 * 2239743 * 2
def baseEnd_2239743 : Nat := 766709801028757152608077

theorem tailTrace_2239743 : CollatzResearch.WordTrace tailWord_2239743 prefixEnd_2239743 766709801028757152608077 := by
  unfold tailWord_2239743
  simp only [CollatzResearch.WordTrace]
  refine ⟨81690138324801103495723883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54460092216534068997149255 81690138324801103495723883)
  ·
    refine ⟨122535207487201655243585825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81690138324801103495723883 122535207487201655243585825)
    ·
      refine ⟨91901405615401241432689369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122535207487201655243585825 91901405615401241432689369)
      ·
        refine ⟨68926054211550931074517027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91901405615401241432689369 68926054211550931074517027)
        ·
          refine ⟨103389081317326396611775541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68926054211550931074517027 103389081317326396611775541)
          ·
            refine ⟨9692726373499349682353957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103389081317326396611775541 9692726373499349682353957)
            ·
              refine ⟨1817386195031128065441367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9692726373499349682353957 1817386195031128065441367)
              ·
                refine ⟨2726079292546692098162051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1817386195031128065441367 2726079292546692098162051)
                ·
                  refine ⟨4089118938820038147243077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2726079292546692098162051 4089118938820038147243077)
                  ·
                    refine ⟨766709801028757152608077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4089118938820038147243077 766709801028757152608077)
                    ·
                      rfl

theorem cell22_2239743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 1, 4].length) (baseStart_2239743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239743 prefixEnd_2239743 := by exact prefixLift 2239743
  have htrace : WordTrace (prefixWord ++ tailWord_2239743) baseStart_2239743 baseEnd_2239743 := by
    simpa [prefixWord, tailWord_2239743, baseEnd_2239743] using wordTrace_append hprefix tailTrace_2239743
  have hstable : (prefixWord ++ tailWord_2239743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239743).length < 2 ^ (prefixWord ++ tailWord_2239743).sum := by decide
  have hdescent : baseEnd_2239743 < baseStart_2239743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239758 : List Nat := [4, 1, 1, 2, 1, 3, 2, 4, 4]
def baseStart_2239758 : Nat := 118140960795 + 2239758 * 2 ^ 59
def prefixEnd_2239758 : Nat := 4983230072969 + 3 ^ 40 * 2239758 * 2
def baseEnd_2239758 : Nat := 255571645278434037827677

theorem tailTrace_2239758 : CollatzResearch.WordTrace tailWord_2239758 prefixEnd_2239758 255571645278434037827677 := by
  unfold tailWord_2239758
  simp only [CollatzResearch.WordTrace]
  refine ⟨10211335677468345132189991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54460456946497840705013285 10211335677468345132189991)
  ·
    refine ⟨15317003516202517698284987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10211335677468345132189991 15317003516202517698284987)
    ·
      refine ⟨22975505274303776547427481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15317003516202517698284987 22975505274303776547427481)
      ·
        refine ⟨17231628955727832410570611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22975505274303776547427481 17231628955727832410570611)
        ·
          refine ⟨25847443433591748615855917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17231628955727832410570611 25847443433591748615855917)
          ·
            refine ⟨9692791287596905730945969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25847443433591748615855917 9692791287596905730945969)
            ·
              refine ⟨7269593465697679298209477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9692791287596905730945969 7269593465697679298209477)
              ·
                refine ⟨1363048774818314868414277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7269593465697679298209477 1363048774818314868414277)
                ·
                  refine ⟨255571645278434037827677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1363048774818314868414277 255571645278434037827677)
                  ·
                    rfl

theorem cell22_2239758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_2239758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239758 prefixEnd_2239758 := by exact prefixLift 2239758
  have htrace : WordTrace (prefixWord ++ tailWord_2239758) baseStart_2239758 baseEnd_2239758 := by
    simpa [prefixWord, tailWord_2239758, baseEnd_2239758] using wordTrace_append hprefix tailTrace_2239758
  have hstable : (prefixWord ++ tailWord_2239758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239758).length < 2 ^ (prefixWord ++ tailWord_2239758).sum := by decide
  have hdescent : baseEnd_2239758 < baseStart_2239758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239773 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_2239773 : Nat := 118140960795 + 2239773 * 2 ^ 59
def prefixEnd_2239773 : Nat := 4983230072969 + 3 ^ 40 * 2239773 * 2
def baseEnd_2239773 : Nat := 766720070641847074357985

theorem tailTrace_2239773 : CollatzResearch.WordTrace tailWord_2239773 prefixEnd_2239773 766720070641847074357985 := by
  unfold tailWord_2239773
  simp only [CollatzResearch.WordTrace]
  refine ⟨81691232514692418619315973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54460821676461612412877315 81691232514692418619315973)
  ·
    refine ⟨15317106096504828491121745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81691232514692418619315973 15317106096504828491121745)
    ·
      refine ⟨11487829572378621368341309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15317106096504828491121745 11487829572378621368341309)
      ·
        refine ⟨4307936089641983013127991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11487829572378621368341309 4307936089641983013127991)
        ·
          refine ⟨6461904134462974519691987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4307936089641983013127991 6461904134462974519691987)
          ·
            refine ⟨9692856201694461779537981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6461904134462974519691987 9692856201694461779537981)
            ·
              refine ⟨3634821075635423167326743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9692856201694461779537981 3634821075635423167326743)
              ·
                refine ⟨5452231613453134750990115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3634821075635423167326743 5452231613453134750990115)
                ·
                  refine ⟨8178347420179702126485173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5452231613453134750990115 8178347420179702126485173)
                  ·
                    refine ⟨766720070641847074357985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8178347420179702126485173 766720070641847074357985)
                    ·
                      rfl

theorem cell22_2239773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_2239773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239773 prefixEnd_2239773 := by exact prefixLift 2239773
  have htrace : WordTrace (prefixWord ++ tailWord_2239773) baseStart_2239773 baseEnd_2239773 := by
    simpa [prefixWord, tailWord_2239773, baseEnd_2239773] using wordTrace_append hprefix tailTrace_2239773
  have hstable : (prefixWord ++ tailWord_2239773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239773).length < 2 ^ (prefixWord ++ tailWord_2239773).sum := by decide
  have hdescent : baseEnd_2239773 < baseStart_2239773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239799 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 3, 8]
def baseStart_2239799 : Nat := 118140960795 + 2239799 * 2 ^ 59
def prefixEnd_2239799 : Nat := 4983230072969 + 3 ^ 40 * 2239799 * 2
def baseEnd_2239799 : Nat := 766728970973191673207905

theorem tailTrace_2239799 : CollatzResearch.WordTrace tailWord_2239799 prefixEnd_2239799 766728970973191673207905 := by
  unfold tailWord_2239799
  simp only [CollatzResearch.WordTrace]
  refine ⟨81692180812598225059762451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54461453875065483373174967 81692180812598225059762451)
  ·
    refine ⟨122538271218897337589643677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81692180812598225059762451 122538271218897337589643677)
    ·
      refine ⟨45951851707086501596116379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122538271218897337589643677 45951851707086501596116379)
      ·
        refine ⟨68927777560629752394174569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45951851707086501596116379 68927777560629752394174569)
        ·
          refine ⟨51695833170472314295630927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68927777560629752394174569 51695833170472314295630927)
          ·
            refine ⟨77543749755708471443446391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51695833170472314295630927 77543749755708471443446391)
            ·
              refine ⟨116315624633562707165169587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77543749755708471443446391 116315624633562707165169587)
              ·
                refine ⟨174473436950344060747754381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116315624633562707165169587 174473436950344060747754381)
                ·
                  refine ⟨65427538856379022780407893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174473436950344060747754381 65427538856379022780407893)
                  ·
                    refine ⟨766728970973191673207905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65427538856379022780407893 766728970973191673207905)
                    ·
                      rfl

theorem cell22_2239799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_2239799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239799 prefixEnd_2239799 := by exact prefixLift 2239799
  have htrace : WordTrace (prefixWord ++ tailWord_2239799) baseStart_2239799 baseEnd_2239799 := by
    simpa [prefixWord, tailWord_2239799, baseEnd_2239799] using wordTrace_append hprefix tailTrace_2239799
  have hstable : (prefixWord ++ tailWord_2239799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239799).length < 2 ^ (prefixWord ++ tailWord_2239799).sum := by decide
  have hdescent : baseEnd_2239799 < baseStart_2239799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239805 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 2, 4]
def baseStart_2239805 : Nat := 118140960795 + 2239805 * 2 ^ 59
def prefixEnd_2239805 : Nat := 4983230072969 + 3 ^ 40 * 2239805 * 2
def baseEnd_2239805 : Nat := 766731024895809657557887

theorem tailTrace_2239805 : CollatzResearch.WordTrace tailWord_2239805 prefixEnd_2239805 766731024895809657557887 := by
  unfold tailWord_2239805
  simp only [CollatzResearch.WordTrace]
  refine ⟨81692399650576488084480869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54461599767050992056320579 81692399650576488084480869)
  ·
    refine ⟨15317324934483091515840163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81692399650576488084480869 15317324934483091515840163)
    ·
      refine ⟨22975987401724637273760245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15317324934483091515840163 22975987401724637273760245)
      ·
        refine ⟨2153998818911684744415023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22975987401724637273760245 2153998818911684744415023)
        ·
          refine ⟨3230998228367527116622535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2153998818911684744415023 3230998228367527116622535)
          ·
            refine ⟨4846497342551290674933803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3230998228367527116622535 4846497342551290674933803)
            ·
              refine ⟨7269746013826936012400705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4846497342551290674933803 7269746013826936012400705)
              ·
                refine ⟨5452309510370202009300529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7269746013826936012400705 5452309510370202009300529)
                ·
                  refine ⟨4089232132777651506975397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5452309510370202009300529 4089232132777651506975397)
                  ·
                    refine ⟨766731024895809657557887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4089232132777651506975397 766731024895809657557887)
                    ·
                      rfl

theorem cell22_2239805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_2239805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239805 prefixEnd_2239805 := by exact prefixLift 2239805
  have htrace : WordTrace (prefixWord ++ tailWord_2239805) baseStart_2239805 baseEnd_2239805 := by
    simpa [prefixWord, tailWord_2239805, baseEnd_2239805] using wordTrace_append hprefix tailTrace_2239805
  have hstable : (prefixWord ++ tailWord_2239805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239805).length < 2 ^ (prefixWord ++ tailWord_2239805).sum := by decide
  have hdescent : baseEnd_2239805 < baseStart_2239805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239908 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 4, 3]
def baseStart_2239908 : Nat := 118140960795 + 2239908 * 2 ^ 59
def prefixEnd_2239908 : Nat := 4983230072969 + 3 ^ 40 * 2239908 * 2
def baseEnd_2239908 : Nat := 766766283900751722232571

theorem tailTrace_2239908 : CollatzResearch.WordTrace tailWord_2239908 prefixEnd_2239908 766766283900751722232571 := by
  unfold tailWord_2239908
  simp only [CollatzResearch.WordTrace]
  refine ⟨40848078184601668337740189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54464104246135557783653585 40848078184601668337740189)
  ·
    refine ⟨15318029319225625626652571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40848078184601668337740189 15318029319225625626652571)
    ·
      refine ⟨22977043978838438439978857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15318029319225625626652571 22977043978838438439978857)
      ·
        refine ⟨17232782984128828829984143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22977043978838438439978857 17232782984128828829984143)
        ·
          refine ⟨25849174476193243244976215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17232782984128828829984143 25849174476193243244976215)
          ·
            refine ⟨38773761714289864867464323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25849174476193243244976215 38773761714289864867464323)
            ·
              refine ⟨58160642571434797301196485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38773761714289864867464323 58160642571434797301196485)
              ·
                refine ⟨10905120482144024493974341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58160642571434797301196485 10905120482144024493974341)
                ·
                  refine ⟨2044710090402004592620189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10905120482144024493974341 2044710090402004592620189)
                  ·
                    refine ⟨766766283900751722232571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2044710090402004592620189 766766283900751722232571)
                    ·
                      rfl

theorem cell22_2239908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_2239908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239908 prefixEnd_2239908 := by exact prefixLift 2239908
  have htrace : WordTrace (prefixWord ++ tailWord_2239908) baseStart_2239908 baseEnd_2239908 := by
    simpa [prefixWord, tailWord_2239908, baseEnd_2239908] using wordTrace_append hprefix tailTrace_2239908
  have hstable : (prefixWord ++ tailWord_2239908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239908).length < 2 ^ (prefixWord ++ tailWord_2239908).sum := by decide
  have hdescent : baseEnd_2239908 < baseStart_2239908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239912 : List Nat := [2, 1, 6, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2239912 : Nat := 118140960795 + 2239912 * 2 ^ 59
def prefixEnd_2239912 : Nat := 4983230072969 + 3 ^ 40 * 2239912 * 2
def baseEnd_2239912 : Nat := 766767653182497045132559

theorem tailTrace_2239912 : CollatzResearch.WordTrace tailWord_2239912 prefixEnd_2239912 766767653182497045132559 := by
  unfold tailWord_2239912
  simp only [CollatzResearch.WordTrace]
  refine ⟨40848151130594422679312995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54464201507459230239083993 40848151130594422679312995)
  ·
    refine ⟨61272226695891634018969493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40848151130594422679312995 61272226695891634018969493)
    ·
      refine ⟨2872135626369920344639195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 61272226695891634018969493 2872135626369920344639195)
      ·
        refine ⟨4308203439554880516958793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2872135626369920344639195 4308203439554880516958793)
        ·
          refine ⟨3231152579666160387719095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4308203439554880516958793 3231152579666160387719095)
          ·
            refine ⟨4846728869499240581578643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3231152579666160387719095 4846728869499240581578643)
            ·
              refine ⟨7270093304248860872367965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4846728869499240581578643 7270093304248860872367965)
              ·
                refine ⟨2726284989093322827137987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7270093304248860872367965 2726284989093322827137987)
                ·
                  refine ⟨4089427483639984240706981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2726284989093322827137987 4089427483639984240706981)
                  ·
                    refine ⟨766767653182497045132559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4089427483639984240706981 766767653182497045132559)
                    ·
                      rfl

theorem cell22_2239912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2239912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239912 prefixEnd_2239912 := by exact prefixLift 2239912
  have htrace : WordTrace (prefixWord ++ tailWord_2239912) baseStart_2239912 baseEnd_2239912 := by
    simpa [prefixWord, tailWord_2239912, baseEnd_2239912] using wordTrace_append hprefix tailTrace_2239912
  have hstable : (prefixWord ++ tailWord_2239912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239912).length < 2 ^ (prefixWord ++ tailWord_2239912).sum := by decide
  have hdescent : baseEnd_2239912 < baseStart_2239912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239921 : List Nat := [1, 2, 2, 4, 1, 1, 11]
def baseStart_2239921 : Nat := 118140960795 + 2239921 * 2 ^ 59
def prefixEnd_2239921 : Nat := 4983230072969 + 3 ^ 40 * 2239921 * 2
def baseEnd_2239921 : Nat := 28398916076534223024353

theorem tailTrace_2239921 : CollatzResearch.WordTrace tailWord_2239921 prefixEnd_2239921 28398916076534223024353 := by
  unfold tailWord_2239921
  simp only [CollatzResearch.WordTrace]
  refine ⟨81696630518156239895703617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54464420345437493263802411 81696630518156239895703617)
  ·
    refine ⟨61272472888617179921777713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81696630518156239895703617 61272472888617179921777713)
    ·
      refine ⟨45954354666462884941333285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61272472888617179921777713 45954354666462884941333285)
      ·
        refine ⟨8616441499961790926499991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45954354666462884941333285 8616441499961790926499991)
        ·
          refine ⟨12924662249942686389749987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8616441499961790926499991 12924662249942686389749987)
          ·
            refine ⟨19386993374914029584624981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12924662249942686389749987 19386993374914029584624981)
            ·
              refine ⟨28398916076534223024353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19386993374914029584624981 28398916076534223024353)
              ·
                rfl

theorem cell22_2239921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 11].length) (baseStart_2239921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239921 prefixEnd_2239921 := by exact prefixLift 2239921
  have htrace : WordTrace (prefixWord ++ tailWord_2239921) baseStart_2239921 baseEnd_2239921 := by
    simpa [prefixWord, tailWord_2239921, baseEnd_2239921] using wordTrace_append hprefix tailTrace_2239921
  have hstable : (prefixWord ++ tailWord_2239921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239921).length < 2 ^ (prefixWord ++ tailWord_2239921).sum := by decide
  have hdescent : baseEnd_2239921 < baseStart_2239921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239925 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 4, 3]
def baseStart_2239925 : Nat := 118140960795 + 2239925 * 2 ^ 59
def prefixEnd_2239925 : Nat := 4983230072969 + 3 ^ 40 * 2239925 * 2
def baseEnd_2239925 : Nat := 766772103348169344557519

theorem tailTrace_2239925 : CollatzResearch.WordTrace tailWord_2239925 prefixEnd_2239925 766772103348169344557519 := by
  unfold tailWord_2239925
  simp only [CollatzResearch.WordTrace]
  refine ⟨81696776410141748578849229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54464517606761165719232819 81696776410141748578849229)
  ·
    refine ⟨30636291153803155717068461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81696776410141748578849229 30636291153803155717068461)
    ·
      refine ⟨11488609182676183393900673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30636291153803155717068461 11488609182676183393900673)
      ·
        refine ⟨8616456887007137545425505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11488609182676183393900673 8616456887007137545425505)
        ·
          refine ⟨6462342665255353159069129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8616456887007137545425505 6462342665255353159069129)
          ·
            refine ⟨4846756998941514869301847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6462342665255353159069129 4846756998941514869301847)
            ·
              refine ⟨7270135498412272303952771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4846756998941514869301847 7270135498412272303952771)
              ·
                refine ⟨10905203247618408455929157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7270135498412272303952771 10905203247618408455929157)
                ·
                  refine ⟨2044725608928451585486717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10905203247618408455929157 2044725608928451585486717)
                  ·
                    refine ⟨766772103348169344557519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2044725608928451585486717 766772103348169344557519)
                    ·
                      rfl

theorem cell22_2239925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_2239925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239925 prefixEnd_2239925 := by exact prefixLift 2239925
  have htrace : WordTrace (prefixWord ++ tailWord_2239925) baseStart_2239925 baseEnd_2239925 := by
    simpa [prefixWord, tailWord_2239925, baseEnd_2239925] using wordTrace_append hprefix tailTrace_2239925
  have hstable : (prefixWord ++ tailWord_2239925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239925).length < 2 ^ (prefixWord ++ tailWord_2239925).sum := by decide
  have hdescent : baseEnd_2239925 < baseStart_2239925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239951 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 2, 6]
def baseStart_2239951 : Nat := 118140960795 + 2239951 * 2 ^ 59
def prefixEnd_2239951 : Nat := 4983230072969 + 3 ^ 40 * 2239951 * 2
def baseEnd_2239951 : Nat := 766781003679513943407439

theorem tailTrace_2239951 : CollatzResearch.WordTrace tailWord_2239951 prefixEnd_2239951 766781003679513943407439 := by
  unfold tailWord_2239951
  simp only [CollatzResearch.WordTrace]
  refine ⟨81697724708047555019295707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54465149805365036679530471 81697724708047555019295707)
  ·
    refine ⟨122546587062071332528943561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81697724708047555019295707 122546587062071332528943561)
    ·
      refine ⟨91909940296553499396707671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122546587062071332528943561 91909940296553499396707671)
      ·
        refine ⟨137864910444830249095061507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91909940296553499396707671 137864910444830249095061507)
        ·
          refine ⟨206797365667245373642592261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137864910444830249095061507 206797365667245373642592261)
          ·
            refine ⟨38774506062608507557986049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206797365667245373642592261 38774506062608507557986049)
            ·
              refine ⟨29080879546956380668489537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38774506062608507557986049 29080879546956380668489537)
              ·
                refine ⟨21810659660217285501367153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29080879546956380668489537 21810659660217285501367153)
                ·
                  refine ⟨16357994745162964126025365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21810659660217285501367153 16357994745162964126025365)
                  ·
                    refine ⟨766781003679513943407439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16357994745162964126025365 766781003679513943407439)
                    ·
                      rfl

theorem cell22_2239951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_2239951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239951 prefixEnd_2239951 := by exact prefixLift 2239951
  have htrace : WordTrace (prefixWord ++ tailWord_2239951) baseStart_2239951 baseEnd_2239951 := by
    simpa [prefixWord, tailWord_2239951, baseEnd_2239951] using wordTrace_append hprefix tailTrace_2239951
  have hstable : (prefixWord ++ tailWord_2239951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239951).length < 2 ^ (prefixWord ++ tailWord_2239951).sum := by decide
  have hdescent : baseEnd_2239951 < baseStart_2239951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240058 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 1, 6]
def baseStart_2240058 : Nat := 118140960795 + 2240058 * 2 ^ 59
def prefixEnd_2240058 : Nat := 4983230072969 + 3 ^ 40 * 2240058 * 2
def baseEnd_2240058 : Nat := 766817631966201330982111

theorem tailTrace_2240058 : CollatzResearch.WordTrace tailWord_2240058 prefixEnd_2240058 766817631966201330982111 := by
  unfold tailWord_2240058
  simp only [CollatzResearch.WordTrace]
  refine ⟨20425406829664978073360207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54467751545773274862293885 20425406829664978073360207)
  ·
    refine ⟨30638110244497467110040311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20425406829664978073360207 30638110244497467110040311)
    ·
      refine ⟨45957165366746200665060467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30638110244497467110040311 45957165366746200665060467)
      ·
        refine ⟨68935748050119300997590701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45957165366746200665060467 68935748050119300997590701)
        ·
          refine ⟨25850905518794737874096513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68935748050119300997590701 25850905518794737874096513)
          ·
            refine ⟨19388179139096053405572385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25850905518794737874096513 19388179139096053405572385)
            ·
              refine ⟨14541134354322040054179289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19388179139096053405572385 14541134354322040054179289)
              ·
                refine ⟨10905850765741530040634467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14541134354322040054179289 10905850765741530040634467)
                ·
                  refine ⟨16358776148612295060951701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10905850765741530040634467 16358776148612295060951701)
                  ·
                    refine ⟨766817631966201330982111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16358776148612295060951701 766817631966201330982111)
                    ·
                      rfl

theorem cell22_2240058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_2240058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240058 prefixEnd_2240058 := by exact prefixLift 2240058
  have htrace : WordTrace (prefixWord ++ tailWord_2240058) baseStart_2240058 baseEnd_2240058 := by
    simpa [prefixWord, tailWord_2240058, baseEnd_2240058] using wordTrace_append hprefix tailTrace_2240058
  have hstable : (prefixWord ++ tailWord_2240058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240058).length < 2 ^ (prefixWord ++ tailWord_2240058).sum := by decide
  have hdescent : baseEnd_2240058 < baseStart_2240058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240103 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 1, 8]
def baseStart_2240103 : Nat := 118140960795 + 2240103 * 2 ^ 59
def prefixEnd_2240103 : Nat := 4983230072969 + 3 ^ 40 * 2240103 * 2
def baseEnd_2240103 : Nat := 766833036385836213606973

theorem tailTrace_2240103 : CollatzResearch.WordTrace tailWord_2240103 prefixEnd_2240103 766833036385836213606973 := by
  unfold tailWord_2240103
  simp only [CollatzResearch.WordTrace]
  refine ⟨81703268603496884978828963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54468845735664589985885975 81703268603496884978828963)
  ·
    refine ⟨122554902905245327468243445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81703268603496884978828963 122554902905245327468243445)
    ·
      refine ⟨11489522147366749450147823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122554902905245327468243445 11489522147366749450147823)
      ·
        refine ⟨17234283221050124175221735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11489522147366749450147823 17234283221050124175221735)
        ·
          refine ⟨25851424831575186262832603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17234283221050124175221735 25851424831575186262832603)
          ·
            refine ⟨38777137247362779394248905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25851424831575186262832603 38777137247362779394248905)
            ·
              refine ⟨29082852935522084545686679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38777137247362779394248905 29082852935522084545686679)
              ·
                refine ⟨43624279403283126818530019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29082852935522084545686679 43624279403283126818530019)
                ·
                  refine ⟨65436419104924690227795029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43624279403283126818530019 65436419104924690227795029)
                  ·
                    refine ⟨766833036385836213606973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65436419104924690227795029 766833036385836213606973)
                    ·
                      rfl

theorem cell22_2240103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_2240103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240103 prefixEnd_2240103 := by exact prefixLift 2240103
  have htrace : WordTrace (prefixWord ++ tailWord_2240103) baseStart_2240103 baseEnd_2240103 := by
    simpa [prefixWord, tailWord_2240103, baseEnd_2240103] using wordTrace_append hprefix tailTrace_2240103
  have hstable : (prefixWord ++ tailWord_2240103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240103).length < 2 ^ (prefixWord ++ tailWord_2240103).sum := by decide
  have hdescent : baseEnd_2240103 < baseStart_2240103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240105 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 3, 3]
def baseStart_2240105 : Nat := 118140960795 + 2240105 * 2 ^ 59
def prefixEnd_2240105 : Nat := 4983230072969 + 3 ^ 40 * 2240105 * 2
def baseEnd_2240105 : Nat := 766833721026708875056967

theorem tailTrace_2240105 : CollatzResearch.WordTrace tailWord_2240105 prefixEnd_2240105 766833721026708875056967 := by
  unfold tailWord_2240105
  simp only [CollatzResearch.WordTrace]
  refine ⟨81703341549489639320401769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54468894366326426213601179 81703341549489639320401769)
  ·
    refine ⟨61277506162117229490301327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81703341549489639320401769 61277506162117229490301327)
    ·
      refine ⟨91916259243175844235451991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61277506162117229490301327 91916259243175844235451991)
      ·
        refine ⟨137874388864763766353177987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91916259243175844235451991 137874388864763766353177987)
        ·
          refine ⟨206811583297145649529766981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137874388864763766353177987 206811583297145649529766981)
          ·
            refine ⟨38777171868214809286831309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206811583297145649529766981 38777171868214809286831309)
            ·
              refine ⟨14541439450580553482561741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38777171868214809286831309 14541439450580553482561741)
              ·
                refine ⟨5453039793967707555960653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14541439450580553482561741 5453039793967707555960653)
                ·
                  refine ⟨2044889922737890333485245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5453039793967707555960653 2044889922737890333485245)
                  ·
                    refine ⟨766833721026708875056967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2044889922737890333485245 766833721026708875056967)
                    ·
                      rfl

theorem cell22_2240105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 3].length) (baseStart_2240105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240105 prefixEnd_2240105 := by exact prefixLift 2240105
  have htrace : WordTrace (prefixWord ++ tailWord_2240105) baseStart_2240105 baseEnd_2240105 := by
    simpa [prefixWord, tailWord_2240105, baseEnd_2240105] using wordTrace_append hprefix tailTrace_2240105
  have hstable : (prefixWord ++ tailWord_2240105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240105).length < 2 ^ (prefixWord ++ tailWord_2240105).sum := by decide
  have hdescent : baseEnd_2240105 < baseStart_2240105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240156 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 3, 3]
def baseStart_2240156 : Nat := 118140960795 + 2240156 * 2 ^ 59
def prefixEnd_2240156 : Nat := 4983230072969 + 3 ^ 40 * 2240156 * 2
def baseEnd_2240156 : Nat := 766851179368961742031811

theorem tailTrace_2240156 : CollatzResearch.WordTrace tailWord_2240156 prefixEnd_2240156 766851179368961742031811 := by
  unfold tailWord_2240156
  simp only [CollatzResearch.WordTrace]
  refine ⟨40852600836152437515254161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54470134448203250020338881 40852600836152437515254161)
  ·
    refine ⟨30639450627114328136440621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40852600836152437515254161 30639450627114328136440621)
    ·
      refine ⟨11489793985167873051165233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30639450627114328136440621 11489793985167873051165233)
      ·
        refine ⟨8617345488875904788373925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11489793985167873051165233 8617345488875904788373925)
        ·
          refine ⟨1615752279164232147820111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8617345488875904788373925 1615752279164232147820111)
          ·
            refine ⟨2423628418746348221730167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1615752279164232147820111 2423628418746348221730167)
            ·
              refine ⟨3635442628119522332595251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2423628418746348221730167 3635442628119522332595251)
              ·
                refine ⟨5453163942179283498892877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3635442628119522332595251 5453163942179283498892877)
                ·
                  refine ⟨2044936478317231312084829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5453163942179283498892877 2044936478317231312084829)
                  ·
                    refine ⟨766851179368961742031811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2044936478317231312084829 766851179368961742031811)
                    ·
                      rfl

theorem cell22_2240156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_2240156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240156 prefixEnd_2240156 := by exact prefixLift 2240156
  have htrace : WordTrace (prefixWord ++ tailWord_2240156) baseStart_2240156 baseEnd_2240156 := by
    simpa [prefixWord, tailWord_2240156, baseEnd_2240156] using wordTrace_append hprefix tailTrace_2240156
  have hstable : (prefixWord ++ tailWord_2240156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240156).length < 2 ^ (prefixWord ++ tailWord_2240156).sum := by decide
  have hdescent : baseEnd_2240156 < baseStart_2240156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240242 : List Nat := [3, 2, 1, 3, 1, 1, 5, 6]
def baseStart_2240242 : Nat := 118140960795 + 2240242 * 2 ^ 59
def prefixEnd_2240242 : Nat := 4983230072969 + 3 ^ 40 * 2240242 * 2
def baseEnd_2240242 : Nat := 85208957658498464931283

theorem tailTrace_2240242 : CollatzResearch.WordTrace tailWord_2240242 prefixEnd_2240242 85208957658498464931283 := by
  unfold tailWord_2240242
  simp only [CollatzResearch.WordTrace]
  refine ⟨20427084587498327929534745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54472225566662207812092653 20427084587498327929534745)
  ·
    refine ⟨15320313440623745947151059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20427084587498327929534745 15320313440623745947151059)
    ·
      refine ⟨22980470160935618920726589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15320313440623745947151059 22980470160935618920726589)
      ·
        refine ⟨8617676310350857095272471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22980470160935618920726589 8617676310350857095272471)
        ·
          refine ⟨12926514465526285642908707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8617676310350857095272471 12926514465526285642908707)
          ·
            refine ⟨19389771698289428464363061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12926514465526285642908707 19389771698289428464363061)
            ·
              refine ⟨1817791096714633918534037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19389771698289428464363061 1817791096714633918534037)
              ·
                refine ⟨85208957658498464931283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1817791096714633918534037 85208957658498464931283)
                ·
                  rfl

theorem cell22_2240242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 6].length) (baseStart_2240242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240242 prefixEnd_2240242 := by exact prefixLift 2240242
  have htrace : WordTrace (prefixWord ++ tailWord_2240242) baseStart_2240242 baseEnd_2240242 := by
    simpa [prefixWord, tailWord_2240242, baseEnd_2240242] using wordTrace_append hprefix tailTrace_2240242
  have hstable : (prefixWord ++ tailWord_2240242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240242).length < 2 ^ (prefixWord ++ tailWord_2240242).sum := by decide
  have hdescent : baseEnd_2240242 < baseStart_2240242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240263 : List Nat := [1, 1, 4, 4, 3, 1, 1, 2, 2, 3]
def baseStart_2240263 : Nat := 118140960795 + 2240263 * 2 ^ 59
def prefixEnd_2240263 : Nat := 4983230072969 + 3 ^ 40 * 2240263 * 2
def baseEnd_2240263 : Nat := 766887807655649129606483

theorem tailTrace_2240263 : CollatzResearch.WordTrace tailWord_2240263 prefixEnd_2240263 766887807655649129606483 := by
  unfold tailWord_2240263
  simp only [CollatzResearch.WordTrace]
  refine ⟨81709104282917232304653443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54472736188611488203102295 81709104282917232304653443)
  ·
    refine ⟨122563656424375848456980165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81709104282917232304653443 122563656424375848456980165)
    ·
      refine ⟨22980685579570471585683781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122563656424375848456980165 22980685579570471585683781)
      ·
        refine ⟨4308878546169463422315709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22980685579570471585683781 4308878546169463422315709)
        ·
          refine ⟨1615829454813548783368391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4308878546169463422315709 1615829454813548783368391)
          ·
            refine ⟨2423744182220323175052587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1615829454813548783368391 2423744182220323175052587)
            ·
              refine ⟨3635616273330484762578881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2423744182220323175052587 3635616273330484762578881)
              ·
                refine ⟨2726712204997863571934161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3635616273330484762578881 2726712204997863571934161)
                ·
                  refine ⟨2045034153748397678950621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2726712204997863571934161 2045034153748397678950621)
                  ·
                    refine ⟨766887807655649129606483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2045034153748397678950621 766887807655649129606483)
                    ·
                      rfl

theorem cell22_2240263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_2240263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240263 prefixEnd_2240263 := by exact prefixLift 2240263
  have htrace : WordTrace (prefixWord ++ tailWord_2240263) baseStart_2240263 baseEnd_2240263 := by
    simpa [prefixWord, tailWord_2240263, baseEnd_2240263] using wordTrace_append hprefix tailTrace_2240263
  have hstable : (prefixWord ++ tailWord_2240263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240263).length < 2 ^ (prefixWord ++ tailWord_2240263).sum := by decide
  have hdescent : baseEnd_2240263 < baseStart_2240263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240308 : List Nat := [2, 5, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_2240308 : Nat := 118140960795 + 2240308 * 2 ^ 59
def prefixEnd_2240308 : Nat := 4983230072969 + 3 ^ 40 * 2240308 * 2
def baseEnd_2240308 : Nat := 766903212075284012231345

theorem tailTrace_2240308 : CollatzResearch.WordTrace tailWord_2240308 prefixEnd_2240308 766903212075284012231345 := by
  unfold tailWord_2240308
  simp only [CollatzResearch.WordTrace]
  refine ⟨40855372783877102495020789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54473830378502803326694385 40855372783877102495020789)
  ·
    refine ⟨3830191198488478358908199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40855372783877102495020789 3830191198488478358908199)
    ·
      refine ⟨5745286797732717538362299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3830191198488478358908199 5745286797732717538362299)
      ·
        refine ⟨8617930196599076307543449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5745286797732717538362299 8617930196599076307543449)
        ·
          refine ⟨6463447647449307230657587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8617930196599076307543449 6463447647449307230657587)
          ·
            refine ⟨9695171471173960845986381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6463447647449307230657587 9695171471173960845986381)
            ·
              refine ⟨3635689301690235317244893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9695171471173960845986381 3635689301690235317244893)
              ·
                refine ⟨1363383488133838243966835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3635689301690235317244893 1363383488133838243966835)
                ·
                  refine ⟨2045075232200757365950253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363383488133838243966835 2045075232200757365950253)
                  ·
                    refine ⟨766903212075284012231345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2045075232200757365950253 766903212075284012231345)
                    ·
                      rfl

theorem cell22_2240308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_2240308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240308 prefixEnd_2240308 := by exact prefixLift 2240308
  have htrace : WordTrace (prefixWord ++ tailWord_2240308) baseStart_2240308 baseEnd_2240308 := by
    simpa [prefixWord, tailWord_2240308, baseEnd_2240308] using wordTrace_append hprefix tailTrace_2240308
  have hstable : (prefixWord ++ tailWord_2240308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240308).length < 2 ^ (prefixWord ++ tailWord_2240308).sum := by decide
  have hdescent : baseEnd_2240308 < baseStart_2240308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240456 : List Nat := [2, 1, 3, 1, 4, 2, 3, 1, 5]
def baseStart_2240456 : Nat := 118140960795 + 2240456 * 2 ^ 59
def prefixEnd_2240456 : Nat := 4983230072969 + 3 ^ 40 * 2240456 * 2
def baseEnd_2240456 : Nat := 255651291833286986510297

theorem tailTrace_2240456 : CollatzResearch.WordTrace tailWord_2240456 prefixEnd_2240456 255651291833286986510297 := by
  unfold tailWord_2240456
  simp only [CollatzResearch.WordTrace]
  refine ⟨40858071785609013133214611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54477429047478684177619481 40858071785609013133214611)
  ·
    refine ⟨61287107678413519699821917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40858071785609013133214611 61287107678413519699821917)
    ·
      refine ⟨22982665379405069887433219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61287107678413519699821917 22982665379405069887433219)
      ·
        refine ⟨34473998069107604831149829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22982665379405069887433219 34473998069107604831149829)
        ·
          refine ⟨6463874637957675905840593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34473998069107604831149829 6463874637957675905840593)
          ·
            refine ⟨4847905978468256929380445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6463874637957675905840593 4847905978468256929380445)
            ·
              refine ⟨1817964741925596348517667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4847905978468256929380445 1817964741925596348517667)
              ·
                refine ⟨2726947112888394522776501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1817964741925596348517667 2726947112888394522776501)
                ·
                  refine ⟨255651291833286986510297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2726947112888394522776501 255651291833286986510297)
                  ·
                    rfl

theorem cell22_2240456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 5].length) (baseStart_2240456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240456 prefixEnd_2240456 := by exact prefixLift 2240456
  have htrace : WordTrace (prefixWord ++ tailWord_2240456) baseStart_2240456 baseEnd_2240456 := by
    simpa [prefixWord, tailWord_2240456, baseEnd_2240456] using wordTrace_append hprefix tailTrace_2240456
  have hstable : (prefixWord ++ tailWord_2240456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240456).length < 2 ^ (prefixWord ++ tailWord_2240456).sum := by decide
  have hdescent : baseEnd_2240456 < baseStart_2240456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240477 : List Nat := [1, 4, 3, 1, 4, 1, 1, 3, 1, 3]
def baseStart_2240477 : Nat := 118140960795 + 2240477 * 2 ^ 59
def prefixEnd_2240477 : Nat := 4983230072969 + 3 ^ 40 * 2240477 * 2
def baseEnd_2240477 : Nat := 766961064229023904755827

theorem tailTrace_2240477 : CollatzResearch.WordTrace tailWord_2240477 prefixEnd_2240477 766961064229023904755827 := by
  unfold tailWord_2240477
  simp only [CollatzResearch.WordTrace]
  refine ⟨81716909504141946852943685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54477939669427964568629123 81716909504141946852943685)
  ·
    refine ⟨15321920532026615034926941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81716909504141946852943685 15321920532026615034926941)
    ·
      refine ⟨5745720199509980638097603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15321920532026615034926941 5745720199509980638097603)
      ·
        refine ⟨8618580299264970957146405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5745720199509980638097603 8618580299264970957146405)
        ·
          refine ⟨1615983806112182054464951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8618580299264970957146405 1615983806112182054464951)
          ·
            refine ⟨2423975709168273081697427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1615983806112182054464951 2423975709168273081697427)
            ·
              refine ⟨3635963563752409622546141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2423975709168273081697427 3635963563752409622546141)
              ·
                refine ⟨1363486336407153608454803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3635963563752409622546141 1363486336407153608454803)
                ·
                  refine ⟨2045229504610730412682205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363486336407153608454803 2045229504610730412682205)
                  ·
                    refine ⟨766961064229023904755827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2045229504610730412682205 766961064229023904755827)
                    ·
                      rfl

theorem cell22_2240477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_2240477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240477 prefixEnd_2240477 := by exact prefixLift 2240477
  have htrace : WordTrace (prefixWord ++ tailWord_2240477) baseStart_2240477 baseEnd_2240477 := by
    simpa [prefixWord, tailWord_2240477, baseEnd_2240477] using wordTrace_append hprefix tailTrace_2240477
  have hstable : (prefixWord ++ tailWord_2240477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240477).length < 2 ^ (prefixWord ++ tailWord_2240477).sum := by decide
  have hdescent : baseEnd_2240477 < baseStart_2240477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240552 : List Nat := [2, 1, 5, 3, 1, 2, 2, 2, 4]
def baseStart_2240552 : Nat := 118140960795 + 2240552 * 2 ^ 59
def prefixEnd_2240552 : Nat := 4983230072969 + 3 ^ 40 * 2240552 * 2
def baseEnd_2240552 : Nat := 255662246087249569710199

theorem tailTrace_2240552 : CollatzResearch.WordTrace tailWord_2240552 prefixEnd_2240552 255662246087249569710199 := by
  unfold tailWord_2240552
  simp only [CollatzResearch.WordTrace]
  refine ⟨40859822489435117330961955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54479763319246823107949273 40859822489435117330961955)
  ·
    refine ⟨61289733734152675996442933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40859822489435117330961955 61289733734152675996442933)
    ·
      refine ⟨5745912537576813374666525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61289733734152675996442933 5745912537576813374666525)
      ·
        refine ⟨2154717201591305015499947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5745912537576813374666525 2154717201591305015499947)
        ·
          refine ⟨3232075802386957523249921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2154717201591305015499947 3232075802386957523249921)
          ·
            refine ⟨2424056851790218142437441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3232075802386957523249921 2424056851790218142437441)
            ·
              refine ⟨1818042638842663606828081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2424056851790218142437441 1818042638842663606828081)
              ·
                refine ⟨1363531979131997705121061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1818042638842663606828081 1363531979131997705121061)
                ·
                  refine ⟨255662246087249569710199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1363531979131997705121061 255662246087249569710199)
                  ·
                    rfl

theorem cell22_2240552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 4].length) (baseStart_2240552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240552 prefixEnd_2240552 := by exact prefixLift 2240552
  have htrace : WordTrace (prefixWord ++ tailWord_2240552) baseStart_2240552 baseEnd_2240552 := by
    simpa [prefixWord, tailWord_2240552, baseEnd_2240552] using wordTrace_append hprefix tailTrace_2240552
  have hstable : (prefixWord ++ tailWord_2240552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240552).length < 2 ^ (prefixWord ++ tailWord_2240552).sum := by decide
  have hdescent : baseEnd_2240552 < baseStart_2240552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240649 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 1, 6]
def baseStart_2240649 : Nat := 118140960795 + 2240649 * 2 ^ 59
def prefixEnd_2240649 : Nat := 4983230072969 + 3 ^ 40 * 2240649 * 2
def baseEnd_2240649 : Nat := 767019943344072789455299

theorem tailTrace_2240649 : CollatzResearch.WordTrace tailWord_2240649 prefixEnd_2240649 767019943344072789455299 := by
  unfold tailWord_2240649
  simp only [CollatzResearch.WordTrace]
  refine ⟨81723182859518820228205001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54482121906345880152136667 81723182859518820228205001)
  ·
    refine ⟨61292387144639115171153751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81723182859518820228205001 61292387144639115171153751)
    ·
      refine ⟨91938580716958672756730627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61292387144639115171153751 91938580716958672756730627)
      ·
        refine ⟨137907871075438009135095941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91938580716958672756730627 137907871075438009135095941)
        ·
          refine ⟨25857725826644626712830489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137907871075438009135095941 25857725826644626712830489)
          ·
            refine ⟨19393294369983470034622867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25857725826644626712830489 19393294369983470034622867)
            ·
              refine ⟨29089941554975205051934301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19393294369983470034622867 29089941554975205051934301)
              ·
                refine ⟨10908728083115701894475363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29089941554975205051934301 10908728083115701894475363)
                ·
                  refine ⟨16363092124673552841713045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10908728083115701894475363 16363092124673552841713045)
                  ·
                    refine ⟨767019943344072789455299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16363092124673552841713045 767019943344072789455299)
                    ·
                      rfl

theorem cell22_2240649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_2240649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240649 prefixEnd_2240649 := by exact prefixLift 2240649
  have htrace : WordTrace (prefixWord ++ tailWord_2240649) baseStart_2240649 baseEnd_2240649 := by
    simpa [prefixWord, tailWord_2240649, baseEnd_2240649] using wordTrace_append hprefix tailTrace_2240649
  have hstable : (prefixWord ++ tailWord_2240649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240649).length < 2 ^ (prefixWord ++ tailWord_2240649).sum := by decide
  have hdescent : baseEnd_2240649 < baseStart_2240649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240668 : List Nat := [2, 2, 3, 2, 1, 1, 2, 4, 2, 3]
def baseStart_2240668 : Nat := 118140960795 + 2240668 * 2 ^ 59
def prefixEnd_2240668 : Nat := 4983230072969 + 3 ^ 40 * 2240668 * 2
def baseEnd_2240668 : Nat := 767026447432363073230241

theorem tailTrace_2240668 : CollatzResearch.WordTrace tailWord_2240668 prefixEnd_2240668 767026447432363073230241 := by
  unfold tailWord_2240668
  simp only [CollatzResearch.WordTrace]
  refine ⟨40861937923224993236573329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54482583897633324315431105 40861937923224993236573329)
  ·
    refine ⟨30646453442418744927429997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40861937923224993236573329 30646453442418744927429997)
    ·
      refine ⟨11492420040907029347786249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30646453442418744927429997 11492420040907029347786249)
      ·
        refine ⟨8619315030680272010839687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11492420040907029347786249 8619315030680272010839687)
        ·
          refine ⟨12928972546020408016259531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8619315030680272010839687 12928972546020408016259531)
          ·
            refine ⟨19393458819030612024389297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12928972546020408016259531 19393458819030612024389297)
            ·
              refine ⟨14545094114272959018291973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19393458819030612024389297 14545094114272959018291973)
              ·
                refine ⟨2727205146426179815929745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14545094114272959018291973 2727205146426179815929745)
                ·
                  refine ⟨2045403859819634861947309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2727205146426179815929745 2045403859819634861947309)
                  ·
                    refine ⟨767026447432363073230241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2045403859819634861947309 767026447432363073230241)
                    ·
                      rfl

theorem cell22_2240668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_2240668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240668 prefixEnd_2240668 := by exact prefixLift 2240668
  have htrace : WordTrace (prefixWord ++ tailWord_2240668) baseStart_2240668 baseEnd_2240668 := by
    simpa [prefixWord, tailWord_2240668, baseEnd_2240668] using wordTrace_append hprefix tailTrace_2240668
  have hstable : (prefixWord ++ tailWord_2240668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240668).length < 2 ^ (prefixWord ++ tailWord_2240668).sum := by decide
  have hdescent : baseEnd_2240668 < baseStart_2240668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240670 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 6]
def baseStart_2240670 : Nat := 118140960795 + 2240670 * 2 ^ 59
def prefixEnd_2240670 : Nat := 4983230072969 + 3 ^ 40 * 2240670 * 2
def baseEnd_2240670 : Nat := 255675710691078578226745

theorem tailTrace_2240670 : CollatzResearch.WordTrace tailWord_2240670 prefixEnd_2240670 255675710691078578226745 := by
  unfold tailWord_2240670
  simp only [CollatzResearch.WordTrace]
  refine ⟨10215493599055342601839933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54482632528295160543146309 10215493599055342601839933)
  ·
    refine ⟨3830810099645753475689975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10215493599055342601839933 3830810099645753475689975)
    ·
      refine ⟨5746215149468630213534963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3830810099645753475689975 5746215149468630213534963)
      ·
        refine ⟨8619322724202945320302445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5746215149468630213534963 8619322724202945320302445)
        ·
          refine ⟨3232246021576104495113417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8619322724202945320302445 3232246021576104495113417)
          ·
            refine ⟨2424184516182078371335063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3232246021576104495113417 2424184516182078371335063)
            ·
              refine ⟨3636276774273117557002595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2424184516182078371335063 3636276774273117557002595)
              ·
                refine ⟨5454415161409676335503893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3636276774273117557002595 5454415161409676335503893)
                ·
                  refine ⟨255675710691078578226745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5454415161409676335503893 255675710691078578226745)
                  ·
                    rfl

theorem cell22_2240670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_2240670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240670 prefixEnd_2240670 := by exact prefixLift 2240670
  have htrace : WordTrace (prefixWord ++ tailWord_2240670) baseStart_2240670 baseEnd_2240670 := by
    simpa [prefixWord, tailWord_2240670, baseEnd_2240670] using wordTrace_append hprefix tailTrace_2240670
  have hstable : (prefixWord ++ tailWord_2240670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240670).length < 2 ^ (prefixWord ++ tailWord_2240670).sum := by decide
  have hdescent : baseEnd_2240670 < baseStart_2240670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240685 : List Nat := [1, 5, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_2240685 : Nat := 118140960795 + 2240685 * 2 ^ 59
def prefixEnd_2240685 : Nat := 4983230072969 + 3 ^ 40 * 2240685 * 2
def baseEnd_2240685 : Nat := 767032266879780695555189

theorem tailTrace_2240685 : CollatzResearch.WordTrace tailWord_2240685 prefixEnd_2240685 767032266879780695555189 := by
  unfold tailWord_2240685
  simp only [CollatzResearch.WordTrace]
  refine ⟨81724495887388398376515509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54482997258258932251010339 81724495887388398376515509)
  ·
    refine ⟨7661671489442662347798329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81724495887388398376515509 7661671489442662347798329)
    ·
      refine ⟨5746253617081996760848747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7661671489442662347798329 5746253617081996760848747)
      ·
        refine ⟨8619380425622995141273121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5746253617081996760848747 8619380425622995141273121)
        ·
          refine ⟨6464535319217246355954841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8619380425622995141273121 6464535319217246355954841)
          ·
            refine ⟨4848401489412934766966131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6464535319217246355954841 4848401489412934766966131)
            ·
              refine ⟨7272602234119402150449197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4848401489412934766966131 7272602234119402150449197)
              ·
                refine ⟨2727225837794775806418449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7272602234119402150449197 2727225837794775806418449)
                ·
                  refine ⟨2045419378346081854813837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2727225837794775806418449 2045419378346081854813837)
                  ·
                    refine ⟨767032266879780695555189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2045419378346081854813837 767032266879780695555189)
                    ·
                      rfl

theorem cell22_2240685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_2240685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240685 prefixEnd_2240685 := by exact prefixLift 2240685
  have htrace : WordTrace (prefixWord ++ tailWord_2240685) baseStart_2240685 baseEnd_2240685 := by
    simpa [prefixWord, tailWord_2240685, baseEnd_2240685] using wordTrace_append hprefix tailTrace_2240685
  have hstable : (prefixWord ++ tailWord_2240685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240685).length < 2 ^ (prefixWord ++ tailWord_2240685).sum := by decide
  have hdescent : baseEnd_2240685 < baseStart_2240685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240696 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 5, 3]
def baseStart_2240696 : Nat := 118140960795 + 2240696 * 2 ^ 59
def prefixEnd_2240696 : Nat := 4983230072969 + 3 ^ 40 * 2240696 * 2
def baseEnd_2240696 : Nat := 767036032404580333530155

theorem tailTrace_2240696 : CollatzResearch.WordTrace tailWord_2240696 prefixEnd_2240696 767036032404580333530155 := by
  unfold tailWord_2240696
  simp only [CollatzResearch.WordTrace]
  refine ⟨40862448545174273627582971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54483264726899031503443961 40862448545174273627582971)
  ·
    refine ⟨61293672817761410441374457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40862448545174273627582971 61293672817761410441374457)
    ·
      refine ⟨45970254613321057831030843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61293672817761410441374457 45970254613321057831030843)
      ·
        refine ⟨68955381919981586746546265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45970254613321057831030843 68955381919981586746546265)
        ·
          refine ⟨51716536439986190059909699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68955381919981586746546265 51716536439986190059909699)
          ·
            refine ⟨77574804659979285089864549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51716536439986190059909699 77574804659979285089864549)
            ·
              refine ⟨14545275873746115954349603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77574804659979285089864549 14545275873746115954349603)
              ·
                refine ⟨21817913810619173931524405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14545275873746115954349603 21817913810619173931524405)
                ·
                  refine ⟨2045429419745547556080413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21817913810619173931524405 2045429419745547556080413)
                  ·
                    refine ⟨767036032404580333530155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2045429419745547556080413 767036032404580333530155)
                    ·
                      rfl

theorem cell22_2240696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_2240696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240696 prefixEnd_2240696 := by exact prefixLift 2240696
  have htrace : WordTrace (prefixWord ++ tailWord_2240696) baseStart_2240696 baseEnd_2240696 := by
    simpa [prefixWord, tailWord_2240696, baseEnd_2240696] using wordTrace_append hprefix tailTrace_2240696
  have hstable : (prefixWord ++ tailWord_2240696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240696).length < 2 ^ (prefixWord ++ tailWord_2240696).sum := by decide
  have hdescent : baseEnd_2240696 < baseStart_2240696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240709 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 9]
def baseStart_2240709 : Nat := 118140960795 + 2240709 * 2 ^ 59
def prefixEnd_2240709 : Nat := 4983230072969 + 3 ^ 40 * 2240709 * 2
def baseEnd_2240709 : Nat := 255680160856750877651705

theorem tailTrace_2240709 : CollatzResearch.WordTrace tailWord_2240709 prefixEnd_2240709 255680160856750877651705 := by
  unfold tailWord_2240709
  simp only [CollatzResearch.WordTrace]
  refine ⟨81725371239301450475389181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54483580826200966983592787 81725371239301450475389181)
  ·
    refine ⟨30647014214738043928270943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81725371239301450475389181 30647014214738043928270943)
    ·
      refine ⟨45970521322107065892406415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30647014214738043928270943 45970521322107065892406415)
      ·
        refine ⟨68955781983160598838609623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45970521322107065892406415 68955781983160598838609623)
        ·
          refine ⟨103433672974740898257914435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68955781983160598838609623 103433672974740898257914435)
          ·
            refine ⟨155150509462111347386871653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103433672974740898257914435 155150509462111347386871653)
            ·
              refine ⟨29090720524145877635038435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155150509462111347386871653 29090720524145877635038435)
              ·
                refine ⟨43636080786218816452557653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29090720524145877635038435 43636080786218816452557653)
                ·
                  refine ⟨255680160856750877651705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43636080786218816452557653 255680160856750877651705)
                  ·
                    rfl

theorem cell22_2240709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_2240709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240709 prefixEnd_2240709 := by exact prefixLift 2240709
  have htrace : WordTrace (prefixWord ++ tailWord_2240709) baseStart_2240709 baseEnd_2240709 := by
    simpa [prefixWord, tailWord_2240709, baseEnd_2240709] using wordTrace_append hprefix tailTrace_2240709
  have hstable : (prefixWord ++ tailWord_2240709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240709).length < 2 ^ (prefixWord ++ tailWord_2240709).sum := by decide
  have hdescent : baseEnd_2240709 < baseStart_2240709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240732 : List Nat := [2, 2, 5, 2, 2, 1, 1, 7]
def baseStart_2240732 : Nat := 118140960795 + 2240732 * 2 ^ 59
def prefixEnd_2240732 : Nat := 4983230072969 + 3 ^ 40 * 2240732 * 2
def baseEnd_2240732 : Nat := 85227595104476471070005

theorem tailTrace_2240732 : CollatzResearch.WordTrace tailWord_2240732 prefixEnd_2240732 85227595104476471070005 := by
  unfold tailWord_2240732
  simp only [CollatzResearch.WordTrace]
  refine ⟨40863105059109062701738225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54484140078812083602317633 40863105059109062701738225)
  ·
    refine ⟨30647328794331797026303669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40863105059109062701738225 30647328794331797026303669)
    ·
      refine ⟨2873187074468605971215969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30647328794331797026303669 2873187074468605971215969)
      ·
        refine ⟨2154890305851454478411977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2873187074468605971215969 2154890305851454478411977)
        ·
          refine ⟨1616167729388590858808983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2154890305851454478411977 1616167729388590858808983)
          ·
            refine ⟨2424251594082886288213475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1616167729388590858808983 2424251594082886288213475)
            ·
              refine ⟨3636377391124329432320213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2424251594082886288213475 3636377391124329432320213)
              ·
                refine ⟨85227595104476471070005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3636377391124329432320213 85227595104476471070005)
                ·
                  rfl

theorem cell22_2240732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 7].length) (baseStart_2240732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240732 prefixEnd_2240732 := by exact prefixLift 2240732
  have htrace : WordTrace (prefixWord ++ tailWord_2240732) baseStart_2240732 baseEnd_2240732 := by
    simpa [prefixWord, tailWord_2240732, baseEnd_2240732] using wordTrace_append hprefix tailTrace_2240732
  have hstable : (prefixWord ++ tailWord_2240732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240732).length < 2 ^ (prefixWord ++ tailWord_2240732).sum := by decide
  have hdescent : baseEnd_2240732 < baseStart_2240732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240741 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 1, 7]
def baseStart_2240741 : Nat := 118140960795 + 2240741 * 2 ^ 59
def prefixEnd_2240741 : Nat := 4983230072969 + 3 ^ 40 * 2240741 * 2
def baseEnd_2240741 : Nat := 767051436824215216155017

theorem tailTrace_2240741 : CollatzResearch.WordTrace tailWord_2240741 prefixEnd_2240741 767051436824215216155017 := by
  unfold tailWord_2240741
  simp only [CollatzResearch.WordTrace]
  refine ⟨81726538375185519940554077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54484358916790346627036051 81726538375185519940554077)
  ·
    refine ⟨30647451890694569977707779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81726538375185519940554077 30647451890694569977707779)
    ·
      refine ⟨45971177836041854966561669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30647451890694569977707779 45971177836041854966561669)
      ·
        refine ⟨8619595844257847806230313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45971177836041854966561669 8619595844257847806230313)
        ·
          refine ⟨6464696883193385854672735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8619595844257847806230313 6464696883193385854672735)
          ·
            refine ⟨9697045324790078782009103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6464696883193385854672735 9697045324790078782009103)
            ·
              refine ⟨14545567987185118173013655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9697045324790078782009103 14545567987185118173013655)
              ·
                refine ⟨21818351980777677259520483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14545567987185118173013655 21818351980777677259520483)
                ·
                  refine ⟨32727527971166515889280725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21818351980777677259520483 32727527971166515889280725)
                  ·
                    refine ⟨767051436824215216155017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32727527971166515889280725 767051436824215216155017)
                    ·
                      rfl

theorem cell22_2240741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_2240741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240741 prefixEnd_2240741 := by exact prefixLift 2240741
  have htrace : WordTrace (prefixWord ++ tailWord_2240741) baseStart_2240741 baseEnd_2240741 := by
    simpa [prefixWord, tailWord_2240741, baseEnd_2240741] using wordTrace_append hprefix tailTrace_2240741
  have hstable : (prefixWord ++ tailWord_2240741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240741).length < 2 ^ (prefixWord ++ tailWord_2240741).sum := by decide
  have hdescent : baseEnd_2240741 < baseStart_2240741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240743 : List Nat := [1, 1, 5, 3, 1, 1, 2, 3, 5]
def baseStart_2240743 : Nat := 118140960795 + 2240743 * 2 ^ 59
def prefixEnd_2240743 : Nat := 4983230072969 + 3 ^ 40 * 2240743 * 2
def baseEnd_2240743 : Nat := 255684040488362625868337

theorem tailTrace_2240743 : CollatzResearch.WordTrace tailWord_2240743 prefixEnd_2240743 255684040488362625868337 := by
  unfold tailWord_2240743
  simp only [CollatzResearch.WordTrace]
  refine ⟨81726611321178274282126883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54484407547452182854751255 81726611321178274282126883)
  ·
    refine ⟨122589916981767411423190325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81726611321178274282126883 122589916981767411423190325)
    ·
      refine ⟨11492804717040694820924093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122589916981767411423190325 11492804717040694820924093)
      ·
        refine ⟨4309801768890260557846535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11492804717040694820924093 4309801768890260557846535)
        ·
          refine ⟨6464702653335390836769803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4309801768890260557846535 6464702653335390836769803)
          ·
            refine ⟨9697053980003086255154705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6464702653335390836769803 9697053980003086255154705)
            ·
              refine ⟨7272790485002314691366029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9697053980003086255154705 7272790485002314691366029)
              ·
                refine ⟨2727296431875868009262261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7272790485002314691366029 2727296431875868009262261)
                ·
                  refine ⟨255684040488362625868337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2727296431875868009262261 255684040488362625868337)
                  ·
                    rfl

theorem cell22_2240743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 5].length) (baseStart_2240743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240743 prefixEnd_2240743 := by exact prefixLift 2240743
  have htrace : WordTrace (prefixWord ++ tailWord_2240743) baseStart_2240743 baseEnd_2240743 := by
    simpa [prefixWord, tailWord_2240743, baseEnd_2240743] using wordTrace_append hprefix tailTrace_2240743
  have hstable : (prefixWord ++ tailWord_2240743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240743).length < 2 ^ (prefixWord ++ tailWord_2240743).sum := by decide
  have hdescent : baseEnd_2240743 < baseStart_2240743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240801 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 1, 6]
def baseStart_2240801 : Nat := 118140960795 + 2240801 * 2 ^ 59
def prefixEnd_2240801 : Nat := 4983230072969 + 3 ^ 40 * 2240801 * 2
def baseEnd_2240801 : Nat := 767071976050395059654833

theorem tailTrace_2240801 : CollatzResearch.WordTrace tailWord_2240801 prefixEnd_2240801 767071976050395059654833 := by
  unfold tailWord_2240801
  simp only [CollatzResearch.WordTrace]
  refine ⟨81728726754968150187738257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54485817836645433458492171 81728726754968150187738257)
  ·
    refine ⟨61296545066226112640803693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81728726754968150187738257 61296545066226112640803693)
    ·
      refine ⟨22986204399834792240301385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61296545066226112640803693 22986204399834792240301385)
      ·
        refine ⟨17239653299876094180226039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22986204399834792240301385 17239653299876094180226039)
        ·
          refine ⟨25859479949814141270339059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17239653299876094180226039 25859479949814141270339059)
          ·
            refine ⟨38789219924721211905508589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25859479949814141270339059 38789219924721211905508589)
            ·
              refine ⟨14545957471770454464565721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38789219924721211905508589 14545957471770454464565721)
              ·
                refine ⟨10909468103827840848424291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14545957471770454464565721 10909468103827840848424291)
                ·
                  refine ⟨16364202155741761272636437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10909468103827840848424291 16364202155741761272636437)
                  ·
                    refine ⟨767071976050395059654833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16364202155741761272636437 767071976050395059654833)
                    ·
                      rfl

theorem cell22_2240801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_2240801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240801 prefixEnd_2240801 := by exact prefixLift 2240801
  have htrace : WordTrace (prefixWord ++ tailWord_2240801) baseStart_2240801 baseEnd_2240801 := by
    simpa [prefixWord, tailWord_2240801, baseEnd_2240801] using wordTrace_append hprefix tailTrace_2240801
  have hstable : (prefixWord ++ tailWord_2240801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240801).length < 2 ^ (prefixWord ++ tailWord_2240801).sum := by decide
  have hdescent : baseEnd_2240801 < baseStart_2240801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240820 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_2240820 : Nat := 118140960795 + 2240820 * 2 ^ 59
def prefixEnd_2240820 : Nat := 4983230072969 + 3 ^ 40 * 2240820 * 2
def baseEnd_2240820 : Nat := 767078480138685343429775

theorem tailTrace_2240820 : CollatzResearch.WordTrace tailWord_2240820 prefixEnd_2240820 767078480138685343429775 := by
  unfold tailWord_2240820
  simp only [CollatzResearch.WordTrace]
  refine ⟨40864709870949658216339957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54486279827932877621786609 40864709870949658216339957)
  ·
    refine ⟨3831066550401530457781871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40864709870949658216339957 3831066550401530457781871)
    ·
      refine ⟨5746599825602295686672807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3831066550401530457781871 5746599825602295686672807)
      ·
        refine ⟨8619899738403443530009211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5746599825602295686672807 8619899738403443530009211)
        ·
          refine ⟨12929849607605165295013817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8619899738403443530009211 12929849607605165295013817)
          ·
            refine ⟨9697387205703873971260363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12929849607605165295013817 9697387205703873971260363)
            ·
              refine ⟨14546080808555810956890545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9697387205703873971260363 14546080808555810956890545)
              ·
                refine ⟨10909560606416858217667909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14546080808555810956890545 10909560606416858217667909)
                ·
                  refine ⟨2045542613703160915812733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10909560606416858217667909 2045542613703160915812733)
                  ·
                    refine ⟨767078480138685343429775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2045542613703160915812733 767078480138685343429775)
                    ·
                      rfl

theorem cell22_2240820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_2240820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240820 prefixEnd_2240820 := by exact prefixLift 2240820
  have htrace : WordTrace (prefixWord ++ tailWord_2240820) baseStart_2240820 baseEnd_2240820 := by
    simpa [prefixWord, tailWord_2240820, baseEnd_2240820] using wordTrace_append hprefix tailTrace_2240820
  have hstable : (prefixWord ++ tailWord_2240820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240820).length < 2 ^ (prefixWord ++ tailWord_2240820).sum := by decide
  have hdescent : baseEnd_2240820 < baseStart_2240820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240908 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 3, 4]
def baseStart_2240908 : Nat := 118140960795 + 2240908 * 2 ^ 59
def prefixEnd_2240908 : Nat := 4983230072969 + 3 ^ 40 * 2240908 * 2
def baseEnd_2240908 : Nat := 767108604337082447229505

theorem tailTrace_2240908 : CollatzResearch.WordTrace tailWord_2240908 prefixEnd_2240908 767108604337082447229505 := by
  unfold tailWord_2240908
  simp only [CollatzResearch.WordTrace]
  refine ⟨40866314682790253730941689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54488419577053671641255585 40866314682790253730941689)
  ·
    refine ⟨30649736012092690298206267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40866314682790253730941689 30649736012092690298206267)
    ·
      refine ⟨45974604018139035447309401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30649736012092690298206267 45974604018139035447309401)
      ·
        refine ⟨34480953013604276585482051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45974604018139035447309401 34480953013604276585482051)
        ·
          refine ⟨51721429520406414878223077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34480953013604276585482051 51721429520406414878223077)
          ·
            refine ⟨9697768035076202789666827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51721429520406414878223077 9697768035076202789666827)
            ·
              refine ⟨14546652052614304184500241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9697768035076202789666827 14546652052614304184500241)
              ·
                refine ⟨10909989039460728138375181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14546652052614304184500241 10909989039460728138375181)
                ·
                  refine ⟨4091245889797773051890693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10909989039460728138375181 4091245889797773051890693)
                  ·
                    refine ⟨767108604337082447229505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4091245889797773051890693 767108604337082447229505)
                    ·
                      rfl

theorem cell22_2240908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_2240908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240908 prefixEnd_2240908 := by exact prefixLift 2240908
  have htrace : WordTrace (prefixWord ++ tailWord_2240908) baseStart_2240908 baseEnd_2240908 := by
    simpa [prefixWord, tailWord_2240908, baseEnd_2240908] using wordTrace_append hprefix tailTrace_2240908
  have hstable : (prefixWord ++ tailWord_2240908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240908).length < 2 ^ (prefixWord ++ tailWord_2240908).sum := by decide
  have hdescent : baseEnd_2240908 < baseStart_2240908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240910 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_2240910 : Nat := 118140960795 + 2240910 * 2 ^ 59
def prefixEnd_2240910 : Nat := 4983230072969 + 3 ^ 40 * 2240910 * 2
def baseEnd_2240910 : Nat := 767109288977955108679499

theorem tailTrace_2240910 : CollatzResearch.WordTrace tailWord_2240910 prefixEnd_2240910 767109288977955108679499 := by
  unfold tailWord_2240910
  simp only [CollatzResearch.WordTrace]
  refine ⟨10216587788946657725432023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54488468207715507868970789 10216587788946657725432023)
  ·
    refine ⟨15324881683419986588148035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10216587788946657725432023 15324881683419986588148035)
    ·
      refine ⟨22987322525129979882222053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15324881683419986588148035 22987322525129979882222053)
      ·
        refine ⟨4310122973461871227916635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22987322525129979882222053 4310122973461871227916635)
        ·
          refine ⟨6465184460192806841874953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4310122973461871227916635 6465184460192806841874953)
          ·
            refine ⟨4848888345144605131406215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6465184460192806841874953 4848888345144605131406215)
            ·
              refine ⟨7273332517716907697109323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4848888345144605131406215 7273332517716907697109323)
              ·
                refine ⟨10909998776575361545663985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7273332517716907697109323 10909998776575361545663985)
                ·
                  refine ⟨8182499082431521159247989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10909998776575361545663985 8182499082431521159247989)
                  ·
                    refine ⟨767109288977955108679499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8182499082431521159247989 767109288977955108679499)
                    ·
                      rfl

theorem cell22_2240910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_2240910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240910 prefixEnd_2240910 := by exact prefixLift 2240910
  have htrace : WordTrace (prefixWord ++ tailWord_2240910) baseStart_2240910 baseEnd_2240910 := by
    simpa [prefixWord, tailWord_2240910, baseEnd_2240910] using wordTrace_append hprefix tailTrace_2240910
  have hstable : (prefixWord ++ tailWord_2240910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240910).length < 2 ^ (prefixWord ++ tailWord_2240910).sum := by decide
  have hdescent : baseEnd_2240910 < baseStart_2240910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240972 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 1, 5]
def baseStart_2240972 : Nat := 118140960795 + 2240972 * 2 ^ 59
def prefixEnd_2240972 : Nat := 4983230072969 + 3 ^ 40 * 2240972 * 2
def baseEnd_2240972 : Nat := 767130512845007613629309

theorem tailTrace_2240972 : CollatzResearch.WordTrace tailWord_2240972 prefixEnd_2240972 767130512845007613629309 := by
  unfold tailWord_2240972
  simp only [CollatzResearch.WordTrace]
  refine ⟨40867481818674323196106585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54489975758232430928142113 40867481818674323196106585)
  ·
    refine ⟨30650611364005742397079939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40867481818674323196106585 30650611364005742397079939)
    ·
      refine ⟨45975917046008613595619909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30650611364005742397079939 45975917046008613595619909)
      ·
        refine ⟨8620484446126615049178733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45975917046008613595619909 8620484446126615049178733)
        ·
          refine ⟨3232681667297480643442025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8620484446126615049178733 3232681667297480643442025)
          ·
            refine ⟨2424511250473110482581519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3232681667297480643442025 2424511250473110482581519)
            ·
              refine ⟨3636766875709665723872279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2424511250473110482581519 3636766875709665723872279)
              ·
                refine ⟨5455150313564498585808419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3636766875709665723872279 5455150313564498585808419)
                ·
                  refine ⟨8182725470346747878712629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5455150313564498585808419 8182725470346747878712629)
                  ·
                    refine ⟨767130512845007613629309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8182725470346747878712629 767130512845007613629309)
                    ·
                      rfl

theorem cell22_2240972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_2240972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2240972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2240972 prefixEnd_2240972 := by exact prefixLift 2240972
  have htrace : WordTrace (prefixWord ++ tailWord_2240972) baseStart_2240972 baseEnd_2240972 := by
    simpa [prefixWord, tailWord_2240972, baseEnd_2240972] using wordTrace_append hprefix tailTrace_2240972
  have hstable : (prefixWord ++ tailWord_2240972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240972).length < 2 ^ (prefixWord ++ tailWord_2240972).sum := by decide
  have hdescent : baseEnd_2240972 < baseStart_2240972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241017 : List Nat := [1, 2, 1, 3, 1, 2, 2, 6, 1, 3]
def baseStart_2241017 : Nat := 118140960795 + 2241017 * 2 ^ 59
def prefixEnd_2241017 : Nat := 4983230072969 + 3 ^ 40 * 2241017 * 2
def baseEnd_2241017 : Nat := 767145917264642496254171

theorem tailTrace_2241017 : CollatzResearch.WordTrace tailWord_2241017 prefixEnd_2241017 767145917264642496254171 := by
  unfold tailWord_2241017
  simp only [CollatzResearch.WordTrace]
  refine ⟨81736604922185619077601305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54491069948123746051734203 81736604922185619077601305)
  ·
    refine ⟨61302453691639214308200979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81736604922185619077601305 61302453691639214308200979)
    ·
      refine ⟨91953680537458821462301469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61302453691639214308200979 91953680537458821462301469)
      ·
        refine ⟨34482630201547058048363051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91953680537458821462301469 34482630201547058048363051)
        ·
          refine ⟨51723945302320587072544577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34482630201547058048363051 51723945302320587072544577)
          ·
            refine ⟨38792958976740440304408433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51723945302320587072544577 38792958976740440304408433)
            ·
              refine ⟨29094719232555330228306325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38792958976740440304408433 29094719232555330228306325)
              ·
                refine ⟨1363814964026031104451859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29094719232555330228306325 1363814964026031104451859)
                ·
                  refine ⟨2045722446039046656677789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363814964026031104451859 2045722446039046656677789)
                  ·
                    refine ⟨767145917264642496254171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2045722446039046656677789 767145917264642496254171)
                    ·
                      rfl

theorem cell22_2241017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 1, 3].length) (baseStart_2241017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241017 prefixEnd_2241017 := by exact prefixLift 2241017
  have htrace : WordTrace (prefixWord ++ tailWord_2241017) baseStart_2241017 baseEnd_2241017 := by
    simpa [prefixWord, tailWord_2241017, baseEnd_2241017] using wordTrace_append hprefix tailTrace_2241017
  have hstable : (prefixWord ++ tailWord_2241017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241017).length < 2 ^ (prefixWord ++ tailWord_2241017).sum := by decide
  have hdescent : baseEnd_2241017 < baseStart_2241017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241094 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_2241094 : Nat := 118140960795 + 2241094 * 2 ^ 59
def prefixEnd_2241094 : Nat := 4983230072969 + 3 ^ 40 * 2241094 * 2
def baseEnd_2241094 : Nat := 767172275938239962078935

theorem tailTrace_2241094 : CollatzResearch.WordTrace tailWord_2241094 prefixEnd_2241094 767172275938239962078935 := by
  unfold tailWord_2241094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2554356666965833163379823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54492942228604440818769557 2554356666965833163379823)
  ·
    refine ⟨3831535000448749745069735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2554356666965833163379823 3831535000448749745069735)
    ·
      refine ⟨5747302500673124617604603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3831535000448749745069735 5747302500673124617604603)
      ·
        refine ⟨8620953751009686926406905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5747302500673124617604603 8620953751009686926406905)
        ·
          refine ⟨6465715313257265194805179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8620953751009686926406905 6465715313257265194805179)
          ·
            refine ⟨9698572969885897792207769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6465715313257265194805179 9698572969885897792207769)
            ·
              refine ⟨7273929727414423344155827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9698572969885897792207769 7273929727414423344155827)
              ·
                refine ⟨10910894591121635016233741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7273929727414423344155827 10910894591121635016233741)
                ·
                  refine ⟨4091585471670613131087653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10910894591121635016233741 4091585471670613131087653)
                  ·
                    refine ⟨767172275938239962078935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4091585471670613131087653 767172275938239962078935)
                    ·
                      rfl

theorem cell22_2241094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_2241094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241094 prefixEnd_2241094 := by exact prefixLift 2241094
  have htrace : WordTrace (prefixWord ++ tailWord_2241094) baseStart_2241094 baseEnd_2241094 := by
    simpa [prefixWord, tailWord_2241094, baseEnd_2241094] using wordTrace_append hprefix tailTrace_2241094
  have hstable : (prefixWord ++ tailWord_2241094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241094).length < 2 ^ (prefixWord ++ tailWord_2241094).sum := by decide
  have hdescent : baseEnd_2241094 < baseStart_2241094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241103 : List Nat := [1, 1, 2, 1, 1, 2, 4, 10]
def baseStart_2241103 : Nat := 118140960795 + 2241103 * 2 ^ 59
def prefixEnd_2241103 : Nat := 4983230072969 + 3 ^ 40 * 2241103 * 2
def baseEnd_2241103 : Nat := 85241706313574104289323

theorem tailTrace_2241103 : CollatzResearch.WordTrace tailWord_2241103 prefixEnd_2241103 85241706313574104289323 := by
  unfold tailWord_2241103
  simp only [CollatzResearch.WordTrace]
  refine ⟨81739741599874055765231963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54493161066582703843487975 81739741599874055765231963)
  ·
    refine ⟨122609612399811083647847945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81739741599874055765231963 122609612399811083647847945)
    ·
      refine ⟨91957209299858312735885959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122609612399811083647847945 91957209299858312735885959)
      ·
        refine ⟨137935813949787469103828939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91957209299858312735885959 137935813949787469103828939)
        ·
          refine ⟨206903720924681203655743409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137935813949787469103828939 206903720924681203655743409)
          ·
            refine ⟨155177790693510902741807557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206903720924681203655743409 155177790693510902741807557)
            ·
              refine ⟨29095835755033294264088917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155177790693510902741807557 29095835755033294264088917)
              ·
                refine ⟨85241706313574104289323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29095835755033294264088917 85241706313574104289323)
                ·
                  rfl

theorem cell22_2241103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 10].length) (baseStart_2241103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241103 prefixEnd_2241103 := by exact prefixLift 2241103
  have htrace : WordTrace (prefixWord ++ tailWord_2241103) baseStart_2241103 baseEnd_2241103 := by
    simpa [prefixWord, tailWord_2241103, baseEnd_2241103] using wordTrace_append hprefix tailTrace_2241103
  have hstable : (prefixWord ++ tailWord_2241103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241103).length < 2 ^ (prefixWord ++ tailWord_2241103).sum := by decide
  have hdescent : baseEnd_2241103 < baseStart_2241103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241105 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 1, 6]
def baseStart_2241105 : Nat := 118140960795 + 2241105 * 2 ^ 59
def prefixEnd_2241105 : Nat := 4983230072969 + 3 ^ 40 * 2241105 * 2
def baseEnd_2241105 : Nat := 767176041463039600053901

theorem tailTrace_2241105 : CollatzResearch.WordTrace tailWord_2241105 prefixEnd_2241105 767176041463039600053901 := by
  unfold tailWord_2241105
  simp only [CollatzResearch.WordTrace]
  refine ⟨81739814545866810106804769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54493209697244540071203179 81739814545866810106804769)
  ·
    refine ⟨61304860909400107580103577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81739814545866810106804769 61304860909400107580103577)
    ·
      refine ⟨45978645682050080685077683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61304860909400107580103577 45978645682050080685077683)
      ·
        refine ⟨68967968523075121027616525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45978645682050080685077683 68967968523075121027616525)
        ·
          refine ⟨25862988196153170385356197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68967968523075121027616525 25862988196153170385356197)
          ·
            refine ⟨4849310286778719447254287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25862988196153170385356197 4849310286778719447254287)
            ·
              refine ⟨7273965430168079170881431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4849310286778719447254287 7273965430168079170881431)
              ·
                refine ⟨10910948145252118756322147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7273965430168079170881431 10910948145252118756322147)
                ·
                  refine ⟨16366422217878178134483221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10910948145252118756322147 16366422217878178134483221)
                  ·
                    refine ⟨767176041463039600053901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16366422217878178134483221 767176041463039600053901)
                    ·
                      rfl

theorem cell22_2241105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_2241105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241105 prefixEnd_2241105 := by exact prefixLift 2241105
  have htrace : WordTrace (prefixWord ++ tailWord_2241105) baseStart_2241105 baseEnd_2241105 := by
    simpa [prefixWord, tailWord_2241105, baseEnd_2241105] using wordTrace_append hprefix tailTrace_2241105
  have hstable : (prefixWord ++ tailWord_2241105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241105).length < 2 ^ (prefixWord ++ tailWord_2241105).sum := by decide
  have hdescent : baseEnd_2241105 < baseStart_2241105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241141 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 1, 5]
def baseStart_2241141 : Nat := 118140960795 + 2241141 * 2 ^ 59
def prefixEnd_2241141 : Nat := 4983230072969 + 3 ^ 40 * 2241141 * 2
def baseEnd_2241141 : Nat := 767188364998747506153791

theorem tailTrace_2241141 : CollatzResearch.WordTrace tailWord_2241141 prefixEnd_2241141 767188364998747506153791 := by
  unfold tailWord_2241141
  simp only [CollatzResearch.WordTrace]
  refine ⟨81741127573736388255115277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54494085049157592170076851 81741127573736388255115277)
  ·
    refine ⟨30652922840151145595668229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81741127573736388255115277 30652922840151145595668229)
    ·
      refine ⟨5747423032528339799187793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30652922840151145595668229 5747423032528339799187793)
      ·
        refine ⟨4310567274396254849390845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5747423032528339799187793 4310567274396254849390845)
        ·
          refine ⟨1616462727898595568521567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4310567274396254849390845 1616462727898595568521567)
          ·
            refine ⟨2424694091847893352782351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1616462727898595568521567 2424694091847893352782351)
            ·
              refine ⟨3637041137771840029173527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2424694091847893352782351 3637041137771840029173527)
              ·
                refine ⟨5455561706657760043760291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3637041137771840029173527 5455561706657760043760291)
                ·
                  refine ⟨8183342559986640065640437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5455561706657760043760291 8183342559986640065640437)
                  ·
                    refine ⟨767188364998747506153791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8183342559986640065640437 767188364998747506153791)
                    ·
                      rfl

theorem cell22_2241141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_2241141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241141 prefixEnd_2241141 := by exact prefixLift 2241141
  have htrace : WordTrace (prefixWord ++ tailWord_2241141) baseStart_2241141 baseEnd_2241141 := by
    simpa [prefixWord, tailWord_2241141, baseEnd_2241141] using wordTrace_append hprefix tailTrace_2241141
  have hstable : (prefixWord ++ tailWord_2241141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241141).length < 2 ^ (prefixWord ++ tailWord_2241141).sum := by decide
  have hdescent : baseEnd_2241141 < baseStart_2241141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241152 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 3, 3]
def baseStart_2241152 : Nat := 118140960795 + 2241152 * 2 ^ 59
def prefixEnd_2241152 : Nat := 4983230072969 + 3 ^ 40 * 2241152 * 2
def baseEnd_2241152 : Nat := 767192130523547144128757

theorem tailTrace_2241152 : CollatzResearch.WordTrace tailWord_2241152 prefixEnd_2241152 767192130523547144128757 := by
  unfold tailWord_2241152
  simp only [CollatzResearch.WordTrace]
  refine ⟨40870764388348268566882855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54494352517797691422510473 40870764388348268566882855)
  ·
    refine ⟨61306146582522402850324283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40870764388348268566882855 61306146582522402850324283)
    ·
      refine ⟨91959219873783604275486425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61306146582522402850324283 91959219873783604275486425)
      ·
        refine ⟨68969414905337703206614819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91959219873783604275486425 68969414905337703206614819)
        ·
          refine ⟨103454122358006554809922229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68969414905337703206614819 103454122358006554809922229)
          ·
            refine ⟨9698823971063114513430209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103454122358006554809922229 9698823971063114513430209)
            ·
              refine ⟨7274117978297335885072657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9698823971063114513430209 7274117978297335885072657)
              ·
                refine ⟨5455588483723001913804493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7274117978297335885072657 5455588483723001913804493)
                ·
                  refine ⟨2045845681396125717676685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5455588483723001913804493 2045845681396125717676685)
                  ·
                    refine ⟨767192130523547144128757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2045845681396125717676685 767192130523547144128757)
                    ·
                      rfl

theorem cell22_2241152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 3, 3].length) (baseStart_2241152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241152 prefixEnd_2241152 := by exact prefixLift 2241152
  have htrace : WordTrace (prefixWord ++ tailWord_2241152) baseStart_2241152 baseEnd_2241152 := by
    simpa [prefixWord, tailWord_2241152, baseEnd_2241152] using wordTrace_append hprefix tailTrace_2241152
  have hstable : (prefixWord ++ tailWord_2241152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241152).length < 2 ^ (prefixWord ++ tailWord_2241152).sum := by decide
  have hdescent : baseEnd_2241152 < baseStart_2241152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241182 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 7]
def baseStart_2241182 : Nat := 118140960795 + 2241182 * 2 ^ 59
def prefixEnd_2241182 : Nat := 4983230072969 + 3 ^ 40 * 2241182 * 2
def baseEnd_2241182 : Nat := 255734133378879021959555

theorem tailTrace_2241182 : CollatzResearch.WordTrace tailWord_2241182 prefixEnd_2241182 255734133378879021959555 := by
  unfold tailWord_2241182
  simp only [CollatzResearch.WordTrace]
  refine ⟨10217827870823481532169725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54495081977725234838238533 10217827870823481532169725)
  ·
    refine ⟨3831685451558805574563647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10217827870823481532169725 3831685451558805574563647)
    ·
      refine ⟨5747528177338208361845471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3831685451558805574563647 5747528177338208361845471)
      ·
        refine ⟨8621292266007312542768207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5747528177338208361845471 8621292266007312542768207)
        ·
          refine ⟨12931938399010968814152311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8621292266007312542768207 12931938399010968814152311)
          ·
            refine ⟨19397907598516453221228467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12931938399010968814152311 19397907598516453221228467)
            ·
              refine ⟨29096861397774679831842701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19397907598516453221228467 29096861397774679831842701)
              ·
                refine ⟨10911323024165504936941013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29096861397774679831842701 10911323024165504936941013)
                ·
                  refine ⟨255734133378879021959555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10911323024165504936941013 255734133378879021959555)
                  ·
                    rfl

theorem cell22_2241182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_2241182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241182 prefixEnd_2241182 := by exact prefixLift 2241182
  have htrace : WordTrace (prefixWord ++ tailWord_2241182) baseStart_2241182 baseEnd_2241182 := by
    simpa [prefixWord, tailWord_2241182, baseEnd_2241182] using wordTrace_append hprefix tailTrace_2241182
  have hstable : (prefixWord ++ tailWord_2241182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241182).length < 2 ^ (prefixWord ++ tailWord_2241182).sum := by decide
  have hdescent : baseEnd_2241182 < baseStart_2241182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241199 : List Nat := [1, 1, 2, 1, 2, 7, 2, 1, 5]
def baseStart_2241199 : Nat := 118140960795 + 2241199 * 2 ^ 59
def prefixEnd_2241199 : Nat := 4983230072969 + 3 ^ 40 * 2241199 * 2
def baseEnd_2241199 : Nat := 255736073194684896067871

theorem tailTrace_2241199 : CollatzResearch.WordTrace tailWord_2241199 prefixEnd_2241199 255736073194684896067871 := by
  unfold tailWord_2241199
  simp only [CollatzResearch.WordTrace]
  refine ⟨81743243007526264160726651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54495495338350842773817767 81743243007526264160726651)
  ·
    refine ⟨122614864511289396241089977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81743243007526264160726651 122614864511289396241089977)
    ·
      refine ⟨91961148383467047180817483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122614864511289396241089977 91961148383467047180817483)
      ·
        refine ⟨137941722575200570771226225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91961148383467047180817483 137941722575200570771226225)
        ·
          refine ⟨103456291931400428078419669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137941722575200570771226225 103456291931400428078419669)
          ·
            refine ⟨2424756842142197533087961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 103456291931400428078419669 2424756842142197533087961)
            ·
              refine ⟨1818567631606648149815971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2424756842142197533087961 1818567631606648149815971)
              ·
                refine ⟨2727851447409972224723957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1818567631606648149815971 2727851447409972224723957)
                ·
                  refine ⟨255736073194684896067871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2727851447409972224723957 255736073194684896067871)
                  ·
                    rfl

theorem cell22_2241199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 5].length) (baseStart_2241199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241199 prefixEnd_2241199 := by exact prefixLift 2241199
  have htrace : WordTrace (prefixWord ++ tailWord_2241199) baseStart_2241199 baseEnd_2241199 := by
    simpa [prefixWord, tailWord_2241199, baseEnd_2241199] using wordTrace_append hprefix tailTrace_2241199
  have hstable : (prefixWord ++ tailWord_2241199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241199).length < 2 ^ (prefixWord ++ tailWord_2241199).sum := by decide
  have hdescent : baseEnd_2241199 < baseStart_2241199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241210 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 8]
def baseStart_2241210 : Nat := 118140960795 + 2241210 * 2 ^ 59
def prefixEnd_2241210 : Nat := 4983230072969 + 3 ^ 40 * 2241210 * 2
def baseEnd_2241210 : Nat := 255737328369618108726193

theorem tailTrace_2241210 : CollatzResearch.WordTrace tailWord_2241210 prefixEnd_2241210 255737328369618108726193 := by
  unfold tailWord_2241210
  simp only [CollatzResearch.WordTrace]
  refine ⟨20435911052621603259844271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54495762806990942026251389 20435911052621603259844271)
  ·
    refine ⟨30653866578932404889766407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20435911052621603259844271 30653866578932404889766407)
    ·
      refine ⟨45980799868398607334649611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30653866578932404889766407 45980799868398607334649611)
      ·
        refine ⟨68971199802597911001974417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45980799868398607334649611 68971199802597911001974417)
        ·
          refine ⟨51728399851948433251480813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68971199802597911001974417 51728399851948433251480813)
          ·
            refine ⟨19398149944480662469305305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51728399851948433251480813 19398149944480662469305305)
            ·
              refine ⟨14548612458360496851978979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19398149944480662469305305 14548612458360496851978979)
              ·
                refine ⟨21822918687540745277968469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14548612458360496851978979 21822918687540745277968469)
                ·
                  refine ⟨255737328369618108726193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21822918687540745277968469 255737328369618108726193)
                  ·
                    rfl

theorem cell22_2241210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_2241210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241210 prefixEnd_2241210 := by exact prefixLift 2241210
  have htrace : WordTrace (prefixWord ++ tailWord_2241210) baseStart_2241210 baseEnd_2241210 := by
    simpa [prefixWord, tailWord_2241210, baseEnd_2241210] using wordTrace_append hprefix tailTrace_2241210
  have hstable : (prefixWord ++ tailWord_2241210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241210).length < 2 ^ (prefixWord ++ tailWord_2241210).sum := by decide
  have hdescent : baseEnd_2241210 < baseStart_2241210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241212 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 3, 4]
def baseStart_2241212 : Nat := 118140960795 + 2241212 * 2 ^ 59
def prefixEnd_2241212 : Nat := 4983230072969 + 3 ^ 40 * 2241212 * 2
def baseEnd_2241212 : Nat := 767212669749726987628573

theorem tailTrace_2241212 : CollatzResearch.WordTrace tailWord_2241212 prefixEnd_2241212 767212669749726987628573 := by
  unfold tailWord_2241212
  simp only [CollatzResearch.WordTrace]
  refine ⟨40871858578239583690474945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54495811437652778253966593 40871858578239583690474945)
  ·
    refine ⟨30653893933679687767856209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40871858578239583690474945 30653893933679687767856209)
    ·
      refine ⟨22990420450259765825892157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30653893933679687767856209 22990420450259765825892157)
      ·
        refine ⟨8621407668847412184709559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22990420450259765825892157 8621407668847412184709559)
        ·
          refine ⟨12932111503271118277064339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8621407668847412184709559 12932111503271118277064339)
          ·
            refine ⟨19398167254906677415596509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12932111503271118277064339 19398167254906677415596509)
            ·
              refine ⟨7274312720590004030848691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19398167254906677415596509 7274312720590004030848691)
              ·
                refine ⟨10911469080885006046273037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7274312720590004030848691 10911469080885006046273037)
                ·
                  refine ⟨4091800905331877267352389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10911469080885006046273037 4091800905331877267352389)
                  ·
                    refine ⟨767212669749726987628573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4091800905331877267352389 767212669749726987628573)
                    ·
                      rfl

theorem cell22_2241212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_2241212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241212 prefixEnd_2241212 := by exact prefixLift 2241212
  have htrace : WordTrace (prefixWord ++ tailWord_2241212) baseStart_2241212 baseEnd_2241212 := by
    simpa [prefixWord, tailWord_2241212, baseEnd_2241212] using wordTrace_append hprefix tailTrace_2241212
  have hstable : (prefixWord ++ tailWord_2241212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241212).length < 2 ^ (prefixWord ++ tailWord_2241212).sum := by decide
  have hdescent : baseEnd_2241212 < baseStart_2241212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241237 : List Nat := [1, 3, 2, 5, 2, 1, 2, 2, 1, 3]
def baseStart_2241237 : Nat := 118140960795 + 2241237 * 2 ^ 59
def prefixEnd_2241237 : Nat := 4983230072969 + 3 ^ 40 * 2241237 * 2
def baseEnd_2241237 : Nat := 767221227760635255753497

theorem tailTrace_2241237 : CollatzResearch.WordTrace tailWord_2241237 prefixEnd_2241237 767221227760635255753497 := by
  unfold tailWord_2241237
  simp only [CollatzResearch.WordTrace]
  refine ⟨81744628981388596650609965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54496419320925731100406643 81744628981388596650609965)
  ·
    refine ⟨30654235868020723743978737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81744628981388596650609965 30654235868020723743978737)
    ·
      refine ⟨22990676901015542807984053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30654235868020723743978737 22990676901015542807984053)
      ·
        refine ⟨2155375959470207138248505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22990676901015542807984053 2155375959470207138248505)
        ·
          refine ⟨1616531969602655353686379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2155375959470207138248505 1616531969602655353686379)
          ·
            refine ⟨2424797954403983030529569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1616531969602655353686379 2424797954403983030529569)
            ·
              refine ⟨1818598465802987272897177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2424797954403983030529569 1818598465802987272897177)
              ·
                refine ⟨1363948849352240454672883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1818598465802987272897177 1363948849352240454672883)
                ·
                  refine ⟨2045923274028360682009325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363948849352240454672883 2045923274028360682009325)
                  ·
                    refine ⟨767221227760635255753497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2045923274028360682009325 767221227760635255753497)
                    ·
                      rfl

theorem cell22_2241237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_2241237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241237 prefixEnd_2241237 := by exact prefixLift 2241237
  have htrace : WordTrace (prefixWord ++ tailWord_2241237) baseStart_2241237 baseEnd_2241237 := by
    simpa [prefixWord, tailWord_2241237, baseEnd_2241237] using wordTrace_append hprefix tailTrace_2241237
  have hstable : (prefixWord ++ tailWord_2241237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241237).length < 2 ^ (prefixWord ++ tailWord_2241237).sum := by decide
  have hdescent : baseEnd_2241237 < baseStart_2241237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241272 : List Nat := [2, 1, 2, 1, 1, 2, 7, 6]
def baseStart_2241272 : Nat := 118140960795 + 2241272 * 2 ^ 59
def prefixEnd_2241272 : Nat := 4983230072969 + 3 ^ 40 * 2241272 * 2
def baseEnd_2241272 : Nat := 85248134330656314569821

theorem tailTrace_2241272 : CollatzResearch.WordTrace tailWord_2241272 prefixEnd_2241272 85248134330656314569821 := by
  unfold tailWord_2241272
  simp only [CollatzResearch.WordTrace]
  refine ⟨40872952768130898814067035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54497270357507865085422713 40872952768130898814067035)
  ·
    refine ⟨61309429152196348221100553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40872952768130898814067035 61309429152196348221100553)
    ·
      refine ⟨45982071864147261165825415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61309429152196348221100553 45982071864147261165825415)
      ·
        refine ⟨68973107796220891748738123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45982071864147261165825415 68973107796220891748738123)
        ·
          refine ⟨103459661694331337623107185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68973107796220891748738123 103459661694331337623107185)
          ·
            refine ⟨77594746270748503217330389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103459661694331337623107185 77594746270748503217330389)
            ·
              refine ⟨1818626865720668044156181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 77594746270748503217330389 1818626865720668044156181)
              ·
                refine ⟨85248134330656314569821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1818626865720668044156181 85248134330656314569821)
                ·
                  rfl

theorem cell22_2241272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 6].length) (baseStart_2241272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241272 prefixEnd_2241272 := by exact prefixLift 2241272
  have htrace : WordTrace (prefixWord ++ tailWord_2241272) baseStart_2241272 baseEnd_2241272 := by
    simpa [prefixWord, tailWord_2241272, baseEnd_2241272] using wordTrace_append hprefix tailTrace_2241272
  have hstable : (prefixWord ++ tailWord_2241272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241272).length < 2 ^ (prefixWord ++ tailWord_2241272).sum := by decide
  have hdescent : baseEnd_2241272 < baseStart_2241272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241392 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 1, 6]
def baseStart_2241392 : Nat := 118140960795 + 2241392 * 2 ^ 59
def prefixEnd_2241392 : Nat := 4983230072969 + 3 ^ 40 * 2241392 * 2
def baseEnd_2241392 : Nat := 767274287428266518128021

theorem tailTrace_2241392 : CollatzResearch.WordTrace tailWord_2241392 prefixEnd_2241392 767274287428266518128021 := by
  unfold tailWord_2241392
  simp only [CollatzResearch.WordTrace]
  refine ⟨40875141147913529061251215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54500188197218038748334953 40875141147913529061251215)
  ·
    refine ⟨61312711721870293591876823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40875141147913529061251215 61312711721870293591876823)
    ·
      refine ⟨91969067582805440387815235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61312711721870293591876823 91969067582805440387815235)
      ·
        refine ⟨137953601374208160581722853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91969067582805440387815235 137953601374208160581722853)
        ·
          refine ⟨25866300257664030109073035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137953601374208160581722853 25866300257664030109073035)
          ·
            refine ⟨38799450386496045163609553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25866300257664030109073035 38799450386496045163609553)
            ·
              refine ⟨29099587789872033872707165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38799450386496045163609553 29099587789872033872707165)
              ·
                refine ⟨10912345421202012702265187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29099587789872033872707165 10912345421202012702265187)
                ·
                  refine ⟨16368518131803019053397781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10912345421202012702265187 16368518131803019053397781)
                  ·
                    refine ⟨767274287428266518128021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16368518131803019053397781 767274287428266518128021)
                    ·
                      rfl

theorem cell22_2241392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_2241392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241392 prefixEnd_2241392 := by exact prefixLift 2241392
  have htrace : WordTrace (prefixWord ++ tailWord_2241392) baseStart_2241392 baseEnd_2241392 := by
    simpa [prefixWord, tailWord_2241392, baseEnd_2241392] using wordTrace_append hprefix tailTrace_2241392
  have hstable : (prefixWord ++ tailWord_2241392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241392).length < 2 ^ (prefixWord ++ tailWord_2241392).sum := by decide
  have hdescent : baseEnd_2241392 < baseStart_2241392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241394 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 6, 3]
def baseStart_2241394 : Nat := 118140960795 + 2241394 * 2 ^ 59
def prefixEnd_2241394 : Nat := 4983230072969 + 3 ^ 40 * 2241394 * 2
def baseEnd_2241394 : Nat := 767274972069139179578015

theorem tailTrace_2241394 : CollatzResearch.WordTrace tailWord_2241394 prefixEnd_2241394 767274972069139179578015 := by
  unfold tailWord_2241394
  simp only [CollatzResearch.WordTrace]
  refine ⟨20437588810454953116018809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54500236827879874976050157 20437588810454953116018809)
  ·
    refine ⟨15328191607841214837014107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20437588810454953116018809 15328191607841214837014107)
    ·
      refine ⟨22992287411761822255521161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15328191607841214837014107 22992287411761822255521161)
      ·
        refine ⟨17244215558821366691640871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22992287411761822255521161 17244215558821366691640871)
        ·
          refine ⟨25866323338232050037461307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17244215558821366691640871 25866323338232050037461307)
          ·
            refine ⟨38799485007348075056191961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25866323338232050037461307 38799485007348075056191961)
            ·
              refine ⟨29099613755511056292143971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38799485007348075056191961 29099613755511056292143971)
              ·
                refine ⟨43649420633266584438215957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29099613755511056292143971 43649420633266584438215957)
                ·
                  refine ⟨2046066592184371145541373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43649420633266584438215957 2046066592184371145541373)
                  ·
                    refine ⟨767274972069139179578015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2046066592184371145541373 767274972069139179578015)
                    ·
                      rfl

theorem cell22_2241394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_2241394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241394 prefixEnd_2241394 := by exact prefixLift 2241394
  have htrace : WordTrace (prefixWord ++ tailWord_2241394) baseStart_2241394 baseEnd_2241394 := by
    simpa [prefixWord, tailWord_2241394, baseEnd_2241394] using wordTrace_append hprefix tailTrace_2241394
  have hstable : (prefixWord ++ tailWord_2241394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241394).length < 2 ^ (prefixWord ++ tailWord_2241394).sum := by decide
  have hdescent : baseEnd_2241394 < baseStart_2241394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241411 : List Nat := [1, 1, 1, 3, 4, 1, 4, 2, 2, 3]
def baseStart_2241411 : Nat := 118140960795 + 2241411 * 2 ^ 59
def prefixEnd_2241411 : Nat := 4983230072969 + 3 ^ 40 * 2241411 * 2
def baseEnd_2241411 : Nat := 767280791516556801902963

theorem tailTrace_2241411 : CollatzResearch.WordTrace tailWord_2241411 prefixEnd_2241411 767280791516556801902963 := by
  unfold tailWord_2241411
  simp only [CollatzResearch.WordTrace]
  refine ⟨81750975282758224367444087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54500650188505482911629391 81750975282758224367444087)
  ·
    refine ⟨122626462924137336551166131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81750975282758224367444087 122626462924137336551166131)
    ·
      refine ⟨183939694386206004826749197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122626462924137336551166131 183939694386206004826749197)
      ·
        refine ⟨68977385394827251810030949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183939694386206004826749197 68977385394827251810030949)
        ·
          refine ⟨12933259761530109714380803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68977385394827251810030949 12933259761530109714380803)
          ·
            refine ⟨19399889642295164571571205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12933259761530109714380803 19399889642295164571571205)
            ·
              refine ⟨3637479307930343357169601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19399889642295164571571205 3637479307930343357169601)
              ·
                refine ⟨2728109480947757517877201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3637479307930343357169601 2728109480947757517877201)
                ·
                  refine ⟨2046082110710818138407901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2728109480947757517877201 2046082110710818138407901)
                  ·
                    refine ⟨767280791516556801902963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2046082110710818138407901 767280791516556801902963)
                    ·
                      rfl

theorem cell22_2241411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 3].length) (baseStart_2241411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241411 prefixEnd_2241411 := by exact prefixLift 2241411
  have htrace : WordTrace (prefixWord ++ tailWord_2241411) baseStart_2241411 baseEnd_2241411 := by
    simpa [prefixWord, tailWord_2241411, baseEnd_2241411] using wordTrace_append hprefix tailTrace_2241411
  have hstable : (prefixWord ++ tailWord_2241411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241411).length < 2 ^ (prefixWord ++ tailWord_2241411).sum := by decide
  have hdescent : baseEnd_2241411 < baseStart_2241411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241413 : List Nat := [1, 3, 1, 1, 3, 5, 2, 2, 4]
def baseStart_2241413 : Nat := 118140960795 + 2241413 * 2 ^ 59
def prefixEnd_2241413 : Nat := 4983230072969 + 3 ^ 40 * 2241413 * 2
def baseEnd_2241413 : Nat := 255760492052476487784319

theorem tailTrace_2241413 : CollatzResearch.WordTrace tailWord_2241413 prefixEnd_2241413 255760492052476487784319 := by
  unfold tailWord_2241413
  simp only [CollatzResearch.WordTrace]
  refine ⟨81751048228750978709016893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54500698819167319139344595 81751048228750978709016893)
  ·
    refine ⟨30656643085781617015881335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81751048228750978709016893 30656643085781617015881335)
    ·
      refine ⟨45984964628672425523822003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30656643085781617015881335 45984964628672425523822003)
      ·
        refine ⟨68977446943008638285733005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45984964628672425523822003 68977446943008638285733005)
        ·
          refine ⟨25866542603628239357149877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68977446943008638285733005 25866542603628239357149877)
          ·
            refine ⟨2424988369090147439732801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25866542603628239357149877 2424988369090147439732801)
            ·
              refine ⟨1818741276817610579799601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2424988369090147439732801 1818741276817610579799601)
              ·
                refine ⟨1364055957613207934849701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1818741276817610579799601 1364055957613207934849701)
                ·
                  refine ⟨255760492052476487784319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1364055957613207934849701 255760492052476487784319)
                  ·
                    rfl

theorem cell22_2241413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_2241413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241413 prefixEnd_2241413 := by exact prefixLift 2241413
  have htrace : WordTrace (prefixWord ++ tailWord_2241413) baseStart_2241413 baseEnd_2241413 := by
    simpa [prefixWord, tailWord_2241413, baseEnd_2241413] using wordTrace_append hprefix tailTrace_2241413
  have hstable : (prefixWord ++ tailWord_2241413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241413).length < 2 ^ (prefixWord ++ tailWord_2241413).sum := by decide
  have hdescent : baseEnd_2241413 < baseStart_2241413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241441 : List Nat := [1, 2, 3, 4, 1, 2, 3, 6]
def baseStart_2241441 : Nat := 118140960795 + 2241441 * 2 ^ 59
def prefixEnd_2241441 : Nat := 4983230072969 + 3 ^ 40 * 2241441 * 2
def baseEnd_2241441 : Nat := 85254562347738524850319

theorem tailTrace_2241441 : CollatzResearch.WordTrace tailWord_2241441 prefixEnd_2241441 85254562347738524850319 := by
  unfold tailWord_2241441
  simp only [CollatzResearch.WordTrace]
  refine ⟨81752069472649539491036177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54501379648433026327357451 81752069472649539491036177)
  ·
    refine ⟨61314052104487154618277133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81752069472649539491036177 61314052104487154618277133)
    ·
      refine ⟨22992769539182682981853925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61314052104487154618277133 22992769539182682981853925)
      ·
        refine ⟨4311144288596753059097611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22992769539182682981853925 4311144288596753059097611)
        ·
          refine ⟨6466716432895129588646417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4311144288596753059097611 6466716432895129588646417)
          ·
            refine ⟨4850037324671347191484813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6466716432895129588646417 4850037324671347191484813)
            ·
              refine ⟨1818763996751755196806805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4850037324671347191484813 1818763996751755196806805)
              ·
                refine ⟨85254562347738524850319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1818763996751755196806805 85254562347738524850319)
                ·
                  rfl

theorem cell22_2241441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 6].length) (baseStart_2241441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241441 prefixEnd_2241441 := by exact prefixLift 2241441
  have htrace : WordTrace (prefixWord ++ tailWord_2241441) baseStart_2241441 baseEnd_2241441 := by
    simpa [prefixWord, tailWord_2241441, baseEnd_2241441] using wordTrace_append hprefix tailTrace_2241441
  have hstable : (prefixWord ++ tailWord_2241441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241441).length < 2 ^ (prefixWord ++ tailWord_2241441).sum := by decide
  have hdescent : baseEnd_2241441 < baseStart_2241441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241452 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 9]
def baseStart_2241452 : Nat := 118140960795 + 2241452 * 2 ^ 59
def prefixEnd_2241452 : Nat := 4983230072969 + 3 ^ 40 * 2241452 * 2
def baseEnd_2241452 : Nat := 255764942218148787209279

theorem tailTrace_2241452 : CollatzResearch.WordTrace tailWord_2241452 prefixEnd_2241452 255764942218148787209279 := by
  unfold tailWord_2241452
  simp only [CollatzResearch.WordTrace]
  refine ⟨40876235337804844184843305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54501647117073125579791073 40876235337804844184843305)
  ·
    refine ⟨30657176503353633138632479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40876235337804844184843305 30657176503353633138632479)
    ·
      refine ⟨45985764755030449707948719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30657176503353633138632479 45985764755030449707948719)
      ·
        refine ⟨68978647132545674561923079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45985764755030449707948719 68978647132545674561923079)
        ·
          refine ⟨103467970698818511842884619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68978647132545674561923079 103467970698818511842884619)
          ·
            refine ⟨155201956048227767764326929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103467970698818511842884619 155201956048227767764326929)
            ·
              refine ⟨116401467036170825823245197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155201956048227767764326929 116401467036170825823245197)
              ·
                refine ⟨43650550138564059683716949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116401467036170825823245197 43650550138564059683716949)
                ·
                  refine ⟨255764942218148787209279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43650550138564059683716949 255764942218148787209279)
                  ·
                    rfl

theorem cell22_2241452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_2241452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241452 prefixEnd_2241452 := by exact prefixLift 2241452
  have htrace : WordTrace (prefixWord ++ tailWord_2241452) baseStart_2241452 baseEnd_2241452 := by
    simpa [prefixWord, tailWord_2241452, baseEnd_2241452] using wordTrace_append hprefix tailTrace_2241452
  have hstable : (prefixWord ++ tailWord_2241452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241452).length < 2 ^ (prefixWord ++ tailWord_2241452).sum := by decide
  have hdescent : baseEnd_2241452 < baseStart_2241452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241462 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2241462 : Nat := 118140960795 + 2241462 * 2 ^ 59
def prefixEnd_2241462 : Nat := 4983230072969 + 3 ^ 40 * 2241462 * 2
def baseEnd_2241462 : Nat := 767298249858809668877807

theorem tailTrace_2241462 : CollatzResearch.WordTrace tailWord_2241462 prefixEnd_2241462 767298249858809668877807 := by
  unfold tailWord_2241462
  simp only [CollatzResearch.WordTrace]
  refine ⟨5109552212848341254846915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54501890270382306718367093 5109552212848341254846915)
  ·
    refine ⟨7664328319272511882270373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5109552212848341254846915 7664328319272511882270373)
    ·
      refine ⟨1437061559863595977925695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7664328319272511882270373 1437061559863595977925695)
      ·
        refine ⟨2155592339795393966888543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1437061559863595977925695 2155592339795393966888543)
        ·
          refine ⟨3233388509693090950332815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2155592339795393966888543 3233388509693090950332815)
          ·
            refine ⟨4850082764539636425499223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3233388509693090950332815 4850082764539636425499223)
            ·
              refine ⟨7275124146809454638248835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4850082764539636425499223 7275124146809454638248835)
              ·
                refine ⟨10912686220214181957373253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7275124146809454638248835 10912686220214181957373253)
                ·
                  refine ⟨2046128666290159117007485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10912686220214181957373253 2046128666290159117007485)
                  ·
                    refine ⟨767298249858809668877807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2046128666290159117007485 767298249858809668877807)
                    ·
                      rfl

theorem cell22_2241462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2241462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241462 prefixEnd_2241462 := by exact prefixLift 2241462
  have htrace : WordTrace (prefixWord ++ tailWord_2241462) baseStart_2241462 baseEnd_2241462 := by
    simpa [prefixWord, tailWord_2241462, baseEnd_2241462] using wordTrace_append hprefix tailTrace_2241462
  have hstable : (prefixWord ++ tailWord_2241462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241462).length < 2 ^ (prefixWord ++ tailWord_2241462).sum := by decide
  have hdescent : baseEnd_2241462 < baseStart_2241462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241484 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 2, 5]
def baseStart_2241484 : Nat := 118140960795 + 2241484 * 2 ^ 59
def prefixEnd_2241484 : Nat := 4983230072969 + 3 ^ 40 * 2241484 * 2
def baseEnd_2241484 : Nat := 767305780908408944827739

theorem tailTrace_2241484 : CollatzResearch.WordTrace tailWord_2241484 prefixEnd_2241484 767305780908408944827739 := by
  unfold tailWord_2241484
  simp only [CollatzResearch.WordTrace]
  refine ⟨40876818905746878917425753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54502425207662505223234337 40876818905746878917425753)
  ·
    refine ⟨30657614179310159188069315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40876818905746878917425753 30657614179310159188069315)
    ·
      refine ⟨45986421268965238782103973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30657614179310159188069315 45986421268965238782103973)
      ·
        refine ⟨8622453987930982271644495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45986421268965238782103973 8622453987930982271644495)
        ·
          refine ⟨12933680981896473407466743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8622453987930982271644495 12933680981896473407466743)
          ·
            refine ⟨19400521472844710111200115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12933680981896473407466743 19400521472844710111200115)
            ·
              refine ⟨29100782209267065166800173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19400521472844710111200115 29100782209267065166800173)
              ·
                refine ⟨10912793328475149437550065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29100782209267065166800173 10912793328475149437550065)
                ·
                  refine ⟨8184594996356362078162549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10912793328475149437550065 8184594996356362078162549)
                  ·
                    refine ⟨767305780908408944827739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8184594996356362078162549 767305780908408944827739)
                    ·
                      rfl

theorem cell22_2241484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_2241484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241484 prefixEnd_2241484 := by exact prefixLift 2241484
  have htrace : WordTrace (prefixWord ++ tailWord_2241484) baseStart_2241484 baseEnd_2241484 := by
    simpa [prefixWord, tailWord_2241484, baseEnd_2241484] using wordTrace_append hprefix tailTrace_2241484
  have hstable : (prefixWord ++ tailWord_2241484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241484).length < 2 ^ (prefixWord ++ tailWord_2241484).sum := by decide
  have hdescent : baseEnd_2241484 < baseStart_2241484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241591 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 3, 3]
def baseStart_2241591 : Nat := 118140960795 + 2241591 * 2 ^ 59
def prefixEnd_2241591 : Nat := 4983230072969 + 3 ^ 40 * 2241591 * 2
def baseEnd_2241591 : Nat := 767342409195096332402411

theorem tailTrace_2241591 : CollatzResearch.WordTrace tailWord_2241591 prefixEnd_2241591 767342409195096332402411 := by
  unfold tailWord_2241591
  simp only [CollatzResearch.WordTrace]
  refine ⟨81757540422106115108996627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54505026948070743405997751 81757540422106115108996627)
  ·
    refine ⟨122636310633159172663494941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81757540422106115108996627 122636310633159172663494941)
    ·
      refine ⟨45988616487434689748810603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122636310633159172663494941 45988616487434689748810603)
      ·
        refine ⟨68982924731152034623215905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45988616487434689748810603 68982924731152034623215905)
        ·
          refine ⟨51737193548364025967411929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68982924731152034623215905 51737193548364025967411929)
          ·
            refine ⟨38802895161273019475558947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51737193548364025967411929 38802895161273019475558947)
            ·
              refine ⟨58204342741909529213338421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38802895161273019475558947 58204342741909529213338421)
              ·
                refine ⟨5456657132054018363750477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58204342741909529213338421 5456657132054018363750477)
                ·
                  refine ⟨2046246424520256886406429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5456657132054018363750477 2046246424520256886406429)
                  ·
                    refine ⟨767342409195096332402411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2046246424520256886406429 767342409195096332402411)
                    ·
                      rfl

theorem cell22_2241591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_2241591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241591 prefixEnd_2241591 := by exact prefixLift 2241591
  have htrace : WordTrace (prefixWord ++ tailWord_2241591) baseStart_2241591 baseEnd_2241591 := by
    simpa [prefixWord, tailWord_2241591, baseEnd_2241591] using wordTrace_append hprefix tailTrace_2241591
  have hstable : (prefixWord ++ tailWord_2241591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241591).length < 2 ^ (prefixWord ++ tailWord_2241591).sum := by decide
  have hdescent : baseEnd_2241591 < baseStart_2241591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241619 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 4, 5]
def baseStart_2241619 : Nat := 118140960795 + 2241619 * 2 ^ 59
def prefixEnd_2241619 : Nat := 4983230072969 + 3 ^ 40 * 2241619 * 2
def baseEnd_2241619 : Nat := 767351994167313592702325

theorem tailTrace_2241619 : CollatzResearch.WordTrace tailWord_2241619 prefixEnd_2241619 767351994167313592702325 := by
  unfold tailWord_2241619
  simp only [CollatzResearch.WordTrace]
  refine ⟨81758561666004675891015911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54505707777336450594010607 81758561666004675891015911)
  ·
    refine ⟨122637842499007013836523867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81758561666004675891015911 122637842499007013836523867)
    ·
      refine ⟨183956763748510520754785801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122637842499007013836523867 183956763748510520754785801)
      ·
        refine ⟨137967572811382890566089351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183956763748510520754785801 137967572811382890566089351)
        ·
          refine ⟨206951359217074335849134027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137967572811382890566089351 206951359217074335849134027)
          ·
            refine ⟨310427038825611503773701041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206951359217074335849134027 310427038825611503773701041)
            ·
              refine ⟨232820279119208627830275781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310427038825611503773701041 232820279119208627830275781)
              ·
                refine ⟨43653802334851617718176709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 232820279119208627830275781 43653802334851617718176709)
                ·
                  refine ⟨8185087937784678322158133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43653802334851617718176709 8185087937784678322158133)
                  ·
                    refine ⟨767351994167313592702325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8185087937784678322158133 767351994167313592702325)
                    ·
                      rfl

theorem cell22_2241619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 5].length) (baseStart_2241619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241619 prefixEnd_2241619 := by exact prefixLift 2241619
  have htrace : WordTrace (prefixWord ++ tailWord_2241619) baseStart_2241619 baseEnd_2241619 := by
    simpa [prefixWord, tailWord_2241619, baseEnd_2241619] using wordTrace_append hprefix tailTrace_2241619
  have hstable : (prefixWord ++ tailWord_2241619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241619).length < 2 ^ (prefixWord ++ tailWord_2241619).sum := by decide
  have hdescent : baseEnd_2241619 < baseStart_2241619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241668 : List Nat := [2, 3, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_2241668 : Nat := 118140960795 + 2241668 * 2 ^ 59
def prefixEnd_2241668 : Nat := 4983230072969 + 3 ^ 40 * 2241668 * 2
def baseEnd_2241668 : Nat := 767368767868693798227175

theorem tailTrace_2241668 : CollatzResearch.WordTrace tailWord_2241668 prefixEnd_2241668 767368767868693798227175 := by
  unfold tailWord_2241668
  simp only [CollatzResearch.WordTrace]
  refine ⟨40880174421413578629774829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54506899228551438173033105 40880174421413578629774829)
  ·
    refine ⟨15330065408030091986165561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40880174421413578629774829 15330065408030091986165561)
    ·
      refine ⟨11497549056022568989624171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15330065408030091986165561 11497549056022568989624171)
      ·
        refine ⟨17246323584033853484436257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11497549056022568989624171 17246323584033853484436257)
        ·
          refine ⟨12934742688025390113327193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17246323584033853484436257 12934742688025390113327193)
          ·
            refine ⟨9701057016019042584995395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12934742688025390113327193 9701057016019042584995395)
            ·
              refine ⟨14551585524028563877493093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9701057016019042584995395 14551585524028563877493093)
              ·
                refine ⟨2728422285755355727029955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14551585524028563877493093 2728422285755355727029955)
                ·
                  refine ⟨4092633428633033590544933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2728422285755355727029955 4092633428633033590544933)
                  ·
                    refine ⟨767368767868693798227175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4092633428633033590544933 767368767868693798227175)
                    ·
                      rfl

theorem cell22_2241668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_2241668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241668 prefixEnd_2241668 := by exact prefixLift 2241668
  have htrace : WordTrace (prefixWord ++ tailWord_2241668) baseStart_2241668 baseEnd_2241668 := by
    simpa [prefixWord, tailWord_2241668, baseEnd_2241668] using wordTrace_append hprefix tailTrace_2241668
  have hstable : (prefixWord ++ tailWord_2241668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241668).length < 2 ^ (prefixWord ++ tailWord_2241668).sum := by decide
  have hdescent : baseEnd_2241668 < baseStart_2241668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241683 : List Nat := [1, 1, 1, 2, 1, 2, 7, 3, 4]
def baseStart_2241683 : Nat := 118140960795 + 2241683 * 2 ^ 59
def prefixEnd_2241683 : Nat := 4983230072969 + 3 ^ 40 * 2241683 * 2
def baseEnd_2241683 : Nat := 255791300891746253034043

theorem tailTrace_2241683 : CollatzResearch.WordTrace tailWord_2241683 prefixEnd_2241683 255791300891746253034043 := by
  unfold tailWord_2241683
  simp only [CollatzResearch.WordTrace]
  refine ⟨81760895937772814821345703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54507263958515209880897135 81760895937772814821345703)
  ·
    refine ⟨122641343906659222232018555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81760895937772814821345703 122641343906659222232018555)
    ·
      refine ⟨183962015859988833348027833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122641343906659222232018555 183962015859988833348027833)
      ·
        refine ⟨137971511894991625011020875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183962015859988833348027833 137971511894991625011020875)
        ·
          refine ⟨206957267842487437516531313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137971511894991625011020875 206957267842487437516531313)
          ·
            refine ⟨155217950881865578137398485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206957267842487437516531313 155217950881865578137398485)
            ·
              refine ⟨3637920723793724487595277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 155217950881865578137398485 3637920723793724487595277)
              ·
                refine ⟨1364220271422646682848229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3637920723793724487595277 1364220271422646682848229)
                ·
                  refine ⟨255791300891746253034043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1364220271422646682848229 255791300891746253034043)
                  ·
                    rfl

theorem cell22_2241683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 4].length) (baseStart_2241683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241683 prefixEnd_2241683 := by exact prefixLift 2241683
  have htrace : WordTrace (prefixWord ++ tailWord_2241683) baseStart_2241683 baseEnd_2241683 := by
    simpa [prefixWord, tailWord_2241683, baseEnd_2241683] using wordTrace_append hprefix tailTrace_2241683
  have hstable : (prefixWord ++ tailWord_2241683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241683).length < 2 ^ (prefixWord ++ tailWord_2241683).sum := by decide
  have hdescent : baseEnd_2241683 < baseStart_2241683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241715 : List Nat := [1, 1, 1, 2, 3, 2, 6, 1, 2, 3]
def baseStart_2241715 : Nat := 118140960795 + 2241715 * 2 ^ 59
def prefixEnd_2241715 : Nat := 4983230072969 + 3 ^ 40 * 2241715 * 2
def baseEnd_2241715 : Nat := 767384856929201342302031

theorem tailTrace_2241715 : CollatzResearch.WordTrace tailWord_2241715 prefixEnd_2241715 767384856929201342302031 := by
  unfold tailWord_2241715
  simp only [CollatzResearch.WordTrace]
  refine ⟨81762063073656884286510599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54508042049104589524340399 81762063073656884286510599)
  ·
    refine ⟨122643094610485326429765899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81762063073656884286510599 122643094610485326429765899)
    ·
      refine ⟨183964641915727989644648849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122643094610485326429765899 183964641915727989644648849)
      ·
        refine ⟨137973481436795992233486637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183964641915727989644648849 137973481436795992233486637)
        ·
          refine ⟨51740055538798497087557489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137973481436795992233486637 51740055538798497087557489)
          ·
            refine ⟨38805041654098872815668117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51740055538798497087557489 38805041654098872815668117)
            ·
              refine ⟨1818986327535884663234443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38805041654098872815668117 1818986327535884663234443)
              ·
                refine ⟨2728479491303826994851665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1818986327535884663234443 2728479491303826994851665)
                ·
                  refine ⟨2046359618477870246138749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2728479491303826994851665 2046359618477870246138749)
                  ·
                    refine ⟨767384856929201342302031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2046359618477870246138749 767384856929201342302031)
                    ·
                      rfl

theorem cell22_2241715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 2, 3].length) (baseStart_2241715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241715 prefixEnd_2241715 := by exact prefixLift 2241715
  have htrace : WordTrace (prefixWord ++ tailWord_2241715) baseStart_2241715 baseEnd_2241715 := by
    simpa [prefixWord, tailWord_2241715, baseEnd_2241715] using wordTrace_append hprefix tailTrace_2241715
  have hstable : (prefixWord ++ tailWord_2241715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241715).length < 2 ^ (prefixWord ++ tailWord_2241715).sum := by decide
  have hdescent : baseEnd_2241715 < baseStart_2241715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241771 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 1, 7]
def baseStart_2241771 : Nat := 118140960795 + 2241771 * 2 ^ 59
def prefixEnd_2241771 : Nat := 4983230072969 + 3 ^ 40 * 2241771 * 2
def baseEnd_2241771 : Nat := 767404026873635862901859

theorem tailTrace_2241771 : CollatzResearch.WordTrace tailWord_2241771 prefixEnd_2241771 767404026873635862901859 := by
  unfold tailWord_2241771
  simp only [CollatzResearch.WordTrace]
  refine ⟨81764105561454005850549167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54509403707636003900366111 81764105561454005850549167)
  ·
    refine ⟨122646158342181008775823751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81764105561454005850549167 122646158342181008775823751)
    ·
      refine ⟨183969237513271513163735627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122646158342181008775823751 183969237513271513163735627)
      ·
        refine ⟨275953856269907269745603441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183969237513271513163735627 275953856269907269745603441)
        ·
          refine ⟨206965392202430452309202581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275953856269907269745603441 206965392202430452309202581)
          ·
            refine ⟨9701502759488927451993871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 206965392202430452309202581 9701502759488927451993871)
            ·
              refine ⟨14552254139233391177990807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9701502759488927451993871 14552254139233391177990807)
              ·
                refine ⟨21828381208850086766986211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14552254139233391177990807 21828381208850086766986211)
                ·
                  refine ⟨32742571813275130150479317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21828381208850086766986211 32742571813275130150479317)
                  ·
                    refine ⟨767404026873635862901859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32742571813275130150479317 767404026873635862901859)
                    ·
                      rfl

theorem cell22_2241771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 7].length) (baseStart_2241771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241771 prefixEnd_2241771 := by exact prefixLift 2241771
  have htrace : WordTrace (prefixWord ++ tailWord_2241771) baseStart_2241771 baseEnd_2241771 := by
    simpa [prefixWord, tailWord_2241771, baseEnd_2241771] using wordTrace_append hprefix tailTrace_2241771
  have hstable : (prefixWord ++ tailWord_2241771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241771).length < 2 ^ (prefixWord ++ tailWord_2241771).sum := by decide
  have hdescent : baseEnd_2241771 < baseStart_2241771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241801 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 8]
def baseStart_2241801 : Nat := 118140960795 + 2241801 * 2 ^ 59
def prefixEnd_2241801 : Nat := 4983230072969 + 3 ^ 40 * 2241801 * 2
def baseEnd_2241801 : Nat := 255804765495575261550589

theorem tailTrace_2241801 : CollatzResearch.WordTrace tailWord_2241801 prefixEnd_2241801 255804765495575261550589 := by
  unfold tailWord_2241801
  simp only [CollatzResearch.WordTrace]
  refine ⟨81765199751345320974141257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54510133167563547316094171 81765199751345320974141257)
  ·
    refine ⟨61323899813508990730605943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81765199751345320974141257 61323899813508990730605943)
    ·
      refine ⟨91985849720263486095908915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61323899813508990730605943 91985849720263486095908915)
      ·
        refine ⟨137978774580395229143863373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91985849720263486095908915 137978774580395229143863373)
        ·
          refine ⟨51742040467648210928948765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137978774580395229143863373 51742040467648210928948765)
          ·
            refine ⟨19403265175368079098355787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51742040467648210928948765 19403265175368079098355787)
            ·
              refine ⟨29104897763052118647533681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19403265175368079098355787 29104897763052118647533681)
              ·
                refine ⟨21828673322289088985650261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29104897763052118647533681 21828673322289088985650261)
                ·
                  refine ⟨255804765495575261550589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21828673322289088985650261 255804765495575261550589)
                  ·
                    rfl

theorem cell22_2241801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 8].length) (baseStart_2241801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241801 prefixEnd_2241801 := by exact prefixLift 2241801
  have htrace : WordTrace (prefixWord ++ tailWord_2241801) baseStart_2241801 baseEnd_2241801 := by
    simpa [prefixWord, tailWord_2241801, baseEnd_2241801] using wordTrace_append hprefix tailTrace_2241801
  have hstable : (prefixWord ++ tailWord_2241801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241801).length < 2 ^ (prefixWord ++ tailWord_2241801).sum := by decide
  have hdescent : baseEnd_2241801 < baseStart_2241801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241818 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 6]
def baseStart_2241818 : Nat := 118140960795 + 2241818 * 2 ^ 59
def prefixEnd_2241818 : Nat := 4983230072969 + 3 ^ 40 * 2241818 * 2
def baseEnd_2241818 : Nat := 255806705311381135658905

theorem tailTrace_2241818 : CollatzResearch.WordTrace tailWord_2241818 prefixEnd_2241818 255806705311381135658905 := by
  unfold tailWord_2241818
  simp only [CollatzResearch.WordTrace]
  refine ⟨20441454948070933219377527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54510546528189155251673405 20441454948070933219377527)
  ·
    refine ⟨30662182422106399829066291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20441454948070933219377527 30662182422106399829066291)
    ·
      refine ⟨45993273633159599743599437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30662182422106399829066291 45993273633159599743599437)
      ·
        refine ⟨17247477612434849903849789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45993273633159599743599437 17247477612434849903849789)
        ·
          refine ⟨6467804104663068713943671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17247477612434849903849789 6467804104663068713943671)
          ·
            refine ⟨9701706156994603070915507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6467804104663068713943671 9701706156994603070915507)
            ·
              refine ⟨14552559235491904606373261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9701706156994603070915507 14552559235491904606373261)
              ·
                refine ⟨5457209713309464227389973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14552559235491904606373261 5457209713309464227389973)
                ·
                  refine ⟨255806705311381135658905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5457209713309464227389973 255806705311381135658905)
                  ·
                    rfl

theorem cell22_2241818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_2241818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241818 prefixEnd_2241818 := by exact prefixLift 2241818
  have htrace : WordTrace (prefixWord ++ tailWord_2241818) baseStart_2241818 baseEnd_2241818 := by
    simpa [prefixWord, tailWord_2241818, baseEnd_2241818] using wordTrace_append hprefix tailTrace_2241818
  have hstable : (prefixWord ++ tailWord_2241818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241818).length < 2 ^ (prefixWord ++ tailWord_2241818).sum := by decide
  have hdescent : baseEnd_2241818 < baseStart_2241818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241837 : List Nat := [1, 5, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_2241837 : Nat := 118140960795 + 2241837 * 2 ^ 59
def prefixEnd_2241837 : Nat := 4983230072969 + 3 ^ 40 * 2241837 * 2
def baseEnd_2241837 : Nat := 767426620022433690751657

theorem tailTrace_2241837 : CollatzResearch.WordTrace tailWord_2241837 prefixEnd_2241837 767426620022433690751657 := by
  unfold tailWord_2241837
  simp only [CollatzResearch.WordTrace]
  refine ⟨81766512779214899122451765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54511008519476599414967843 81766512779214899122451765)
  ·
    refine ⟨7665610573051396792729853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81766512779214899122451765 7665610573051396792729853)
    ·
      refine ⟨2874603964894273797273695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7665610573051396792729853 2874603964894273797273695)
      ·
        refine ⟨4311905947341410695910543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2874603964894273797273695 4311905947341410695910543)
        ·
          refine ⟨6467858921012116043865815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4311905947341410695910543 6467858921012116043865815)
          ·
            refine ⟨9701788381518174065798723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6467858921012116043865815 9701788381518174065798723)
            ·
              refine ⟨14552682572277261098698085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9701788381518174065798723 14552682572277261098698085)
              ·
                refine ⟨2728627982301986456005891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14552682572277261098698085 2728627982301986456005891)
                ·
                  refine ⟨4092941973452979684008837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2728627982301986456005891 4092941973452979684008837)
                  ·
                    refine ⟨767426620022433690751657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4092941973452979684008837 767426620022433690751657)
                    ·
                      rfl

theorem cell22_2241837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_2241837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241837 prefixEnd_2241837 := by exact prefixLift 2241837
  have htrace : WordTrace (prefixWord ++ tailWord_2241837) baseStart_2241837 baseEnd_2241837 := by
    simpa [prefixWord, tailWord_2241837, baseEnd_2241837] using wordTrace_append hprefix tailTrace_2241837
  have hstable : (prefixWord ++ tailWord_2241837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241837).length < 2 ^ (prefixWord ++ tailWord_2241837).sum := by decide
  have hdescent : baseEnd_2241837 < baseStart_2241837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241848 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 2, 4]
def baseStart_2241848 : Nat := 118140960795 + 2241848 * 2 ^ 59
def prefixEnd_2241848 : Nat := 4983230072969 + 3 ^ 40 * 2241848 * 2
def baseEnd_2241848 : Nat := 767430385547233328726623

theorem tailTrace_2241848 : CollatzResearch.WordTrace tailWord_2241848 prefixEnd_2241848 767430385547233328726623 := by
  unfold tailWord_2241848
  simp only [CollatzResearch.WordTrace]
  refine ⟨40883456991087524000551099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54511275988116698667401465 40883456991087524000551099)
  ·
    refine ⟨61325185486631286000826649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40883456991087524000551099 61325185486631286000826649)
    ·
      refine ⟨45993889114973464500619987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61325185486631286000826649 45993889114973464500619987)
      ·
        refine ⟨68990833672460196750929981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45993889114973464500619987 68990833672460196750929981)
        ·
          refine ⟨25871562627172573781598743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68990833672460196750929981 25871562627172573781598743)
          ·
            refine ⟨38807343940758860672398115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25871562627172573781598743 38807343940758860672398115)
            ·
              refine ⟨58211015911138291008597173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38807343940758860672398115 58211015911138291008597173)
              ·
                refine ⟨5457282741669214782055985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58211015911138291008597173 5457282741669214782055985)
                ·
                  refine ⟨4092962056251911086541989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5457282741669214782055985 4092962056251911086541989)
                  ·
                    refine ⟨767430385547233328726623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4092962056251911086541989 767430385547233328726623)
                    ·
                      rfl

theorem cell22_2241848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_2241848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241848 prefixEnd_2241848 := by exact prefixLift 2241848
  have htrace : WordTrace (prefixWord ++ tailWord_2241848) baseStart_2241848 baseEnd_2241848 := by
    simpa [prefixWord, tailWord_2241848, baseEnd_2241848] using wordTrace_append hprefix tailTrace_2241848
  have hstable : (prefixWord ++ tailWord_2241848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241848).length < 2 ^ (prefixWord ++ tailWord_2241848).sum := by decide
  have hdescent : baseEnd_2241848 < baseStart_2241848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241852 : List Nat := [2, 2, 2, 2, 1, 5, 1, 3, 4]
def baseStart_2241852 : Nat := 118140960795 + 2241852 * 2 ^ 59
def prefixEnd_2241852 : Nat := 4983230072969 + 3 ^ 40 * 2241852 * 2
def baseEnd_2241852 : Nat := 255810584942992883875537

theorem tailTrace_2241852 : CollatzResearch.WordTrace tailWord_2241852 prefixEnd_2241852 255810584942992883875537 := by
  unfold tailWord_2241852
  simp only [CollatzResearch.WordTrace]
  refine ⟨40883529937080278342123905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54511373249440371122831873 40883529937080278342123905)
  ·
    refine ⟨30662647452810208756592929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40883529937080278342123905 30662647452810208756592929)
    ·
      refine ⟨22996985589607656567444697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30662647452810208756592929 22996985589607656567444697)
      ·
        refine ⟨17247739192205742425583523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22996985589607656567444697 17247739192205742425583523)
        ·
          refine ⟨25871608788308613638375285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17247739192205742425583523 25871608788308613638375285)
          ·
            refine ⟨2425463323903932528597683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25871608788308613638375285 2425463323903932528597683)
            ·
              refine ⟨3638194985855898792896525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2425463323903932528597683 3638194985855898792896525)
              ·
                refine ⟨1364323119695962047336197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3638194985855898792896525 1364323119695962047336197)
                ·
                  refine ⟨255810584942992883875537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1364323119695962047336197 255810584942992883875537)
                  ·
                    rfl

theorem cell22_2241852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_2241852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241852 prefixEnd_2241852 := by exact prefixLift 2241852
  have htrace : WordTrace (prefixWord ++ tailWord_2241852) baseStart_2241852 baseEnd_2241852 := by
    simpa [prefixWord, tailWord_2241852, baseEnd_2241852] using wordTrace_append hprefix tailTrace_2241852
  have hstable : (prefixWord ++ tailWord_2241852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241852).length < 2 ^ (prefixWord ++ tailWord_2241852).sum := by decide
  have hdescent : baseEnd_2241852 < baseStart_2241852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241863 : List Nat := [1, 1, 4, 1, 2, 5, 8]
def baseStart_2241863 : Nat := 118140960795 + 2241863 * 2 ^ 59
def prefixEnd_2241863 : Nat := 4983230072969 + 3 ^ 40 * 2241863 * 2
def baseEnd_2241863 : Nat := 28423537790880677392651

theorem tailTrace_2241863 : CollatzResearch.WordTrace tailWord_2241863 prefixEnd_2241863 28423537790880677392651 := by
  unfold tailWord_2241863
  simp only [CollatzResearch.WordTrace]
  refine ⟨81767461077120705562898243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54511640718080470375265495 81767461077120705562898243)
  ·
    refine ⟨122651191615681058344347365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81767461077120705562898243 122651191615681058344347365)
    ·
      refine ⟨22997098427940198439565131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122651191615681058344347365 22997098427940198439565131)
      ·
        refine ⟨34495647641910297659347697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22997098427940198439565131 34495647641910297659347697)
        ·
          refine ⟨25871735731432723244510773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34495647641910297659347697 25871735731432723244510773)
          ·
            refine ⟨2425475224821817804172885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25871735731432723244510773 2425475224821817804172885)
            ·
              refine ⟨28423537790880677392651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2425475224821817804172885 28423537790880677392651)
              ·
                rfl

theorem cell22_2241863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 8].length) (baseStart_2241863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241863 prefixEnd_2241863 := by exact prefixLift 2241863
  have htrace : WordTrace (prefixWord ++ tailWord_2241863) baseStart_2241863 baseEnd_2241863 := by
    simpa [prefixWord, tailWord_2241863, baseEnd_2241863] using wordTrace_append hprefix tailTrace_2241863
  have hstable : (prefixWord ++ tailWord_2241863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241863).length < 2 ^ (prefixWord ++ tailWord_2241863).sum := by decide
  have hdescent : baseEnd_2241863 < baseStart_2241863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241869 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 6]
def baseStart_2241869 : Nat := 118140960795 + 2241869 * 2 ^ 59
def prefixEnd_2241869 : Nat := 4983230072969 + 3 ^ 40 * 2241869 * 2
def baseEnd_2241869 : Nat := 255812524758798757983853

theorem tailTrace_2241869 : CollatzResearch.WordTrace tailWord_2241869 prefixEnd_2241869 255812524758798757983853 := by
  unfold tailWord_2241869
  simp only [CollatzResearch.WordTrace]
  refine ⟨81767679915098968587616661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54511786610065979058411107 81767679915098968587616661)
  ·
    refine ⟨3832859996020264152544531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81767679915098968587616661 3832859996020264152544531)
    ·
      refine ⟨5749289994030396228816797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3832859996020264152544531 5749289994030396228816797)
      ·
        refine ⟨2155983747761398585806299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5749289994030396228816797 2155983747761398585806299)
        ·
          refine ⟨3233975621642097878709449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2155983747761398585806299 3233975621642097878709449)
          ·
            refine ⟨2425481716231573409032087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3233975621642097878709449 2425481716231573409032087)
            ·
              refine ⟨3638222574347360113548131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2425481716231573409032087 3638222574347360113548131)
              ·
                refine ⟨5457333861521040170322197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3638222574347360113548131 5457333861521040170322197)
                ·
                  refine ⟨255812524758798757983853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5457333861521040170322197 255812524758798757983853)
                  ·
                    rfl

theorem cell22_2241869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_2241869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241869 prefixEnd_2241869 := by exact prefixLift 2241869
  have htrace : WordTrace (prefixWord ++ tailWord_2241869) baseStart_2241869 baseEnd_2241869 := by
    simpa [prefixWord, tailWord_2241869, baseEnd_2241869] using wordTrace_append hprefix tailTrace_2241869
  have hstable : (prefixWord ++ tailWord_2241869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241869).length < 2 ^ (prefixWord ++ tailWord_2241869).sum := by decide
  have hdescent : baseEnd_2241869 < baseStart_2241869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241929 : List Nat := [1, 2, 1, 1, 7, 1, 1, 4, 1, 3]
def baseStart_2241929 : Nat := 118140960795 + 2241929 * 2 ^ 59
def prefixEnd_2241929 : Nat := 4983230072969 + 3 ^ 40 * 2241929 * 2
def baseEnd_2241929 : Nat := 767458113502576117451375

theorem tailTrace_2241929 : CollatzResearch.WordTrace tailWord_2241929 prefixEnd_2241929 767458113502576117451375 := by
  unfold tailWord_2241929
  simp only [CollatzResearch.WordTrace]
  refine ⟨81769868294881598834800841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54513245529921065889867227 81769868294881598834800841)
  ·
    refine ⟨61327401221161199126100631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81769868294881598834800841 61327401221161199126100631)
    ·
      refine ⟨91991101831741798689150947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61327401221161199126100631 91991101831741798689150947)
      ·
        refine ⟨137986652747612698033726421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91991101831741798689150947 137986652747612698033726421)
        ·
          refine ⟨3234062173772172610165463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 137986652747612698033726421 3234062173772172610165463)
          ·
            refine ⟨4851093260658258915248195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3234062173772172610165463 4851093260658258915248195)
            ·
              refine ⟨7276639890987388372872293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4851093260658258915248195 7276639890987388372872293)
              ·
                refine ⟨1364369979560135319913555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7276639890987388372872293 1364369979560135319913555)
                ·
                  refine ⟨2046554969340202979870333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1364369979560135319913555 2046554969340202979870333)
                  ·
                    refine ⟨767458113502576117451375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2046554969340202979870333 767458113502576117451375)
                    ·
                      rfl

theorem cell22_2241929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 1, 3].length) (baseStart_2241929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241929 prefixEnd_2241929 := by exact prefixLift 2241929
  have htrace : WordTrace (prefixWord ++ tailWord_2241929) baseStart_2241929 baseEnd_2241929 := by
    simpa [prefixWord, tailWord_2241929, baseEnd_2241929] using wordTrace_append hprefix tailTrace_2241929
  have hstable : (prefixWord ++ tailWord_2241929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241929).length < 2 ^ (prefixWord ++ tailWord_2241929).sum := by decide
  have hdescent : baseEnd_2241929 < baseStart_2241929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241940 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_2241940 : Nat := 118140960795 + 2241940 * 2 ^ 59
def prefixEnd_2241940 : Nat := 4983230072969 + 3 ^ 40 * 2241940 * 2
def baseEnd_2241940 : Nat := 767461879027375755426341

theorem tailTrace_2241940 : CollatzResearch.WordTrace tailWord_2241940 prefixEnd_2241940 767461879027375755426341 := by
  unfold tailWord_2241940
  simp only [CollatzResearch.WordTrace]
  refine ⟨40885134748920873856725637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54513512998561165142300849 40885134748920873856725637)
  ·
    refine ⟨7665962765422663848136057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40885134748920873856725637 7665962765422663848136057)
    ·
      refine ⟨5749472074066997886102043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7665962765422663848136057 5749472074066997886102043)
      ·
        refine ⟨8624208111100496829153065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5749472074066997886102043 8624208111100496829153065)
        ·
          refine ⟨6468156083325372621864799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8624208111100496829153065 6468156083325372621864799)
          ·
            refine ⟨9702234124988058932797199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6468156083325372621864799 9702234124988058932797199)
            ·
              refine ⟨14553351187482088399195799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9702234124988058932797199 14553351187482088399195799)
              ·
                refine ⟨21830026781223132598793699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14553351187482088399195799 21830026781223132598793699)
                ·
                  refine ⟨32745040171834698898190549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21830026781223132598793699 32745040171834698898190549)
                  ·
                    refine ⟨767461879027375755426341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32745040171834698898190549 767461879027375755426341)
                    ·
                      rfl

theorem cell22_2241940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_2241940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241940 prefixEnd_2241940 := by exact prefixLift 2241940
  have htrace : WordTrace (prefixWord ++ tailWord_2241940) baseStart_2241940 baseEnd_2241940 := by
    simpa [prefixWord, tailWord_2241940, baseEnd_2241940] using wordTrace_append hprefix tailTrace_2241940
  have hstable : (prefixWord ++ tailWord_2241940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241940).length < 2 ^ (prefixWord ++ tailWord_2241940).sum := by decide
  have hdescent : baseEnd_2241940 < baseStart_2241940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241955 : List Nat := [1, 1, 1, 4, 1, 3, 2, 4, 1, 4]
def baseStart_2241955 : Nat := 118140960795 + 2241955 * 2 ^ 59
def prefixEnd_2241955 : Nat := 4983230072969 + 3 ^ 40 * 2241955 * 2
def baseEnd_2241955 : Nat := 767467013833920716301295

theorem tailTrace_2241955 : CollatzResearch.WordTrace tailWord_2241955 prefixEnd_2241955 767467013833920716301295 := by
  unfold tailWord_2241955
  simp only [CollatzResearch.WordTrace]
  refine ⟨81770816592787405275247319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54513877728524936850164879 81770816592787405275247319)
  ·
    refine ⟨122656224889181107912870979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81770816592787405275247319 122656224889181107912870979)
    ·
      refine ⟨183984337333771661869306469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122656224889181107912870979 183984337333771661869306469)
      ·
        refine ⟨34497063250082186600494963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183984337333771661869306469 34497063250082186600494963)
        ·
          refine ⟨51745594875123279900742445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34497063250082186600494963 51745594875123279900742445)
          ·
            refine ⟨19404598078171229962778417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51745594875123279900742445 19404598078171229962778417)
            ·
              refine ⟨14553448558628422472083813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19404598078171229962778417 14553448558628422472083813)
              ·
                refine ⟨2728771604742829213515715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14553448558628422472083813 2728771604742829213515715)
                ·
                  refine ⟨4093157407114243820273573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2728771604742829213515715 4093157407114243820273573)
                  ·
                    refine ⟨767467013833920716301295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4093157407114243820273573 767467013833920716301295)
                    ·
                      rfl

theorem cell22_2241955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 4].length) (baseStart_2241955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241955 prefixEnd_2241955 := by exact prefixLift 2241955
  have htrace : WordTrace (prefixWord ++ tailWord_2241955) baseStart_2241955 baseEnd_2241955 := by
    simpa [prefixWord, tailWord_2241955, baseEnd_2241955] using wordTrace_append hprefix tailTrace_2241955
  have hstable : (prefixWord ++ tailWord_2241955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241955).length < 2 ^ (prefixWord ++ tailWord_2241955).sum := by decide
  have hdescent : baseEnd_2241955 < baseStart_2241955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241968 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 3, 5]
def baseStart_2241968 : Nat := 118140960795 + 2241968 * 2 ^ 59
def prefixEnd_2241968 : Nat := 4983230072969 + 3 ^ 40 * 2241968 * 2
def baseEnd_2241968 : Nat := 767471463999593015726255

theorem tailTrace_2241968 : CollatzResearch.WordTrace tailWord_2241968 prefixEnd_2241968 767471463999593015726255 := by
  unfold tailWord_2241968
  simp only [CollatzResearch.WordTrace]
  refine ⟨40885645370870154247735279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54514193827826872330313705 40885645370870154247735279)
  ·
    refine ⟨61328468056305231371602919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40885645370870154247735279 61328468056305231371602919)
    ·
      refine ⟨91992702084457847057404379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61328468056305231371602919 91992702084457847057404379)
      ·
        refine ⟨137989053126686770586106569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91992702084457847057404379 137989053126686770586106569)
        ·
          refine ⟨103491789845015077939579927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137989053126686770586106569 103491789845015077939579927)
          ·
            refine ⟨155237684767522616909369891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103491789845015077939579927 155237684767522616909369891)
            ·
              refine ⟨232856527151283925364054837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155237684767522616909369891 232856527151283925364054837)
              ·
                refine ⟨21830299420432868002880141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 232856527151283925364054837 21830299420432868002880141)
                ·
                  refine ⟨8186362282662325501080053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21830299420432868002880141 8186362282662325501080053)
                  ·
                    refine ⟨767471463999593015726255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8186362282662325501080053 767471463999593015726255)
                    ·
                      rfl

theorem cell22_2241968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_2241968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2241968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2241968 prefixEnd_2241968 := by exact prefixLift 2241968
  have htrace : WordTrace (prefixWord ++ tailWord_2241968) baseStart_2241968 baseEnd_2241968 := by
    simpa [prefixWord, tailWord_2241968, baseEnd_2241968] using wordTrace_append hprefix tailTrace_2241968
  have hstable : (prefixWord ++ tailWord_2241968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241968).length < 2 ^ (prefixWord ++ tailWord_2241968).sum := by decide
  have hdescent : baseEnd_2241968 < baseStart_2241968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242094 : List Nat := [4, 1, 3, 1, 2, 2, 2, 2, 5]
def baseStart_2242094 : Nat := 118140960795 + 2242094 * 2 ^ 59
def prefixEnd_2242094 : Nat := 4983230072969 + 3 ^ 40 * 2242094 * 2
def baseEnd_2242094 : Nat := 255838198791523562358623

theorem tailTrace_2242094 : CollatzResearch.WordTrace tailWord_2242094 prefixEnd_2242094 255838198791523562358623 := by
  unfold tailWord_2242094
  simp only [CollatzResearch.WordTrace]
  refine ⟨10221985792410479001819667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54517257559522554676371557 10221985792410479001819667)
  ·
    refine ⟨15332978688615718502729501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10221985792410479001819667 15332978688615718502729501)
    ·
      refine ⟨5749867008230894438523563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15332978688615718502729501 5749867008230894438523563)
      ·
        refine ⟨8624800512346341657785345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5749867008230894438523563 8624800512346341657785345)
        ·
          refine ⟨6468600384259756243339009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8624800512346341657785345 6468600384259756243339009)
          ·
            refine ⟨4851450288194817182504257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6468600384259756243339009 4851450288194817182504257)
            ·
              refine ⟨3638587716146112886878193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4851450288194817182504257 3638587716146112886878193)
              ·
                refine ⟨2728940787109584665158645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3638587716146112886878193 2728940787109584665158645)
                ·
                  refine ⟨255838198791523562358623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2728940787109584665158645 255838198791523562358623)
                  ·
                    rfl

theorem cell22_2242094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_2242094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242094 prefixEnd_2242094 := by exact prefixLift 2242094
  have htrace : WordTrace (prefixWord ++ tailWord_2242094) baseStart_2242094 baseEnd_2242094 := by
    simpa [prefixWord, tailWord_2242094, baseEnd_2242094] using wordTrace_append hprefix tailTrace_2242094
  have hstable : (prefixWord ++ tailWord_2242094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242094).length < 2 ^ (prefixWord ++ tailWord_2242094).sum := by decide
  have hdescent : baseEnd_2242094 < baseStart_2242094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242154 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 4, 3]
def baseStart_2242154 : Nat := 118140960795 + 2242154 * 2 ^ 59
def prefixEnd_2242154 : Nat := 4983230072969 + 3 ^ 40 * 2242154 * 2
def baseEnd_2242154 : Nat := 767535135600750530575685

theorem tailTrace_2242154 : CollatzResearch.WordTrace tailWord_2242154 prefixEnd_2242154 767535135600750530575685 := by
  unfold tailWord_2242154
  simp only [CollatzResearch.WordTrace]
  refine ⟨20444518679766615565435379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54518716479377641507827677 20444518679766615565435379)
  ·
    refine ⟨30666778019649923348153069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20444518679766615565435379 30666778019649923348153069)
    ·
      refine ⟨11500041757368721255557401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30666778019649923348153069 11500041757368721255557401)
      ·
        refine ⟨8625031318026540941668051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11500041757368721255557401 8625031318026540941668051)
        ·
          refine ⟨12937546977039811412502077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8625031318026540941668051 12937546977039811412502077)
          ·
            refine ⟨4851580116389929279688279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12937546977039811412502077 4851580116389929279688279)
            ·
              refine ⟨7277370174584893919532419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4851580116389929279688279 7277370174584893919532419)
              ·
                refine ⟨10916055261877340879298629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7277370174584893919532419 10916055261877340879298629)
                ·
                  refine ⟨2046760361602001414868493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10916055261877340879298629 2046760361602001414868493)
                  ·
                    refine ⟨767535135600750530575685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2046760361602001414868493 767535135600750530575685)
                    ·
                      rfl

theorem cell22_2242154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_2242154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242154 prefixEnd_2242154 := by exact prefixLift 2242154
  have htrace : WordTrace (prefixWord ++ tailWord_2242154) baseStart_2242154 baseEnd_2242154 := by
    simpa [prefixWord, tailWord_2242154, baseEnd_2242154] using wordTrace_append hprefix tailTrace_2242154
  have hstable : (prefixWord ++ tailWord_2242154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242154).length < 2 ^ (prefixWord ++ tailWord_2242154).sum := by decide
  have hdescent : baseEnd_2242154 < baseStart_2242154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242184 : List Nat := [2, 1, 3, 5, 1, 1, 1, 8]
def baseStart_2242184 : Nat := 118140960795 + 2242184 * 2 ^ 59
def prefixEnd_2242184 : Nat := 4983230072969 + 3 ^ 40 * 2242184 * 2
def baseEnd_2242184 : Nat := 85282822801537828036177

theorem tailTrace_2242184 : CollatzResearch.WordTrace tailWord_2242184 prefixEnd_2242184 85282822801537828036177 := by
  unfold tailWord_2242184
  simp only [CollatzResearch.WordTrace]
  refine ⟨40889584454478888692666803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54519445939305184923555737 40889584454478888692666803)
  ·
    refine ⟨61334376681718333039000205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40889584454478888692666803 61334376681718333039000205)
    ·
      refine ⟨23000391255644374889625077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61334376681718333039000205 23000391255644374889625077)
      ·
        refine ⟨2156286680216660145902351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23000391255644374889625077 2156286680216660145902351)
        ·
          refine ⟨3234430020324990218853527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2156286680216660145902351 3234430020324990218853527)
          ·
            refine ⟨4851645030487485328280291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3234430020324990218853527 4851645030487485328280291)
            ·
              refine ⟨7277467545731227992420437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4851645030487485328280291 7277467545731227992420437)
              ·
                refine ⟨85282822801537828036177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7277467545731227992420437 85282822801537828036177)
                ·
                  rfl

theorem cell22_2242184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 8].length) (baseStart_2242184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242184 prefixEnd_2242184 := by exact prefixLift 2242184
  have htrace : WordTrace (prefixWord ++ tailWord_2242184) baseStart_2242184 baseEnd_2242184 := by
    simpa [prefixWord, tailWord_2242184, baseEnd_2242184] using wordTrace_append hprefix tailTrace_2242184
  have hstable : (prefixWord ++ tailWord_2242184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242184).length < 2 ^ (prefixWord ++ tailWord_2242184).sum := by decide
  have hdescent : baseEnd_2242184 < baseStart_2242184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242212 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 7]
def baseStart_2242212 : Nat := 118140960795 + 2242212 * 2 ^ 59
def prefixEnd_2242212 : Nat := 4983230072969 + 3 ^ 40 * 2242212 * 2
def baseEnd_2242212 : Nat := 255851663395352570875169

theorem tailTrace_2242212 : CollatzResearch.WordTrace tailWord_2242212 prefixEnd_2242212 255851663395352570875169 := by
  unfold tailWord_2242212
  simp only [CollatzResearch.WordTrace]
  refine ⟨40890095076428169083676445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54520126768570892111568593 40890095076428169083676445)
  ·
    refine ⟨15333785653660563406378667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40890095076428169083676445 15333785653660563406378667)
    ·
      refine ⟨23000678480490845109568001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15333785653660563406378667 23000678480490845109568001)
      ·
        refine ⟨17250508860368133832176001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23000678480490845109568001 17250508860368133832176001)
        ·
          refine ⟨12937881645276100374132001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17250508860368133832176001 12937881645276100374132001)
          ·
            refine ⟨9703411233957075280599001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12937881645276100374132001 9703411233957075280599001)
            ·
              refine ⟨7277558425467806460449251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9703411233957075280599001 7277558425467806460449251)
              ·
                refine ⟨10916337638201709690673877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7277558425467806460449251 10916337638201709690673877)
                ·
                  refine ⟨255851663395352570875169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10916337638201709690673877 255851663395352570875169)
                  ·
                    rfl

theorem cell22_2242212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_2242212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242212 prefixEnd_2242212 := by exact prefixLift 2242212
  have htrace : WordTrace (prefixWord ++ tailWord_2242212) baseStart_2242212 baseEnd_2242212 := by
    simpa [prefixWord, tailWord_2242212, baseEnd_2242212] using wordTrace_append hprefix tailTrace_2242212
  have hstable : (prefixWord ++ tailWord_2242212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242212).length < 2 ^ (prefixWord ++ tailWord_2242212).sum := by decide
  have hdescent : baseEnd_2242212 < baseStart_2242212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242222 : List Nat := [4, 1, 4, 1, 3, 1, 2, 1, 2, 3]
def baseStart_2242222 : Nat := 118140960795 + 2242222 * 2 ^ 59
def prefixEnd_2242222 : Nat := 4983230072969 + 3 ^ 40 * 2242222 * 2
def baseEnd_2242222 : Nat := 767558413390421019875477

theorem tailTrace_2242222 : CollatzResearch.WordTrace tailWord_2242222 prefixEnd_2242222 767558413390421019875477 := by
  unfold tailWord_2242222
  simp only [CollatzResearch.WordTrace]
  refine ⟨10222569360352513734402115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54520369921880073250144613 10222569360352513734402115)
  ·
    refine ⟨15333854040528770601603173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10222569360352513734402115 15333854040528770601603173)
    ·
      refine ⟨2875097632599144487800595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15333854040528770601603173 2875097632599144487800595)
      ·
        refine ⟨4312646448898716731700893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2875097632599144487800595 4312646448898716731700893)
        ·
          refine ⟨1617242418337018774387835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4312646448898716731700893 1617242418337018774387835)
          ·
            refine ⟨2425863627505528161581753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1617242418337018774387835 2425863627505528161581753)
            ·
              refine ⟨1819397720629146121186315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2425863627505528161581753 1819397720629146121186315)
              ·
                refine ⟨2729096580943719181779473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819397720629146121186315 2729096580943719181779473)
                ·
                  refine ⟨2046822435707789386334605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2729096580943719181779473 2046822435707789386334605)
                  ·
                    refine ⟨767558413390421019875477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2046822435707789386334605 767558413390421019875477)
                    ·
                      rfl

theorem cell22_2242222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_2242222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242222 prefixEnd_2242222 := by exact prefixLift 2242222
  have htrace : WordTrace (prefixWord ++ tailWord_2242222) baseStart_2242222 baseEnd_2242222 := by
    simpa [prefixWord, tailWord_2242222, baseEnd_2242222] using wordTrace_append hprefix tailTrace_2242222
  have hstable : (prefixWord ++ tailWord_2242222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242222).length < 2 ^ (prefixWord ++ tailWord_2242222).sum := by decide
  have hdescent : baseEnd_2242222 < baseStart_2242222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242287 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 1, 6]
def baseStart_2242287 : Nat := 118140960795 + 2242287 * 2 ^ 59
def prefixEnd_2242287 : Nat := 4983230072969 + 3 ^ 40 * 2242287 * 2
def baseEnd_2242287 : Nat := 767580664218782517000277

theorem tailTrace_2242287 : CollatzResearch.WordTrace tailWord_2242287 prefixEnd_2242287 767580664218782517000277 := by
  unfold tailWord_2242287
  simp only [CollatzResearch.WordTrace]
  refine ⟨81782925627584625976333115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54521950418389750650888743 81782925627584625976333115)
  ·
    refine ⟨122674388441376938964499673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81782925627584625976333115 122674388441376938964499673)
    ·
      refine ⟨92005791331032704223374755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122674388441376938964499673 92005791331032704223374755)
      ·
        refine ⟨138008686996549056335062133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92005791331032704223374755 138008686996549056335062133)
        ·
          refine ⟨12938314405926474031412075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138008686996549056335062133 12938314405926474031412075)
          ·
            refine ⟨19407471608889711047118113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12938314405926474031412075 19407471608889711047118113)
            ·
              refine ⟨14555603706667283285338585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19407471608889711047118113 14555603706667283285338585)
              ·
                refine ⟨10916702780000462464003939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14555603706667283285338585 10916702780000462464003939)
                ·
                  refine ⟨16375054170000693696005909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10916702780000462464003939 16375054170000693696005909)
                  ·
                    refine ⟨767580664218782517000277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16375054170000693696005909 767580664218782517000277)
                    ·
                      rfl

theorem cell22_2242287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_2242287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242287 prefixEnd_2242287 := by exact prefixLift 2242287
  have htrace : WordTrace (prefixWord ++ tailWord_2242287) baseStart_2242287 baseEnd_2242287 := by
    simpa [prefixWord, tailWord_2242287, baseEnd_2242287] using wordTrace_append hprefix tailTrace_2242287
  have hstable : (prefixWord ++ tailWord_2242287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242287).length < 2 ^ (prefixWord ++ tailWord_2242287).sum := by decide
  have hdescent : baseEnd_2242287 < baseStart_2242287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242289 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 1, 5]
def baseStart_2242289 : Nat := 118140960795 + 2242289 * 2 ^ 59
def prefixEnd_2242289 : Nat := 4983230072969 + 3 ^ 40 * 2242289 * 2
def baseEnd_2242289 : Nat := 767581348859655178450271

theorem tailTrace_2242289 : CollatzResearch.WordTrace tailWord_2242289 prefixEnd_2242289 767581348859655178450271 := by
  unfold tailWord_2242289
  simp only [CollatzResearch.WordTrace]
  refine ⟨81782998573577380317905921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54521999049051586878603947 81782998573577380317905921)
  ·
    refine ⟨61337248930183035238429441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81782998573577380317905921 61337248930183035238429441)
    ·
      refine ⟨46002936697637276428822081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61337248930183035238429441 46002936697637276428822081)
      ·
        refine ⟨34502202523227957321616561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46002936697637276428822081 34502202523227957321616561)
        ·
          refine ⟨25876651892420967991212421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34502202523227957321616561 25876651892420967991212421)
          ·
            refine ⟨4851872229828931498352329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25876651892420967991212421 4851872229828931498352329)
            ·
              refine ⟨3638904172371698623764247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4851872229828931498352329 3638904172371698623764247)
              ·
                refine ⟨5458356258557547935646371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3638904172371698623764247 5458356258557547935646371)
                ·
                  refine ⟨8187534387836321903469557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5458356258557547935646371 8187534387836321903469557)
                  ·
                    refine ⟨767581348859655178450271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8187534387836321903469557 767581348859655178450271)
                    ·
                      rfl

theorem cell22_2242289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_2242289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242289 prefixEnd_2242289 := by exact prefixLift 2242289
  have htrace : WordTrace (prefixWord ++ tailWord_2242289) baseStart_2242289 baseEnd_2242289 := by
    simpa [prefixWord, tailWord_2242289, baseEnd_2242289] using wordTrace_append hprefix tailTrace_2242289
  have hstable : (prefixWord ++ tailWord_2242289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242289).length < 2 ^ (prefixWord ++ tailWord_2242289).sum := by decide
  have hdescent : baseEnd_2242289 < baseStart_2242289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242306 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_2242306 : Nat := 118140960795 + 2242306 * 2 ^ 59
def prefixEnd_2242306 : Nat := 4983230072969 + 3 ^ 40 * 2242306 * 2
def baseEnd_2242306 : Nat := 767587168307072800775219

theorem tailTrace_2242306 : CollatzResearch.WordTrace tailWord_2242306 prefixEnd_2242306 767587168307072800775219 := by
  unfold tailWord_2242306
  simp only [CollatzResearch.WordTrace]
  refine ⟨20445904653628948055318693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54522412409677194814183181 20445904653628948055318693)
  ·
    refine ⟨3833607122555427760372255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20445904653628948055318693 3833607122555427760372255)
    ·
      refine ⟨5750410683833141640558383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3833607122555427760372255 5750410683833141640558383)
      ·
        refine ⟨8625616025749712460837575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5750410683833141640558383 8625616025749712460837575)
        ·
          refine ⟨12938424038624568691256363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8625616025749712460837575 12938424038624568691256363)
          ·
            refine ⟨19407636057936853036884545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12938424038624568691256363 19407636057936853036884545)
            ·
              refine ⟨14555727043452639777663409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19407636057936853036884545 14555727043452639777663409)
              ·
                refine ⟨10916795282589479833247557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14555727043452639777663409 10916795282589479833247557)
                ·
                  refine ⟨2046899115485527468733917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10916795282589479833247557 2046899115485527468733917)
                  ·
                    refine ⟨767587168307072800775219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2046899115485527468733917 767587168307072800775219)
                    ·
                      rfl

theorem cell22_2242306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_2242306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242306 prefixEnd_2242306 := by exact prefixLift 2242306
  have htrace : WordTrace (prefixWord ++ tailWord_2242306) baseStart_2242306 baseEnd_2242306 := by
    simpa [prefixWord, tailWord_2242306, baseEnd_2242306] using wordTrace_append hprefix tailTrace_2242306
  have hstable : (prefixWord ++ tailWord_2242306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242306).length < 2 ^ (prefixWord ++ tailWord_2242306).sum := by decide
  have hdescent : baseEnd_2242306 < baseStart_2242306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242381 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 7]
def baseStart_2242381 : Nat := 118140960795 + 2242381 * 2 ^ 59
def prefixEnd_2242381 : Nat := 4983230072969 + 3 ^ 40 * 2242381 * 2
def baseEnd_2242381 : Nat := 255870947446599201716663

theorem tailTrace_2242381 : CollatzResearch.WordTrace tailWord_2242381 prefixEnd_2242381 255870947446599201716663 := by
  unfold tailWord_2242381
  simp only [CollatzResearch.WordTrace]
  refine ⟨81786354089244080030254997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54524236059496053353503331 81786354089244080030254997)
  ·
    refine ⟨3833735347933316251418203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81786354089244080030254997 3833735347933316251418203)
    ·
      refine ⟨5750603021899974377127305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3833735347933316251418203 5750603021899974377127305)
      ·
        refine ⟨4312952266424980782845479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5750603021899974377127305 4312952266424980782845479)
        ·
          refine ⟨6469428399637471174268219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4312952266424980782845479 6469428399637471174268219)
          ·
            refine ⟨9704142599456206761402329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6469428399637471174268219 9704142599456206761402329)
            ·
              refine ⟨7278106949592155071051747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9704142599456206761402329 7278106949592155071051747)
              ·
                refine ⟨10917160424388232606577621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7278106949592155071051747 10917160424388232606577621)
                ·
                  refine ⟨255870947446599201716663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10917160424388232606577621 255870947446599201716663)
                  ·
                    rfl

theorem cell22_2242381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_2242381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242381 prefixEnd_2242381 := by exact prefixLift 2242381
  have htrace : WordTrace (prefixWord ++ tailWord_2242381) baseStart_2242381 baseEnd_2242381 := by
    simpa [prefixWord, tailWord_2242381, baseEnd_2242381] using wordTrace_append hprefix tailTrace_2242381
  have hstable : (prefixWord ++ tailWord_2242381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242381).length < 2 ^ (prefixWord ++ tailWord_2242381).sum := by decide
  have hdescent : baseEnd_2242381 < baseStart_2242381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242385 : List Nat := [1, 2, 2, 1, 5, 2, 3, 2, 1, 3]
def baseStart_2242385 : Nat := 118140960795 + 2242385 * 2 ^ 59
def prefixEnd_2242385 : Nat := 4983230072969 + 3 ^ 40 * 2242385 * 2
def baseEnd_2242385 : Nat := 767614211621542928049977

theorem tailTrace_2242385 : CollatzResearch.WordTrace tailWord_2242385 prefixEnd_2242385 767614211621542928049977 := by
  unfold tailWord_2242385
  simp only [CollatzResearch.WordTrace]
  refine ⟨81786499981229588713400609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54524333320819725808933739 81786499981229588713400609)
  ·
    refine ⟨61339874985922191535050457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81786499981229588713400609 61339874985922191535050457)
    ·
      refine ⟨46004906239441643651287843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61339874985922191535050457 46004906239441643651287843)
      ·
        refine ⟨69007359359162465476931765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46004906239441643651287843 69007359359162465476931765)
        ·
          refine ⟨6469439939921481138462353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69007359359162465476931765 6469439939921481138462353)
          ·
            refine ⟨4852079954941110853846765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6469439939921481138462353 4852079954941110853846765)
            ·
              refine ⟨1819529983102916570192537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4852079954941110853846765 1819529983102916570192537)
              ·
                refine ⟨1364647487327187427644403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1819529983102916570192537 1364647487327187427644403)
                ·
                  refine ⟨2046971230990781141466605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1364647487327187427644403 2046971230990781141466605)
                  ·
                    refine ⟨767614211621542928049977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2046971230990781141466605 767614211621542928049977)
                    ·
                      rfl

theorem cell22_2242385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 1, 3].length) (baseStart_2242385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242385 prefixEnd_2242385 := by exact prefixLift 2242385
  have htrace : WordTrace (prefixWord ++ tailWord_2242385) baseStart_2242385 baseEnd_2242385 := by
    simpa [prefixWord, tailWord_2242385, baseEnd_2242385] using wordTrace_append hprefix tailTrace_2242385
  have hstable : (prefixWord ++ tailWord_2242385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242385).length < 2 ^ (prefixWord ++ tailWord_2242385).sum := by decide
  have hdescent : baseEnd_2242385 < baseStart_2242385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242394 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 3, 4]
def baseStart_2242394 : Nat := 118140960795 + 2242394 * 2 ^ 59
def prefixEnd_2242394 : Nat := 4983230072969 + 3 ^ 40 * 2242394 * 2
def baseEnd_2242394 : Nat := 767617292505469904574949

theorem tailTrace_2242394 : CollatzResearch.WordTrace tailWord_2242394 prefixEnd_2242394 767617292505469904574949 := by
  unfold tailWord_2242394
  simp only [CollatzResearch.WordTrace]
  refine ⟨20446707059549245812619559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54524552158797988833652157 20446707059549245812619559)
  ·
    refine ⟨30670060589323868718929339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20446707059549245812619559 30670060589323868718929339)
    ·
      refine ⟨46005090883985803078394009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30670060589323868718929339 46005090883985803078394009)
      ·
        refine ⟨34503818162989352308795507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46005090883985803078394009 34503818162989352308795507)
        ·
          refine ⟨51755727244484028463193261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34503818162989352308795507 51755727244484028463193261)
          ·
            refine ⟨19408397716681510673697473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51755727244484028463193261 19408397716681510673697473)
            ·
              refine ⟨14556298287511133005273105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19408397716681510673697473 14556298287511133005273105)
              ·
                refine ⟨10917223715633349753954829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14556298287511133005273105 10917223715633349753954829)
                ·
                  refine ⟨4093958893362506157733061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10917223715633349753954829 4093958893362506157733061)
                  ·
                    refine ⟨767617292505469904574949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4093958893362506157733061 767617292505469904574949)
                    ·
                      rfl

theorem cell22_2242394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_2242394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242394 prefixEnd_2242394 := by exact prefixLift 2242394
  have htrace : WordTrace (prefixWord ++ tailWord_2242394) baseStart_2242394 baseEnd_2242394 := by
    simpa [prefixWord, tailWord_2242394, baseEnd_2242394] using wordTrace_append hprefix tailTrace_2242394
  have hstable : (prefixWord ++ tailWord_2242394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242394).length < 2 ^ (prefixWord ++ tailWord_2242394).sum := by decide
  have hdescent : baseEnd_2242394 < baseStart_2242394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242458 : List Nat := [3, 1, 1, 4, 2, 1, 2, 3, 2, 3]
def baseStart_2242458 : Nat := 118140960795 + 2242458 * 2 ^ 59
def prefixEnd_2242458 : Nat := 4983230072969 + 3 ^ 40 * 2242458 * 2
def baseEnd_2242458 : Nat := 767639201013395070974753

theorem tailTrace_2242458 : CollatzResearch.WordTrace tailWord_2242458 prefixEnd_2242458 767639201013395070974753 := by
  unfold tailWord_2242458
  simp only [CollatzResearch.WordTrace]
  refine ⟨20447290627491280545202007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54526108339976748120538685 20447290627491280545202007)
  ·
    refine ⟨30670935941236920817803011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20447290627491280545202007 30670935941236920817803011)
    ·
      refine ⟨46006403911855381226704517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30670935941236920817803011 46006403911855381226704517)
      ·
        refine ⟨8626200733472883980007097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46006403911855381226704517 8626200733472883980007097)
        ·
          refine ⟨6469650550104662985005323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8626200733472883980007097 6469650550104662985005323)
          ·
            refine ⟨9704475825156994477507985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6469650550104662985005323 9704475825156994477507985)
            ·
              refine ⟨7278356868867745858130989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9704475825156994477507985 7278356868867745858130989)
              ·
                refine ⟨2729383825825404696799121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7278356868867745858130989 2729383825825404696799121)
                ·
                  refine ⟨2047037869369053522599341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2729383825825404696799121 2047037869369053522599341)
                  ·
                    refine ⟨767639201013395070974753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2047037869369053522599341 767639201013395070974753)
                    ·
                      rfl

theorem cell22_2242458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_2242458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242458 prefixEnd_2242458 := by exact prefixLift 2242458
  have htrace : WordTrace (prefixWord ++ tailWord_2242458) baseStart_2242458 baseEnd_2242458 := by
    simpa [prefixWord, tailWord_2242458, baseEnd_2242458] using wordTrace_append hprefix tailTrace_2242458
  have hstable : (prefixWord ++ tailWord_2242458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242458).length < 2 ^ (prefixWord ++ tailWord_2242458).sum := by decide
  have hdescent : baseEnd_2242458 < baseStart_2242458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242492 : List Nat := [2, 2, 2, 5, 1, 2, 1, 2, 2, 3]
def baseStart_2242492 : Nat := 118140960795 + 2242492 * 2 ^ 59
def prefixEnd_2242492 : Nat := 4983230072969 + 3 ^ 40 * 2242492 * 2
def baseEnd_2242492 : Nat := 767650839908230315624649

theorem tailTrace_2242492 : CollatzResearch.WordTrace tailWord_2242492 prefixEnd_2242492 767650839908230315624649 := by
  unfold tailWord_2242492
  simp only [CollatzResearch.WordTrace]
  refine ⟨40895201295920972993772865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54526935061227963991697153 40895201295920972993772865)
  ·
    refine ⟨30671400971940729745329649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40895201295920972993772865 30671400971940729745329649)
    ·
      refine ⟨23003550728955547308997237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30671400971940729745329649 23003550728955547308997237)
      ·
        refine ⟨2156582880839582560218491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23003550728955547308997237 2156582880839582560218491)
        ·
          refine ⟨3234874321259373840327737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2156582880839582560218491 3234874321259373840327737)
          ·
            refine ⟨2426155740944530380245803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3234874321259373840327737 2426155740944530380245803)
            ·
              refine ⟨3639233611416795570368705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2426155740944530380245803 3639233611416795570368705)
              ·
                refine ⟨2729425208562596677776529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3639233611416795570368705 2729425208562596677776529)
                ·
                  refine ⟨2047068906421947508332397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2729425208562596677776529 2047068906421947508332397)
                  ·
                    refine ⟨767650839908230315624649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2047068906421947508332397 767650839908230315624649)
                    ·
                      rfl

theorem cell22_2242492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_2242492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242492 prefixEnd_2242492 := by exact prefixLift 2242492
  have htrace : WordTrace (prefixWord ++ tailWord_2242492) baseStart_2242492 baseEnd_2242492 := by
    simpa [prefixWord, tailWord_2242492, baseEnd_2242492] using wordTrace_append hprefix tailTrace_2242492
  have hstable : (prefixWord ++ tailWord_2242492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242492).length < 2 ^ (prefixWord ++ tailWord_2242492).sum := by decide
  have hdescent : baseEnd_2242492 < baseStart_2242492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242544 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 8]
def baseStart_2242544 : Nat := 118140960795 + 2242544 * 2 ^ 59
def prefixEnd_2242544 : Nat := 4983230072969 + 3 ^ 40 * 2242544 * 2
def baseEnd_2242544 : Nat := 255889546856973171108163

theorem tailTrace_2242544 : CollatzResearch.WordTrace tailWord_2242544 prefixEnd_2242544 255889546856973171108163 := by
  unfold tailWord_2242544
  simp only [CollatzResearch.WordTrace]
  refine ⟨40896149593826779434219343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54528199458435705912292457 40896149593826779434219343)
  ·
    refine ⟨61344224390740169151329015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40896149593826779434219343 61344224390740169151329015)
    ·
      refine ⟨92016336586110253726993523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61344224390740169151329015 92016336586110253726993523)
      ·
        refine ⟨138024504879165380590490285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92016336586110253726993523 138024504879165380590490285)
        ·
          refine ⟨51759189329687017721433857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138024504879165380590490285 51759189329687017721433857)
          ·
            refine ⟨38819391997265263291075393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51759189329687017721433857 38819391997265263291075393)
            ·
              refine ⟨29114543997948947468306545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38819391997265263291075393 29114543997948947468306545)
              ·
                refine ⟨21835907998461710601229909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29114543997948947468306545 21835907998461710601229909)
                ·
                  refine ⟨255889546856973171108163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21835907998461710601229909 255889546856973171108163)
                  ·
                    rfl

theorem cell22_2242544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 8].length) (baseStart_2242544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242544 prefixEnd_2242544 := by exact prefixLift 2242544
  have htrace : WordTrace (prefixWord ++ tailWord_2242544) baseStart_2242544 baseEnd_2242544 := by
    simpa [prefixWord, tailWord_2242544, baseEnd_2242544] using wordTrace_append hprefix tailTrace_2242544
  have hstable : (prefixWord ++ tailWord_2242544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242544).length < 2 ^ (prefixWord ++ tailWord_2242544).sum := by decide
  have hdescent : baseEnd_2242544 < baseStart_2242544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242593 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 1, 5]
def baseStart_2242593 : Nat := 118140960795 + 2242593 * 2 ^ 59
def prefixEnd_2242593 : Nat := 4983230072969 + 3 ^ 40 * 2242593 * 2
def baseEnd_2242593 : Nat := 767685414272299718849339

theorem tailTrace_2242593 : CollatzResearch.WordTrace tailWord_2242593 prefixEnd_2242593 767685414272299718849339 := by
  unfold tailWord_2242593
  simp only [CollatzResearch.WordTrace]
  refine ⟨81794086364476040236972433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54529390909650693491314955 81794086364476040236972433)
  ·
    refine ⟨61345564773357030177729325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81794086364476040236972433 61345564773357030177729325)
    ·
      refine ⟨23004586790008886316648497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61345564773357030177729325 23004586790008886316648497)
      ·
        refine ⟨17253440092506664737486373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23004586790008886316648497 17253440092506664737486373)
        ·
          refine ⟨3235020017344999638278695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17253440092506664737486373 3235020017344999638278695)
          ·
            refine ⟨4852530026017499457418043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3235020017344999638278695 4852530026017499457418043)
            ·
              refine ⟨7278795039026249186127065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4852530026017499457418043 7278795039026249186127065)
              ·
                refine ⟨5459096279269686889595299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7278795039026249186127065 5459096279269686889595299)
                ·
                  refine ⟨8188644418904530334392949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5459096279269686889595299 8188644418904530334392949)
                  ·
                    refine ⟨767685414272299718849339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8188644418904530334392949 767685414272299718849339)
                    ·
                      rfl

theorem cell22_2242593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_2242593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242593 prefixEnd_2242593 := by exact prefixLift 2242593
  have htrace : WordTrace (prefixWord ++ tailWord_2242593) baseStart_2242593 baseEnd_2242593 := by
    simpa [prefixWord, tailWord_2242593, baseEnd_2242593] using wordTrace_append hprefix tailTrace_2242593
  have hstable : (prefixWord ++ tailWord_2242593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242593).length < 2 ^ (prefixWord ++ tailWord_2242593).sum := by decide
  have hdescent : baseEnd_2242593 < baseStart_2242593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242606 : List Nat := [4, 1, 3, 1, 1, 12]
def baseStart_2242606 : Nat := 118140960795 + 2242606 * 2 ^ 59
def prefixEnd_2242606 : Nat := 4983230072969 + 3 ^ 40 * 2242606 * 2
def baseEnd_2242606 : Nat := 9477652647382370595979

theorem tailTrace_2242606 : CollatzResearch.WordTrace tailWord_2242606 prefixEnd_2242606 9477652647382370595979 := by
  unfold tailWord_2242606
  simp only [CollatzResearch.WordTrace]
  refine ⟨10224320064178617932149459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54529707008952628971463781 10224320064178617932149459)
  ·
    refine ⟨15336480096267926898224189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10224320064178617932149459 15336480096267926898224189)
    ·
      refine ⟨5751180036100472586834071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15336480096267926898224189 5751180036100472586834071)
      ·
        refine ⟨8626770054150708880251107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5751180036100472586834071 8626770054150708880251107)
        ·
          refine ⟨12940155081226063320376661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8626770054150708880251107 12940155081226063320376661)
          ·
            refine ⟨9477652647382370595979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 12940155081226063320376661 9477652647382370595979)
            ·
              rfl

theorem cell22_2242606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 12].length) (baseStart_2242606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242606 prefixEnd_2242606 := by exact prefixLift 2242606
  have htrace : WordTrace (prefixWord ++ tailWord_2242606) baseStart_2242606 baseEnd_2242606 := by
    simpa [prefixWord, tailWord_2242606, baseEnd_2242606] using wordTrace_append hprefix tailTrace_2242606
  have hstable : (prefixWord ++ tailWord_2242606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242606).length < 2 ^ (prefixWord ++ tailWord_2242606).sum := by decide
  have hdescent : baseEnd_2242606 < baseStart_2242606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242610 : List Nat := [3, 2, 1, 1, 2, 4, 2, 2, 2, 3]
def baseStart_2242610 : Nat := 118140960795 + 2242610 * 2 ^ 59
def prefixEnd_2242610 : Nat := 4983230072969 + 3 ^ 40 * 2242610 * 2
def baseEnd_2242610 : Nat := 767691233719717341174287

theorem tailTrace_2242610 : CollatzResearch.WordTrace tailWord_2242610 prefixEnd_2242610 767691233719717341174287 := by
  unfold tailWord_2242610
  simp only [CollatzResearch.WordTrace]
  refine ⟨20448676601353613035085321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54529804270276301426894189 20448676601353613035085321)
  ·
    refine ⟨15336507451015209776313991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20448676601353613035085321 15336507451015209776313991)
    ·
      refine ⟨23004761176522814664470987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15336507451015209776313991 23004761176522814664470987)
      ·
        refine ⟨34507141764784221996706481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23004761176522814664470987 34507141764784221996706481)
        ·
          refine ⟨25880356323588166497529861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34507141764784221996706481 25880356323588166497529861)
          ·
            refine ⟨4852566810672781218286849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25880356323588166497529861 4852566810672781218286849)
            ·
              refine ⟨3639425108004585913715137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4852566810672781218286849 3639425108004585913715137)
              ·
                refine ⟨2729568831003439435286353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3639425108004585913715137 2729568831003439435286353)
                ·
                  refine ⟨2047176623252579576464765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2729568831003439435286353 2047176623252579576464765)
                  ·
                    refine ⟨767691233719717341174287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2047176623252579576464765 767691233719717341174287)
                    ·
                      rfl

theorem cell22_2242610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_2242610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242610 prefixEnd_2242610 := by exact prefixLift 2242610
  have htrace : WordTrace (prefixWord ++ tailWord_2242610) baseStart_2242610 baseEnd_2242610 := by
    simpa [prefixWord, tailWord_2242610, baseEnd_2242610] using wordTrace_append hprefix tailTrace_2242610
  have hstable : (prefixWord ++ tailWord_2242610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242610).length < 2 ^ (prefixWord ++ tailWord_2242610).sum := by decide
  have hdescent : baseEnd_2242610 < baseStart_2242610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242612 : List Nat := [2, 5, 1, 2, 2, 1, 1, 4, 4]
def baseStart_2242612 : Nat := 118140960795 + 2242612 * 2 ^ 59
def prefixEnd_2242612 : Nat := 4983230072969 + 3 ^ 40 * 2242612 * 2
def baseEnd_2242612 : Nat := 255897306120196667541427

theorem tailTrace_2242612 : CollatzResearch.WordTrace tailWord_2242612 prefixEnd_2242612 255897306120196667541427 := by
  unfold tailWord_2242612
  simp only [CollatzResearch.WordTrace]
  refine ⟨40897389675703603240957045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54529852900938137654609393 40897389675703603240957045)
  ·
    refine ⟨3834130282097212803839723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40897389675703603240957045 3834130282097212803839723)
    ·
      refine ⟨5751195423145819205759585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3834130282097212803839723 5751195423145819205759585)
      ·
        refine ⟨4313396567359364404319689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5751195423145819205759585 4313396567359364404319689)
        ·
          refine ⟨3235047425519523303239767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4313396567359364404319689 3235047425519523303239767)
          ·
            refine ⟨4852571138279284954859651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3235047425519523303239767 4852571138279284954859651)
            ·
              refine ⟨7278856707418927432289477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4852571138279284954859651 7278856707418927432289477)
              ·
                refine ⟨1364785632641048893554277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7278856707418927432289477 1364785632641048893554277)
                ·
                  refine ⟨255897306120196667541427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1364785632641048893554277 255897306120196667541427)
                  ·
                    rfl

theorem cell22_2242612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_2242612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242612 prefixEnd_2242612 := by exact prefixLift 2242612
  have htrace : WordTrace (prefixWord ++ tailWord_2242612) baseStart_2242612 baseEnd_2242612 := by
    simpa [prefixWord, tailWord_2242612, baseEnd_2242612] using wordTrace_append hprefix tailTrace_2242612
  have hstable : (prefixWord ++ tailWord_2242612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242612).length < 2 ^ (prefixWord ++ tailWord_2242612).sum := by decide
  have hdescent : baseEnd_2242612 < baseStart_2242612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242638 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 5, 3]
def baseStart_2242638 : Nat := 118140960795 + 2242638 * 2 ^ 59
def prefixEnd_2242638 : Nat := 4983230072969 + 3 ^ 40 * 2242638 * 2
def baseEnd_2242638 : Nat := 767700818691934601474201

theorem tailTrace_2242638 : CollatzResearch.WordTrace tailWord_2242638 prefixEnd_2242638 767700818691934601474201 := by
  unfold tailWord_2242638
  simp only [CollatzResearch.WordTrace]
  refine ⟨10224465956164126615295071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54530485099542008614907045 10224465956164126615295071)
  ·
    refine ⟨15336698934246189922942607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10224465956164126615295071 15336698934246189922942607)
    ·
      refine ⟨23005048401369284884413911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15336698934246189922942607 23005048401369284884413911)
      ·
        refine ⟨34507572602053927326620867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23005048401369284884413911 34507572602053927326620867)
        ·
          refine ⟨51761358903080890989931301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34507572602053927326620867 51761358903080890989931301)
          ·
            refine ⟨9705254794327667060612119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51761358903080890989931301 9705254794327667060612119)
            ·
              refine ⟨14557882191491500590918179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9705254794327667060612119 14557882191491500590918179)
              ·
                refine ⟨21836823287237250886377269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14557882191491500590918179 21836823287237250886377269)
                ·
                  refine ⟨2047202183178492270597869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21836823287237250886377269 2047202183178492270597869)
                  ·
                    refine ⟨767700818691934601474201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2047202183178492270597869 767700818691934601474201)
                    ·
                      rfl

theorem cell22_2242638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_2242638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242638 prefixEnd_2242638 := by exact prefixLift 2242638
  have htrace : WordTrace (prefixWord ++ tailWord_2242638) baseStart_2242638 baseEnd_2242638 := by
    simpa [prefixWord, tailWord_2242638, baseEnd_2242638] using wordTrace_append hprefix tailTrace_2242638
  have hstable : (prefixWord ++ tailWord_2242638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242638).length < 2 ^ (prefixWord ++ tailWord_2242638).sum := by decide
  have hdescent : baseEnd_2242638 < baseStart_2242638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242642 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 2, 4]
def baseStart_2242642 : Nat := 118140960795 + 2242642 * 2 ^ 59
def prefixEnd_2242642 : Nat := 4983230072969 + 3 ^ 40 * 2242642 * 2
def baseEnd_2242642 : Nat := 767702187973679924374189

theorem tailTrace_2242642 : CollatzResearch.WordTrace tailWord_2242642 prefixEnd_2242642 767702187973679924374189 := by
  unfold tailWord_2242642
  simp only [CollatzResearch.WordTrace]
  refine ⟨20448968385324630401376545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54530582360865681070337453 20448968385324630401376545)
  ·
    refine ⟨15336726288993472801032409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20448968385324630401376545 15336726288993472801032409)
    ·
      refine ⟨11502544716745104600774307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15336726288993472801032409 11502544716745104600774307)
      ·
        refine ⟨17253817075117656901161461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11502544716745104600774307 17253817075117656901161461)
        ·
          refine ⟨1617545350792280334483887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17253817075117656901161461 1617545350792280334483887)
          ·
            refine ⟨2426318026188420501725831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1617545350792280334483887 2426318026188420501725831)
            ·
              refine ⟨3639477039282630752588747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2426318026188420501725831 3639477039282630752588747)
              ·
                refine ⟨5459215558923946128883121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3639477039282630752588747 5459215558923946128883121)
                ·
                  refine ⟨4094411669192959596662341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5459215558923946128883121 4094411669192959596662341)
                  ·
                    refine ⟨767702187973679924374189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4094411669192959596662341 767702187973679924374189)
                    ·
                      rfl

theorem cell22_2242642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_2242642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242642 prefixEnd_2242642 := by exact prefixLift 2242642
  have htrace : WordTrace (prefixWord ++ tailWord_2242642) baseStart_2242642 baseEnd_2242642 := by
    simpa [prefixWord, tailWord_2242642, baseEnd_2242642] using wordTrace_append hprefix tailTrace_2242642
  have hstable : (prefixWord ++ tailWord_2242642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242642).length < 2 ^ (prefixWord ++ tailWord_2242642).sum := by decide
  have hdescent : baseEnd_2242642 < baseStart_2242642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242668 : List Nat := [2, 2, 1, 1, 3, 3, 3, 2, 5]
def baseStart_2242668 : Nat := 118140960795 + 2242668 * 2 ^ 59
def prefixEnd_2242668 : Nat := 4983230072969 + 3 ^ 40 * 2242668 * 2
def baseEnd_2242668 : Nat := 255903696101674841074703

theorem tailTrace_2242668 : CollatzResearch.WordTrace tailWord_2242668 prefixEnd_2242668 255903696101674841074703 := by
  unfold tailWord_2242668
  simp only [CollatzResearch.WordTrace]
  refine ⟨40898410919602164022976329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54531214559469552030635105 40898410919602164022976329)
  ·
    refine ⟨30673808189701623017232247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40898410919602164022976329 30673808189701623017232247)
    ·
      refine ⟨46010712284552434525848371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30673808189701623017232247 46010712284552434525848371)
      ·
        refine ⟨69016068426828651788772557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46010712284552434525848371 69016068426828651788772557)
        ·
          refine ⟨25881025660060744420789709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69016068426828651788772557 25881025660060744420789709)
          ·
            refine ⟨9705384622522779157796141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25881025660060744420789709 9705384622522779157796141)
            ·
              refine ⟨3639519233446042184173553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9705384622522779157796141 3639519233446042184173553)
              ·
                refine ⟨2729639425084531638130165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3639519233446042184173553 2729639425084531638130165)
                ·
                  refine ⟨255903696101674841074703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2729639425084531638130165 255903696101674841074703)
                  ·
                    rfl

theorem cell22_2242668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_2242668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242668 prefixEnd_2242668 := by exact prefixLift 2242668
  have htrace : WordTrace (prefixWord ++ tailWord_2242668) baseStart_2242668 baseEnd_2242668 := by
    simpa [prefixWord, tailWord_2242668, baseEnd_2242668] using wordTrace_append hprefix tailTrace_2242668
  have hstable : (prefixWord ++ tailWord_2242668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242668).length < 2 ^ (prefixWord ++ tailWord_2242668).sum := by decide
  have hdescent : baseEnd_2242668 < baseStart_2242668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242685 : List Nat := [1, 4, 1, 1, 3, 3, 3, 1, 5]
def baseStart_2242685 : Nat := 118140960795 + 2242685 * 2 ^ 59
def prefixEnd_2242685 : Nat := 4983230072969 + 3 ^ 40 * 2242685 * 2
def baseEnd_2242685 : Nat := 255905635917480715183019

theorem tailTrace_2242685 : CollatzResearch.WordTrace tailWord_2242685 prefixEnd_2242685 255905635917480715183019 := by
  unfold tailWord_2242685
  simp only [CollatzResearch.WordTrace]
  refine ⟨81797441880142739949321509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54531627920095159966214339 81797441880142739949321509)
  ·
    refine ⟨15337020352526763740497783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81797441880142739949321509 15337020352526763740497783)
    ·
      refine ⟨23005530528790145610746675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15337020352526763740497783 23005530528790145610746675)
      ·
        refine ⟨34508295793185218416120013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23005530528790145610746675 34508295793185218416120013)
        ·
          refine ⟨12940610922444456906045005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34508295793185218416120013 12940610922444456906045005)
          ·
            refine ⟨4852729095916671339766877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12940610922444456906045005 4852729095916671339766877)
            ·
              refine ⟨1819773410968751752412579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4852729095916671339766877 1819773410968751752412579)
              ·
                refine ⟨2729660116453127628618869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819773410968751752412579 2729660116453127628618869)
                ·
                  refine ⟨255905635917480715183019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2729660116453127628618869 255905635917480715183019)
                  ·
                    rfl

theorem cell22_2242685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_2242685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242685 prefixEnd_2242685 := by exact prefixLift 2242685
  have htrace : WordTrace (prefixWord ++ tailWord_2242685) baseStart_2242685 baseEnd_2242685 := by
    simpa [prefixWord, tailWord_2242685, baseEnd_2242685] using wordTrace_append hprefix tailTrace_2242685
  have hstable : (prefixWord ++ tailWord_2242685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242685).length < 2 ^ (prefixWord ++ tailWord_2242685).sum := by decide
  have hdescent : baseEnd_2242685 < baseStart_2242685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242745 : List Nat := [1, 2, 1, 4, 1, 2, 3, 3, 2, 3]
def baseStart_2242745 : Nat := 118140960795 + 2242745 * 2 ^ 59
def prefixEnd_2242745 : Nat := 4983230072969 + 3 ^ 40 * 2242745 * 2
def baseEnd_2242745 : Nat := 767737446978621989048873

theorem tailTrace_2242745 : CollatzResearch.WordTrace tailWord_2242745 prefixEnd_2242745 767737446978621989048873 := by
  unfold tailWord_2242745
  simp only [CollatzResearch.WordTrace]
  refine ⟨81799630259925370196505689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54533086839950246797670459 81799630259925370196505689)
  ·
    refine ⟨61349722694944027647379267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81799630259925370196505689 61349722694944027647379267)
    ·
      refine ⟨92024584042416041471068901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61349722694944027647379267 92024584042416041471068901)
      ·
        refine ⟨17254609507953007775825419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92024584042416041471068901 17254609507953007775825419)
        ·
          refine ⟨25881914261929511663738129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17254609507953007775825419 25881914261929511663738129)
          ·
            refine ⟨19411435696447133747803597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25881914261929511663738129 19411435696447133747803597)
            ·
              refine ⟨7279288386167675155426349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19411435696447133747803597 7279288386167675155426349)
              ·
                refine ⟨2729733144812878183284881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7279288386167675155426349 2729733144812878183284881)
                ·
                  refine ⟨2047299858609658637463661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2729733144812878183284881 2047299858609658637463661)
                  ·
                    refine ⟨767737446978621989048873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2047299858609658637463661 767737446978621989048873)
                    ·
                      rfl

theorem cell22_2242745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 3].length) (baseStart_2242745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242745 prefixEnd_2242745 := by exact prefixLift 2242745
  have htrace : WordTrace (prefixWord ++ tailWord_2242745) baseStart_2242745 baseEnd_2242745 := by
    simpa [prefixWord, tailWord_2242745, baseEnd_2242745] using wordTrace_append hprefix tailTrace_2242745
  have hstable : (prefixWord ++ tailWord_2242745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242745).length < 2 ^ (prefixWord ++ tailWord_2242745).sum := by decide
  have hdescent : baseEnd_2242745 < baseStart_2242745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242771 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 3, 8]
def baseStart_2242771 : Nat := 118140960795 + 2242771 * 2 ^ 59
def prefixEnd_2242771 : Nat := 4983230072969 + 3 ^ 40 * 2242771 * 2
def baseEnd_2242771 : Nat := 767746347309966587898793

theorem tailTrace_2242771 : CollatzResearch.WordTrace tailWord_2242771 prefixEnd_2242771 767746347309966587898793 := by
  unfold tailWord_2242771
  simp only [CollatzResearch.WordTrace]
  refine ⟨81800578557831176636952167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54533719038554117757968111 81800578557831176636952167)
  ·
    refine ⟨122700867836746764955428251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81800578557831176636952167 122700867836746764955428251)
    ·
      refine ⟨184051301755120147433142377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122700867836746764955428251 184051301755120147433142377)
      ·
        refine ⟨138038476316340110574856783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184051301755120147433142377 138038476316340110574856783)
        ·
          refine ⟨207057714474510165862285175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138038476316340110574856783 207057714474510165862285175)
          ·
            refine ⟨310586571711765248793427763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207057714474510165862285175 310586571711765248793427763)
            ·
              refine ⟨465879857567647873190141645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310586571711765248793427763 465879857567647873190141645)
              ·
                refine ⟨174704946587867952446303117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 465879857567647873190141645 174704946587867952446303117)
                ·
                  refine ⟨65514354970450482167363669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174704946587867952446303117 65514354970450482167363669)
                  ·
                    refine ⟨767746347309966587898793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65514354970450482167363669 767746347309966587898793)
                    ·
                      rfl

theorem cell22_2242771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 8].length) (baseStart_2242771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242771 prefixEnd_2242771 := by exact prefixLift 2242771
  have htrace : WordTrace (prefixWord ++ tailWord_2242771) baseStart_2242771 baseEnd_2242771 := by
    simpa [prefixWord, tailWord_2242771, baseEnd_2242771] using wordTrace_append hprefix tailTrace_2242771
  have hstable : (prefixWord ++ tailWord_2242771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242771).length < 2 ^ (prefixWord ++ tailWord_2242771).sum := by decide
  have hdescent : baseEnd_2242771 < baseStart_2242771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242803 : List Nat := [1, 1, 1, 2, 2, 4, 1, 5, 5]
def baseStart_2242803 : Nat := 118140960795 + 2242803 * 2 ^ 59
def prefixEnd_2242803 : Nat := 4983230072969 + 3 ^ 40 * 2242803 * 2
def baseEnd_2242803 : Nat := 255919100521309723699565

theorem tailTrace_2242803 : CollatzResearch.WordTrace tailWord_2242803 prefixEnd_2242803 255919100521309723699565 := by
  unfold tailWord_2242803
  simp only [CollatzResearch.WordTrace]
  refine ⟨81801745693715246102117063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54534497129143497401411375 81801745693715246102117063)
  ·
    refine ⟨122702618540572869153175595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81801745693715246102117063 122702618540572869153175595)
    ·
      refine ⟨184053927810859303729763393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122702618540572869153175595 184053927810859303729763393)
      ·
        refine ⟨138040445858144477797322545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184053927810859303729763393 138040445858144477797322545)
        ·
          refine ⟨103530334393608358347991909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138040445858144477797322545 103530334393608358347991909)
          ·
            refine ⟨19411937698801567190248483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103530334393608358347991909 19411937698801567190248483)
            ·
              refine ⟨29117906548202350785372725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19411937698801567190248483 29117906548202350785372725)
              ·
                refine ⟨2729803738893970386128693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29117906548202350785372725 2729803738893970386128693)
                ·
                  refine ⟨255919100521309723699565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2729803738893970386128693 255919100521309723699565)
                  ·
                    rfl

theorem cell22_2242803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 5].length) (baseStart_2242803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242803 prefixEnd_2242803 := by exact prefixLift 2242803
  have htrace : WordTrace (prefixWord ++ tailWord_2242803) baseStart_2242803 baseEnd_2242803 := by
    simpa [prefixWord, tailWord_2242803, baseEnd_2242803] using wordTrace_append hprefix tailTrace_2242803
  have hstable : (prefixWord ++ tailWord_2242803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242803).length < 2 ^ (prefixWord ++ tailWord_2242803).sum := by decide
  have hdescent : baseEnd_2242803 < baseStart_2242803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242824 : List Nat := [2, 1, 3, 2, 3, 2, 2, 3, 1, 3]
def baseStart_2242824 : Nat := 118140960795 + 2242824 * 2 ^ 59
def prefixEnd_2242824 : Nat := 4983230072969 + 3 ^ 40 * 2242824 * 2
def baseEnd_2242824 : Nat := 767764490293092116323631

theorem tailTrace_2242824 : CollatzResearch.WordTrace tailWord_2242824 prefixEnd_2242824 767764490293092116323631 := by
  unfold tailWord_2242824
  simp only [CollatzResearch.WordTrace]
  refine ⟨40901255813319583344315763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54535007751092777792421017 40901255813319583344315763)
  ·
    refine ⟨61351883719979375016473645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40901255813319583344315763 61351883719979375016473645)
    ·
      refine ⟨23006956394992265631177617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61351883719979375016473645 23006956394992265631177617)
      ·
        refine ⟨17255217296244199223383213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23006956394992265631177617 17255217296244199223383213)
        ·
          refine ⟨6470706486091574708768705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17255217296244199223383213 6470706486091574708768705)
          ·
            refine ⟨4853029864568681031576529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6470706486091574708768705 4853029864568681031576529)
            ·
              refine ⟨3639772398426510773682397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4853029864568681031576529 3639772398426510773682397)
              ·
                refine ⟨1364914649409941540130899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3639772398426510773682397 1364914649409941540130899)
                ·
                  refine ⟨2047371974114912310196349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1364914649409941540130899 2047371974114912310196349)
                  ·
                    refine ⟨767764490293092116323631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2047371974114912310196349 767764490293092116323631)
                    ·
                      rfl

theorem cell22_2242824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_2242824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242824 prefixEnd_2242824 := by exact prefixLift 2242824
  have htrace : WordTrace (prefixWord ++ tailWord_2242824) baseStart_2242824 baseEnd_2242824 := by
    simpa [prefixWord, tailWord_2242824, baseEnd_2242824] using wordTrace_append hprefix tailTrace_2242824
  have hstable : (prefixWord ++ tailWord_2242824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242824).length < 2 ^ (prefixWord ++ tailWord_2242824).sum := by decide
  have hdescent : baseEnd_2242824 < baseStart_2242824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242914 : List Nat := [3, 3, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_2242914 : Nat := 118140960795 + 2242914 * 2 ^ 59
def prefixEnd_2242914 : Nat := 4983230072969 + 3 ^ 40 * 2242914 * 2
def baseEnd_2242914 : Nat := 767795299132361881573355

theorem tailTrace_2242914 : CollatzResearch.WordTrace tailWord_2242914 prefixEnd_2242914 767795299132361881573355 := by
  unfold tailWord_2242914
  simp only [CollatzResearch.WordTrace]
  refine ⟨20451448549078278014851949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54537196130875408039605197 20451448549078278014851949)
  ·
    refine ⟨7669293205904354255569481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20451448549078278014851949 7669293205904354255569481)
    ·
      refine ⟨5751969904428265691677111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7669293205904354255569481 5751969904428265691677111)
      ·
        refine ⟨8627954856642398537515667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5751969904428265691677111 8627954856642398537515667)
        ·
          refine ⟨12941932284963597806273501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8627954856642398537515667 12941932284963597806273501)
          ·
            refine ⟨4853224606861349177352563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12941932284963597806273501 4853224606861349177352563)
            ·
              refine ⟨7279836910292023766028845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4853224606861349177352563 7279836910292023766028845)
              ·
                refine ⟨2729938841359508912260817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7279836910292023766028845 2729938841359508912260817)
                ·
                  refine ⟨2047454131019631684195613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2729938841359508912260817 2047454131019631684195613)
                  ·
                    refine ⟨767795299132361881573355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2047454131019631684195613 767795299132361881573355)
                    ·
                      rfl

theorem cell22_2242914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_2242914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242914 prefixEnd_2242914 := by exact prefixLift 2242914
  have htrace : WordTrace (prefixWord ++ tailWord_2242914) baseStart_2242914 baseEnd_2242914 := by
    simpa [prefixWord, tailWord_2242914, baseEnd_2242914] using wordTrace_append hprefix tailTrace_2242914
  have hstable : (prefixWord ++ tailWord_2242914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242914).length < 2 ^ (prefixWord ++ tailWord_2242914).sum := by decide
  have hdescent : baseEnd_2242914 < baseStart_2242914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242923 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 2, 6]
def baseStart_2242923 : Nat := 118140960795 + 2242923 * 2 ^ 59
def prefixEnd_2242923 : Nat := 4983230072969 + 3 ^ 40 * 2242923 * 2
def baseEnd_2242923 : Nat := 767798380016288858098327

theorem tailTrace_2242923 : CollatzResearch.WordTrace tailWord_2242923 prefixEnd_2242923 767798380016288858098327 := by
  unfold tailWord_2242923
  simp only [CollatzResearch.WordTrace]
  refine ⟨81806122453280506596485423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54537414968853671064323615 81806122453280506596485423)
  ·
    refine ⟨122709183679920759894728135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81806122453280506596485423 122709183679920759894728135)
    ·
      refine ⟨184063775519881139842092203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122709183679920759894728135 184063775519881139842092203)
      ·
        refine ⟨276095663279821709763138305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184063775519881139842092203 276095663279821709763138305)
        ·
          refine ⟨207071747459866282322353729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276095663279821709763138305 207071747459866282322353729)
          ·
            refine ⟨155303810594899711741765297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207071747459866282322353729 155303810594899711741765297)
            ·
              refine ⟨116477857946174783806323973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155303810594899711741765297 116477857946174783806323973)
              ·
                refine ⟨21839598364907771963685745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116477857946174783806323973 21839598364907771963685745)
                ·
                  refine ⟨16379698773680828972764309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21839598364907771963685745 16379698773680828972764309)
                  ·
                    refine ⟨767798380016288858098327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16379698773680828972764309 767798380016288858098327)
                    ·
                      rfl

theorem cell22_2242923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 6].length) (baseStart_2242923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242923 prefixEnd_2242923 := by exact prefixLift 2242923
  have htrace : WordTrace (prefixWord ++ tailWord_2242923) baseStart_2242923 baseEnd_2242923 := by
    simpa [prefixWord, tailWord_2242923, baseEnd_2242923] using wordTrace_append hprefix tailTrace_2242923
  have hstable : (prefixWord ++ tailWord_2242923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242923).length < 2 ^ (prefixWord ++ tailWord_2242923).sum := by decide
  have hdescent : baseEnd_2242923 < baseStart_2242923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242955 : List Nat := [1, 1, 1, 1, 4, 4, 1, 4, 5]
def baseStart_2242955 : Nat := 118140960795 + 2242955 * 2 ^ 59
def prefixEnd_2242955 : Nat := 4983230072969 + 3 ^ 40 * 2242955 * 2
def baseEnd_2242955 : Nat := 255936444756750480432743

theorem tailTrace_2242955 : CollatzResearch.WordTrace tailWord_2242955 prefixEnd_2242955 255936444756750480432743 := by
  unfold tailWord_2242955
  simp only [CollatzResearch.WordTrace]
  refine ⟨81807289589164576061650319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54538193059443050707766879 81807289589164576061650319)
  ·
    refine ⟨122710934383746864092475479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81807289589164576061650319 122710934383746864092475479)
    ·
      refine ⟨184066401575620296138713219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122710934383746864092475479 184066401575620296138713219)
      ·
        refine ⟨276099602363430444208069829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184066401575620296138713219 276099602363430444208069829)
        ·
          refine ⟨51768675443143208289013093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 276099602363430444208069829 51768675443143208289013093)
          ·
            refine ⟨9706626645589351554189955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51768675443143208289013093 9706626645589351554189955)
            ·
              refine ⟨14559939968384027331284933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9706626645589351554189955 14559939968384027331284933)
              ·
                refine ⟨2729988744072005124615925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14559939968384027331284933 2729988744072005124615925)
                ·
                  refine ⟨255936444756750480432743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2729988744072005124615925 255936444756750480432743)
                  ·
                    rfl

theorem cell22_2242955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 5].length) (baseStart_2242955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242955 prefixEnd_2242955 := by exact prefixLift 2242955
  have htrace : WordTrace (prefixWord ++ tailWord_2242955) baseStart_2242955 baseEnd_2242955 := by
    simpa [prefixWord, tailWord_2242955, baseEnd_2242955] using wordTrace_append hprefix tailTrace_2242955
  have hstable : (prefixWord ++ tailWord_2242955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242955).length < 2 ^ (prefixWord ++ tailWord_2242955).sum := by decide
  have hdescent : baseEnd_2242955 < baseStart_2242955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242970 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 1, 7]
def baseStart_2242970 : Nat := 118140960795 + 2242970 * 2 ^ 59
def prefixEnd_2242970 : Nat := 4983230072969 + 3 ^ 40 * 2242970 * 2
def baseEnd_2242970 : Nat := 767814469076796402173183

theorem tailTrace_2242970 : CollatzResearch.WordTrace tailWord_2242970 prefixEnd_2242970 767814469076796402173183 := by
  unfold tailWord_2242970
  simp only [CollatzResearch.WordTrace]
  refine ⟨20451959171027558405861591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54538557789406822415630909 20451959171027558405861591)
  ·
    refine ⟨30677938756541337608792387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20451959171027558405861591 30677938756541337608792387)
    ·
      refine ⟨46016908134812006413188581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30677938756541337608792387 46016908134812006413188581)
      ·
        refine ⟨8628170275277251202472859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46016908134812006413188581 8628170275277251202472859)
        ·
          refine ⟨12942255412915876803709289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8628170275277251202472859 12942255412915876803709289)
          ·
            refine ⟨9706691559686907602781967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12942255412915876803709289 9706691559686907602781967)
            ·
              refine ⟨14560037339530361404172951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9706691559686907602781967 14560037339530361404172951)
              ·
                refine ⟨21840056009295542106259427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14560037339530361404172951 21840056009295542106259427)
                ·
                  refine ⟨32760084013943313159389141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21840056009295542106259427 32760084013943313159389141)
                  ·
                    refine ⟨767814469076796402173183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32760084013943313159389141 767814469076796402173183)
                    ·
                      rfl

theorem cell22_2242970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_2242970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2242970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2242970 prefixEnd_2242970 := by exact prefixLift 2242970
  have htrace : WordTrace (prefixWord ++ tailWord_2242970) baseStart_2242970 baseEnd_2242970 := by
    simpa [prefixWord, tailWord_2242970, baseEnd_2242970] using wordTrace_append hprefix tailTrace_2242970
  have hstable : (prefixWord ++ tailWord_2242970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242970).length < 2 ^ (prefixWord ++ tailWord_2242970).sum := by decide
  have hdescent : baseEnd_2242970 < baseStart_2242970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243017 : List Nat := [1, 2, 1, 1, 2, 1, 6, 4, 4]
def baseStart_2243017 : Nat := 118140960795 + 2243017 * 2 ^ 59
def prefixEnd_2243017 : Nat := 4983230072969 + 3 ^ 40 * 2243017 * 2
def baseEnd_2243017 : Nat := 255943519379101315416013

theorem tailTrace_2243017 : CollatzResearch.WordTrace tailWord_2243017 prefixEnd_2243017 255943519379101315416013 := by
  unfold tailWord_2243017
  simp only [CollatzResearch.WordTrace]
  refine ⟨81809550914939960650407305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54539700609959973766938203 81809550914939960650407305)
  ·
    refine ⟨61357163186204970487805479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81809550914939960650407305 61357163186204970487805479)
    ·
      refine ⟨92035744779307455731708219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61357163186204970487805479 92035744779307455731708219)
      ·
        refine ⟨138053617168961183597562329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92035744779307455731708219 138053617168961183597562329)
        ·
          refine ⟨103540212876720887698171747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138053617168961183597562329 103540212876720887698171747)
          ·
            refine ⟨155310319315081331547257621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103540212876720887698171747 155310319315081331547257621)
            ·
              refine ⟨7280171217894437416277701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 155310319315081331547257621 7280171217894437416277701)
              ·
                refine ⟨1365032103355207015552069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7280171217894437416277701 1365032103355207015552069)
                ·
                  refine ⟨255943519379101315416013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1365032103355207015552069 255943519379101315416013)
                  ·
                    rfl

theorem cell22_2243017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 4].length) (baseStart_2243017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243017 prefixEnd_2243017 := by exact prefixLift 2243017
  have htrace : WordTrace (prefixWord ++ tailWord_2243017) baseStart_2243017 baseEnd_2243017 := by
    simpa [prefixWord, tailWord_2243017, baseEnd_2243017] using wordTrace_append hprefix tailTrace_2243017
  have hstable : (prefixWord ++ tailWord_2243017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243017).length < 2 ^ (prefixWord ++ tailWord_2243017).sum := by decide
  have hdescent : baseEnd_2243017 < baseStart_2243017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243047 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 2, 4]
def baseStart_2243047 : Nat := 118140960795 + 2243047 * 2 ^ 59
def prefixEnd_2243047 : Nat := 4983230072969 + 3 ^ 40 * 2243047 * 2
def baseEnd_2243047 : Nat := 767840827750393867997947

theorem tailTrace_2243047 : CollatzResearch.WordTrace tailWord_2243047 prefixEnd_2243047 767840827750393867997947 := by
  unfold tailWord_2243047
  simp only [CollatzResearch.WordTrace]
  refine ⟨81810645104831275773999395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54540430069887517182666263 81810645104831275773999395)
  ·
    refine ⟨122715967657246913660999093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81810645104831275773999395 122715967657246913660999093)
    ·
      refine ⟨11504621967866898155718665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122715967657246913660999093 11504621967866898155718665)
      ·
        refine ⟨8628466475900173616788999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11504621967866898155718665 8628466475900173616788999)
        ·
          refine ⟨12942699713850260425183499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8628466475900173616788999 12942699713850260425183499)
          ·
            refine ⟨19414049570775390637775249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12942699713850260425183499 19414049570775390637775249)
            ·
              refine ⟨14560537178081542978331437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19414049570775390637775249 14560537178081542978331437)
              ·
                refine ⟨5460201441780578616874289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14560537178081542978331437 5460201441780578616874289)
                ·
                  refine ⟨4095151081335433962655717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5460201441780578616874289 4095151081335433962655717)
                  ·
                    refine ⟨767840827750393867997947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4095151081335433962655717 767840827750393867997947)
                    ·
                      rfl

theorem cell22_2243047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_2243047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243047 prefixEnd_2243047 := by exact prefixLift 2243047
  have htrace : WordTrace (prefixWord ++ tailWord_2243047) baseStart_2243047 baseEnd_2243047 := by
    simpa [prefixWord, tailWord_2243047, baseEnd_2243047] using wordTrace_append hprefix tailTrace_2243047
  have hstable : (prefixWord ++ tailWord_2243047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243047).length < 2 ^ (prefixWord ++ tailWord_2243047).sum := by decide
  have hdescent : baseEnd_2243047 < baseStart_2243047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243075 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 2, 6]
def baseStart_2243075 : Nat := 118140960795 + 2243075 * 2 ^ 59
def prefixEnd_2243075 : Nat := 4983230072969 + 3 ^ 40 * 2243075 * 2
def baseEnd_2243075 : Nat := 767850412722611128297861

theorem tailTrace_2243075 : CollatzResearch.WordTrace tailWord_2243075 prefixEnd_2243075 767850412722611128297861 := by
  unfold tailWord_2243075
  simp only [CollatzResearch.WordTrace]
  refine ⟨81811666348729836556018679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54541110899153224370679119 81811666348729836556018679)
  ·
    refine ⟨122717499523094754834028019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81811666348729836556018679 122717499523094754834028019)
    ·
      refine ⟨184076249284642132251042029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122717499523094754834028019 184076249284642132251042029)
      ·
        refine ⟨69028593481740799594140761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184076249284642132251042029 69028593481740799594140761)
        ·
          refine ⟨51771445111305599695605571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69028593481740799594140761 51771445111305599695605571)
          ·
            refine ⟨77657167666958399543408357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51771445111305599695605571 77657167666958399543408357)
            ·
              refine ⟨14560718937554699914389067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77657167666958399543408357 14560718937554699914389067)
              ·
                refine ⟨21841078406332049871583601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14560718937554699914389067 21841078406332049871583601)
                ·
                  refine ⟨16380808804749037403687701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21841078406332049871583601 16380808804749037403687701)
                  ·
                    refine ⟨767850412722611128297861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16380808804749037403687701 767850412722611128297861)
                    ·
                      rfl

theorem cell22_2243075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 6].length) (baseStart_2243075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243075 prefixEnd_2243075 := by exact prefixLift 2243075
  have htrace : WordTrace (prefixWord ++ tailWord_2243075) baseStart_2243075 baseEnd_2243075 := by
    simpa [prefixWord, tailWord_2243075, baseEnd_2243075] using wordTrace_append hprefix tailTrace_2243075
  have hstable : (prefixWord ++ tailWord_2243075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243075).length < 2 ^ (prefixWord ++ tailWord_2243075).sum := by decide
  have hdescent : baseEnd_2243075 < baseStart_2243075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243154 : List Nat := [3, 2, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_2243154 : Nat := 118140960795 + 2243154 * 2 ^ 59
def prefixEnd_2243154 : Nat := 4983230072969 + 3 ^ 40 * 2243154 * 2
def baseEnd_2243154 : Nat := 767877456037081255572619

theorem tailTrace_2243154 : CollatzResearch.WordTrace tailWord_2243154 prefixEnd_2243154 767877456037081255572619 := by
  unfold tailWord_2243154
  simp only [CollatzResearch.WordTrace]
  refine ⟨20453636928860908262036129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54543031810295755365429677 20453636928860908262036129)
  ·
    refine ⟨15340227696645681196527097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20453636928860908262036129 15340227696645681196527097)
    ·
      refine ⟨11505170772484260897395323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15340227696645681196527097 11505170772484260897395323)
      ·
        refine ⟨17257756158726391346092985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11505170772484260897395323 17257756158726391346092985)
        ·
          refine ⟨12943317119044793509569739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17257756158726391346092985 12943317119044793509569739)
          ·
            refine ⟨19414975678567190264354609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12943317119044793509569739 19414975678567190264354609)
            ·
              refine ⟨14561231758925392698265957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19414975678567190264354609 14561231758925392698265957)
              ·
                refine ⟨2730230954798511130924867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14561231758925392698265957 2730230954798511130924867)
                ·
                  refine ⟨4095346432197766696387301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2730230954798511130924867 4095346432197766696387301)
                  ·
                    refine ⟨767877456037081255572619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4095346432197766696387301 767877456037081255572619)
                    ·
                      rfl

theorem cell22_2243154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_2243154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243154 prefixEnd_2243154 := by exact prefixLift 2243154
  have htrace : WordTrace (prefixWord ++ tailWord_2243154) baseStart_2243154 baseEnd_2243154 := by
    simpa [prefixWord, tailWord_2243154, baseEnd_2243154] using wordTrace_append hprefix tailTrace_2243154
  have hstable : (prefixWord ++ tailWord_2243154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243154).length < 2 ^ (prefixWord ++ tailWord_2243154).sum := by decide
  have hdescent : baseEnd_2243154 < baseStart_2243154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243169 : List Nat := [1, 2, 3, 1, 1, 4, 1, 5, 4]
def baseStart_2243169 : Nat := 118140960795 + 2243169 * 2 ^ 59
def prefixEnd_2243169 : Nat := 4983230072969 + 3 ^ 40 * 2243169 * 2
def baseEnd_2243169 : Nat := 255960863614542072149191

theorem tailTrace_2243169 : CollatzResearch.WordTrace tailWord_2243169 prefixEnd_2243169 255960863614542072149191 := by
  unfold tailWord_2243169
  simp only [CollatzResearch.WordTrace]
  refine ⟨81815094810389290609940561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54543396540259527073293707 81815094810389290609940561)
  ·
    refine ⟨61361321107791967957455421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81815094810389290609940561 61361321107791967957455421)
    ·
      refine ⟨23010495415421987984045783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61361321107791967957455421 23010495415421987984045783)
      ·
        refine ⟨34515743123132981976068675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23010495415421987984045783 34515743123132981976068675)
        ·
          refine ⟨51773614684699472964103013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34515743123132981976068675 51773614684699472964103013)
          ·
            refine ⟨9707552753381151180769315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51773614684699472964103013 9707552753381151180769315)
            ·
              refine ⟨14561329130071726771153973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9707552753381151180769315 14561329130071726771153973)
              ·
                refine ⟨1365124605944224384795685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14561329130071726771153973 1365124605944224384795685)
                ·
                  refine ⟨255960863614542072149191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1365124605944224384795685 255960863614542072149191)
                  ·
                    rfl

theorem cell22_2243169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 4].length) (baseStart_2243169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243169 prefixEnd_2243169 := by exact prefixLift 2243169
  have htrace : WordTrace (prefixWord ++ tailWord_2243169) baseStart_2243169 baseEnd_2243169 := by
    simpa [prefixWord, tailWord_2243169, baseEnd_2243169] using wordTrace_append hprefix tailTrace_2243169
  have hstable : (prefixWord ++ tailWord_2243169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243169).length < 2 ^ (prefixWord ++ tailWord_2243169).sum := by decide
  have hdescent : baseEnd_2243169 < baseStart_2243169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243229 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 5, 3]
def baseStart_2243229 : Nat := 118140960795 + 2243229 * 2 ^ 59
def prefixEnd_2243229 : Nat := 4983230072969 + 3 ^ 40 * 2243229 * 2
def baseEnd_2243229 : Nat := 767903130069806059947389

theorem tailTrace_2243229 : CollatzResearch.WordTrace tailWord_2243229 prefixEnd_2243229 767903130069806059947389 := by
  unfold tailWord_2243229
  simp only [CollatzResearch.WordTrace]
  refine ⟨81817283190171920857124741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54544855460114613904749827 81817283190171920857124741)
  ·
    refine ⟨15340740598157235160710889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81817283190171920857124741 15340740598157235160710889)
    ·
      refine ⟨11505555448617926370533167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15340740598157235160710889 11505555448617926370533167)
      ·
        refine ⟨17258333172926889555799751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11505555448617926370533167 17258333172926889555799751)
        ·
          refine ⟨25887499759390334333699627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17258333172926889555799751 25887499759390334333699627)
          ·
            refine ⟨38831249639085501500549441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25887499759390334333699627 38831249639085501500549441)
            ·
              refine ⟨29123437229314126125412081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38831249639085501500549441 29123437229314126125412081)
              ·
                refine ⟨21842577921985594594059061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29123437229314126125412081 21842577921985594594059061)
                ·
                  refine ⟨2047741680186149493193037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21842577921985594594059061 2047741680186149493193037)
                  ·
                    refine ⟨767903130069806059947389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2047741680186149493193037 767903130069806059947389)
                    ·
                      rfl

theorem cell22_2243229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_2243229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243229 prefixEnd_2243229 := by exact prefixLift 2243229
  have htrace : WordTrace (prefixWord ++ tailWord_2243229) baseStart_2243229 baseEnd_2243229 := by
    simpa [prefixWord, tailWord_2243229, baseEnd_2243229] using wordTrace_append hprefix tailTrace_2243229
  have hstable : (prefixWord ++ tailWord_2243229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243229).length < 2 ^ (prefixWord ++ tailWord_2243229).sum := by decide
  have hdescent : baseEnd_2243229 < baseStart_2243229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243257 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 1, 7]
def baseStart_2243257 : Nat := 118140960795 + 2243257 * 2 ^ 59
def prefixEnd_2243257 : Nat := 4983230072969 + 3 ^ 40 * 2243257 * 2
def baseEnd_2243257 : Nat := 767912715042023320247303

theorem tailTrace_2243257 : CollatzResearch.WordTrace tailWord_2243257 prefixEnd_2243257 767912715042023320247303 := by
  unfold tailWord_2243257
  simp only [CollatzResearch.WordTrace]
  refine ⟨81818304434070481639144025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54545536289380321092762683 81818304434070481639144025)
  ·
    refine ⟨61363728325552861229358019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81818304434070481639144025 61363728325552861229358019)
    ·
      refine ⟨92045592488329291844037029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61363728325552861229358019 92045592488329291844037029)
      ·
        refine ⟨17258548591561742220756943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92045592488329291844037029 17258548591561742220756943)
        ·
          refine ⟨25887822887342613331135415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17258548591561742220756943 25887822887342613331135415)
          ·
            refine ⟨38831734331013919996703123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25887822887342613331135415 38831734331013919996703123)
            ·
              refine ⟨58247601496520879995054685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38831734331013919996703123 58247601496520879995054685)
              ·
                refine ⟨21842850561195329998145507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58247601496520879995054685 21842850561195329998145507)
                ·
                  refine ⟨32764275841792994997218261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21842850561195329998145507 32764275841792994997218261)
                  ·
                    refine ⟨767912715042023320247303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32764275841792994997218261 767912715042023320247303)
                    ·
                      rfl

theorem cell22_2243257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_2243257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243257 prefixEnd_2243257 := by exact prefixLift 2243257
  have htrace : WordTrace (prefixWord ++ tailWord_2243257) baseStart_2243257 baseEnd_2243257 := by
    simpa [prefixWord, tailWord_2243257, baseEnd_2243257] using wordTrace_append hprefix tailTrace_2243257
  have hstable : (prefixWord ++ tailWord_2243257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243257).length < 2 ^ (prefixWord ++ tailWord_2243257).sum := by decide
  have hdescent : baseEnd_2243257 < baseStart_2243257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243319 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 6, 3]
def baseStart_2243319 : Nat := 118140960795 + 2243319 * 2 ^ 59
def prefixEnd_2243319 : Nat := 4983230072969 + 3 ^ 40 * 2243319 * 2
def baseEnd_2243319 : Nat := 767933938909075825197113

theorem tailTrace_2243319 : CollatzResearch.WordTrace tailWord_2243319 prefixEnd_2243319 767933938909075825197113 := by
  unfold tailWord_2243319
  simp only [CollatzResearch.WordTrace]
  refine ⟨81820565759845866227901011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54547043839897244151934007 81820565759845866227901011)
  ·
    refine ⟨122730848639768799341851517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81820565759845866227901011 122730848639768799341851517)
    ·
      refine ⟨46024068239913299753194319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122730848639768799341851517 46024068239913299753194319)
      ·
        refine ⟨69036102359869949629791479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46024068239913299753194319 69036102359869949629791479)
        ·
          refine ⟨103554153539804924444687219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69036102359869949629791479 103554153539804924444687219)
          ·
            refine ⟨155331230309707386667030829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103554153539804924444687219 155331230309707386667030829)
            ·
              refine ⟨58249211366140270000136561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155331230309707386667030829 58249211366140270000136561)
              ·
                refine ⟨43686908524605202500102421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58249211366140270000136561 43686908524605202500102421)
                ·
                  refine ⟨2047823837090868867192301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43686908524605202500102421 2047823837090868867192301)
                  ·
                    refine ⟨767933938909075825197113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2047823837090868867192301 767933938909075825197113)
                    ·
                      rfl

theorem cell22_2243319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_2243319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243319 prefixEnd_2243319 := by exact prefixLift 2243319
  have htrace : WordTrace (prefixWord ++ tailWord_2243319) baseStart_2243319 baseEnd_2243319 := by
    simpa [prefixWord, tailWord_2243319, baseEnd_2243319] using wordTrace_append hprefix tailTrace_2243319
  have hstable : (prefixWord ++ tailWord_2243319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243319).length < 2 ^ (prefixWord ++ tailWord_2243319).sum := by decide
  have hdescent : baseEnd_2243319 < baseStart_2243319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243370 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 1, 5]
def baseStart_2243370 : Nat := 118140960795 + 2243370 * 2 ^ 59
def prefixEnd_2243370 : Nat := 4983230072969 + 3 ^ 40 * 2243370 * 2
def baseEnd_2243370 : Nat := 767951397251328692171957

theorem tailTrace_2243370 : CollatzResearch.WordTrace tailWord_2243370 prefixEnd_2243370 767951397251328692171957 := by
  unfold tailWord_2243370
  simp only [CollatzResearch.WordTrace]
  refine ⟨20455606470665275484501891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54548283921774067958671709 20455606470665275484501891)
  ·
    refine ⟨30683409705997913226752837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20455606470665275484501891 30683409705997913226752837)
    ·
      refine ⟨5753139319874608730016157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30683409705997913226752837 5753139319874608730016157)
      ·
        refine ⟨2157427244952978273756059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5753139319874608730016157 2157427244952978273756059)
        ·
          refine ⟨3236140867429467410634089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2157427244952978273756059 3236140867429467410634089)
          ·
            refine ⟨2427105650572100557975567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3236140867429467410634089 2427105650572100557975567)
            ·
              refine ⟨3640658475858150836963351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2427105650572100557975567 3640658475858150836963351)
              ·
                refine ⟨5460987713787226255445027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3640658475858150836963351 5460987713787226255445027)
                ·
                  refine ⟨8191481570680839383167541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5460987713787226255445027 8191481570680839383167541)
                  ·
                    refine ⟨767951397251328692171957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8191481570680839383167541 767951397251328692171957)
                    ·
                      rfl

theorem cell22_2243370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_2243370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243370 prefixEnd_2243370 := by exact prefixLift 2243370
  have htrace : WordTrace (prefixWord ++ tailWord_2243370) baseStart_2243370 baseEnd_2243370 := by
    simpa [prefixWord, tailWord_2243370, baseEnd_2243370] using wordTrace_append hprefix tailTrace_2243370
  have hstable : (prefixWord ++ tailWord_2243370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243370).length < 2 ^ (prefixWord ++ tailWord_2243370).sum := by decide
  have hdescent : baseEnd_2243370 < baseStart_2243370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243428 : List Nat := [2, 3, 1, 1, 4, 1, 4, 1, 5]
def baseStart_2243428 : Nat := 118140960795 + 2243428 * 2 ^ 59
def prefixEnd_2243428 : Nat := 4983230072969 + 3 ^ 40 * 2243428 * 2
def baseEnd_2243428 : Nat := 255990417278878624740593

theorem tailTrace_2243428 : CollatzResearch.WordTrace tailWord_2243428 prefixEnd_2243428 255990417278878624740593 := by
  unfold tailWord_2243428
  simp only [CollatzResearch.WordTrace]
  refine ⟨40912270658225488921809469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54549694210967318562412625 40912270658225488921809469)
  ·
    refine ⟨15342101496834558345678551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40912270658225488921809469 15342101496834558345678551)
    ·
      refine ⟨23013152245251837518517827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15342101496834558345678551 23013152245251837518517827)
      ·
        refine ⟨34519728367877756277776741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23013152245251837518517827 34519728367877756277776741)
        ·
          refine ⟨6472449068977079302083139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34519728367877756277776741 6472449068977079302083139)
          ·
            refine ⟨9708673603465618953124709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6472449068977079302083139 9708673603465618953124709)
            ·
              refine ⟨1820376300649803553710883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9708673603465618953124709 1820376300649803553710883)
              ·
                refine ⟨2730564450974705330566325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1820376300649803553710883 2730564450974705330566325)
                ·
                  refine ⟨255990417278878624740593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2730564450974705330566325 255990417278878624740593)
                  ·
                    rfl

theorem cell22_2243428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_2243428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243428 prefixEnd_2243428 := by exact prefixLift 2243428
  have htrace : WordTrace (prefixWord ++ tailWord_2243428) baseStart_2243428 baseEnd_2243428 := by
    simpa [prefixWord, tailWord_2243428, baseEnd_2243428] using wordTrace_append hprefix tailTrace_2243428
  have hstable : (prefixWord ++ tailWord_2243428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243428).length < 2 ^ (prefixWord ++ tailWord_2243428).sum := by decide
  have hdescent : baseEnd_2243428 < baseStart_2243428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243439 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 6]
def baseStart_2243439 : Nat := 118140960795 + 2243439 * 2 ^ 59
def prefixEnd_2243439 : Nat := 4983230072969 + 3 ^ 40 * 2243439 * 2
def baseEnd_2243439 : Nat := 255991672453811837398915

theorem tailTrace_2243439 : CollatzResearch.WordTrace tailWord_2243439 prefixEnd_2243439 255991672453811837398915 := by
  unfold tailWord_2243439
  simp only [CollatzResearch.WordTrace]
  refine ⟨81824942519411126722269371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54549961679607417814846247 81824942519411126722269371)
  ·
    refine ⟨122737413779116690083404057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81824942519411126722269371 122737413779116690083404057)
    ·
      refine ⟨92053060334337517562553043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122737413779116690083404057 92053060334337517562553043)
      ·
        refine ⟨138079590501506276343829565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92053060334337517562553043 138079590501506276343829565)
        ·
          refine ⟨51779846438064853628936087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138079590501506276343829565 51779846438064853628936087)
          ·
            refine ⟨77669769657097280443404131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51779846438064853628936087 77669769657097280443404131)
            ·
              refine ⟨116504654485645920665106197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77669769657097280443404131 116504654485645920665106197)
              ·
                refine ⟨5461155679014652531176853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 116504654485645920665106197 5461155679014652531176853)
                ·
                  refine ⟨255991672453811837398915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5461155679014652531176853 255991672453811837398915)
                  ·
                    rfl

theorem cell22_2243439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 6].length) (baseStart_2243439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243439 prefixEnd_2243439 := by exact prefixLift 2243439
  have htrace : WordTrace (prefixWord ++ tailWord_2243439) baseStart_2243439 baseEnd_2243439 := by
    simpa [prefixWord, tailWord_2243439, baseEnd_2243439] using wordTrace_append hprefix tailTrace_2243439
  have hstable : (prefixWord ++ tailWord_2243439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243439).length < 2 ^ (prefixWord ++ tailWord_2243439).sum := by decide
  have hdescent : baseEnd_2243439 < baseStart_2243439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243441 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 3, 4]
def baseStart_2243441 : Nat := 118140960795 + 2243441 * 2 ^ 59
def prefixEnd_2243441 : Nat := 4983230072969 + 3 ^ 40 * 2243441 * 2
def baseEnd_2243441 : Nat := 767975702002308173646739

theorem tailTrace_2243441 : CollatzResearch.WordTrace tailWord_2243441 prefixEnd_2243441 767975702002308173646739 := by
  unfold tailWord_2243441
  simp only [CollatzResearch.WordTrace]
  refine ⟨81825015465403881063842177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54550010310269254042561451 81825015465403881063842177)
  ·
    refine ⟨61368761599052910797881633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81825015465403881063842177 61368761599052910797881633)
    ·
      refine ⟨46026571199289683098411225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61368761599052910797881633 46026571199289683098411225)
      ·
        refine ⟨34519928399467262323808419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46026571199289683098411225 34519928399467262323808419)
        ·
          refine ⟨51779892599200893485712629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34519928399467262323808419 51779892599200893485712629)
          ·
            refine ⟨4854364931175083764285559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51779892599200893485712629 4854364931175083764285559)
            ·
              refine ⟨7281547396762625646428339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4854364931175083764285559 7281547396762625646428339)
              ·
                refine ⟨10922321095143938469642509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7281547396762625646428339 10922321095143938469642509)
                ·
                  refine ⟨4095870410678976926115941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10922321095143938469642509 4095870410678976926115941)
                  ·
                    refine ⟨767975702002308173646739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4095870410678976926115941 767975702002308173646739)
                    ·
                      rfl

theorem cell22_2243441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_2243441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243441 prefixEnd_2243441 := by exact prefixLift 2243441
  have htrace : WordTrace (prefixWord ++ tailWord_2243441) baseStart_2243441 baseEnd_2243441 := by
    simpa [prefixWord, tailWord_2243441, baseEnd_2243441] using wordTrace_append hprefix tailTrace_2243441
  have hstable : (prefixWord ++ tailWord_2243441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243441).length < 2 ^ (prefixWord ++ tailWord_2243441).sum := by decide
  have hdescent : baseEnd_2243441 < baseStart_2243441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243488 : List Nat := [2, 1, 1, 4, 1, 1, 4, 3, 2, 3]
def baseStart_2243488 : Nat := 118140960795 + 2243488 * 2 ^ 59
def prefixEnd_2243488 : Nat := 4983230072969 + 3 ^ 40 * 2243488 * 2
def baseEnd_2243488 : Nat := 767991791062815717721595

theorem tailTrace_2243488 : CollatzResearch.WordTrace tailWord_2243488 prefixEnd_2243488 767991791062815717721595 := by
  unfold tailWord_2243488
  simp only [CollatzResearch.WordTrace]
  refine ⟨40913364848116804045401559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54551153130822405393868745 40913364848116804045401559)
  ·
    refine ⟨61370047272175206068102339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40913364848116804045401559 61370047272175206068102339)
    ·
      refine ⟨92055070908262809102153509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61370047272175206068102339 92055070908262809102153509)
      ·
        refine ⟨17260325795299276706653783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92055070908262809102153509 17260325795299276706653783)
        ·
          refine ⟨25890488692948915059980675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17260325795299276706653783 25890488692948915059980675)
          ·
            refine ⟨38835733039423372589971013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25890488692948915059980675 38835733039423372589971013)
            ·
              refine ⟨7281699944891882360619565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38835733039423372589971013 7281699944891882360619565)
              ·
                refine ⟨2730637479334455885232337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7281699944891882360619565 2730637479334455885232337)
                ·
                  refine ⟨2047978109500841913924253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2730637479334455885232337 2047978109500841913924253)
                  ·
                    refine ⟨767991791062815717721595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2047978109500841913924253 767991791062815717721595)
                    ·
                      rfl

theorem cell22_2243488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 2, 3].length) (baseStart_2243488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243488 prefixEnd_2243488 := by exact prefixLift 2243488
  have htrace : WordTrace (prefixWord ++ tailWord_2243488) baseStart_2243488 baseEnd_2243488 := by
    simpa [prefixWord, tailWord_2243488, baseEnd_2243488] using wordTrace_append hprefix tailTrace_2243488
  have hstable : (prefixWord ++ tailWord_2243488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243488).length < 2 ^ (prefixWord ++ tailWord_2243488).sum := by decide
  have hdescent : baseEnd_2243488 < baseStart_2243488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243499 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 2, 7]
def baseStart_2243499 : Nat := 118140960795 + 2243499 * 2 ^ 59
def prefixEnd_2243499 : Nat := 4983230072969 + 3 ^ 40 * 2243499 * 2
def baseEnd_2243499 : Nat := 767995556587615355696561

theorem tailTrace_2243499 : CollatzResearch.WordTrace tailWord_2243499 prefixEnd_2243499 767995556587615355696561 := by
  unfold tailWord_2243499
  simp only [CollatzResearch.WordTrace]
  refine ⟨81827130899193756969453551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54551420599462504646302367 81827130899193756969453551)
  ·
    refine ⟨122740696348790635454180327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81827130899193756969453551 122740696348790635454180327)
    ·
      refine ⟨184111044523185953181270491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122740696348790635454180327 184111044523185953181270491)
      ·
        refine ⟨276166566784778929771905737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184111044523185953181270491 276166566784778929771905737)
        ·
          refine ⟨207124925088584197328929303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276166566784778929771905737 207124925088584197328929303)
          ·
            refine ⟨310687387632876295993393955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207124925088584197328929303 310687387632876295993393955)
            ·
              refine ⟨466031081449314443990090933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310687387632876295993393955 466031081449314443990090933)
              ·
                refine ⟨43690413885873229124071025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 466031081449314443990090933 43690413885873229124071025)
                ·
                  refine ⟨32767810414404921843053269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43690413885873229124071025 32767810414404921843053269)
                  ·
                    refine ⟨767995556587615355696561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32767810414404921843053269 767995556587615355696561)
                    ·
                      rfl

theorem cell22_2243499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 7].length) (baseStart_2243499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243499 prefixEnd_2243499 := by exact prefixLift 2243499
  have htrace : WordTrace (prefixWord ++ tailWord_2243499) baseStart_2243499 baseEnd_2243499 := by
    simpa [prefixWord, tailWord_2243499, baseEnd_2243499] using wordTrace_append hprefix tailTrace_2243499
  have hstable : (prefixWord ++ tailWord_2243499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243499).length < 2 ^ (prefixWord ++ tailWord_2243499).sum := by decide
  have hdescent : baseEnd_2243499 < baseStart_2243499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243567 : List Nat := [1, 1, 2, 1, 4, 5, 1, 3, 1, 3]
def baseStart_2243567 : Nat := 118140960795 + 2243567 * 2 ^ 59
def prefixEnd_2243567 : Nat := 4983230072969 + 3 ^ 40 * 2243567 * 2
def baseEnd_2243567 : Nat := 768018834377285844996353

theorem tailTrace_2243567 : CollatzResearch.WordTrace tailWord_2243567 prefixEnd_2243567 768018834377285844996353 := by
  unfold tailWord_2243567
  simp only [CollatzResearch.WordTrace]
  refine ⟨81829611062947404582928955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54553074041964936388619303 81829611062947404582928955)
  ·
    refine ⟨122744416594421106874393433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81829611062947404582928955 122744416594421106874393433)
    ·
      refine ⟨92058312445815830155795075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122744416594421106874393433 92058312445815830155795075)
      ·
        refine ⟨138087468668723745233692613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92058312445815830155795075 138087468668723745233692613)
        ·
          refine ⟨25891400375385702231317365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138087468668723745233692613 25891400375385702231317365)
          ·
            refine ⟨2427318785192409584186003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25891400375385702231317365 2427318785192409584186003)
            ·
              refine ⟨3640978177788614376279005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2427318785192409584186003 3640978177788614376279005)
              ·
                refine ⟨1365366816670730391104627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3640978177788614376279005 1365366816670730391104627)
                ·
                  refine ⟨2048050225006095586656941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1365366816670730391104627 2048050225006095586656941)
                  ·
                    refine ⟨768018834377285844996353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2048050225006095586656941 768018834377285844996353)
                    ·
                      rfl

theorem cell22_2243567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 1, 3].length) (baseStart_2243567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243567 prefixEnd_2243567 := by exact prefixLift 2243567
  have htrace : WordTrace (prefixWord ++ tailWord_2243567) baseStart_2243567 baseEnd_2243567 := by
    simpa [prefixWord, tailWord_2243567, baseEnd_2243567] using wordTrace_append hprefix tailTrace_2243567
  have hstable : (prefixWord ++ tailWord_2243567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243567).length < 2 ^ (prefixWord ++ tailWord_2243567).sum := by decide
  have hdescent : baseEnd_2243567 < baseStart_2243567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243576 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 5, 4]
def baseStart_2243576 : Nat := 118140960795 + 2243576 * 2 ^ 59
def prefixEnd_2243576 : Nat := 4983230072969 + 3 ^ 40 * 2243576 * 2
def baseEnd_2243576 : Nat := 768021915261212821521325

theorem tailTrace_2243576 : CollatzResearch.WordTrace tailWord_2243576 prefixEnd_2243576 768021915261212821521325 := by
  unfold tailWord_2243576
  simp only [CollatzResearch.WordTrace]
  refine ⟨40914969659957399560003291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54553292879943199413337721 40914969659957399560003291)
  ·
    refine ⟨61372454489936099340004937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40914969659957399560003291 61372454489936099340004937)
    ·
      refine ⟨46029340867452074505003703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61372454489936099340004937 46029340867452074505003703)
      ·
        refine ⟨69044011301178111757505555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46029340867452074505003703 69044011301178111757505555)
        ·
          refine ⟨103566016951767167636258333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69044011301178111757505555 103566016951767167636258333)
          ·
            refine ⟨38837256356912687863596875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103566016951767167636258333 38837256356912687863596875)
            ·
              refine ⟨58255884535369031795395313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38837256356912687863596875 58255884535369031795395313)
              ·
                refine ⟨43691913401526773846546485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58255884535369031795395313 43691913401526773846546485)
                ·
                  refine ⟨4096116881393135048113733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43691913401526773846546485 4096116881393135048113733)
                  ·
                    refine ⟨768021915261212821521325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4096116881393135048113733 768021915261212821521325)
                    ·
                      rfl

theorem cell22_2243576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_2243576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243576 prefixEnd_2243576 := by exact prefixLift 2243576
  have htrace : WordTrace (prefixWord ++ tailWord_2243576) baseStart_2243576 baseEnd_2243576 := by
    simpa [prefixWord, tailWord_2243576, baseEnd_2243576] using wordTrace_append hprefix tailTrace_2243576
  have hstable : (prefixWord ++ tailWord_2243576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243576).length < 2 ^ (prefixWord ++ tailWord_2243576).sum := by decide
  have hdescent : baseEnd_2243576 < baseStart_2243576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243640 : List Nat := [2, 1, 2, 1, 5, 1, 1, 4, 2, 3]
def baseStart_2243640 : Nat := 118140960795 + 2243640 * 2 ^ 59
def prefixEnd_2243640 : Nat := 4983230072969 + 3 ^ 40 * 2243640 * 2
def baseEnd_2243640 : Nat := 768043823769137987921129

theorem tailTrace_2243640 : CollatzResearch.WordTrace tailWord_2243640 prefixEnd_2243640 768043823769137987921129 := by
  unfold tailWord_2243640
  simp only [CollatzResearch.WordTrace]
  refine ⟨40916136795841469025168187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54554849061121958700224249 40916136795841469025168187)
  ·
    refine ⟨61374205193762203537752281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40916136795841469025168187 61374205193762203537752281)
    ·
      refine ⟨46030653895321652653314211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61374205193762203537752281 46030653895321652653314211)
      ·
        refine ⟨69045980842982478979971317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46030653895321652653314211 69045980842982478979971317)
        ·
          refine ⟨6473060704029607404372311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69045980842982478979971317 6473060704029607404372311)
          ·
            refine ⟨9709591056044411106558467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6473060704029607404372311 9709591056044411106558467)
            ·
              refine ⟨14564386584066616659837701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9709591056044411106558467 14564386584066616659837701)
              ·
                refine ⟨2730822484512490623719569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14564386584066616659837701 2730822484512490623719569)
                ·
                  refine ⟨2048116863384367967789677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2730822484512490623719569 2048116863384367967789677)
                  ·
                    refine ⟨768043823769137987921129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2048116863384367967789677 768043823769137987921129)
                    ·
                      rfl

theorem cell22_2243640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_2243640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243640 prefixEnd_2243640 := by exact prefixLift 2243640
  have htrace : WordTrace (prefixWord ++ tailWord_2243640) baseStart_2243640 baseEnd_2243640 := by
    simpa [prefixWord, tailWord_2243640, baseEnd_2243640] using wordTrace_append hprefix tailTrace_2243640
  have hstable : (prefixWord ++ tailWord_2243640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243640).length < 2 ^ (prefixWord ++ tailWord_2243640).sum := by decide
  have hdescent : baseEnd_2243640 < baseStart_2243640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243698 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 7]
def baseStart_2243698 : Nat := 118140960795 + 2243698 * 2 ^ 59
def prefixEnd_2243698 : Nat := 4983230072969 + 3 ^ 40 * 2243698 * 2
def baseEnd_2243698 : Nat := 256021226118148389990317

theorem tailTrace_2243698 : CollatzResearch.WordTrace tailWord_2243698 prefixEnd_2243698 256021226118148389990317 := by
  unfold tailWord_2243698
  simp only [CollatzResearch.WordTrace]
  refine ⟨20458597256368203488986937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54556259350315209303965165 20458597256368203488986937)
  ·
    refine ⟨15343947942276152616740203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20458597256368203488986937 15343947942276152616740203)
    ·
      refine ⟨23015921913414228925110305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15343947942276152616740203 23015921913414228925110305)
      ·
        refine ⟨17261941435060671693832729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23015921913414228925110305 17261941435060671693832729)
        ·
          refine ⟨12946456076295503770374547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17261941435060671693832729 12946456076295503770374547)
          ·
            refine ⟨19419684114443255655561821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12946456076295503770374547 19419684114443255655561821)
            ·
              refine ⟨7282381542916220870835683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19419684114443255655561821 7282381542916220870835683)
              ·
                refine ⟨10923572314374331306253525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7282381542916220870835683 10923572314374331306253525)
                ·
                  refine ⟨256021226118148389990317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10923572314374331306253525 256021226118148389990317)
                  ·
                    rfl

theorem cell22_2243698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_2243698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243698 prefixEnd_2243698 := by exact prefixLift 2243698
  have htrace : WordTrace (prefixWord ++ tailWord_2243698) baseStart_2243698 baseEnd_2243698 := by
    simpa [prefixWord, tailWord_2243698, baseEnd_2243698] using wordTrace_append hprefix tailTrace_2243698
  have hstable : (prefixWord ++ tailWord_2243698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243698).length < 2 ^ (prefixWord ++ tailWord_2243698).sum := by decide
  have hdescent : baseEnd_2243698 < baseStart_2243698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243702 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_2243702 : Nat := 118140960795 + 2243702 * 2 ^ 59
def prefixEnd_2243702 : Nat := 4983230072969 + 3 ^ 40 * 2243702 * 2
def baseEnd_2243702 : Nat := 768065047636190492870939

theorem tailTrace_2243702 : CollatzResearch.WordTrace tailWord_2243702 prefixEnd_2243702 768065047636190492870939 := by
  unfold tailWord_2243702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5114658432341145164943335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54556356611638881759395573 5114658432341145164943335)
  ·
    refine ⟨7671987648511717747415003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5114658432341145164943335 7671987648511717747415003)
    ·
      refine ⟨11507981472767576621122505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7671987648511717747415003 11507981472767576621122505)
      ·
        refine ⟨8630986104575682465841879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11507981472767576621122505 8630986104575682465841879)
        ·
          refine ⟨12946479156863523698762819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8630986104575682465841879 12946479156863523698762819)
          ·
            refine ⟨19419718735295285548144229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12946479156863523698762819 19419718735295285548144229)
            ·
              refine ⟨3641197262867866040277043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19419718735295285548144229 3641197262867866040277043)
              ·
                refine ⟨5461795894301799060415565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3641197262867866040277043 5461795894301799060415565)
                ·
                  refine ⟨2048173460363174647655837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5461795894301799060415565 2048173460363174647655837)
                  ·
                    refine ⟨768065047636190492870939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2048173460363174647655837 768065047636190492870939)
                    ·
                      rfl

theorem cell22_2243702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_2243702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243702 prefixEnd_2243702 := by exact prefixLift 2243702
  have htrace : WordTrace (prefixWord ++ tailWord_2243702) baseStart_2243702 baseEnd_2243702 := by
    simpa [prefixWord, tailWord_2243702, baseEnd_2243702] using wordTrace_append hprefix tailTrace_2243702
  have hstable : (prefixWord ++ tailWord_2243702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243702).length < 2 ^ (prefixWord ++ tailWord_2243702).sum := by decide
  have hdescent : baseEnd_2243702 < baseStart_2243702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243715 : List Nat := [1, 1, 1, 3, 3, 2, 5, 1, 5]
def baseStart_2243715 : Nat := 118140960795 + 2243715 * 2 ^ 59
def prefixEnd_2243715 : Nat := 4983230072969 + 3 ^ 40 * 2243715 * 2
def baseEnd_2243715 : Nat := 256023165933954264098633

theorem tailTrace_2243715 : CollatzResearch.WordTrace tailWord_2243715 prefixEnd_2243715 256023165933954264098633 := by
  unfold tailWord_2243715
  simp only [CollatzResearch.WordTrace]
  refine ⟨81835009066411225859316599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54556672710940817239544399 81835009066411225859316599)
  ·
    refine ⟨122752513599616838788974899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81835009066411225859316599 122752513599616838788974899)
    ·
      refine ⟨184128770399425258183462349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122752513599616838788974899 184128770399425258183462349)
      ·
        refine ⟨69048288899784471818798381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184128770399425258183462349 69048288899784471818798381)
        ·
          refine ⟨25893108337419176932049393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69048288899784471818798381 25893108337419176932049393)
          ·
            refine ⟨19419831253064382699037045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25893108337419176932049393 19419831253064382699037045)
            ·
              refine ⟨1820609179974785878034723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19419831253064382699037045 1820609179974785878034723)
              ·
                refine ⟨2730913769962178817052085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1820609179974785878034723 2730913769962178817052085)
                ·
                  refine ⟨256023165933954264098633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2730913769962178817052085 256023165933954264098633)
                  ·
                    rfl

theorem cell22_2243715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 5].length) (baseStart_2243715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243715 prefixEnd_2243715 := by exact prefixLift 2243715
  have htrace : WordTrace (prefixWord ++ tailWord_2243715) baseStart_2243715 baseEnd_2243715 := by
    simpa [prefixWord, tailWord_2243715, baseEnd_2243715] using wordTrace_append hprefix tailTrace_2243715
  have hstable : (prefixWord ++ tailWord_2243715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243715).length < 2 ^ (prefixWord ++ tailWord_2243715).sum := by decide
  have hdescent : baseEnd_2243715 < baseStart_2243715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243745 : List Nat := [1, 2, 3, 3, 1, 1, 1, 5, 1, 4]
def baseStart_2243745 : Nat := 118140960795 + 2243745 * 2 ^ 59
def prefixEnd_2243745 : Nat := 4983230072969 + 3 ^ 40 * 2243745 * 2
def baseEnd_2243745 : Nat := 768079767414952714045807

theorem tailTrace_2243745 : CollatzResearch.WordTrace tailWord_2243745 prefixEnd_2243745 768079767414952714045807 := by
  unfold tailWord_2243745
  simp only [CollatzResearch.WordTrace]
  refine ⟨81836103256302540982908689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54557402170868360655272459 81836103256302540982908689)
  ·
    refine ⟨61377077442226905737181517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81836103256302540982908689 61377077442226905737181517)
    ·
      refine ⟨23016404040835089651443069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61377077442226905737181517 23016404040835089651443069)
      ·
        refine ⟨8631151515313158619291151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23016404040835089651443069 8631151515313158619291151)
        ·
          refine ⟨12946727272969737928936727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8631151515313158619291151 12946727272969737928936727)
          ·
            refine ⟨19420090909454606893405091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12946727272969737928936727 19420090909454606893405091)
            ·
              refine ⟨29130136364181910340107637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19420090909454606893405091 29130136364181910340107637)
              ·
                refine ⟨2730950284142054094385091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29130136364181910340107637 2730950284142054094385091)
                ·
                  refine ⟨4096425426213081141577637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2730950284142054094385091 4096425426213081141577637)
                  ·
                    refine ⟨768079767414952714045807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4096425426213081141577637 768079767414952714045807)
                    ·
                      rfl

theorem cell22_2243745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_2243745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243745 prefixEnd_2243745 := by exact prefixLift 2243745
  have htrace : WordTrace (prefixWord ++ tailWord_2243745) baseStart_2243745 baseEnd_2243745 := by
    simpa [prefixWord, tailWord_2243745, baseEnd_2243745] using wordTrace_append hprefix tailTrace_2243745
  have hstable : (prefixWord ++ tailWord_2243745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243745).length < 2 ^ (prefixWord ++ tailWord_2243745).sum := by decide
  have hdescent : baseEnd_2243745 < baseStart_2243745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243773 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_2243773 : Nat := 118140960795 + 2243773 * 2 ^ 59
def prefixEnd_2243773 : Nat := 4983230072969 + 3 ^ 40 * 2243773 * 2
def baseEnd_2243773 : Nat := 768089352387169974345721

theorem tailTrace_2243773 : CollatzResearch.WordTrace tailWord_2243773 prefixEnd_2243773 768089352387169974345721 := by
  unfold tailWord_2243773
  simp only [CollatzResearch.WordTrace]
  refine ⟨81837124500201101764927973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54558083000134067843285315 81837124500201101764927973)
  ·
    refine ⟨15344460843787706580923995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81837124500201101764927973 15344460843787706580923995)
    ·
      refine ⟨23016691265681559871385993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15344460843787706580923995 23016691265681559871385993)
      ·
        refine ⟨17262518449261169903539495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23016691265681559871385993 17262518449261169903539495)
        ·
          refine ⟨25893777673891754855309243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17262518449261169903539495 25893777673891754855309243)
          ·
            refine ⟨38840666510837632282963865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25893777673891754855309243 38840666510837632282963865)
            ·
              refine ⟨29130499883128224212222899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38840666510837632282963865 29130499883128224212222899)
              ·
                refine ⟨43695749824692336318334349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29130499883128224212222899 43695749824692336318334349)
                ·
                  refine ⟨16385906184259626119375381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43695749824692336318334349 16385906184259626119375381)
                  ·
                    refine ⟨768089352387169974345721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16385906184259626119375381 768089352387169974345721)
                    ·
                      rfl

theorem cell22_2243773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_2243773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243773 prefixEnd_2243773 := by exact prefixLift 2243773
  have htrace : WordTrace (prefixWord ++ tailWord_2243773) baseStart_2243773 baseEnd_2243773 := by
    simpa [prefixWord, tailWord_2243773, baseEnd_2243773] using wordTrace_append hprefix tailTrace_2243773
  have hstable : (prefixWord ++ tailWord_2243773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243773).length < 2 ^ (prefixWord ++ tailWord_2243773).sum := by decide
  have hdescent : baseEnd_2243773 < baseStart_2243773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243796 : List Nat := [2, 4, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_2243796 : Nat := 118140960795 + 2243796 * 2 ^ 59
def prefixEnd_2243796 : Nat := 4983230072969 + 3 ^ 40 * 2243796 * 2
def baseEnd_2243796 : Nat := 768097225757205581020651

theorem tailTrace_2243796 : CollatzResearch.WordTrace tailWord_2243796 prefixEnd_2243796 768097225757205581020651 := by
  unfold tailWord_2243796
  simp only [CollatzResearch.WordTrace]
  refine ⟨40918981689558888346507621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54558642252745184462010161 40918981689558888346507621)
  ·
    refine ⟨7672309066792291564970179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40918981689558888346507621 7672309066792291564970179)
    ·
      refine ⟨11508463600188437347455269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7672309066792291564970179 11508463600188437347455269)
      ·
        refine ⟨2157836925035332002647863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11508463600188437347455269 2157836925035332002647863)
        ·
          refine ⟨3236755387552998003971795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2157836925035332002647863 3236755387552998003971795)
          ·
            refine ⟨4855133081329497005957693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3236755387552998003971795 4855133081329497005957693)
            ·
              refine ⟨1820674905498561377234135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4855133081329497005957693 1820674905498561377234135)
              ·
                refine ⟨2731012358247842065851203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1820674905498561377234135 2731012358247842065851203)
                ·
                  refine ⟨4096518537371763098776805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2731012358247842065851203 4096518537371763098776805)
                  ·
                    refine ⟨768097225757205581020651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4096518537371763098776805 768097225757205581020651)
                    ·
                      rfl

theorem cell22_2243796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_2243796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243796 prefixEnd_2243796 := by exact prefixLift 2243796
  have htrace : WordTrace (prefixWord ++ tailWord_2243796) baseStart_2243796 baseEnd_2243796 := by
    simpa [prefixWord, tailWord_2243796, baseEnd_2243796] using wordTrace_append hprefix tailTrace_2243796
  have hstable : (prefixWord ++ tailWord_2243796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243796).length < 2 ^ (prefixWord ++ tailWord_2243796).sum := by decide
  have hdescent : baseEnd_2243796 < baseStart_2243796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243805 : List Nat := [1, 4, 3, 2, 2, 10]
def baseStart_2243805 : Nat := 118140960795 + 2243805 * 2 ^ 59
def prefixEnd_2243805 : Nat := 4983230072969 + 3 ^ 40 * 2243805 * 2
def baseEnd_2243805 : Nat := 9482719835075710586983

theorem tailTrace_2243805 : CollatzResearch.WordTrace tailWord_2243805 prefixEnd_2243805 9482719835075710586983 := by
  unfold tailWord_2243805
  simp only [CollatzResearch.WordTrace]
  refine ⟨81838291636085171230092869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54558861090723447486728579 81838291636085171230092869)
  ·
    refine ⟨15344679681765969605642413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81838291636085171230092869 15344679681765969605642413)
    ·
      refine ⟨5754254880662238602115905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15344679681765969605642413 5754254880662238602115905)
      ·
        refine ⟨4315691160496678951586929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5754254880662238602115905 4315691160496678951586929)
        ·
          refine ⟨3236768370372509213690197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4315691160496678951586929 3236768370372509213690197)
          ·
            refine ⟨9482719835075710586983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3236768370372509213690197 9482719835075710586983)
            ·
              rfl

theorem cell22_2243805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 10].length) (baseStart_2243805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243805 prefixEnd_2243805 := by exact prefixLift 2243805
  have htrace : WordTrace (prefixWord ++ tailWord_2243805) baseStart_2243805 baseEnd_2243805 := by
    simpa [prefixWord, tailWord_2243805, baseEnd_2243805] using wordTrace_append hprefix tailTrace_2243805
  have hstable : (prefixWord ++ tailWord_2243805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243805).length < 2 ^ (prefixWord ++ tailWord_2243805).sum := by decide
  have hdescent : baseEnd_2243805 < baseStart_2243805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243854 : List Nat := [4, 1, 1, 2, 1, 3, 1, 5, 1, 3]
def baseStart_2243854 : Nat := 118140960795 + 2243854 * 2 ^ 59
def prefixEnd_2243854 : Nat := 4983230072969 + 3 ^ 40 * 2243854 * 2
def baseEnd_2243854 : Nat := 768117080342512763070473

theorem tailTrace_2243854 : CollatzResearch.WordTrace tailWord_2243854 prefixEnd_2243854 768117080342512763070473 := by
  unfold tailWord_2243854
  simp only [CollatzResearch.WordTrace]
  refine ⟨10230009851613456574828327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54560052541938435065751077 10230009851613456574828327)
  ·
    refine ⟨15345014777420184862242491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10230009851613456574828327 15345014777420184862242491)
    ·
      refine ⟨23017522166130277293363737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15345014777420184862242491 23017522166130277293363737)
      ·
        refine ⟨17263141624597707970022803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23017522166130277293363737 17263141624597707970022803)
        ·
          refine ⟨25894712436896561955034205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17263141624597707970022803 25894712436896561955034205)
          ·
            refine ⟨9710517163836210733137827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25894712436896561955034205 9710517163836210733137827)
            ·
              refine ⟨14565775745754316099706741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9710517163836210733137827 14565775745754316099706741)
              ·
                refine ⟨1365541476164467134347507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14565775745754316099706741 1365541476164467134347507)
                ·
                  refine ⟨2048312214246700701521261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1365541476164467134347507 2048312214246700701521261)
                  ·
                    refine ⟨768117080342512763070473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2048312214246700701521261 768117080342512763070473)
                    ·
                      rfl

theorem cell22_2243854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_2243854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243854 prefixEnd_2243854 := by exact prefixLift 2243854
  have htrace : WordTrace (prefixWord ++ tailWord_2243854) baseStart_2243854 baseEnd_2243854 := by
    simpa [prefixWord, tailWord_2243854, baseEnd_2243854] using wordTrace_append hprefix tailTrace_2243854
  have hstable : (prefixWord ++ tailWord_2243854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243854).length < 2 ^ (prefixWord ++ tailWord_2243854).sum := by decide
  have hdescent : baseEnd_2243854 < baseStart_2243854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243882 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 2, 5]
def baseStart_2243882 : Nat := 118140960795 + 2243882 * 2 ^ 59
def prefixEnd_2243882 : Nat := 4983230072969 + 3 ^ 40 * 2243882 * 2
def baseEnd_2243882 : Nat := 768126665314730023370387

theorem tailTrace_2243882 : CollatzResearch.WordTrace tailWord_2243882 prefixEnd_2243882 768126665314730023370387 := by
  unfold tailWord_2243882
  simp only [CollatzResearch.WordTrace]
  refine ⟨20460275014201553345161475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54560733371204142253763933 20460275014201553345161475)
  ·
    refine ⟨30690412521302330017742213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20460275014201553345161475 30690412521302330017742213)
    ·
      refine ⟨5754452347744186878326665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30690412521302330017742213 5754452347744186878326665)
      ·
        refine ⟨4315839260808140158744999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5754452347744186878326665 4315839260808140158744999)
        ·
          refine ⟨6473758891212210238117499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4315839260808140158744999 6473758891212210238117499)
          ·
            refine ⟨9710638336818315357176249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6473758891212210238117499 9710638336818315357176249)
            ·
              refine ⟨7282978752613736517882187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9710638336818315357176249 7282978752613736517882187)
              ·
                refine ⟨10924468128920604776823281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7282978752613736517882187 10924468128920604776823281)
                ·
                  refine ⟨8193351096690453582617461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10924468128920604776823281 8193351096690453582617461)
                  ·
                    refine ⟨768126665314730023370387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8193351096690453582617461 768126665314730023370387)
                    ·
                      rfl

theorem cell22_2243882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_2243882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243882 prefixEnd_2243882 := by exact prefixLift 2243882
  have htrace : WordTrace (prefixWord ++ tailWord_2243882) baseStart_2243882 baseEnd_2243882 := by
    simpa [prefixWord, tailWord_2243882, baseEnd_2243882] using wordTrace_append hprefix tailTrace_2243882
  have hstable : (prefixWord ++ tailWord_2243882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243882).length < 2 ^ (prefixWord ++ tailWord_2243882).sum := by decide
  have hdescent : baseEnd_2243882 < baseStart_2243882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243927 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 4, 3]
def baseStart_2243927 : Nat := 118140960795 + 2243927 * 2 ^ 59
def prefixEnd_2243927 : Nat := 4983230072969 + 3 ^ 40 * 2243927 * 2
def baseEnd_2243927 : Nat := 768142069734364905995249

theorem tailTrace_2243927 : CollatzResearch.WordTrace tailWord_2243927 prefixEnd_2243927 768142069734364905995249 := by
  unfold tailWord_2243927
  simp only [CollatzResearch.WordTrace]
  refine ⟨81842741341643186066034035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54561827561095457377356023 81842741341643186066034035)
  ·
    refine ⟨122764112012464779099051053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81842741341643186066034035 122764112012464779099051053)
    ·
      refine ⟨46036542004674292162144145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122764112012464779099051053 46036542004674292162144145)
      ·
        refine ⟨34527406503505719121608109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46036542004674292162144145 34527406503505719121608109)
        ·
          refine ⟨12947777438814644670603041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34527406503505719121608109 12947777438814644670603041)
          ·
            refine ⟨9710833079110983502952281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12947777438814644670603041 9710833079110983502952281)
            ·
              refine ⟨7283124809333237627214211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9710833079110983502952281 7283124809333237627214211)
              ·
                refine ⟨10924687213999856440821317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7283124809333237627214211 10924687213999856440821317)
                ·
                  refine ⟨2048378852624973082653997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10924687213999856440821317 2048378852624973082653997)
                  ·
                    refine ⟨768142069734364905995249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2048378852624973082653997 768142069734364905995249)
                    ·
                      rfl

theorem cell22_2243927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_2243927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243927 prefixEnd_2243927 := by exact prefixLift 2243927
  have htrace : WordTrace (prefixWord ++ tailWord_2243927) baseStart_2243927 baseEnd_2243927 := by
    simpa [prefixWord, tailWord_2243927, baseEnd_2243927] using wordTrace_append hprefix tailTrace_2243927
  have hstable : (prefixWord ++ tailWord_2243927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243927).length < 2 ^ (prefixWord ++ tailWord_2243927).sum := by decide
  have hdescent : baseEnd_2243927 < baseStart_2243927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243940 : List Nat := [2, 3, 1, 1, 3, 2, 1, 9]
def baseStart_2243940 : Nat := 118140960795 + 2243940 * 2 ^ 59
def prefixEnd_2243940 : Nat := 4983230072969 + 3 ^ 40 * 2243940 * 2
def baseEnd_2243940 : Nat := 85349613322226356157801

theorem tailTrace_2243940 : CollatzResearch.WordTrace tailWord_2243940 prefixEnd_2243940 85349613322226356157801 := by
  unfold tailWord_2243940
  simp only [CollatzResearch.WordTrace]
  refine ⟨40921607745298044643128637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54562143660397392857504849 40921607745298044643128637)
  ·
    refine ⟨15345602904486766741173239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40921607745298044643128637 15345602904486766741173239)
    ·
      refine ⟨23018404356730150111759859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15345602904486766741173239 23018404356730150111759859)
      ·
        refine ⟨34527606535095225167639789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23018404356730150111759859 34527606535095225167639789)
        ·
          refine ⟨12947852450660709437864921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34527606535095225167639789 12947852450660709437864921)
          ·
            refine ⟨9710889337995532078398691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12947852450660709437864921 9710889337995532078398691)
            ·
              refine ⟨14566334006993298117598037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9710889337995532078398691 14566334006993298117598037)
              ·
                refine ⟨85349613322226356157801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14566334006993298117598037 85349613322226356157801)
                ·
                  rfl

theorem cell22_2243940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 9].length) (baseStart_2243940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2243940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2243940 prefixEnd_2243940 := by exact prefixLift 2243940
  have htrace : WordTrace (prefixWord ++ tailWord_2243940) baseStart_2243940 baseEnd_2243940 := by
    simpa [prefixWord, tailWord_2243940, baseEnd_2243940] using wordTrace_append hprefix tailTrace_2243940
  have hstable : (prefixWord ++ tailWord_2243940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243940).length < 2 ^ (prefixWord ++ tailWord_2243940).sum := by decide
  have hdescent : baseEnd_2243940 < baseStart_2243940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244036 : List Nat := [2, 3, 3, 2, 1, 3, 1, 2, 5]
def baseStart_2244036 : Nat := 118140960795 + 2244036 * 2 ^ 59
def prefixEnd_2244036 : Nat := 4983230072969 + 3 ^ 40 * 2244036 * 2
def baseEnd_2244036 : Nat := 256059794220641651673305

theorem tailTrace_2244036 : CollatzResearch.WordTrace tailWord_2244036 prefixEnd_2244036 256059794220641651673305 := by
  unfold tailWord_2244036
  simp only [CollatzResearch.WordTrace]
  refine ⟨40923358449124148840875981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54564477932165531787834641 40923358449124148840875981)
  ·
    refine ⟨15346259418421555815328493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40923358449124148840875981 15346259418421555815328493)
    ·
      refine ⟨5754847281908083430748185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15346259418421555815328493 5754847281908083430748185)
      ·
        refine ⟨4316135461431062573061139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5754847281908083430748185 4316135461431062573061139)
        ·
          refine ⟨6474203192146593859591709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4316135461431062573061139 6474203192146593859591709)
          ·
            refine ⟨2427826197054972697346891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6474203192146593859591709 2427826197054972697346891)
            ·
              refine ⟨3641739295582459046020337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2427826197054972697346891 3641739295582459046020337)
              ·
                refine ⟨2731304471686844284515253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3641739295582459046020337 2731304471686844284515253)
                ·
                  refine ⟨256059794220641651673305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2731304471686844284515253 256059794220641651673305)
                  ·
                    rfl

theorem cell22_2244036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_2244036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244036 prefixEnd_2244036 := by exact prefixLift 2244036
  have htrace : WordTrace (prefixWord ++ tailWord_2244036) baseStart_2244036 baseEnd_2244036 := by
    simpa [prefixWord, tailWord_2244036, baseEnd_2244036] using wordTrace_append hprefix tailTrace_2244036
  have hstable : (prefixWord ++ tailWord_2244036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244036).length < 2 ^ (prefixWord ++ tailWord_2244036).sum := by decide
  have hdescent : baseEnd_2244036 < baseStart_2244036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244081 : List Nat := [1, 2, 2, 2, 3, 4, 1, 3, 4]
def baseStart_2244081 : Nat := 118140960795 + 2244081 * 2 ^ 59
def prefixEnd_2244081 : Nat := 4983230072969 + 3 ^ 40 * 2244081 * 2
def baseEnd_2244081 : Nat := 256064929027186612548259

theorem tailTrace_2244081 : CollatzResearch.WordTrace tailWord_2244081 prefixEnd_2244081 256064929027186612548259 := by
  unfold tailWord_2244081
  simp only [CollatzResearch.WordTrace]
  refine ⟨81848358183085270367140097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54565572122056846911426731 81848358183085270367140097)
  ·
    refine ⟨61386268637313952775355073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81848358183085270367140097 61386268637313952775355073)
    ·
      refine ⟨46039701477985464581516305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61386268637313952775355073 46039701477985464581516305)
      ·
        refine ⟨34529776108489098436137229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46039701477985464581516305 34529776108489098436137229)
        ·
          refine ⟨12948666040683411913551461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34529776108489098436137229 12948666040683411913551461)
          ·
            refine ⟨2427874882628139733790899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12948666040683411913551461 2427874882628139733790899)
            ·
              refine ⟨3641812323942209600686349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2427874882628139733790899 3641812323942209600686349)
              ·
                refine ⟨1365679621478328600257381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3641812323942209600686349 1365679621478328600257381)
                ·
                  refine ⟨256064929027186612548259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1365679621478328600257381 256064929027186612548259)
                  ·
                    rfl

theorem cell22_2244081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 4].length) (baseStart_2244081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244081 prefixEnd_2244081 := by exact prefixLift 2244081
  have htrace : WordTrace (prefixWord ++ tailWord_2244081) baseStart_2244081 baseEnd_2244081 := by
    simpa [prefixWord, tailWord_2244081, baseEnd_2244081] using wordTrace_append hprefix tailTrace_2244081
  have hstable : (prefixWord ++ tailWord_2244081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244081).length < 2 ^ (prefixWord ++ tailWord_2244081).sum := by decide
  have hdescent : baseEnd_2244081 < baseStart_2244081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244124 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 5, 3]
def baseStart_2244124 : Nat := 118140960795 + 2244124 * 2 ^ 59
def prefixEnd_2244124 : Nat := 4983230072969 + 3 ^ 40 * 2244124 * 2
def baseEnd_2244124 : Nat := 768209506860322058819645

theorem tailTrace_2244124 : CollatzResearch.WordTrace tailWord_2244124 prefixEnd_2244124 768209506860322058819645 := by
  unfold tailWord_2244124
  simp only [CollatzResearch.WordTrace]
  refine ⟨40924963260964744355477713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54566617681286325807303617 40924963260964744355477713)
  ·
    refine ⟨30693722445723558266608285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40924963260964744355477713 30693722445723558266608285)
    ·
      refine ⟨11510145917146334349978107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30693722445723558266608285 11510145917146334349978107)
      ·
        refine ⟨17265218875719501524967161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11510145917146334349978107 17265218875719501524967161)
        ·
          refine ⟨12948914156789626143725371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17265218875719501524967161 12948914156789626143725371)
          ·
            refine ⟨19423371235184439215588057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12948914156789626143725371 19423371235184439215588057)
            ·
              refine ⟨14567528426388329411691043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19423371235184439215588057 14567528426388329411691043)
              ·
                refine ⟨21851292639582494117536565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14567528426388329411691043 21851292639582494117536565)
                ·
                  refine ⟨2048558684960858823519053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21851292639582494117536565 2048558684960858823519053)
                  ·
                    refine ⟨768209506860322058819645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2048558684960858823519053 768209506860322058819645)
                    ·
                      rfl

theorem cell22_2244124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_2244124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244124 prefixEnd_2244124 := by exact prefixLift 2244124
  have htrace : WordTrace (prefixWord ++ tailWord_2244124) baseStart_2244124 baseEnd_2244124 := by
    simpa [prefixWord, tailWord_2244124, baseEnd_2244124] using wordTrace_append hprefix tailTrace_2244124
  have hstable : (prefixWord ++ tailWord_2244124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244124).length < 2 ^ (prefixWord ++ tailWord_2244124).sum := by decide
  have hdescent : baseEnd_2244124 < baseStart_2244124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244154 : List Nat := [3, 1, 1, 1, 3, 2, 4, 2, 5]
def baseStart_2244154 : Nat := 118140960795 + 2244154 * 2 ^ 59
def prefixEnd_2244154 : Nat := 4983230072969 + 3 ^ 40 * 2244154 * 2
def baseEnd_2244154 : Nat := 256073258824470660189851

theorem tailTrace_2244154 : CollatzResearch.WordTrace tailWord_2244154 prefixEnd_2244154 256073258824470660189851 := by
  unfold tailWord_2244154
  simp only [CollatzResearch.WordTrace]
  refine ⟨20462755177955200958636879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54567347141213869223031677 20462755177955200958636879)
  ·
    refine ⟨30694132766932801437955319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20462755177955200958636879 30694132766932801437955319)
    ·
      refine ⟨46041199150399202156932979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30694132766932801437955319 46041199150399202156932979)
      ·
        refine ⟨69061798725598803235399469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46041199150399202156932979 69061798725598803235399469)
        ·
          refine ⟨25898174522099551213274801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69061798725598803235399469 25898174522099551213274801)
          ·
            refine ⟨19423630891574663409956101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25898174522099551213274801 19423630891574663409956101)
            ·
              refine ⟨3641930792170249389366769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19423630891574663409956101 3641930792170249389366769)
              ·
                refine ⟨2731448094127687042025077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3641930792170249389366769 2731448094127687042025077)
                ·
                  refine ⟨256073258824470660189851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2731448094127687042025077 256073258824470660189851)
                  ·
                    rfl

theorem cell22_2244154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_2244154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244154 prefixEnd_2244154 := by exact prefixLift 2244154
  have htrace : WordTrace (prefixWord ++ tailWord_2244154) baseStart_2244154 baseEnd_2244154 := by
    simpa [prefixWord, tailWord_2244154, baseEnd_2244154] using wordTrace_append hprefix tailTrace_2244154
  have hstable : (prefixWord ++ tailWord_2244154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244154).length < 2 ^ (prefixWord ++ tailWord_2244154).sum := by decide
  have hdescent : baseEnd_2244154 < baseStart_2244154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244184 : List Nat := [2, 1, 2, 2, 1, 2, 1, 6, 1, 4]
def baseStart_2244184 : Nat := 118140960795 + 2244184 * 2 ^ 59
def prefixEnd_2244184 : Nat := 4983230072969 + 3 ^ 40 * 2244184 * 2
def baseEnd_2244184 : Nat := 768230046086501902319461

theorem tailTrace_2244184 : CollatzResearch.WordTrace tailWord_2244184 prefixEnd_2244184 768230046086501902319461 := by
  unfold tailWord_2244184
  simp only [CollatzResearch.WordTrace]
  refine ⟨40926057450856059479069803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54568076601141412638759737 40926057450856059479069803)
  ·
    refine ⟨61389086176284089218604705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40926057450856059479069803 61389086176284089218604705)
    ·
      refine ⟨46041814632213066913953529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61389086176284089218604705 46041814632213066913953529)
      ·
        refine ⟨34531360974159800185465147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46041814632213066913953529 34531360974159800185465147)
        ·
          refine ⟨51797041461239700278197721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34531360974159800185465147 51797041461239700278197721)
          ·
            refine ⟨38847781095929775208648291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51797041461239700278197721 38847781095929775208648291)
            ·
              refine ⟨58271671643894662812972437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38847781095929775208648291 58271671643894662812972437)
              ·
                refine ⟨2731484608307562319358083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58271671643894662812972437 2731484608307562319358083)
                ·
                  refine ⟨4097226912461343479037125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2731484608307562319358083 4097226912461343479037125)
                  ·
                    refine ⟨768230046086501902319461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4097226912461343479037125 768230046086501902319461)
                    ·
                      rfl

theorem cell22_2244184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_2244184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244184 prefixEnd_2244184 := by exact prefixLift 2244184
  have htrace : WordTrace (prefixWord ++ tailWord_2244184) baseStart_2244184 baseEnd_2244184 := by
    simpa [prefixWord, tailWord_2244184, baseEnd_2244184] using wordTrace_append hprefix tailTrace_2244184
  have hstable : (prefixWord ++ tailWord_2244184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244184).length < 2 ^ (prefixWord ++ tailWord_2244184).sum := by decide
  have hdescent : baseEnd_2244184 < baseStart_2244184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244201 : List Nat := [1, 2, 1, 1, 1, 4, 6, 1, 1, 4]
def baseStart_2244201 : Nat := 118140960795 + 2244201 * 2 ^ 59
def prefixEnd_2244201 : Nat := 4983230072969 + 3 ^ 40 * 2244201 * 2
def baseEnd_2244201 : Nat := 768235865533919524644409

theorem tailTrace_2244201 : CollatzResearch.WordTrace tailWord_2244201 prefixEnd_2244201 768235865533919524644409 := by
  unfold tailWord_2244201
  simp only [CollatzResearch.WordTrace]
  refine ⟨81852734942650530861508457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54568489961767020574338971 81852734942650530861508457)
  ·
    refine ⟨61389551206987898146131343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81852734942650530861508457 61389551206987898146131343)
    ·
      refine ⟨92084326810481847219197015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61389551206987898146131343 92084326810481847219197015)
      ·
        refine ⟨138126490215722770828795523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92084326810481847219197015 138126490215722770828795523)
        ·
          refine ⟨207189735323584156243193285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138126490215722770828795523 207189735323584156243193285)
          ·
            refine ⟨38848075373172029295598741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207189735323584156243193285 38848075373172029295598741)
            ·
              refine ⟨1821003533117438873231191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38848075373172029295598741 1821003533117438873231191)
              ·
                refine ⟨2731505299676158309846787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1821003533117438873231191 2731505299676158309846787)
                ·
                  refine ⟨4097257949514237464770181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2731505299676158309846787 4097257949514237464770181)
                  ·
                    refine ⟨768235865533919524644409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4097257949514237464770181 768235865533919524644409)
                    ·
                      rfl

theorem cell22_2244201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 1, 4].length) (baseStart_2244201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244201 prefixEnd_2244201 := by exact prefixLift 2244201
  have htrace : WordTrace (prefixWord ++ tailWord_2244201) baseStart_2244201 baseEnd_2244201 := by
    simpa [prefixWord, tailWord_2244201, baseEnd_2244201] using wordTrace_append hprefix tailTrace_2244201
  have hstable : (prefixWord ++ tailWord_2244201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244201).length < 2 ^ (prefixWord ++ tailWord_2244201).sum := by decide
  have hdescent : baseEnd_2244201 < baseStart_2244201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244227 : List Nat := [1, 1, 1, 3, 3, 1, 1, 11]
def baseStart_2244227 : Nat := 118140960795 + 2244227 * 2 ^ 59
def prefixEnd_2244227 : Nat := 4983230072969 + 3 ^ 40 * 2244227 * 2
def baseEnd_2244227 : Nat := 85360529540584902610481

theorem tailTrace_2244227 : CollatzResearch.WordTrace tailWord_2244227 prefixEnd_2244227 85360529540584902610481 := by
  unfold tailWord_2244227
  simp only [CollatzResearch.WordTrace]
  refine ⟨81853683240556337301954935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54569122160370891534636623 81853683240556337301954935)
  ·
    refine ⟨122780524860834505952932403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81853683240556337301954935 122780524860834505952932403)
    ·
      refine ⟨184170787291251758929398605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122780524860834505952932403 184170787291251758929398605)
      ·
        refine ⟨69064045234219409598524477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184170787291251758929398605 69064045234219409598524477)
        ·
          refine ⟨25899016962832278599446679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69064045234219409598524477 25899016962832278599446679)
          ·
            refine ⟨38848525444248417899170019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25899016962832278599446679 38848525444248417899170019)
            ·
              refine ⟨58272788166372626848755029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38848525444248417899170019 58272788166372626848755029)
              ·
                refine ⟨85360529540584902610481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 58272788166372626848755029 85360529540584902610481)
                ·
                  rfl

theorem cell22_2244227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 11].length) (baseStart_2244227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244227 prefixEnd_2244227 := by exact prefixLift 2244227
  have htrace : WordTrace (prefixWord ++ tailWord_2244227) baseStart_2244227 baseEnd_2244227 := by
    simpa [prefixWord, tailWord_2244227, baseEnd_2244227] using wordTrace_append hprefix tailTrace_2244227
  have hstable : (prefixWord ++ tailWord_2244227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244227).length < 2 ^ (prefixWord ++ tailWord_2244227).sum := by decide
  have hdescent : baseEnd_2244227 < baseStart_2244227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244231 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 1, 5]
def baseStart_2244231 : Nat := 118140960795 + 2244231 * 2 ^ 59
def prefixEnd_2244231 : Nat := 4983230072969 + 3 ^ 40 * 2244231 * 2
def baseEnd_2244231 : Nat := 768246135147009446394317

theorem tailTrace_2244231 : CollatzResearch.WordTrace tailWord_2244231 prefixEnd_2244231 768246135147009446394317 := by
  unfold tailWord_2244231
  simp only [CollatzResearch.WordTrace]
  refine ⟨81853829132541845985100547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54569219421694563990067031 81853829132541845985100547)
  ·
    refine ⟨122780743698812768977650821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81853829132541845985100547 122780743698812768977650821)
    ·
      refine ⟨23021389443527394183309529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122780743698812768977650821 23021389443527394183309529)
      ·
        refine ⟨17266042082645545637482147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23021389443527394183309529 17266042082645545637482147)
        ·
          refine ⟨25899063123968318456223221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17266042082645545637482147 25899063123968318456223221)
          ·
            refine ⟨2428037167872029855270927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25899063123968318456223221 2428037167872029855270927)
            ·
              refine ⟨3642055751808044782906391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2428037167872029855270927 3642055751808044782906391)
              ·
                refine ⟨5463083627712067174359587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3642055751808044782906391 5463083627712067174359587)
                ·
                  refine ⟨8194625441568100761539381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5463083627712067174359587 8194625441568100761539381)
                  ·
                    refine ⟨768246135147009446394317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8194625441568100761539381 768246135147009446394317)
                    ·
                      rfl

theorem cell22_2244231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_2244231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244231 prefixEnd_2244231 := by exact prefixLift 2244231
  have htrace : WordTrace (prefixWord ++ tailWord_2244231) baseStart_2244231 baseEnd_2244231 := by
    simpa [prefixWord, tailWord_2244231, baseEnd_2244231] using wordTrace_append hprefix tailTrace_2244231
  have hstable : (prefixWord ++ tailWord_2244231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244231).length < 2 ^ (prefixWord ++ tailWord_2244231).sum := by decide
  have hdescent : baseEnd_2244231 < baseStart_2244231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244278 : List Nat := [5, 1, 3, 1, 1, 2, 2, 7]
def baseStart_2244278 : Nat := 118140960795 + 2244278 * 2 ^ 59
def prefixEnd_2244278 : Nat := 4983230072969 + 3 ^ 40 * 2244278 * 2
def baseEnd_2244278 : Nat := 85362469356390776718797

theorem tailTrace_2244278 : CollatzResearch.WordTrace tailWord_2244278 prefixEnd_2244278 85362469356390776718797 := by
  unfold tailWord_2244278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5115971460210723313253843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54570362242247715341374325 5115971460210723313253843)
  ·
    refine ⟨7673957190316084969880765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5115971460210723313253843 7673957190316084969880765)
    ·
      refine ⟨2877733946368531863705287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7673957190316084969880765 2877733946368531863705287)
      ·
        refine ⟨4316600919552797795557931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2877733946368531863705287 4316600919552797795557931)
        ·
          refine ⟨6474901379329196693336897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4316600919552797795557931 6474901379329196693336897)
          ·
            refine ⟨4856176034496897520002673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6474901379329196693336897 4856176034496897520002673)
            ·
              refine ⟨3642132025872673140002005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4856176034496897520002673 3642132025872673140002005)
              ·
                refine ⟨85362469356390776718797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3642132025872673140002005 85362469356390776718797)
                ·
                  rfl

theorem cell22_2244278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_2244278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244278 prefixEnd_2244278 := by exact prefixLift 2244278
  have htrace : WordTrace (prefixWord ++ tailWord_2244278) baseStart_2244278 baseEnd_2244278 := by
    simpa [prefixWord, tailWord_2244278, baseEnd_2244278] using wordTrace_append hprefix tailTrace_2244278
  have hstable : (prefixWord ++ tailWord_2244278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244278).length < 2 ^ (prefixWord ++ tailWord_2244278).sum := by decide
  have hdescent : baseEnd_2244278 < baseStart_2244278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244323 : List Nat := [1, 1, 1, 7, 2, 1, 2, 2, 5]
def baseStart_2244323 : Nat := 118140960795 + 2244323 * 2 ^ 59
def prefixEnd_2244323 : Nat := 4983230072969 + 3 ^ 40 * 2244323 * 2
def baseEnd_2244323 : Nat := 256092542875717291031345

theorem tailTrace_2244323 : CollatzResearch.WordTrace tailWord_2244323 prefixEnd_2244323 256092542875717291031345 := by
  unfold tailWord_2244323
  simp only [CollatzResearch.WordTrace]
  refine ⟨81857184648208545697449623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54571456432139030464966415 81857184648208545697449623)
  ·
    refine ⟨122785776972312818546174435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81857184648208545697449623 122785776972312818546174435)
    ·
      refine ⟨184178665458469227819261653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122785776972312818546174435 184178665458469227819261653)
      ·
        refine ⟨4316687471682872527013945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 184178665458469227819261653 4316687471682872527013945)
        ·
          refine ⟨3237515603762154395260459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4316687471682872527013945 3237515603762154395260459)
          ·
            refine ⟨4856273405643231592890689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3237515603762154395260459 4856273405643231592890689)
            ·
              refine ⟨3642205054232423694668017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4856273405643231592890689 3642205054232423694668017)
              ·
                refine ⟨2731653790674317771001013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3642205054232423694668017 2731653790674317771001013)
                ·
                  refine ⟨256092542875717291031345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2731653790674317771001013 256092542875717291031345)
                  ·
                    rfl

theorem cell22_2244323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 5].length) (baseStart_2244323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244323 prefixEnd_2244323 := by exact prefixLift 2244323
  have htrace : WordTrace (prefixWord ++ tailWord_2244323) baseStart_2244323 baseEnd_2244323 := by
    simpa [prefixWord, tailWord_2244323, baseEnd_2244323] using wordTrace_append hprefix tailTrace_2244323
  have hstable : (prefixWord ++ tailWord_2244323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244323).length < 2 ^ (prefixWord ++ tailWord_2244323).sum := by decide
  have hdescent : baseEnd_2244323 < baseStart_2244323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244327 : List Nat := [1, 1, 5, 4, 1, 1, 1, 4, 1, 3]
def baseStart_2244327 : Nat := 118140960795 + 2244327 * 2 ^ 59
def prefixEnd_2244327 : Nat := 4983230072969 + 3 ^ 40 * 2244327 * 2
def baseEnd_2244327 : Nat := 768278997908897195994023

theorem tailTrace_2244327 : CollatzResearch.WordTrace tailWord_2244327 prefixEnd_2244327 768278997908897195994023 := by
  unfold tailWord_2244327
  simp only [CollatzResearch.WordTrace]
  refine ⟨81857330540194054380595235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54571553693462702920396823 81857330540194054380595235)
  ·
    refine ⟨122785995810291081570892853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81857330540194054380595235 122785995810291081570892853)
    ·
      refine ⟨11511187107214788897271205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122785995810291081570892853 11511187107214788897271205)
      ·
        refine ⟨2158347582602772918238351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11511187107214788897271205 2158347582602772918238351)
        ·
          refine ⟨3237521373904159377357527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2158347582602772918238351 3237521373904159377357527)
          ·
            refine ⟨4856282060856239066036291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3237521373904159377357527 4856282060856239066036291)
            ·
              refine ⟨7284423091284358599054437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4856282060856239066036291 7284423091284358599054437)
              ·
                refine ⟨1365829329615817237322707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7284423091284358599054437 1365829329615817237322707)
                ·
                  refine ⟨2048743994423725855984061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1365829329615817237322707 2048743994423725855984061)
                  ·
                    refine ⟨768278997908897195994023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2048743994423725855984061 768278997908897195994023)
                    ·
                      rfl

theorem cell22_2244327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_2244327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244327 prefixEnd_2244327 := by exact prefixLift 2244327
  have htrace : WordTrace (prefixWord ++ tailWord_2244327) baseStart_2244327 baseEnd_2244327 := by
    simpa [prefixWord, tailWord_2244327, baseEnd_2244327] using wordTrace_append hprefix tailTrace_2244327
  have hstable : (prefixWord ++ tailWord_2244327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244327).length < 2 ^ (prefixWord ++ tailWord_2244327).sum := by decide
  have hdescent : baseEnd_2244327 < baseStart_2244327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244340 : List Nat := [2, 6, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2244340 : Nat := 118140960795 + 2244340 * 2 ^ 59
def prefixEnd_2244340 : Nat := 4983230072969 + 3 ^ 40 * 2244340 * 2
def baseEnd_2244340 : Nat := 256094482691523165139661

theorem tailTrace_2244340 : CollatzResearch.WordTrace tailWord_2244340 prefixEnd_2244340 256094482691523165139661 := by
  unfold tailWord_2244340
  simp only [CollatzResearch.WordTrace]
  refine ⟨40928902344573478800409237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54571869792764638400545649 40928902344573478800409237)
  ·
    refine ⟨1918542297401881818769183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40928902344573478800409237 1918542297401881818769183)
    ·
      refine ⟨2877813446102822728153775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1918542297401881818769183 2877813446102822728153775)
      ·
        refine ⟨4316720169154234092230663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2877813446102822728153775 4316720169154234092230663)
        ·
          refine ⟨6475080253731351138345995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4316720169154234092230663 6475080253731351138345995)
          ·
            refine ⟨9712620380597026707518993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6475080253731351138345995 9712620380597026707518993)
            ·
              refine ⟨7284465285447770030639245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9712620380597026707518993 7284465285447770030639245)
              ·
                refine ⟨2731674482042913761489717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7284465285447770030639245 2731674482042913761489717)
                ·
                  refine ⟨256094482691523165139661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2731674482042913761489717 256094482691523165139661)
                  ·
                    rfl

theorem cell22_2244340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2244340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244340 prefixEnd_2244340 := by exact prefixLift 2244340
  have htrace : WordTrace (prefixWord ++ tailWord_2244340) baseStart_2244340 baseEnd_2244340 := by
    simpa [prefixWord, tailWord_2244340, baseEnd_2244340] using wordTrace_append hprefix tailTrace_2244340
  have hstable : (prefixWord ++ tailWord_2244340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244340).length < 2 ^ (prefixWord ++ tailWord_2244340).sum := by decide
  have hdescent : baseEnd_2244340 < baseStart_2244340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244366 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_2244366 : Nat := 118140960795 + 2244366 * 2 ^ 59
def prefixEnd_2244366 : Nat := 4983230072969 + 3 ^ 40 * 2244366 * 2
def baseEnd_2244366 : Nat := 768292348405914094268903

theorem tailTrace_2244366 : CollatzResearch.WordTrace tailWord_2244366 prefixEnd_2244366 768292348405914094268903 := by
  unfold tailWord_2244366
  simp only [CollatzResearch.WordTrace]
  refine ⟨10232344123381595505158119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54572501991368509360843301 10232344123381595505158119)
  ·
    refine ⟨15348516185072393257737179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10232344123381595505158119 15348516185072393257737179)
    ·
      refine ⟨23022774277608589886605769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15348516185072393257737179 23022774277608589886605769)
      ·
        refine ⟨17267080708206442414954327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23022774277608589886605769 17267080708206442414954327)
        ·
          refine ⟨25900621062309663622431491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17267080708206442414954327 25900621062309663622431491)
          ·
            refine ⟨38850931593464495433647237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25900621062309663622431491 38850931593464495433647237)
            ·
              refine ⟨7284549673774592893808857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38850931593464495433647237 7284549673774592893808857)
              ·
                refine ⟨5463412255330944670356643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7284549673774592893808857 5463412255330944670356643)
                ·
                  refine ⟨8195118382996417005534965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5463412255330944670356643 8195118382996417005534965)
                  ·
                    refine ⟨768292348405914094268903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8195118382996417005534965 768292348405914094268903)
                    ·
                      rfl

theorem cell22_2244366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_2244366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244366 prefixEnd_2244366 := by exact prefixLift 2244366
  have htrace : WordTrace (prefixWord ++ tailWord_2244366) baseStart_2244366 baseEnd_2244366 := by
    simpa [prefixWord, tailWord_2244366, baseEnd_2244366] using wordTrace_append hprefix tailTrace_2244366
  have hstable : (prefixWord ++ tailWord_2244366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244366).length < 2 ^ (prefixWord ++ tailWord_2244366).sum := by decide
  have hdescent : baseEnd_2244366 < baseStart_2244366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244370 : List Nat := [3, 2, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_2244370 : Nat := 118140960795 + 2244370 * 2 ^ 59
def prefixEnd_2244370 : Nat := 4983230072969 + 3 ^ 40 * 2244370 * 2
def baseEnd_2244370 : Nat := 768293717687659417168891

theorem tailTrace_2244370 : CollatzResearch.WordTrace tailWord_2244370 prefixEnd_2244370 768293717687659417168891 := by
  unfold tailWord_2244370
  simp only [CollatzResearch.WordTrace]
  refine ⟨20464724719759568181102641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54572599252692181816273709 20464724719759568181102641)
  ·
    refine ⟨15348543539819676135826981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20464724719759568181102641 15348543539819676135826981)
    ·
      refine ⟨2877851913716189275467559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15348543539819676135826981 2877851913716189275467559)
      ·
        refine ⟨4316777870574283913201339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2877851913716189275467559 4316777870574283913201339)
        ·
          refine ⟨6475166805861425869802009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4316777870574283913201339 6475166805861425869802009)
          ·
            refine ⟨4856375104396069402351507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6475166805861425869802009 4856375104396069402351507)
            ·
              refine ⟨7284562656594104103527261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4856375104396069402351507 7284562656594104103527261)
              ·
                refine ⟨2731710996222789038822723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7284562656594104103527261 2731710996222789038822723)
                ·
                  refine ⟨4097566494334183558234085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2731710996222789038822723 4097566494334183558234085)
                  ·
                    refine ⟨768293717687659417168891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4097566494334183558234085 768293717687659417168891)
                    ·
                      rfl

theorem cell22_2244370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_2244370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244370 prefixEnd_2244370 := by exact prefixLift 2244370
  have htrace : WordTrace (prefixWord ++ tailWord_2244370) baseStart_2244370 baseEnd_2244370 := by
    simpa [prefixWord, tailWord_2244370, baseEnd_2244370] using wordTrace_append hprefix tailTrace_2244370
  have hstable : (prefixWord ++ tailWord_2244370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244370).length < 2 ^ (prefixWord ++ tailWord_2244370).sum := by decide
  have hdescent : baseEnd_2244370 < baseStart_2244370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244413 : List Nat := [1, 4, 1, 4, 1, 1, 4, 6]
def baseStart_2244413 : Nat := 118140960795 + 2244413 * 2 ^ 59
def prefixEnd_2244413 : Nat := 4983230072969 + 3 ^ 40 * 2244413 * 2
def baseEnd_2244413 : Nat := 85367604162935737593751

theorem tailTrace_2244413 : CollatzResearch.WordTrace tailWord_2244413 prefixEnd_2244413 85367604162935737593751 := by
  unfold tailWord_2244413
  simp only [CollatzResearch.WordTrace]
  refine ⟨81860467217882491068225893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54573644811921660712150595 81860467217882491068225893)
  ·
    refine ⟨15348837603352967075292355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81860467217882491068225893 15348837603352967075292355)
    ·
      refine ⟨23023256405029450612938533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15348837603352967075292355 23023256405029450612938533)
      ·
        refine ⟨4316860575943021989925975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23023256405029450612938533 4316860575943021989925975)
        ·
          refine ⟨6475290863914532984888963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4316860575943021989925975 6475290863914532984888963)
          ·
            refine ⟨9712936295871799477333445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6475290863914532984888963 9712936295871799477333445)
            ·
              refine ⟨1821175555475962402000021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9712936295871799477333445 1821175555475962402000021)
              ·
                refine ⟨85367604162935737593751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1821175555475962402000021 85367604162935737593751)
                ·
                  rfl

theorem cell22_2244413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 6].length) (baseStart_2244413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244413 prefixEnd_2244413 := by exact prefixLift 2244413
  have htrace : WordTrace (prefixWord ++ tailWord_2244413) baseStart_2244413 baseEnd_2244413 := by
    simpa [prefixWord, tailWord_2244413, baseEnd_2244413] using wordTrace_append hprefix tailTrace_2244413
  have hstable : (prefixWord ++ tailWord_2244413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244413).length < 2 ^ (prefixWord ++ tailWord_2244413).sum := by decide
  have hdescent : baseEnd_2244413 < baseStart_2244413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244441 : List Nat := [1, 2, 1, 2, 2, 3, 2, 4, 5]
def baseStart_2244441 : Nat := 118140960795 + 2244441 * 2 ^ 59
def prefixEnd_2244441 : Nat := 4983230072969 + 3 ^ 40 * 2244441 * 2
def baseEnd_2244441 : Nat := 256106007479546299547891

theorem tailTrace_2244441 : CollatzResearch.WordTrace tailWord_2244441 prefixEnd_2244441 256106007479546299547891 := by
  unfold tailWord_2244441
  simp only [CollatzResearch.WordTrace]
  refine ⟨81861488461781051850245177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54574325641187367900163451 81861488461781051850245177)
  ·
    refine ⟨61396116346335788887683883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81861488461781051850245177 61396116346335788887683883)
    ·
      refine ⟨92094174519503683331525825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61396116346335788887683883 92094174519503683331525825)
      ·
        refine ⟨69070630889627762498644369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92094174519503683331525825 69070630889627762498644369)
        ·
          refine ⟨51802973167220821873983277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69070630889627762498644369 51802973167220821873983277)
          ·
            refine ⟨19426114937707808202743729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51802973167220821873983277 19426114937707808202743729)
            ·
              refine ⟨14569586203280856152057797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19426114937707808202743729 14569586203280856152057797)
              ·
                refine ⟨2731797413115160528510837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14569586203280856152057797 2731797413115160528510837)
                ·
                  refine ⟨256106007479546299547891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2731797413115160528510837 256106007479546299547891)
                  ·
                    rfl

theorem cell22_2244441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 5].length) (baseStart_2244441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244441 prefixEnd_2244441 := by exact prefixLift 2244441
  have htrace : WordTrace (prefixWord ++ tailWord_2244441) baseStart_2244441 baseEnd_2244441 := by
    simpa [prefixWord, tailWord_2244441, baseEnd_2244441] using wordTrace_append hprefix tailTrace_2244441
  have hstable : (prefixWord ++ tailWord_2244441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244441).length < 2 ^ (prefixWord ++ tailWord_2244441).sum := by decide
  have hdescent : baseEnd_2244441 < baseStart_2244441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244456 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 1, 7]
def baseStart_2244456 : Nat := 118140960795 + 2244456 * 2 ^ 59
def prefixEnd_2244456 : Nat := 4983230072969 + 3 ^ 40 * 2244456 * 2
def baseEnd_2244456 : Nat := 768323157245183859518627

theorem tailTrace_2244456 : CollatzResearch.WordTrace tailWord_2244456 prefixEnd_2244456 768323157245183859518627 := by
  unfold tailWord_2244456
  simp only [CollatzResearch.WordTrace]
  refine ⟨40931017778363354706020611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54574690371151139608027481 40931017778363354706020611)
  ·
    refine ⟨61396526667545032059030917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40931017778363354706020611 61396526667545032059030917)
    ·
      refine ⟨11511848750164693511068297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61396526667545032059030917 11511848750164693511068297)
      ·
        refine ⟨8633886562623520133301223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11511848750164693511068297 8633886562623520133301223)
        ·
          refine ⟨12950829843935280199951835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8633886562623520133301223 12950829843935280199951835)
          ·
            refine ⟨19426244765902920299927753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12950829843935280199951835 19426244765902920299927753)
            ·
              refine ⟨14569683574427190224945815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19426244765902920299927753 14569683574427190224945815)
              ·
                refine ⟨21854525361640785337418723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14569683574427190224945815 21854525361640785337418723)
                ·
                  refine ⟨32781788042461178006128085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21854525361640785337418723 32781788042461178006128085)
                  ·
                    refine ⟨768323157245183859518627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32781788042461178006128085 768323157245183859518627)
                    ·
                      rfl

theorem cell22_2244456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_2244456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244456 prefixEnd_2244456 := by exact prefixLift 2244456
  have htrace : WordTrace (prefixWord ++ tailWord_2244456) baseStart_2244456 baseEnd_2244456 := by
    simpa [prefixWord, tailWord_2244456, baseEnd_2244456] using wordTrace_append hprefix tailTrace_2244456
  have hstable : (prefixWord ++ tailWord_2244456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244456).length < 2 ^ (prefixWord ++ tailWord_2244456).sum := by decide
  have hdescent : baseEnd_2244456 < baseStart_2244456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244501 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 3, 5]
def baseStart_2244501 : Nat := 118140960795 + 2244501 * 2 ^ 59
def prefixEnd_2244501 : Nat := 4983230072969 + 3 ^ 40 * 2244501 * 2
def baseEnd_2244501 : Nat := 768338561664818742143489

theorem tailTrace_2244501 : CollatzResearch.WordTrace tailWord_2244501 prefixEnd_2244501 768338561664818742143489 := by
  unfold tailWord_2244501
  simp only [CollatzResearch.WordTrace]
  refine ⟨81863676841563682097429357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54575784561042454731619571 81863676841563682097429357)
  ·
    refine ⟨30698878815586380786536009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81863676841563682097429357 30698878815586380786536009)
    ·
      refine ⟨23024159111689785589902007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30698878815586380786536009 23024159111689785589902007)
      ·
        refine ⟨34536238667534678384853011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23024159111689785589902007 34536238667534678384853011)
        ·
          refine ⟨51804358001302017577279517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34536238667534678384853011 51804358001302017577279517)
          ·
            refine ⟨19426634250488256591479819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51804358001302017577279517 19426634250488256591479819)
            ·
              refine ⟨29139951375732384887219729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19426634250488256591479819 29139951375732384887219729)
              ·
                refine ⟨21854963531799288665414797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29139951375732384887219729 21854963531799288665414797)
                ·
                  refine ⟨8195611324424733249530549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21854963531799288665414797 8195611324424733249530549)
                  ·
                    refine ⟨768338561664818742143489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8195611324424733249530549 768338561664818742143489)
                    ·
                      rfl

theorem cell22_2244501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_2244501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244501 prefixEnd_2244501 := by exact prefixLift 2244501
  have htrace : WordTrace (prefixWord ++ tailWord_2244501) baseStart_2244501 baseEnd_2244501 := by
    simpa [prefixWord, tailWord_2244501, baseEnd_2244501] using wordTrace_append hprefix tailTrace_2244501
  have hstable : (prefixWord ++ tailWord_2244501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244501).length < 2 ^ (prefixWord ++ tailWord_2244501).sum := by decide
  have hdescent : baseEnd_2244501 < baseStart_2244501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244533 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 1, 6]
def baseStart_2244533 : Nat := 118140960795 + 2244533 * 2 ^ 59
def prefixEnd_2244533 : Nat := 4983230072969 + 3 ^ 40 * 2244533 * 2
def baseEnd_2244533 : Nat := 768349515918781325343391

theorem tailTrace_2244533 : CollatzResearch.WordTrace tailWord_2244533 prefixEnd_2244533 768349515918781325343391 := by
  unfold tailWord_2244533
  simp only [CollatzResearch.WordTrace]
  refine ⟨81864843977447751562594253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54576562651631834375062835 81864843977447751562594253)
  ·
    refine ⟨30699316491542906835972845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81864843977447751562594253 30699316491542906835972845)
    ·
      refine ⟨11512243684328590063489817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30699316491542906835972845 11512243684328590063489817)
      ·
        refine ⟨8634182763246442547617363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11512243684328590063489817 8634182763246442547617363)
        ·
          refine ⟨12951274144869663821426045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8634182763246442547617363 12951274144869663821426045)
          ·
            refine ⟨4856727804326123933034767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12951274144869663821426045 4856727804326123933034767)
            ·
              refine ⟨7285091706489185899552151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4856727804326123933034767 7285091706489185899552151)
              ·
                refine ⟨10927637559733778849328227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7285091706489185899552151 10927637559733778849328227)
                ·
                  refine ⟨16391456339600668273992341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10927637559733778849328227 16391456339600668273992341)
                  ·
                    refine ⟨768349515918781325343391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16391456339600668273992341 768349515918781325343391)
                    ·
                      rfl

theorem cell22_2244533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_2244533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244533 prefixEnd_2244533 := by exact prefixLift 2244533
  have htrace : WordTrace (prefixWord ++ tailWord_2244533) baseStart_2244533 baseEnd_2244533 := by
    simpa [prefixWord, tailWord_2244533, baseEnd_2244533] using wordTrace_append hprefix tailTrace_2244533
  have hstable : (prefixWord ++ tailWord_2244533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244533).length < 2 ^ (prefixWord ++ tailWord_2244533).sum := by decide
  have hdescent : baseEnd_2244533 < baseStart_2244533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244552 : List Nat := [2, 1, 3, 1, 4, 3, 1, 2, 2, 3]
def baseStart_2244552 : Nat := 118140960795 + 2244552 * 2 ^ 59
def prefixEnd_2244552 : Nat := 4983230072969 + 3 ^ 40 * 2244552 * 2
def baseEnd_2244552 : Nat := 768356020007071609118333

theorem tailTrace_2244552 : CollatzResearch.WordTrace tailWord_2244552 prefixEnd_2244552 768356020007071609118333 := by
  unfold tailWord_2244552
  simp only [CollatzResearch.WordTrace]
  refine ⟨40932768482189458903767955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54577024642919278538357273 40932768482189458903767955)
  ·
    refine ⟨61399152723284188355651933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40932768482189458903767955 61399152723284188355651933)
    ·
      refine ⟨23024682271231570633369475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61399152723284188355651933 23024682271231570633369475)
      ·
        refine ⟨34537023406847355950054213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23024682271231570633369475 34537023406847355950054213)
        ·
          refine ⟨6475691888783879240635165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34537023406847355950054213 6475691888783879240635165)
          ·
            refine ⟨2428384458293954715238187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6475691888783879240635165 2428384458293954715238187)
            ·
              refine ⟨3642576687440932072857281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2428384458293954715238187 3642576687440932072857281)
              ·
                refine ⟨2731932515580699054642961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3642576687440932072857281 2731932515580699054642961)
                ·
                  refine ⟨2048949386685524290982221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2731932515580699054642961 2048949386685524290982221)
                  ·
                    refine ⟨768356020007071609118333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2048949386685524290982221 768356020007071609118333)
                    ·
                      rfl

theorem cell22_2244552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_2244552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244552 prefixEnd_2244552 := by exact prefixLift 2244552
  have htrace : WordTrace (prefixWord ++ tailWord_2244552) baseStart_2244552 baseEnd_2244552 := by
    simpa [prefixWord, tailWord_2244552, baseEnd_2244552] using wordTrace_append hprefix tailTrace_2244552
  have hstable : (prefixWord ++ tailWord_2244552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244552).length < 2 ^ (prefixWord ++ tailWord_2244552).sum := by decide
  have hdescent : baseEnd_2244552 < baseStart_2244552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244561 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 2, 6]
def baseStart_2244561 : Nat := 118140960795 + 2244561 * 2 ^ 59
def prefixEnd_2244561 : Nat := 4983230072969 + 3 ^ 40 * 2244561 * 2
def baseEnd_2244561 : Nat := 768359100890998585643305

theorem tailTrace_2244561 : CollatzResearch.WordTrace tailWord_2244561 prefixEnd_2244561 768359100890998585643305 := by
  unfold tailWord_2244561
  simp only [CollatzResearch.WordTrace]
  refine ⟨81865865221346312344613537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54577243480897541563075691 81865865221346312344613537)
  ·
    refine ⟨61399398916009734258460153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81865865221346312344613537 61399398916009734258460153)
    ·
      refine ⟨46049549187007300693845115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61399398916009734258460153 46049549187007300693845115)
      ·
        refine ⟨69074323780510951040767673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46049549187007300693845115 69074323780510951040767673)
        ·
          refine ⟨51805742835383213280575755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69074323780510951040767673 51805742835383213280575755)
          ·
            refine ⟨77708614253074819920863633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51805742835383213280575755 77708614253074819920863633)
            ·
              refine ⟨58281460689806114940647725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77708614253074819920863633 58281460689806114940647725)
              ·
                refine ⟨21855547758677293102742897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58281460689806114940647725 21855547758677293102742897)
                ·
                  refine ⟨16391660819007969827057173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21855547758677293102742897 16391660819007969827057173)
                  ·
                    refine ⟨768359100890998585643305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16391660819007969827057173 768359100890998585643305)
                    ·
                      rfl

theorem cell22_2244561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_2244561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244561 prefixEnd_2244561 := by exact prefixLift 2244561
  have htrace : WordTrace (prefixWord ++ tailWord_2244561) baseStart_2244561 baseEnd_2244561 := by
    simpa [prefixWord, tailWord_2244561, baseEnd_2244561] using wordTrace_append hprefix tailTrace_2244561
  have hstable : (prefixWord ++ tailWord_2244561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244561).length < 2 ^ (prefixWord ++ tailWord_2244561).sum := by decide
  have hdescent : baseEnd_2244561 < baseStart_2244561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244657 : List Nat := [1, 2, 2, 3, 1, 4, 3, 1, 1, 4]
def baseStart_2244657 : Nat := 118140960795 + 2244657 * 2 ^ 59
def prefixEnd_2244657 : Nat := 4983230072969 + 3 ^ 40 * 2244657 * 2
def baseEnd_2244657 : Nat := 768391963652886335243011

theorem tailTrace_2244657 : CollatzResearch.WordTrace tailWord_2244657 prefixEnd_2244657 768391963652886335243011 := by
  unfold tailWord_2244657
  simp only [CollatzResearch.WordTrace]
  refine ⟨81869366628998520740108225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54579577752665680493405483 81869366628998520740108225)
  ·
    refine ⟨61402024971748890555081169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81869366628998520740108225 61402024971748890555081169)
    ·
      refine ⟨46051518728811667916310877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61402024971748890555081169 46051518728811667916310877)
      ·
        refine ⟨17269319523304375468616579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46051518728811667916310877 17269319523304375468616579)
        ·
          refine ⟨25903979284956563202924869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17269319523304375468616579 25903979284956563202924869)
          ·
            refine ⟨4856996115929355600548413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25903979284956563202924869 4856996115929355600548413)
            ·
              refine ⟨1821373543473508350205655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4856996115929355600548413 1821373543473508350205655)
              ·
                refine ⟨2732060315210262525308483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1821373543473508350205655 2732060315210262525308483)
                ·
                  refine ⟨4098090472815393787962725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2732060315210262525308483 4098090472815393787962725)
                  ·
                    refine ⟨768391963652886335243011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4098090472815393787962725 768391963652886335243011)
                    ·
                      rfl

theorem cell22_2244657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_2244657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244657 prefixEnd_2244657 := by exact prefixLift 2244657
  have htrace : WordTrace (prefixWord ++ tailWord_2244657) baseStart_2244657 baseEnd_2244657 := by
    simpa [prefixWord, tailWord_2244657, baseEnd_2244657] using wordTrace_append hprefix tailTrace_2244657
  have hstable : (prefixWord ++ tailWord_2244657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244657).length < 2 ^ (prefixWord ++ tailWord_2244657).sum := by decide
  have hdescent : baseEnd_2244657 < baseStart_2244657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244672 : List Nat := [2, 1, 1, 2, 2, 4, 4, 2, 4]
def baseStart_2244672 : Nat := 118140960795 + 2244672 * 2 ^ 59
def prefixEnd_2244672 : Nat := 4983230072969 + 3 ^ 40 * 2244672 * 2
def baseEnd_2244672 : Nat := 256132366153143765372655

theorem tailTrace_2244672 : CollatzResearch.WordTrace tailWord_2244672 prefixEnd_2244672 256132366153143765372655 := by
  unfold tailWord_2244672
  simp only [CollatzResearch.WordTrace]
  refine ⟨40934956861972089150952135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54579942482629452201269513 40934956861972089150952135)
  ·
    refine ⟨61402435292958133726428203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40934956861972089150952135 61402435292958133726428203)
    ·
      refine ⟨92103652939437200589642305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61402435292958133726428203 92103652939437200589642305)
      ·
        refine ⟨69077739704577900442231729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92103652939437200589642305 69077739704577900442231729)
        ·
          refine ⟨51808304778433425331673797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69077739704577900442231729 51808304778433425331673797)
          ·
            refine ⟨9714057145956267249688837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51808304778433425331673797 9714057145956267249688837)
            ·
              refine ⟨1821385714866800109316657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9714057145956267249688837 1821385714866800109316657)
              ·
                refine ⟨1366039286150100081987493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1821385714866800109316657 1366039286150100081987493)
                ·
                  refine ⟨256132366153143765372655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1366039286150100081987493 256132366153143765372655)
                  ·
                    rfl

theorem cell22_2244672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 4].length) (baseStart_2244672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244672 prefixEnd_2244672 := by exact prefixLift 2244672
  have htrace : WordTrace (prefixWord ++ tailWord_2244672) baseStart_2244672 baseEnd_2244672 := by
    simpa [prefixWord, tailWord_2244672, baseEnd_2244672] using wordTrace_append hprefix tailTrace_2244672
  have hstable : (prefixWord ++ tailWord_2244672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244672).length < 2 ^ (prefixWord ++ tailWord_2244672).sum := by decide
  have hdescent : baseEnd_2244672 < baseStart_2244672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244685 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_2244685 : Nat := 118140960795 + 2244685 * 2 ^ 59
def prefixEnd_2244685 : Nat := 4983230072969 + 3 ^ 40 * 2244685 * 2
def baseEnd_2244685 : Nat := 768401548625103595542925

theorem tailTrace_2244685 : CollatzResearch.WordTrace tailWord_2244685 prefixEnd_2244685 768401548625103595542925 := by
  unfold tailWord_2244685
  simp only [CollatzResearch.WordTrace]
  refine ⟨81870387872897081522127509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54580258581931387681418339 81870387872897081522127509)
  ·
    refine ⟨3837674431542050696349727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81870387872897081522127509 3837674431542050696349727)
    ·
      refine ⟨5756511647313076044524591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3837674431542050696349727 5756511647313076044524591)
      ·
        refine ⟨8634767470969614066786887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5756511647313076044524591 8634767470969614066786887)
        ·
          refine ⟨12952151206454421100180331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8634767470969614066786887 12952151206454421100180331)
          ·
            refine ⟨19428226809681631650270497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12952151206454421100180331 19428226809681631650270497)
            ·
              refine ⟨14571170107261223737702873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19428226809681631650270497 14571170107261223737702873)
              ·
                refine ⟨10928377580445917803277155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14571170107261223737702873 10928377580445917803277155)
                ·
                  refine ⟨16392566370668876704915733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10928377580445917803277155 16392566370668876704915733)
                  ·
                    refine ⟨768401548625103595542925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16392566370668876704915733 768401548625103595542925)
                    ·
                      rfl

theorem cell22_2244685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_2244685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244685 prefixEnd_2244685 := by exact prefixLift 2244685
  have htrace : WordTrace (prefixWord ++ tailWord_2244685) baseStart_2244685 baseEnd_2244685 := by
    simpa [prefixWord, tailWord_2244685, baseEnd_2244685] using wordTrace_append hprefix tailTrace_2244685
  have hstable : (prefixWord ++ tailWord_2244685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244685).length < 2 ^ (prefixWord ++ tailWord_2244685).sum := by decide
  have hdescent : baseEnd_2244685 < baseStart_2244685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244732 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 3, 3]
def baseStart_2244732 : Nat := 118140960795 + 2244732 * 2 ^ 59
def prefixEnd_2244732 : Nat := 4983230072969 + 3 ^ 40 * 2244732 * 2
def baseEnd_2244732 : Nat := 768417637685611139617781

theorem tailTrace_2244732 : CollatzResearch.WordTrace tailWord_2244732 prefixEnd_2244732 768417637685611139617781 := by
  unfold tailWord_2244732
  simp only [CollatzResearch.WordTrace]
  refine ⟨40936051051863404274544225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54581401402484539032725633 40936051051863404274544225)
  ·
    refine ⟨30702038288897553205908169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40936051051863404274544225 30702038288897553205908169)
    ·
      refine ⟨23026528716673164904431127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30702038288897553205908169 23026528716673164904431127)
      ·
        refine ⟨34539793075009747356646691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23026528716673164904431127 34539793075009747356646691)
        ·
          refine ⟨51809689612514621034970037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34539793075009747356646691 51809689612514621034970037)
          ·
            refine ⟨4857158401173245722028441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51809689612514621034970037 4857158401173245722028441)
            ·
              refine ⟨3642868800879934291521331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4857158401173245722028441 3642868800879934291521331)
              ·
                refine ⟨5464303201319901437281997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3642868800879934291521331 5464303201319901437281997)
                ·
                  refine ⟨2049113700494963038980749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5464303201319901437281997 2049113700494963038980749)
                  ·
                    refine ⟨768417637685611139617781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2049113700494963038980749 768417637685611139617781)
                    ·
                      rfl

theorem cell22_2244732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_2244732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244732 prefixEnd_2244732 := by exact prefixLift 2244732
  have htrace : WordTrace (prefixWord ++ tailWord_2244732) baseStart_2244732 baseEnd_2244732 := by
    simpa [prefixWord, tailWord_2244732, baseEnd_2244732] using wordTrace_append hprefix tailTrace_2244732
  have hstable : (prefixWord ++ tailWord_2244732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244732).length < 2 ^ (prefixWord ++ tailWord_2244732).sum := by decide
  have hdescent : baseEnd_2244732 < baseStart_2244732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244796 : List Nat := [2, 2, 2, 3, 4, 1, 2, 1, 5]
def baseStart_2244796 : Nat := 118140960795 + 2244796 * 2 ^ 59
def prefixEnd_2244796 : Nat := 4983230072969 + 3 ^ 40 * 2244796 * 2
def baseEnd_2244796 : Nat := 256146515397845435339195

theorem tailTrace_2244796 : CollatzResearch.WordTrace tailWord_2244796 prefixEnd_2244796 256146515397845435339195 := by
  unfold tailWord_2244796
  simp only [CollatzResearch.WordTrace]
  refine ⟨40937218187747473739709121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54582957583663298319612161 40937218187747473739709121)
  ·
    refine ⟨30702913640810605304781841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40937218187747473739709121 30702913640810605304781841)
    ·
      refine ⟨23027185230607953978586381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30702913640810605304781841 23027185230607953978586381)
      ·
        refine ⟨8635194461477982741969893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23027185230607953978586381 8635194461477982741969893)
        ·
          refine ⟨1619098961527121764119355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8635194461477982741969893 1619098961527121764119355)
          ·
            refine ⟨2428648442290682646179033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1619098961527121764119355 2428648442290682646179033)
            ·
              refine ⟨1821486331718011984634275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2428648442290682646179033 1821486331718011984634275)
              ·
                refine ⟨2732229497577017976951413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1821486331718011984634275 2732229497577017976951413)
                ·
                  refine ⟨256146515397845435339195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2732229497577017976951413 256146515397845435339195)
                  ·
                    rfl

theorem cell22_2244796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_2244796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244796 prefixEnd_2244796 := by exact prefixLift 2244796
  have htrace : WordTrace (prefixWord ++ tailWord_2244796) baseStart_2244796 baseEnd_2244796 := by
    simpa [prefixWord, tailWord_2244796, baseEnd_2244796] using wordTrace_append hprefix tailTrace_2244796
  have hstable : (prefixWord ++ tailWord_2244796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244796).length < 2 ^ (prefixWord ++ tailWord_2244796).sum := by decide
  have hdescent : baseEnd_2244796 < baseStart_2244796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244834 : List Nat := [3, 3, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2244834 : Nat := 118140960795 + 2244834 * 2 ^ 59
def prefixEnd_2244834 : Nat := 4983230072969 + 3 ^ 40 * 2244834 * 2
def baseEnd_2244834 : Nat := 768452554370116873567469

theorem tailTrace_2244834 : CollatzResearch.WordTrace tailWord_2244834 prefixEnd_2244834 768452554370116873567469 := by
  unfold tailWord_2244834
  simp only [CollatzResearch.WordTrace]
  refine ⟨20468955587339319992325389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54583881566238186646201037 20468955587339319992325389)
  ·
    refine ⟨7675858345252244997122021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20468955587339319992325389 7675858345252244997122021)
    ·
      refine ⟨1439223439734795936960379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7675858345252244997122021 1439223439734795936960379)
      ·
        refine ⟨2158835159602193905440569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1439223439734795936960379 2158835159602193905440569)
        ·
          refine ⟨1619126369701645429080427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2158835159602193905440569 1619126369701645429080427)
          ·
            refine ⟨2428689554552468143620641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1619126369701645429080427 2428689554552468143620641)
            ·
              refine ⟨1821517165914351107715481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2428689554552468143620641 1821517165914351107715481)
              ·
                refine ⟨1366137874435763330786611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1821517165914351107715481 1366137874435763330786611)
                ·
                  refine ⟨2049206811653644996179917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366137874435763330786611 2049206811653644996179917)
                  ·
                    refine ⟨768452554370116873567469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2049206811653644996179917 768452554370116873567469)
                    ·
                      rfl

theorem cell22_2244834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2244834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244834 prefixEnd_2244834 := by exact prefixLift 2244834
  have htrace : WordTrace (prefixWord ++ tailWord_2244834) baseStart_2244834 baseEnd_2244834 := by
    simpa [prefixWord, tailWord_2244834, baseEnd_2244834] using wordTrace_append hprefix tailTrace_2244834
  have hstable : (prefixWord ++ tailWord_2244834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244834).length < 2 ^ (prefixWord ++ tailWord_2244834).sum := by decide
  have hdescent : baseEnd_2244834 < baseStart_2244834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244835 : List Nat := [1, 1, 1, 8, 11]
def baseStart_2244835 : Nat := 118140960795 + 2244835 * 2 ^ 59
def prefixEnd_2244835 : Nat := 4983230072969 + 3 ^ 40 * 2244835 * 2
def baseEnd_2244835 : Nat := 3162357599549601663755

theorem tailTrace_2244835 : CollatzResearch.WordTrace tailWord_2244835 prefixEnd_2244835 3162357599549601663755 := by
  unfold tailWord_2244835
  simp only [CollatzResearch.WordTrace]
  refine ⟨81875858822353657140087959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54583905881569104760058639 81875858822353657140087959)
  ·
    refine ⟨122813788233530485710131939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81875858822353657140087959 122813788233530485710131939)
    ·
      refine ⟨184220682350295728565197909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122813788233530485710131939 184220682350295728565197909)
      ·
        refine ⟨2158836121292528069123413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 184220682350295728565197909 2158836121292528069123413)
        ·
          refine ⟨3162357599549601663755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2158836121292528069123413 3162357599549601663755)
          ·
            rfl

theorem cell22_2244835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 11].length) (baseStart_2244835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244835 prefixEnd_2244835 := by exact prefixLift 2244835
  have htrace : WordTrace (prefixWord ++ tailWord_2244835) baseStart_2244835 baseEnd_2244835 := by
    simpa [prefixWord, tailWord_2244835, baseEnd_2244835] using wordTrace_append hprefix tailTrace_2244835
  have hstable : (prefixWord ++ tailWord_2244835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244835).length < 2 ^ (prefixWord ++ tailWord_2244835).sum := by decide
  have hdescent : baseEnd_2244835 < baseStart_2244835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244837 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 2, 4]
def baseStart_2244837 : Nat := 118140960795 + 2244837 * 2 ^ 59
def prefixEnd_2244837 : Nat := 4983230072969 + 3 ^ 40 * 2244837 * 2
def baseEnd_2244837 : Nat := 768453581331425865742459

theorem tailTrace_2244837 : CollatzResearch.WordTrace tailWord_2244837 prefixEnd_2244837 768453581331425865742459 := by
  unfold tailWord_2244837
  simp only [CollatzResearch.WordTrace]
  refine ⟨81875931768346411481660765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54583954512230940987773843 81875931768346411481660765)
  ·
    refine ⟨30703474413129904305622787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81875931768346411481660765 30703474413129904305622787)
    ·
      refine ⟨46055211619694856458434181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30703474413129904305622787 46055211619694856458434181)
      ·
        refine ⟨8635352178692785585956409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46055211619694856458434181 8635352178692785585956409)
        ·
          refine ⟨6476514134019589189467307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8635352178692785585956409 6476514134019589189467307)
          ·
            refine ⟨9714771201029383784200961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6476514134019589189467307 9714771201029383784200961)
            ·
              refine ⟨7286078400772037838150721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9714771201029383784200961 7286078400772037838150721)
              ·
                refine ⟨5464558800579028378613041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7286078400772037838150721 5464558800579028378613041)
                ·
                  refine ⟨4098419100434271283959781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5464558800579028378613041 4098419100434271283959781)
                  ·
                    refine ⟨768453581331425865742459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4098419100434271283959781 768453581331425865742459)
                    ·
                      rfl

theorem cell22_2244837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_2244837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244837 prefixEnd_2244837 := by exact prefixLift 2244837
  have htrace : WordTrace (prefixWord ++ tailWord_2244837) baseStart_2244837 baseEnd_2244837 := by
    simpa [prefixWord, tailWord_2244837, baseEnd_2244837] using wordTrace_append hprefix tailTrace_2244837
  have hstable : (prefixWord ++ tailWord_2244837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244837).length < 2 ^ (prefixWord ++ tailWord_2244837).sum := by decide
  have hdescent : baseEnd_2244837 < baseStart_2244837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244839 : List Nat := [1, 1, 5, 3, 1, 1, 1, 4, 2, 3]
def baseStart_2244839 : Nat := 118140960795 + 2244839 * 2 ^ 59
def prefixEnd_2244839 : Nat := 4983230072969 + 3 ^ 40 * 2244839 * 2
def baseEnd_2244839 : Nat := 768454265972298527192453

theorem tailTrace_2244839 : CollatzResearch.WordTrace tailWord_2244839 prefixEnd_2244839 768454265972298527192453 := by
  unfold tailWord_2244839
  simp only [CollatzResearch.WordTrace]
  refine ⟨81876004714339165823233571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54584003142892777215489047 81876004714339165823233571)
  ·
    refine ⟨122814007071508748734850357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81876004714339165823233571 122814007071508748734850357)
    ·
      refine ⟨11513813162953945193892221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122814007071508748734850357 11513813162953945193892221)
      ·
        refine ⟨4317679936107729447709583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11513813162953945193892221 4317679936107729447709583)
        ·
          refine ⟨6476519904161594171564375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4317679936107729447709583 6476519904161594171564375)
          ·
            refine ⟨9714779856242391257346563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6476519904161594171564375 9714779856242391257346563)
            ·
              refine ⟨14572169784363586886019845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9714779856242391257346563 14572169784363586886019845)
              ·
                refine ⟨2732281834568172541128721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14572169784363586886019845 2732281834568172541128721)
                ·
                  refine ⟨2049211375926129405846541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2732281834568172541128721 2049211375926129405846541)
                  ·
                    refine ⟨768454265972298527192453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2049211375926129405846541 768454265972298527192453)
                    ·
                      rfl

theorem cell22_2244839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_2244839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244839 prefixEnd_2244839 := by exact prefixLift 2244839
  have htrace : WordTrace (prefixWord ++ tailWord_2244839) baseStart_2244839 baseEnd_2244839 := by
    simpa [prefixWord, tailWord_2244839, baseEnd_2244839] using wordTrace_append hprefix tailTrace_2244839
  have hstable : (prefixWord ++ tailWord_2244839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244839).length < 2 ^ (prefixWord ++ tailWord_2244839).sum := by decide
  have hdescent : baseEnd_2244839 < baseStart_2244839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244865 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 2, 6]
def baseStart_2244865 : Nat := 118140960795 + 2244865 * 2 ^ 59
def prefixEnd_2244865 : Nat := 4983230072969 + 3 ^ 40 * 2244865 * 2
def baseEnd_2244865 : Nat := 768463166303643126042373

theorem tailTrace_2244865 : CollatzResearch.WordTrace tailWord_2244865 prefixEnd_2244865 768463166303643126042373 := by
  unfold tailWord_2244865
  simp only [CollatzResearch.WordTrace]
  refine ⟨81876953012244972263680049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54584635341496648175786699 81876953012244972263680049)
  ·
    refine ⟨61407714759183729197760037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81876953012244972263680049 61407714759183729197760037)
    ·
      refine ⟨11513946517346949224580007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61407714759183729197760037 11513946517346949224580007)
      ·
        refine ⟨17270919776020423836870011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11513946517346949224580007 17270919776020423836870011)
        ·
          refine ⟨25906379664030635755305017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17270919776020423836870011 25906379664030635755305017)
          ·
            refine ⟨19429784748022976816478763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25906379664030635755305017 19429784748022976816478763)
            ·
              refine ⟨29144677122034465224718145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19429784748022976816478763 29144677122034465224718145)
              ·
                refine ⟨21858507841525848918538609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29144677122034465224718145 21858507841525848918538609)
                ·
                  refine ⟨16393880881144386688903957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21858507841525848918538609 16393880881144386688903957)
                  ·
                    refine ⟨768463166303643126042373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16393880881144386688903957 768463166303643126042373)
                    ·
                      rfl

theorem cell22_2244865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_2244865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244865 prefixEnd_2244865 := by exact prefixLift 2244865
  have htrace : WordTrace (prefixWord ++ tailWord_2244865) baseStart_2244865 baseEnd_2244865 := by
    simpa [prefixWord, tailWord_2244865, baseEnd_2244865] using wordTrace_append hprefix tailTrace_2244865
  have hstable : (prefixWord ++ tailWord_2244865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244865).length < 2 ^ (prefixWord ++ tailWord_2244865).sum := by decide
  have hdescent : baseEnd_2244865 < baseStart_2244865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244867 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 3, 3]
def baseStart_2244867 : Nat := 118140960795 + 2244867 * 2 ^ 59
def prefixEnd_2244867 : Nat := 4983230072969 + 3 ^ 40 * 2244867 * 2
def baseEnd_2244867 : Nat := 768463850944515787492367

theorem tailTrace_2244867 : CollatzResearch.WordTrace tailWord_2244867 prefixEnd_2244867 768463850944515787492367 := by
  unfold tailWord_2244867
  simp only [CollatzResearch.WordTrace]
  refine ⟨81877025958237726605252855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54584683972158484403501903 81877025958237726605252855)
  ·
    refine ⟨122815538937356589907879283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81877025958237726605252855 122815538937356589907879283)
    ·
      refine ⟨184223308406034884861818925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122815538937356589907879283 184223308406034884861818925)
      ·
        refine ⟨69083740652263081823182097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184223308406034884861818925 69083740652263081823182097)
        ·
          refine ⟨51812805489197311367386573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69083740652263081823182097 51812805489197311367386573)
          ·
            refine ⟨19429802058448991762769965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51812805489197311367386573 19429802058448991762769965)
            ·
              refine ⟨7286175771918371911038737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19429802058448991762769965 7286175771918371911038737)
              ·
                refine ⟨5464631828938778933279053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7286175771918371911038737 5464631828938778933279053)
                ·
                  refine ⟨2049236935852042099979645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5464631828938778933279053 2049236935852042099979645)
                  ·
                    refine ⟨768463850944515787492367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2049236935852042099979645 768463850944515787492367)
                    ·
                      rfl

theorem cell22_2244867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 3].length) (baseStart_2244867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244867 prefixEnd_2244867 := by exact prefixLift 2244867
  have htrace : WordTrace (prefixWord ++ tailWord_2244867) baseStart_2244867 baseEnd_2244867 := by
    simpa [prefixWord, tailWord_2244867, baseEnd_2244867] using wordTrace_append hprefix tailTrace_2244867
  have hstable : (prefixWord ++ tailWord_2244867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244867).length < 2 ^ (prefixWord ++ tailWord_2244867).sum := by decide
  have hdescent : baseEnd_2244867 < baseStart_2244867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244871 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 2, 4]
def baseStart_2244871 : Nat := 118140960795 + 2244871 * 2 ^ 59
def prefixEnd_2244871 : Nat := 4983230072969 + 3 ^ 40 * 2244871 * 2
def baseEnd_2244871 : Nat := 768465220226261110392355

theorem tailTrace_2244871 : CollatzResearch.WordTrace tailWord_2244871 prefixEnd_2244871 768465220226261110392355 := by
  unfold tailWord_2244871
  simp only [CollatzResearch.WordTrace]
  refine ⟨81877171850223235288398467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54584781233482156858932311 81877171850223235288398467)
  ·
    refine ⟨122815757775334852932597701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81877171850223235288398467 122815757775334852932597701)
    ·
      refine ⟨23027954582875284924862069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122815757775334852932597701 23027954582875284924862069)
      ·
        refine ⟨2158870742144557961705819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23027954582875284924862069 2158870742144557961705819)
        ·
          refine ⟨3238306113216836942558729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2158870742144557961705819 3238306113216836942558729)
          ·
            refine ⟨2428729584912627706919047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3238306113216836942558729 2428729584912627706919047)
            ·
              refine ⟨3643094377368941560378571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2428729584912627706919047 3643094377368941560378571)
              ·
                refine ⟨5464641566053412340567857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3643094377368941560378571 5464641566053412340567857)
                ·
                  refine ⟨4098481174540059255425893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5464641566053412340567857 4098481174540059255425893)
                  ·
                    refine ⟨768465220226261110392355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4098481174540059255425893 768465220226261110392355)
                    ·
                      rfl

theorem cell22_2244871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_2244871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244871 prefixEnd_2244871 := by exact prefixLift 2244871
  have htrace : WordTrace (prefixWord ++ tailWord_2244871) baseStart_2244871 baseEnd_2244871 := by
    simpa [prefixWord, tailWord_2244871, baseEnd_2244871] using wordTrace_append hprefix tailTrace_2244871
  have hstable : (prefixWord ++ tailWord_2244871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244871).length < 2 ^ (prefixWord ++ tailWord_2244871).sum := by decide
  have hdescent : baseEnd_2244871 < baseStart_2244871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244897 : List Nat := [1, 2, 3, 2, 1, 1, 5, 2, 5]
def baseStart_2244897 : Nat := 118140960795 + 2244897 * 2 ^ 59
def prefixEnd_2244897 : Nat := 4983230072969 + 3 ^ 40 * 2244897 * 2
def baseEnd_2244897 : Nat := 256158040185868569747425

theorem tailTrace_2244897 : CollatzResearch.WordTrace tailWord_2244897 prefixEnd_2244897 256158040185868569747425 := by
  unfold tailWord_2244897
  simp only [CollatzResearch.WordTrace]
  refine ⟨81878120148129041728844945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54585413432086027819229963 81878120148129041728844945)
  ·
    refine ⟨61408590111096781296633709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81878120148129041728844945 61408590111096781296633709)
    ·
      refine ⟨23028221291661292986237641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61408590111096781296633709 23028221291661292986237641)
      ·
        refine ⟨17271165968745969739678231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23028221291661292986237641 17271165968745969739678231)
        ·
          refine ⟨25906748953118954609517347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17271165968745969739678231 25906748953118954609517347)
          ·
            refine ⟨38860123429678431914276021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25906748953118954609517347 38860123429678431914276021)
            ·
              refine ⟨3643136571532352991963377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38860123429678431914276021 3643136571532352991963377)
              ·
                refine ⟨2732352428649264743972533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3643136571532352991963377 2732352428649264743972533)
                ·
                  refine ⟨256158040185868569747425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2732352428649264743972533 256158040185868569747425)
                  ·
                    rfl

theorem cell22_2244897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 5].length) (baseStart_2244897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244897 prefixEnd_2244897 := by exact prefixLift 2244897
  have htrace : WordTrace (prefixWord ++ tailWord_2244897) baseStart_2244897 baseEnd_2244897 := by
    simpa [prefixWord, tailWord_2244897, baseEnd_2244897] using wordTrace_append hprefix tailTrace_2244897
  have hstable : (prefixWord ++ tailWord_2244897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244897).length < 2 ^ (prefixWord ++ tailWord_2244897).sum := by decide
  have hdescent : baseEnd_2244897 < baseStart_2244897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244989 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_2244989 : Nat := 118140960795 + 2244989 * 2 ^ 59
def prefixEnd_2244989 : Nat := 4983230072969 + 3 ^ 40 * 2244989 * 2
def baseEnd_2244989 : Nat := 768505614037748135941993

theorem tailTrace_2244989 : CollatzResearch.WordTrace tailWord_2244989 prefixEnd_2244989 768505614037748135941993 := by
  unfold tailWord_2244989
  simp only [CollatzResearch.WordTrace]
  refine ⟨81881475663795741441194021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54587650442530494294129347 81881475663795741441194021)
  ·
    refine ⟨15352776686961701520223879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81881475663795741441194021 15352776686961701520223879)
    ·
      refine ⟨23029165030442552280335819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15352776686961701520223879 23029165030442552280335819)
      ·
        refine ⟨34543747545663828420503729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23029165030442552280335819 34543747545663828420503729)
        ·
          refine ⟨25907810659247871315377797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34543747545663828420503729 25907810659247871315377797)
          ·
            refine ⟨4857714498608975871633337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25907810659247871315377797 4857714498608975871633337)
            ·
              refine ⟨3643285873956731903725003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4857714498608975871633337 3643285873956731903725003)
              ·
                refine ⟨5464928810935097855587505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3643285873956731903725003 5464928810935097855587505)
                ·
                  refine ⟨4098696608201323391690629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5464928810935097855587505 4098696608201323391690629)
                  ·
                    refine ⟨768505614037748135941993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4098696608201323391690629 768505614037748135941993)
                    ·
                      rfl

theorem cell22_2244989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_2244989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2244989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2244989 prefixEnd_2244989 := by exact prefixLift 2244989
  have htrace : WordTrace (prefixWord ++ tailWord_2244989) baseStart_2244989 baseEnd_2244989 := by
    simpa [prefixWord, tailWord_2244989, baseEnd_2244989] using wordTrace_append hprefix tailTrace_2244989
  have hstable : (prefixWord ++ tailWord_2244989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244989).length < 2 ^ (prefixWord ++ tailWord_2244989).sum := by decide
  have hdescent : baseEnd_2244989 < baseStart_2244989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245021 : List Nat := [1, 4, 2, 1, 5, 1, 1, 7]
def baseStart_2245021 : Nat := 118140960795 + 2245021 * 2 ^ 59
def prefixEnd_2245021 : Nat := 4983230072969 + 3 ^ 40 * 2245021 * 2
def baseEnd_2245021 : Nat := 85390729810190079904655

theorem tailTrace_2245021 : CollatzResearch.WordTrace tailWord_2245021 prefixEnd_2245021 85390729810190079904655 := by
  unfold tailWord_2245021
  simp only [CollatzResearch.WordTrace]
  refine ⟨81882642799679810906358917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54588428533119873937572611 81882642799679810906358917)
  ·
    refine ⟨15352995524939964544942297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81882642799679810906358917 15352995524939964544942297)
    ·
      refine ⟨11514746643704973408706723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15352995524939964544942297 11514746643704973408706723)
      ·
        refine ⟨17272119965557460113060085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11514746643704973408706723 17272119965557460113060085)
        ·
          refine ⟨1619261246771011885599383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17272119965557460113060085 1619261246771011885599383)
          ·
            refine ⟨2428891870156517828399075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1619261246771011885599383 2428891870156517828399075)
            ·
              refine ⟨3643337805234776742598613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2428891870156517828399075 3643337805234776742598613)
              ·
                refine ⟨85390729810190079904655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3643337805234776742598613 85390729810190079904655)
                ·
                  rfl

theorem cell22_2245021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 7].length) (baseStart_2245021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245021 prefixEnd_2245021 := by exact prefixLift 2245021
  have htrace : WordTrace (prefixWord ++ tailWord_2245021) baseStart_2245021 baseEnd_2245021 := by
    simpa [prefixWord, tailWord_2245021, baseEnd_2245021] using wordTrace_append hprefix tailTrace_2245021
  have hstable : (prefixWord ++ tailWord_2245021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245021).length < 2 ^ (prefixWord ++ tailWord_2245021).sum := by decide
  have hdescent : baseEnd_2245021 < baseStart_2245021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245053 : List Nat := [1, 4, 1, 2, 2, 3, 2, 3, 1, 3]
def baseStart_2245053 : Nat := 118140960795 + 2245053 * 2 ^ 59
def prefixEnd_2245053 : Nat := 4983230072969 + 3 ^ 40 * 2245053 * 2
def baseEnd_2245053 : Nat := 768527522545673302341797

theorem tailTrace_2245053 : CollatzResearch.WordTrace tailWord_2245053 prefixEnd_2245053 768527522545673302341797 := by
  unfold tailWord_2245053
  simp only [CollatzResearch.WordTrace]
  refine ⟨81883809935563880371523813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54589206623709253581015875 81883809935563880371523813)
  ·
    refine ⟨15353214362918227569660715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81883809935563880371523813 15353214362918227569660715)
    ·
      refine ⟨23029821544377341354491073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15353214362918227569660715 23029821544377341354491073)
      ·
        refine ⟨17272366158283006015868305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23029821544377341354491073 17272366158283006015868305)
        ·
          refine ⟨12954274618712254511901229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17272366158283006015868305 12954274618712254511901229)
          ·
            refine ⟨4857852982017095441962961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12954274618712254511901229 4857852982017095441962961)
            ·
              refine ⟨3643389736512821581472221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4857852982017095441962961 3643389736512821581472221)
              ·
                refine ⟨1366271151192308093052083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3643389736512821581472221 1366271151192308093052083)
                ·
                  refine ⟨2049406726788462139578125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366271151192308093052083 2049406726788462139578125)
                  ·
                    refine ⟨768527522545673302341797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2049406726788462139578125 768527522545673302341797)
                    ·
                      rfl

theorem cell22_2245053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_2245053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245053 prefixEnd_2245053 := by exact prefixLift 2245053
  have htrace : WordTrace (prefixWord ++ tailWord_2245053) baseStart_2245053 baseEnd_2245053 := by
    simpa [prefixWord, tailWord_2245053, baseEnd_2245053] using wordTrace_append hprefix tailTrace_2245053
  have hstable : (prefixWord ++ tailWord_2245053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245053).length < 2 ^ (prefixWord ++ tailWord_2245053).sum := by decide
  have hdescent : baseEnd_2245053 < baseStart_2245053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245096 : List Nat := [2, 1, 4, 1, 1, 4, 2, 2, 1, 4]
def baseStart_2245096 : Nat := 118140960795 + 2245096 * 2 ^ 59
def prefixEnd_2245096 : Nat := 4983230072969 + 3 ^ 40 * 2245096 * 2
def baseEnd_2245096 : Nat := 768542242324435523516665

theorem tailTrace_2245096 : CollatzResearch.WordTrace tailWord_2245096 prefixEnd_2245096 768542242324435523516665 := by
  unfold tailWord_2245096
  simp only [CollatzResearch.WordTrace]
  refine ⟨40942689137204049357669571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54590252182938732476892761 40942689137204049357669571)
  ·
    refine ⟨61414033705806074036504357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40942689137204049357669571 61414033705806074036504357)
    ·
      refine ⟨11515131319838638881844567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61414033705806074036504357 11515131319838638881844567)
      ·
        refine ⟨17272696979757958322766851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11515131319838638881844567 17272696979757958322766851)
        ·
          refine ⟨25909045469636937484150277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17272696979757958322766851 25909045469636937484150277)
          ·
            refine ⟨4857946025556925778278177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25909045469636937484150277 4857946025556925778278177)
            ·
              refine ⟨3643459519167694333708633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4857946025556925778278177 3643459519167694333708633)
              ·
                refine ⟨2732594639375770750281475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3643459519167694333708633 2732594639375770750281475)
                ·
                  refine ⟨4098891959063656125422213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2732594639375770750281475 4098891959063656125422213)
                  ·
                    refine ⟨768542242324435523516665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4098891959063656125422213 768542242324435523516665)
                    ·
                      rfl

theorem cell22_2245096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_2245096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245096 prefixEnd_2245096 := by exact prefixLift 2245096
  have htrace : WordTrace (prefixWord ++ tailWord_2245096) baseStart_2245096 baseEnd_2245096 := by
    simpa [prefixWord, tailWord_2245096, baseEnd_2245096] using wordTrace_append hprefix tailTrace_2245096
  have hstable : (prefixWord ++ tailWord_2245096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245096).length < 2 ^ (prefixWord ++ tailWord_2245096).sum := by decide
  have hdescent : baseEnd_2245096 < baseStart_2245096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245107 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 1, 6]
def baseStart_2245107 : Nat := 118140960795 + 2245107 * 2 ^ 59
def prefixEnd_2245107 : Nat := 4983230072969 + 3 ^ 40 * 2245107 * 2
def baseEnd_2245107 : Nat := 768546007849235161491631

theorem tailTrace_2245107 : CollatzResearch.WordTrace tailWord_2245107 prefixEnd_2245107 768546007849235161491631 := by
  unfold tailWord_2245107
  simp only [CollatzResearch.WordTrace]
  refine ⟨81885779477368247593989575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54590519651578831729326383 81885779477368247593989575)
  ·
    refine ⟨122828669216052371390984363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81885779477368247593989575 122828669216052371390984363)
    ·
      refine ⟨184243003824078557086476545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122828669216052371390984363 184243003824078557086476545)
      ·
        refine ⟨138182252868058917814857409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184243003824078557086476545 138182252868058917814857409)
        ·
          refine ⟨103636689651044188361143057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138182252868058917814857409 103636689651044188361143057)
          ·
            refine ⟨77727517238283141270857293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103636689651044188361143057 77727517238283141270857293)
            ·
              refine ⟨29147818964356177976571485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77727517238283141270857293 29147818964356177976571485)
              ·
                refine ⟨10930432111633566741214307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29147818964356177976571485 10930432111633566741214307)
                ·
                  refine ⟨16395648167450350111821461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10930432111633566741214307 16395648167450350111821461)
                  ·
                    refine ⟨768546007849235161491631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16395648167450350111821461 768546007849235161491631)
                    ·
                      rfl

theorem cell22_2245107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 6].length) (baseStart_2245107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245107 prefixEnd_2245107 := by exact prefixLift 2245107
  have htrace : WordTrace (prefixWord ++ tailWord_2245107) baseStart_2245107 baseEnd_2245107 := by
    simpa [prefixWord, tailWord_2245107, baseEnd_2245107] using wordTrace_append hprefix tailTrace_2245107
  have hstable : (prefixWord ++ tailWord_2245107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245107).length < 2 ^ (prefixWord ++ tailWord_2245107).sum := by decide
  have hdescent : baseEnd_2245107 < baseStart_2245107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245137 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 2, 7]
def baseStart_2245137 : Nat := 118140960795 + 2245137 * 2 ^ 59
def prefixEnd_2245137 : Nat := 4983230072969 + 3 ^ 40 * 2245137 * 2
def baseEnd_2245137 : Nat := 768556277462325083241539

theorem tailTrace_2245137 : CollatzResearch.WordTrace tailWord_2245137 prefixEnd_2245137 768556277462325083241539 := by
  unfold tailWord_2245137
  simp only [CollatzResearch.WordTrace]
  refine ⟨81886873667259562717581665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54591249111506375145054443 81886873667259562717581665)
  ·
    refine ⟨61415155250444672038186249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81886873667259562717581665 61415155250444672038186249)
    ·
      refine ⟨46061366437833504028639687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61415155250444672038186249 46061366437833504028639687)
      ·
        refine ⟨69092049656750256042959531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46061366437833504028639687 69092049656750256042959531)
        ·
          refine ⟨103638074485125384064439297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69092049656750256042959531 103638074485125384064439297)
          ·
            refine ⟨77728555863844038048329473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103638074485125384064439297 77728555863844038048329473)
            ·
              refine ⟨58296416897883028536247105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77728555863844038048329473 58296416897883028536247105)
              ·
                refine ⟨43722312673412271402185329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58296416897883028536247105 43722312673412271402185329)
                ·
                  refine ⟨32791734505059203551638997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43722312673412271402185329 32791734505059203551638997)
                  ·
                    refine ⟨768556277462325083241539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32791734505059203551638997 768556277462325083241539)
                    ·
                      rfl

theorem cell22_2245137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_2245137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245137 prefixEnd_2245137 := by exact prefixLift 2245137
  have htrace : WordTrace (prefixWord ++ tailWord_2245137) baseStart_2245137 baseEnd_2245137 := by
    simpa [prefixWord, tailWord_2245137, baseEnd_2245137] using wordTrace_append hprefix tailTrace_2245137
  have hstable : (prefixWord ++ tailWord_2245137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245137).length < 2 ^ (prefixWord ++ tailWord_2245137).sum := by decide
  have hdescent : baseEnd_2245137 < baseStart_2245137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245184 : List Nat := [2, 1, 1, 2, 2, 2, 3, 4, 5]
def baseStart_2245184 : Nat := 118140960795 + 2245184 * 2 ^ 59
def prefixEnd_2245184 : Nat := 4983230072969 + 3 ^ 40 * 2245184 * 2
def baseEnd_2245184 : Nat := 256190788840944209105465

theorem tailTrace_2245184 : CollatzResearch.WordTrace tailWord_2245184 prefixEnd_2245184 256190788840944209105465 := by
  unfold tailWord_2245184
  simp only [CollatzResearch.WordTrace]
  refine ⟨40944293949044644872271303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54592391932059526496361737 40944293949044644872271303)
  ·
    refine ⟨61416440923566967308406955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40944293949044644872271303 61416440923566967308406955)
    ·
      refine ⟨92124661385350450962610433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61416440923566967308406955 92124661385350450962610433)
      ·
        refine ⟨69093496039012838221957825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92124661385350450962610433 69093496039012838221957825)
        ·
          refine ⟨51820122029259628666468369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69093496039012838221957825 51820122029259628666468369)
          ·
            refine ⟨38865091521944721499851277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51820122029259628666468369 38865091521944721499851277)
            ·
              refine ⟨14574409320729270562444229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38865091521944721499851277 14574409320729270562444229)
              ·
                refine ⟨2732701747636738230458293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14574409320729270562444229 2732701747636738230458293)
                ·
                  refine ⟨256190788840944209105465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2732701747636738230458293 256190788840944209105465)
                  ·
                    rfl

theorem cell22_2245184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 5].length) (baseStart_2245184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245184 prefixEnd_2245184 := by exact prefixLift 2245184
  have htrace : WordTrace (prefixWord ++ tailWord_2245184) baseStart_2245184 baseEnd_2245184 := by
    simpa [prefixWord, tailWord_2245184, baseEnd_2245184] using wordTrace_append hprefix tailTrace_2245184
  have hstable : (prefixWord ++ tailWord_2245184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245184).length < 2 ^ (prefixWord ++ tailWord_2245184).sum := by decide
  have hdescent : baseEnd_2245184 < baseStart_2245184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245244 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 3, 5]
def baseStart_2245244 : Nat := 118140960795 + 2245244 * 2 ^ 59
def prefixEnd_2245244 : Nat := 4983230072969 + 3 ^ 40 * 2245244 * 2
def baseEnd_2245244 : Nat := 768592905749012470816211

theorem tailTrace_2245244 : CollatzResearch.WordTrace tailWord_2245244 prefixEnd_2245244 768592905749012470816211 := by
  unfold tailWord_2245244
  simp only [CollatzResearch.WordTrace]
  refine ⟨40945388138935959995863393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54593850851914613327817857 40945388138935959995863393)
  ·
    refine ⟨30709041104201969996897545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40945388138935959995863393 30709041104201969996897545)
    ·
      refine ⟨23031780828151477497673159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30709041104201969996897545 23031780828151477497673159)
      ·
        refine ⟨34547671242227216246509739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23031780828151477497673159 34547671242227216246509739)
        ·
          refine ⟨51821506863340824369764609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34547671242227216246509739 51821506863340824369764609)
          ·
            refine ⟨38866130147505618277323457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51821506863340824369764609 38866130147505618277323457)
            ·
              refine ⟨29149597610629213707992593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38866130147505618277323457 29149597610629213707992593)
              ·
                refine ⟨21862198207971910280994445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29149597610629213707992593 21862198207971910280994445)
                ·
                  refine ⟨8198324327989466355372917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21862198207971910280994445 8198324327989466355372917)
                  ·
                    refine ⟨768592905749012470816211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8198324327989466355372917 768592905749012470816211)
                    ·
                      rfl

theorem cell22_2245244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_2245244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245244 prefixEnd_2245244 := by exact prefixLift 2245244
  have htrace : WordTrace (prefixWord ++ tailWord_2245244) baseStart_2245244 baseEnd_2245244 := by
    simpa [prefixWord, tailWord_2245244, baseEnd_2245244] using wordTrace_append hprefix tailTrace_2245244
  have hstable : (prefixWord ++ tailWord_2245244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245244).length < 2 ^ (prefixWord ++ tailWord_2245244).sum := by decide
  have hdescent : baseEnd_2245244 < baseStart_2245244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245259 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 6, 4]
def baseStart_2245259 : Nat := 118140960795 + 2245259 * 2 ^ 59
def prefixEnd_2245259 : Nat := 4983230072969 + 3 ^ 40 * 2245259 * 2
def baseEnd_2245259 : Nat := 768598040555557431691165

theorem tailTrace_2245259 : CollatzResearch.WordTrace tailWord_2245259 prefixEnd_2245259 768598040555557431691165 := by
  unfold tailWord_2245259
  simp only [CollatzResearch.WordTrace]
  refine ⟨81891323372817577553522831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54594215581878385035681887 81891323372817577553522831)
  ·
    refine ⟨122836985059226366330284247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81891323372817577553522831 122836985059226366330284247)
    ·
      refine ⟨184255477588839549495426371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122836985059226366330284247 184255477588839549495426371)
      ·
        refine ⟨276383216383259324243139557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184255477588839549495426371 276383216383259324243139557)
        ·
          refine ⟨51821853071861123295588667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 276383216383259324243139557 51821853071861123295588667)
          ·
            refine ⟨77732779607791684943383001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51821853071861123295588667 77732779607791684943383001)
            ·
              refine ⟨58299584705843763707537251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77732779607791684943383001 58299584705843763707537251)
              ·
                refine ⟨87449377058765645561305877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58299584705843763707537251 87449377058765645561305877)
                ·
                  refine ⟨4099189549629639635686213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87449377058765645561305877 4099189549629639635686213)
                  ·
                    refine ⟨768598040555557431691165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4099189549629639635686213 768598040555557431691165)
                    ·
                      rfl

theorem cell22_2245259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 4].length) (baseStart_2245259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245259 prefixEnd_2245259 := by exact prefixLift 2245259
  have htrace : WordTrace (prefixWord ++ tailWord_2245259) baseStart_2245259 baseEnd_2245259 := by
    simpa [prefixWord, tailWord_2245259, baseEnd_2245259] using wordTrace_append hprefix tailTrace_2245259
  have hstable : (prefixWord ++ tailWord_2245259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245259).length < 2 ^ (prefixWord ++ tailWord_2245259).sum := by decide
  have hdescent : baseEnd_2245259 < baseStart_2245259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245276 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 1, 6]
def baseStart_2245276 : Nat := 118140960795 + 2245276 * 2 ^ 59
def prefixEnd_2245276 : Nat := 4983230072969 + 3 ^ 40 * 2245276 * 2
def baseEnd_2245276 : Nat := 768603860002975054016113

theorem tailTrace_2245276 : CollatzResearch.WordTrace tailWord_2245276 prefixEnd_2245276 768603860002975054016113 := by
  unfold tailWord_2245276
  simp only [CollatzResearch.WordTrace]
  refine ⟨40945971706877994728445841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54594628942503992971261121 40945971706877994728445841)
  ·
    refine ⟨30709478780158496046334381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40945971706877994728445841 30709478780158496046334381)
    ·
      refine ⟨11516054542559436017375393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30709478780158496046334381 11516054542559436017375393)
      ·
        refine ⟨8637040906919577013031545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11516054542559436017375393 8637040906919577013031545)
        ·
          refine ⟨6477780680189682759773659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8637040906919577013031545 6477780680189682759773659)
          ·
            refine ⟨9716671020284524139660489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6477780680189682759773659 9716671020284524139660489)
            ·
              refine ⟨7287503265213393104745367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9716671020284524139660489 7287503265213393104745367)
              ·
                refine ⟨10931254897820089657118051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7287503265213393104745367 10931254897820089657118051)
                ·
                  refine ⟨16396882346730134485677077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10931254897820089657118051 16396882346730134485677077)
                  ·
                    refine ⟨768603860002975054016113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16396882346730134485677077 768603860002975054016113)
                    ·
                      rfl

theorem cell22_2245276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_2245276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245276 prefixEnd_2245276 := by exact prefixLift 2245276
  have htrace : WordTrace (prefixWord ++ tailWord_2245276) baseStart_2245276 baseEnd_2245276 := by
    simpa [prefixWord, tailWord_2245276, baseEnd_2245276] using wordTrace_append hprefix tailTrace_2245276
  have hstable : (prefixWord ++ tailWord_2245276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245276).length < 2 ^ (prefixWord ++ tailWord_2245276).sum := by decide
  have hdescent : baseEnd_2245276 < baseStart_2245276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245278 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_2245278 : Nat := 118140960795 + 2245278 * 2 ^ 59
def prefixEnd_2245278 : Nat := 4983230072969 + 3 ^ 40 * 2245278 * 2
def baseEnd_2245278 : Nat := 768604544643847715466107

theorem tailTrace_2245278 : CollatzResearch.WordTrace tailWord_2245278 prefixEnd_2245278 768604544643847715466107 := by
  unfold tailWord_2245278
  simp only [CollatzResearch.WordTrace]
  refine ⟨10236502044968592974808061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54594677573165829198976325 10236502044968592974808061)
  ·
    refine ⟨3838688266863222365553023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10236502044968592974808061 3838688266863222365553023)
    ·
      refine ⟨5758032400294833548329535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3838688266863222365553023 5758032400294833548329535)
      ·
        refine ⟨8637048600442250322494303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5758032400294833548329535 8637048600442250322494303)
        ·
          refine ⟨12955572900663375483741455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8637048600442250322494303 12955572900663375483741455)
          ·
            refine ⟨19433359350995063225612183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12955572900663375483741455 19433359350995063225612183)
            ·
              refine ⟨29150039026492594838418275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19433359350995063225612183 29150039026492594838418275)
              ·
                refine ⟨43725058539738892257627413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29150039026492594838418275 43725058539738892257627413)
                ·
                  refine ⟨2049612119050260574576285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43725058539738892257627413 2049612119050260574576285)
                  ·
                    refine ⟨768604544643847715466107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2049612119050260574576285 768604544643847715466107)
                    ·
                      rfl

theorem cell22_2245278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_2245278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245278 prefixEnd_2245278 := by exact prefixLift 2245278
  have htrace : WordTrace (prefixWord ++ tailWord_2245278) baseStart_2245278 baseEnd_2245278 := by
    simpa [prefixWord, tailWord_2245278, baseEnd_2245278] using wordTrace_append hprefix tailTrace_2245278
  have hstable : (prefixWord ++ tailWord_2245278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245278).length < 2 ^ (prefixWord ++ tailWord_2245278).sum := by decide
  have hdescent : baseEnd_2245278 < baseStart_2245278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245280 : List Nat := [2, 1, 1, 4, 4, 2, 1, 3, 4]
def baseStart_2245280 : Nat := 118140960795 + 2245280 * 2 ^ 59
def prefixEnd_2245280 : Nat := 4983230072969 + 3 ^ 40 * 2245280 * 2
def baseEnd_2245280 : Nat := 256201743094906792305367

theorem tailTrace_2245280 : CollatzResearch.WordTrace tailWord_2245280 prefixEnd_2245280 256201743094906792305367 := by
  unfold tailWord_2245280
  simp only [CollatzResearch.WordTrace]
  refine ⟨40946044652870749070018647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54594726203827665426691529 40946044652870749070018647)
  ·
    refine ⟨61419066979306123605027971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40946044652870749070018647 61419066979306123605027971)
    ·
      refine ⟨92128600468959185407541957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61419066979306123605027971 92128600468959185407541957)
      ·
        refine ⟨17274112587929847263914117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92128600468959185407541957 17274112587929847263914117)
        ·
          refine ⟨3238896110236846361983897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17274112587929847263914117 3238896110236846361983897)
          ·
            refine ⟨2429172082677634771487923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3238896110236846361983897 2429172082677634771487923)
            ·
              refine ⟨3643758124016452157231885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2429172082677634771487923 3643758124016452157231885)
              ·
                refine ⟨1366409296506169558961957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3643758124016452157231885 1366409296506169558961957)
                ·
                  refine ⟨256201743094906792305367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1366409296506169558961957 256201743094906792305367)
                  ·
                    rfl

theorem cell22_2245280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 4].length) (baseStart_2245280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245280 prefixEnd_2245280 := by exact prefixLift 2245280
  have htrace : WordTrace (prefixWord ++ tailWord_2245280) baseStart_2245280 baseEnd_2245280 := by
    simpa [prefixWord, tailWord_2245280, baseEnd_2245280] using wordTrace_append hprefix tailTrace_2245280
  have hstable : (prefixWord ++ tailWord_2245280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245280).length < 2 ^ (prefixWord ++ tailWord_2245280).sum := by decide
  have hdescent : baseEnd_2245280 < baseStart_2245280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245293 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_2245293 : Nat := 118140960795 + 2245293 * 2 ^ 59
def prefixEnd_2245293 : Nat := 4983230072969 + 3 ^ 40 * 2245293 * 2
def baseEnd_2245293 : Nat := 768609679450392676341061

theorem tailTrace_2245293 : CollatzResearch.WordTrace tailWord_2245293 prefixEnd_2245293 768609679450392676341061 := by
  unfold tailWord_2245293
  simp only [CollatzResearch.WordTrace]
  refine ⟨81892563454694401360260533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54595042303129600906840355 81892563454694401360260533)
  ·
    refine ⟨7677427823877600127524425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81892563454694401360260533 7677427823877600127524425)
    ·
      refine ⟨5758070867908200095643319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7677427823877600127524425 5758070867908200095643319)
      ·
        refine ⟨8637106301862300143464979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5758070867908200095643319 8637106301862300143464979)
        ·
          refine ⟨12955659452793450215197469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8637106301862300143464979 12955659452793450215197469)
          ·
            refine ⟨4858372294797543830699051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12955659452793450215197469 4858372294797543830699051)
            ·
              refine ⟨7287558442196315746048577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4858372294797543830699051 7287558442196315746048577)
              ·
                refine ⟨5465668831647236809536433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7287558442196315746048577 5465668831647236809536433)
                ·
                  refine ⟨4099251623735427607152325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5465668831647236809536433 4099251623735427607152325)
                  ·
                    refine ⟨768609679450392676341061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4099251623735427607152325 768609679450392676341061)
                    ·
                      rfl

theorem cell22_2245293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_2245293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245293 prefixEnd_2245293 := by exact prefixLift 2245293
  have htrace : WordTrace (prefixWord ++ tailWord_2245293) baseStart_2245293 baseEnd_2245293 := by
    simpa [prefixWord, tailWord_2245293, baseEnd_2245293] using wordTrace_append hprefix tailTrace_2245293
  have hstable : (prefixWord ++ tailWord_2245293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245293).length < 2 ^ (prefixWord ++ tailWord_2245293).sum := by decide
  have hdescent : baseEnd_2245293 < baseStart_2245293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245297 : List Nat := [1, 2, 2, 6, 1, 1, 3, 2, 4]
def baseStart_2245297 : Nat := 118140960795 + 2245297 * 2 ^ 59
def prefixEnd_2245297 : Nat := 4983230072969 + 3 ^ 40 * 2245297 * 2
def baseEnd_2245297 : Nat := 256203682910712666413683

theorem tailTrace_2245297 : CollatzResearch.WordTrace tailWord_2245297 prefixEnd_2245297 256203682910712666413683 := by
  unfold tailWord_2245297
  simp only [CollatzResearch.WordTrace]
  refine ⟨81892709346679910043406145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54595139564453273362270763 81892709346679910043406145)
  ·
    refine ⟨61419532010009932532554609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81892709346679910043406145 61419532010009932532554609)
    ·
      refine ⟨46064649007507449399415957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61419532010009932532554609 46064649007507449399415957)
      ·
        refine ⟨2159280422226911690597623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46064649007507449399415957 2159280422226911690597623)
        ·
          refine ⟨3238920633340367535896435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2159280422226911690597623 3238920633340367535896435)
          ·
            refine ⟨4858380950010551303844653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3238920633340367535896435 4858380950010551303844653)
            ·
              refine ⟨1821892856253956738941745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4858380950010551303844653 1821892856253956738941745)
              ·
                refine ⟨1366419642190467554206309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1821892856253956738941745 1366419642190467554206309)
                ·
                  refine ⟨256203682910712666413683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1366419642190467554206309 256203682910712666413683)
                  ·
                    rfl

theorem cell22_2245297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 4].length) (baseStart_2245297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245297 prefixEnd_2245297 := by exact prefixLift 2245297
  have htrace : WordTrace (prefixWord ++ tailWord_2245297) baseStart_2245297 baseEnd_2245297 := by
    simpa [prefixWord, tailWord_2245297, baseEnd_2245297] using wordTrace_append hprefix tailTrace_2245297
  have hstable : (prefixWord ++ tailWord_2245297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245297).length < 2 ^ (prefixWord ++ tailWord_2245297).sum := by decide
  have hdescent : baseEnd_2245297 < baseStart_2245297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245319 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 9]
def baseStart_2245319 : Nat := 118140960795 + 2245319 * 2 ^ 59
def prefixEnd_2245319 : Nat := 4983230072969 + 3 ^ 40 * 2245319 * 2
def baseEnd_2245319 : Nat := 256206193260579091730327

theorem tailTrace_2245319 : CollatzResearch.WordTrace tailWord_2245319 prefixEnd_2245319 256206193260579091730327 := by
  unfold tailWord_2245319
  simp only [CollatzResearch.WordTrace]
  refine ⟨81893511752600207800707011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54595674501733471867138007 81893511752600207800707011)
  ·
    refine ⟨122840267628900311701060517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81893511752600207800707011 122840267628900311701060517)
    ·
      refine ⟨23032550180418808443948847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122840267628900311701060517 23032550180418808443948847)
      ·
        refine ⟨34548825270628212665923271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23032550180418808443948847 34548825270628212665923271)
        ·
          refine ⟨51823237905942318998884907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34548825270628212665923271 51823237905942318998884907)
          ·
            refine ⟨77734856858913478498327361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51823237905942318998884907 77734856858913478498327361)
            ·
              refine ⟨58301142644185108873745521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77734856858913478498327361 58301142644185108873745521)
              ·
                refine ⟨43725856983138831655309141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58301142644185108873745521 43725856983138831655309141)
                ·
                  refine ⟨256206193260579091730327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43725856983138831655309141 256206193260579091730327)
                  ·
                    rfl

theorem cell22_2245319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 9].length) (baseStart_2245319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245319 prefixEnd_2245319 := by exact prefixLift 2245319
  have htrace : WordTrace (prefixWord ++ tailWord_2245319) baseStart_2245319 baseEnd_2245319 := by
    simpa [prefixWord, tailWord_2245319, baseEnd_2245319] using wordTrace_append hprefix tailTrace_2245319
  have hstable : (prefixWord ++ tailWord_2245319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245319).length < 2 ^ (prefixWord ++ tailWord_2245319).sum := by decide
  have hdescent : baseEnd_2245319 < baseStart_2245319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245383 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 3, 4]
def baseStart_2245383 : Nat := 118140960795 + 2245383 * 2 ^ 59
def prefixEnd_2245383 : Nat := 4983230072969 + 3 ^ 40 * 2245383 * 2
def baseEnd_2245383 : Nat := 768640488289662441590785

theorem tailTrace_2245383 : CollatzResearch.WordTrace tailWord_2245383 prefixEnd_2245383 768640488289662441590785 := by
  unfold tailWord_2245383
  simp only [CollatzResearch.WordTrace]
  refine ⟨81895846024368346731036803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54597230682912231154024535 81895846024368346731036803)
  ·
    refine ⟨122843769036552520096555205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81895846024368346731036803 122843769036552520096555205)
    ·
      refine ⟨23033206694353597518104101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122843769036552520096555205 23033206694353597518104101)
      ·
        refine ⟨4318726255191299534644519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23033206694353597518104101 4318726255191299534644519)
        ·
          refine ⟨6478089382786949301966779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4318726255191299534644519 6478089382786949301966779)
          ·
            refine ⟨9717134074180423952950169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6478089382786949301966779 9717134074180423952950169)
            ·
              refine ⟨7287850555635317964712627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9717134074180423952950169 7287850555635317964712627)
              ·
                refine ⟨10931775833452976947068941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7287850555635317964712627 10931775833452976947068941)
                ·
                  refine ⟨4099415937544866355150853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10931775833452976947068941 4099415937544866355150853)
                  ·
                    refine ⟨768640488289662441590785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4099415937544866355150853 768640488289662441590785)
                    ·
                      rfl

theorem cell22_2245383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_2245383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245383 prefixEnd_2245383 := by exact prefixLift 2245383
  have htrace : WordTrace (prefixWord ++ tailWord_2245383) baseStart_2245383 baseEnd_2245383 := by
    simpa [prefixWord, tailWord_2245383, baseEnd_2245383] using wordTrace_append hprefix tailTrace_2245383
  have hstable : (prefixWord ++ tailWord_2245383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245383).length < 2 ^ (prefixWord ++ tailWord_2245383).sum := by decide
  have hdescent : baseEnd_2245383 < baseStart_2245383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245411 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 4, 4]
def baseStart_2245411 : Nat := 118140960795 + 2245411 * 2 ^ 59
def prefixEnd_2245411 : Nat := 4983230072969 + 3 ^ 40 * 2245411 * 2
def baseEnd_2245411 : Nat := 768650073261879701890699

theorem tailTrace_2245411 : CollatzResearch.WordTrace tailWord_2245411 prefixEnd_2245411 768650073261879701890699 := by
  unfold tailWord_2245411
  simp only [CollatzResearch.WordTrace]
  refine ⟨81896867268266907513056087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54597911512177938342037391 81896867268266907513056087)
  ·
    refine ⟨122845300902400361269584131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81896867268266907513056087 122845300902400361269584131)
    ·
      refine ⟨184267951353600541904376197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122845300902400361269584131 184267951353600541904376197)
      ·
        refine ⟨34550240878800101607070537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184267951353600541904376197 34550240878800101607070537)
        ·
          refine ⟨25912680659100076205302903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34550240878800101607070537 25912680659100076205302903)
          ·
            refine ⟨38869020988650114307954355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25912680659100076205302903 38869020988650114307954355)
            ·
              refine ⟨58303531482975171461931533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38869020988650114307954355 58303531482975171461931533)
              ·
                refine ⟨21863824306115689298224325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58303531482975171461931533 21863824306115689298224325)
                ·
                  refine ⟨4099467057396691743417061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21863824306115689298224325 4099467057396691743417061)
                  ·
                    refine ⟨768650073261879701890699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4099467057396691743417061 768650073261879701890699)
                    ·
                      rfl

theorem cell22_2245411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 4].length) (baseStart_2245411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245411 prefixEnd_2245411 := by exact prefixLift 2245411
  have htrace : WordTrace (prefixWord ++ tailWord_2245411) baseStart_2245411 baseEnd_2245411 := by
    simpa [prefixWord, tailWord_2245411, baseEnd_2245411] using wordTrace_append hprefix tailTrace_2245411
  have hstable : (prefixWord ++ tailWord_2245411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245411).length < 2 ^ (prefixWord ++ tailWord_2245411).sum := by decide
  have hdescent : baseEnd_2245411 < baseStart_2245411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245413 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 4, 3]
def baseStart_2245413 : Nat := 118140960795 + 2245413 * 2 ^ 59
def prefixEnd_2245413 : Nat := 4983230072969 + 3 ^ 40 * 2245413 * 2
def baseEnd_2245413 : Nat := 768650757902752363340693

theorem tailTrace_2245413 : CollatzResearch.WordTrace tailWord_2245413 prefixEnd_2245413 768650757902752363340693 := by
  unfold tailWord_2245413
  simp only [CollatzResearch.WordTrace]
  refine ⟨81896940214259661854628893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54597960142839774569752595 81896940214259661854628893)
  ·
    refine ⟨30711352580347373195485835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81896940214259661854628893 30711352580347373195485835)
    ·
      refine ⟨46067028870521059793228753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30711352580347373195485835 46067028870521059793228753)
      ·
        refine ⟨34550271652890794844921565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46067028870521059793228753 34550271652890794844921565)
        ·
          refine ⟨12956351869834048066845587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34550271652890794844921565 12956351869834048066845587)
          ·
            refine ⟨19434527804751072100268381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12956351869834048066845587 19434527804751072100268381)
            ·
              refine ⟨7287947926781652037600643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19434527804751072100268381 7287947926781652037600643)
              ·
                refine ⟨10931921890172478056400965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7287947926781652037600643 10931921890172478056400965)
                ·
                  refine ⟨2049735354407339635575181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10931921890172478056400965 2049735354407339635575181)
                  ·
                    refine ⟨768650757902752363340693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2049735354407339635575181 768650757902752363340693)
                    ·
                      rfl

theorem cell22_2245413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_2245413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245413 prefixEnd_2245413 := by exact prefixLift 2245413
  have htrace : WordTrace (prefixWord ++ tailWord_2245413) baseStart_2245413 baseEnd_2245413 := by
    simpa [prefixWord, tailWord_2245413, baseEnd_2245413] using wordTrace_append hprefix tailTrace_2245413
  have hstable : (prefixWord ++ tailWord_2245413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245413).length < 2 ^ (prefixWord ++ tailWord_2245413).sum := by decide
  have hdescent : baseEnd_2245413 < baseStart_2245413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245426 : List Nat := [3, 2, 1, 1, 3, 1, 2, 9]
def baseStart_2245426 : Nat := 118140960795 + 2245426 * 2 ^ 59
def prefixEnd_2245426 : Nat := 4983230072969 + 3 ^ 40 * 2245426 * 2
def baseEnd_2245426 : Nat := 85406134229824962529517

theorem tailTrace_2245426 : CollatzResearch.WordTrace tailWord_2245426 prefixEnd_2245426 85406134229824962529517 := by
  unfold tailWord_2245426
  simp only [CollatzResearch.WordTrace]
  refine ⟨20474353590803141268713033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54598276242141710049901421 20474353590803141268713033)
  ·
    refine ⟨15355765193102355951534775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20474353590803141268713033 15355765193102355951534775)
    ·
      refine ⟨23033647789653533927302163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15355765193102355951534775 23033647789653533927302163)
      ·
        refine ⟨34550471684480300890953245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23033647789653533927302163 34550471684480300890953245)
        ·
          refine ⟨12956426881680112834107467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34550471684480300890953245 12956426881680112834107467)
          ·
            refine ⟨19434640322520169251161201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12956426881680112834107467 19434640322520169251161201)
            ·
              refine ⟨14575980241890126938370901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19434640322520169251161201 14575980241890126938370901)
              ·
                refine ⟨85406134229824962529517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14575980241890126938370901 85406134229824962529517)
                ·
                  rfl

theorem cell22_2245426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 9].length) (baseStart_2245426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245426 prefixEnd_2245426 := by exact prefixLift 2245426
  have htrace : WordTrace (prefixWord ++ tailWord_2245426) baseStart_2245426 baseEnd_2245426 := by
    simpa [prefixWord, tailWord_2245426, baseEnd_2245426] using wordTrace_append hprefix tailTrace_2245426
  have hstable : (prefixWord ++ tailWord_2245426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245426).length < 2 ^ (prefixWord ++ tailWord_2245426).sum := by decide
  have hdescent : baseEnd_2245426 < baseStart_2245426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245460 : List Nat := [2, 4, 1, 1, 5, 1, 8]
def baseStart_2245460 : Nat := 118140960795 + 2245460 * 2 ^ 59
def prefixEnd_2245460 : Nat := 4983230072969 + 3 ^ 40 * 2245460 * 2
def baseEnd_2245460 : Nat := 28469142480120737311687

theorem tailTrace_2245460 : CollatzResearch.WordTrace tailWord_2245460 prefixEnd_2245460 28469142480120737311687 := by
  unfold tailWord_2245460
  simp only [CollatzResearch.WordTrace]
  refine ⟨40949327222544694440794917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54599102963392925921059889 40949327222544694440794917)
  ·
    refine ⟨7677998854227130207649047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40949327222544694440794917 7677998854227130207649047)
    ·
      refine ⟨11516998281340695311473571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7677998854227130207649047 11516998281340695311473571)
      ·
        refine ⟨17275497422011042967210357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11516998281340695311473571 17275497422011042967210357)
        ·
          refine ⟨1619577883313535278175971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17275497422011042967210357 1619577883313535278175971)
          ·
            refine ⟨2429366824970302917263957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1619577883313535278175971 2429366824970302917263957)
            ·
              refine ⟨28469142480120737311687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2429366824970302917263957 28469142480120737311687)
              ·
                rfl

theorem cell22_2245460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 8].length) (baseStart_2245460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245460 prefixEnd_2245460 := by exact prefixLift 2245460
  have htrace : WordTrace (prefixWord ++ tailWord_2245460) baseStart_2245460 baseEnd_2245460 := by
    simpa [prefixWord, tailWord_2245460, baseEnd_2245460] using wordTrace_append hprefix tailTrace_2245460
  have hstable : (prefixWord ++ tailWord_2245460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245460).length < 2 ^ (prefixWord ++ tailWord_2245460).sum := by decide
  have hdescent : baseEnd_2245460 < baseStart_2245460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245471 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 7]
def baseStart_2245471 : Nat := 118140960795 + 2245471 * 2 ^ 59
def prefixEnd_2245471 : Nat := 4983230072969 + 3 ^ 40 * 2245471 * 2
def baseEnd_2245471 : Nat := 256223537496019848463505

theorem tailTrace_2245471 : CollatzResearch.WordTrace tailWord_2245471 prefixEnd_2245471 256223537496019848463505 := by
  unfold tailWord_2245471
  simp only [CollatzResearch.WordTrace]
  refine ⟨81899055648049537760240267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54599370432033025173493511 81899055648049537760240267)
  ·
    refine ⟨122848583472074306640360401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81899055648049537760240267 122848583472074306640360401)
    ·
      refine ⟨92136437604055729980270301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122848583472074306640360401 92136437604055729980270301)
      ·
        refine ⟨34551164101520898742601363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92136437604055729980270301 34551164101520898742601363)
        ·
          refine ⟨51826746152281348113902045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34551164101520898742601363 51826746152281348113902045)
          ·
            refine ⟨19435029807105505542713267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51826746152281348113902045 19435029807105505542713267)
            ·
              refine ⟨29152544710658258314069901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19435029807105505542713267 29152544710658258314069901)
              ·
                refine ⟨10932204266496846867776213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29152544710658258314069901 10932204266496846867776213)
                ·
                  refine ⟨256223537496019848463505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10932204266496846867776213 256223537496019848463505)
                  ·
                    rfl

theorem cell22_2245471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 7].length) (baseStart_2245471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245471 prefixEnd_2245471 := by exact prefixLift 2245471
  have htrace : WordTrace (prefixWord ++ tailWord_2245471) baseStart_2245471 baseEnd_2245471 := by
    simpa [prefixWord, tailWord_2245471, baseEnd_2245471] using wordTrace_append hprefix tailTrace_2245471
  have hstable : (prefixWord ++ tailWord_2245471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245471).length < 2 ^ (prefixWord ++ tailWord_2245471).sum := by decide
  have hdescent : baseEnd_2245471 < baseStart_2245471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245475 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 3, 3]
def baseStart_2245475 : Nat := 118140960795 + 2245475 * 2 ^ 59
def prefixEnd_2245475 : Nat := 4983230072969 + 3 ^ 40 * 2245475 * 2
def baseEnd_2245475 : Nat := 768671981769804868290503

theorem tailTrace_2245475 : CollatzResearch.WordTrace tailWord_2245475 prefixEnd_2245475 768671981769804868290503 := by
  unfold tailWord_2245475
  simp only [CollatzResearch.WordTrace]
  refine ⟨81899201540035046443385879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54599467693356697628923919 81899201540035046443385879)
  ·
    refine ⟨122848802310052569665078819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81899201540035046443385879 122848802310052569665078819)
    ·
      refine ⟨184273203465078854497618229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122848802310052569665078819 184273203465078854497618229)
      ·
        refine ⟨17275612824851142609151709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 184273203465078854497618229 17275612824851142609151709)
        ·
          refine ⟨6478354809319178478431891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17275612824851142609151709 6478354809319178478431891)
          ·
            refine ⟨9717532213978767717647837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6478354809319178478431891 9717532213978767717647837)
            ·
              refine ⟨3644074580242037894117939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9717532213978767717647837 3644074580242037894117939)
              ·
                refine ⟨5466111870363056841176909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3644074580242037894117939 5466111870363056841176909)
                ·
                  refine ⟨2049791951386146315441341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5466111870363056841176909 2049791951386146315441341)
                  ·
                    refine ⟨768671981769804868290503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2049791951386146315441341 768671981769804868290503)
                    ·
                      rfl

theorem cell22_2245475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 3].length) (baseStart_2245475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245475 prefixEnd_2245475 := by exact prefixLift 2245475
  have htrace : WordTrace (prefixWord ++ tailWord_2245475) baseStart_2245475 baseEnd_2245475 := by
    simpa [prefixWord, tailWord_2245475, baseEnd_2245475] using wordTrace_append hprefix tailTrace_2245475
  have hstable : (prefixWord ++ tailWord_2245475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245475).length < 2 ^ (prefixWord ++ tailWord_2245475).sum := by decide
  have hdescent : baseEnd_2245475 < baseStart_2245475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245522 : List Nat := [3, 2, 3, 2, 2, 1, 2, 2, 5]
def baseStart_2245522 : Nat := 118140960795 + 2245522 * 2 ^ 59
def prefixEnd_2245522 : Nat := 4983230072969 + 3 ^ 40 * 2245522 * 2
def baseEnd_2245522 : Nat := 256229356943437470788453

theorem tailTrace_2245522 : CollatzResearch.WordTrace tailWord_2245522 prefixEnd_2245522 256229356943437470788453 := by
  unfold tailWord_2245522
  simp only [CollatzResearch.WordTrace]
  refine ⟨20475228942716193367586705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54600610513909848980231213 20475228942716193367586705)
  ·
    refine ⟨15356421707037145025690029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20475228942716193367586705 15356421707037145025690029)
    ·
      refine ⟨5758658140138929384633761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15356421707037145025690029 5758658140138929384633761)
      ·
        refine ⟨4318993605104197038475321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5758658140138929384633761 4318993605104197038475321)
        ·
          refine ⟨3239245203828147778856491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4318993605104197038475321 3239245203828147778856491)
          ·
            refine ⟨4858867805742221668284737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3239245203828147778856491 4858867805742221668284737)
            ·
              refine ⟨3644150854306666251213553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4858867805742221668284737 3644150854306666251213553)
              ·
                refine ⟨2733113140729999688410165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3644150854306666251213553 2733113140729999688410165)
                ·
                  refine ⟨256229356943437470788453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2733113140729999688410165 256229356943437470788453)
                  ·
                    rfl

theorem cell22_2245522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_2245522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245522 prefixEnd_2245522 := by exact prefixLift 2245522
  have htrace : WordTrace (prefixWord ++ tailWord_2245522) baseStart_2245522 baseEnd_2245522 := by
    simpa [prefixWord, tailWord_2245522, baseEnd_2245522] using wordTrace_append hprefix tailTrace_2245522
  have hstable : (prefixWord ++ tailWord_2245522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245522).length < 2 ^ (prefixWord ++ tailWord_2245522).sum := by decide
  have hdescent : baseEnd_2245522 < baseStart_2245522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245533 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 6]
def baseStart_2245533 : Nat := 118140960795 + 2245533 * 2 ^ 59
def prefixEnd_2245533 : Nat := 4983230072969 + 3 ^ 40 * 2245533 * 2
def baseEnd_2245533 : Nat := 256230612118370683446775

theorem tailTrace_2245533 : CollatzResearch.WordTrace tailWord_2245533 prefixEnd_2245533 256230612118370683446775 := by
  unfold tailWord_2245533
  simp only [CollatzResearch.WordTrace]
  refine ⟨81901316973824922348997253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54600877982549948232664835 81901316973824922348997253)
  ·
    refine ⟨15356496932592172940436985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81901316973824922348997253 15356496932592172940436985)
    ·
      refine ⟨11517372699444129705327739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15356496932592172940436985 11517372699444129705327739)
      ·
        refine ⟨17276059049166194557991609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11517372699444129705327739 17276059049166194557991609)
        ·
          refine ⟨12957044286874645918493707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17276059049166194557991609 12957044286874645918493707)
          ·
            refine ⟨19435566430311968877740561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12957044286874645918493707 19435566430311968877740561)
            ·
              refine ⟨14576674822733976658305421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19435566430311968877740561 14576674822733976658305421)
              ·
                refine ⟨5466253058525241246864533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14576674822733976658305421 5466253058525241246864533)
                ·
                  refine ⟨256230612118370683446775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5466253058525241246864533 256230612118370683446775)
                  ·
                    rfl

theorem cell22_2245533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_2245533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245533 prefixEnd_2245533 := by exact prefixLift 2245533
  have htrace : WordTrace (prefixWord ++ tailWord_2245533) baseStart_2245533 baseEnd_2245533 := by
    simpa [prefixWord, tailWord_2245533, baseEnd_2245533] using wordTrace_append hprefix tailTrace_2245533
  have hstable : (prefixWord ++ tailWord_2245533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245533).length < 2 ^ (prefixWord ++ tailWord_2245533).sum := by decide
  have hdescent : baseEnd_2245533 < baseStart_2245533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245582 : List Nat := [4, 1, 1, 1, 2, 3, 3, 2, 2, 3]
def baseStart_2245582 : Nat := 118140960795 + 2245582 * 2 ^ 59
def prefixEnd_2245582 : Nat := 4983230072969 + 3 ^ 40 * 2245582 * 2
def baseEnd_2245582 : Nat := 768708610056492255865175

theorem tailTrace_2245582 : CollatzResearch.WordTrace tailWord_2245582 prefixEnd_2245582 768708610056492255865175 := by
  unfold tailWord_2245582
  simp only [CollatzResearch.WordTrace]
  refine ⟨10237888018830925464691375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54602069433764935811687333 10237888018830925464691375)
  ·
    refine ⟨15356832028246388197037063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10237888018830925464691375 15356832028246388197037063)
    ·
      refine ⟨23035248042369582295555595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15356832028246388197037063 23035248042369582295555595)
      ·
        refine ⟨34552872063554373443333393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23035248042369582295555595 34552872063554373443333393)
        ·
          refine ⟨25914654047665780082500045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34552872063554373443333393 25914654047665780082500045)
          ·
            refine ⟨9717995267874667530937517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25914654047665780082500045 9717995267874667530937517)
            ·
              refine ⟨3644248225453000324101569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9717995267874667530937517 3644248225453000324101569)
              ·
                refine ⟨2733186169089750243076177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3644248225453000324101569 2733186169089750243076177)
                ·
                  refine ⟨2049889626817312682307133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2733186169089750243076177 2049889626817312682307133)
                  ·
                    refine ⟨768708610056492255865175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2049889626817312682307133 768708610056492255865175)
                    ·
                      rfl

theorem cell22_2245582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_2245582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245582 prefixEnd_2245582 := by exact prefixLift 2245582
  have htrace : WordTrace (prefixWord ++ tailWord_2245582) baseStart_2245582 baseEnd_2245582 := by
    simpa [prefixWord, tailWord_2245582, baseEnd_2245582] using wordTrace_append hprefix tailTrace_2245582
  have hstable : (prefixWord ++ tailWord_2245582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245582).length < 2 ^ (prefixWord ++ tailWord_2245582).sum := by decide
  have hdescent : baseEnd_2245582 < baseStart_2245582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245599 : List Nat := [1, 1, 2, 3, 5, 1, 3, 1, 2, 3]
def baseStart_2245599 : Nat := 118140960795 + 2245599 * 2 ^ 59
def prefixEnd_2245599 : Nat := 4983230072969 + 3 ^ 40 * 2245599 * 2
def baseEnd_2245599 : Nat := 768714429503909878190123

theorem tailTrace_2245599 : CollatzResearch.WordTrace tailWord_2245599 prefixEnd_2245599 768714429503909878190123 := by
  unfold tailWord_2245599
  simp only [CollatzResearch.WordTrace]
  refine ⟨81903724191585815620899851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54602482794390543747266567 81903724191585815620899851)
  ·
    refine ⟨122855586287378723431349777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81903724191585815620899851 122855586287378723431349777)
    ·
      refine ⟨92141689715534042573512333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122855586287378723431349777 92141689715534042573512333)
      ·
        refine ⟨34553133643325265965067125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92141689715534042573512333 34553133643325265965067125)
        ·
          refine ⟨3239356279061743684225043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34553133643325265965067125 3239356279061743684225043)
          ·
            refine ⟨4859034418592615526337565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3239356279061743684225043 4859034418592615526337565)
            ·
              refine ⟨1822137906972230822376587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4859034418592615526337565 1822137906972230822376587)
              ·
                refine ⟨2733206860458346233564881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822137906972230822376587 2733206860458346233564881)
                ·
                  refine ⟨2049905145343759675173661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2733206860458346233564881 2049905145343759675173661)
                  ·
                    refine ⟨768714429503909878190123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2049905145343759675173661 768714429503909878190123)
                    ·
                      rfl

theorem cell22_2245599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 2, 3].length) (baseStart_2245599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245599 prefixEnd_2245599 := by exact prefixLift 2245599
  have htrace : WordTrace (prefixWord ++ tailWord_2245599) baseStart_2245599 baseEnd_2245599 := by
    simpa [prefixWord, tailWord_2245599, baseEnd_2245599] using wordTrace_append hprefix tailTrace_2245599
  have hstable : (prefixWord ++ tailWord_2245599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245599).length < 2 ^ (prefixWord ++ tailWord_2245599).sum := by decide
  have hdescent : baseEnd_2245599 < baseStart_2245599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245608 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 2, 6]
def baseStart_2245608 : Nat := 118140960795 + 2245608 * 2 ^ 59
def prefixEnd_2245608 : Nat := 4983230072969 + 3 ^ 40 * 2245608 * 2
def baseEnd_2245608 : Nat := 768717510387836854715095

theorem tailTrace_2245608 : CollatzResearch.WordTrace tailWord_2245608 prefixEnd_2245608 768717510387836854715095 := by
  unfold tailWord_2245608
  simp only [CollatzResearch.WordTrace]
  refine ⟨40952026224276605078988739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54602701632368806771984985 40952026224276605078988739)
  ·
    refine ⟨61428039336414907618483109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40952026224276605078988739 61428039336414907618483109)
    ·
      refine ⟨11517757375577795178465583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61428039336414907618483109 11517757375577795178465583)
      ·
        refine ⟨17276636063366692767698375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11517757375577795178465583 17276636063366692767698375)
        ·
          refine ⟨25914954095050039151547563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17276636063366692767698375 25914954095050039151547563)
          ·
            refine ⟨38872431142575058727321345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25914954095050039151547563 38872431142575058727321345)
            ·
              refine ⟨29154323356931294045491009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38872431142575058727321345 29154323356931294045491009)
              ·
                refine ⟨21865742517698470534118257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29154323356931294045491009 21865742517698470534118257)
                ·
                  refine ⟨16399306888273852900588693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21865742517698470534118257 16399306888273852900588693)
                  ·
                    refine ⟨768717510387836854715095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16399306888273852900588693 768717510387836854715095)
                    ·
                      rfl

theorem cell22_2245608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_2245608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245608 prefixEnd_2245608 := by exact prefixLift 2245608
  have htrace : WordTrace (prefixWord ++ tailWord_2245608) baseStart_2245608 baseEnd_2245608 := by
    simpa [prefixWord, tailWord_2245608, baseEnd_2245608] using wordTrace_append hprefix tailTrace_2245608
  have hstable : (prefixWord ++ tailWord_2245608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245608).length < 2 ^ (prefixWord ++ tailWord_2245608).sum := by decide
  have hdescent : baseEnd_2245608 < baseStart_2245608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245650 : List Nat := [3, 2, 5, 1, 1, 2, 2, 1, 2, 3]
def baseStart_2245650 : Nat := 118140960795 + 2245650 * 2 ^ 59
def prefixEnd_2245650 : Nat := 4983230072969 + 3 ^ 40 * 2245650 * 2
def baseEnd_2245650 : Nat := 768731887846162745164967

theorem tailTrace_2245650 : CollatzResearch.WordTrace tailWord_2245650 prefixEnd_2245650 768731887846162745164967 := by
  unfold tailWord_2245650
  simp only [CollatzResearch.WordTrace]
  refine ⟨20476396078600262832751601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54603722876267367554004269 20476396078600262832751601)
  ·
    refine ⟨15357297058950197124563701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20476396078600262832751601 15357297058950197124563701)
    ·
      refine ⟨1439746599276580980427847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15357297058950197124563701 1439746599276580980427847)
      ·
        refine ⟨2159619898914871470641771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1439746599276580980427847 2159619898914871470641771)
        ·
          refine ⟨3239429848372307205962657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2159619898914871470641771 3239429848372307205962657)
          ·
            refine ⟨2429572386279230404471993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3239429848372307205962657 2429572386279230404471993)
            ·
              refine ⟨1822179289709422803353995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2429572386279230404471993 1822179289709422803353995)
              ·
                refine ⟨2733268934564134205030993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822179289709422803353995 2733268934564134205030993)
                ·
                  refine ⟨2049951700923100653773245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2733268934564134205030993 2049951700923100653773245)
                  ·
                    refine ⟨768731887846162745164967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2049951700923100653773245 768731887846162745164967)
                    ·
                      rfl

theorem cell22_2245650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_2245650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245650 prefixEnd_2245650 := by exact prefixLift 2245650
  have htrace : WordTrace (prefixWord ++ tailWord_2245650) baseStart_2245650 baseEnd_2245650 := by
    simpa [prefixWord, tailWord_2245650, baseEnd_2245650] using wordTrace_append hprefix tailTrace_2245650
  have hstable : (prefixWord ++ tailWord_2245650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245650).length < 2 ^ (prefixWord ++ tailWord_2245650).sum := by decide
  have hdescent : baseEnd_2245650 < baseStart_2245650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245717 : List Nat := [1, 3, 2, 2, 1, 2, 1, 5, 2, 3]
def baseStart_2245717 : Nat := 118140960795 + 2245717 * 2 ^ 59
def prefixEnd_2245717 : Nat := 4983230072969 + 3 ^ 40 * 2245717 * 2
def baseEnd_2245717 : Nat := 768754823315396903739761

theorem tailTrace_2245717 : CollatzResearch.WordTrace tailWord_2245717 prefixEnd_2245717 768754823315396903739761 := by
  unfold tailWord_2245717
  simp only [CollatzResearch.WordTrace]
  refine ⟨81908028005158321773695405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54605352003438881182463603 81908028005158321773695405)
  ·
    refine ⟨30715510501934370665135777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81908028005158321773695405 30715510501934370665135777)
    ·
      refine ⟨23036632876450777998851833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30715510501934370665135777 23036632876450777998851833)
      ·
        refine ⟨17277474657338083499138875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23036632876450777998851833 17277474657338083499138875)
        ·
          refine ⟨25916211986007125248708313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17277474657338083499138875 25916211986007125248708313)
          ·
            refine ⟨19437158989505343936531235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25916211986007125248708313 19437158989505343936531235)
            ·
              refine ⟨29155738484258015904796853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19437158989505343936531235 29155738484258015904796853)
              ·
                refine ⟨2733350482899188991074705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29155738484258015904796853 2733350482899188991074705)
                ·
                  refine ⟨2050012862174391743306029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2733350482899188991074705 2050012862174391743306029)
                  ·
                    refine ⟨768754823315396903739761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2050012862174391743306029 768754823315396903739761)
                    ·
                      rfl

theorem cell22_2245717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_2245717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245717 prefixEnd_2245717 := by exact prefixLift 2245717
  have htrace : WordTrace (prefixWord ++ tailWord_2245717) baseStart_2245717 baseEnd_2245717 := by
    simpa [prefixWord, tailWord_2245717, baseEnd_2245717] using wordTrace_append hprefix tailTrace_2245717
  have hstable : (prefixWord ++ tailWord_2245717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245717).length < 2 ^ (prefixWord ++ tailWord_2245717).sum := by decide
  have hdescent : baseEnd_2245717 < baseStart_2245717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245736 : List Nat := [2, 1, 4, 4, 1, 1, 2, 3, 4]
def baseStart_2245736 : Nat := 118140960795 + 2245736 * 2 ^ 59
def prefixEnd_2245736 : Nat := 4983230072969 + 3 ^ 40 * 2245736 * 2
def baseEnd_2245736 : Nat := 256253775801229062504901

theorem tailTrace_2245736 : CollatzResearch.WordTrace tailWord_2245736 prefixEnd_2245736 256253775801229062504901 := by
  unfold tailWord_2245736
  simp only [CollatzResearch.WordTrace]
  refine ⟨40954360496044744009318531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54605813994726325345758041 40954360496044744009318531)
  ·
    refine ⟨61431540744067116013977797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40954360496044744009318531 61431540744067116013977797)
    ·
      refine ⟨11518413889512584252620837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61431540744067116013977797 11518413889512584252620837)
      ·
        refine ⟨2159702604283609547366407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11518413889512584252620837 2159702604283609547366407)
        ·
          refine ⟨3239553906425414321049611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2159702604283609547366407 3239553906425414321049611)
          ·
            refine ⟨4859330859638121481574417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3239553906425414321049611 4859330859638121481574417)
            ·
              refine ⟨3644498144728591111180813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4859330859638121481574417 3644498144728591111180813)
              ·
                refine ⟨1366686804273221666692805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3644498144728591111180813 1366686804273221666692805)
                ·
                  refine ⟨256253775801229062504901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1366686804273221666692805 256253775801229062504901)
                  ·
                    rfl

theorem cell22_2245736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 4].length) (baseStart_2245736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245736 prefixEnd_2245736 := by exact prefixLift 2245736
  have htrace : WordTrace (prefixWord ++ tailWord_2245736) baseStart_2245736 baseEnd_2245736 := by
    simpa [prefixWord, tailWord_2245736, baseEnd_2245736] using wordTrace_append hprefix tailTrace_2245736
  have hstable : (prefixWord ++ tailWord_2245736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245736).length < 2 ^ (prefixWord ++ tailWord_2245736).sum := by decide
  have hdescent : baseEnd_2245736 < baseStart_2245736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245796 : List Nat := [2, 3, 1, 2, 3, 1, 3, 3, 1, 3]
def baseStart_2245796 : Nat := 118140960795 + 2245796 * 2 ^ 59
def prefixEnd_2245796 : Nat := 4983230072969 + 3 ^ 40 * 2245796 * 2
def baseEnd_2245796 : Nat := 768781866629867031014519

theorem tailTrace_2245796 : CollatzResearch.WordTrace tailWord_2245796 prefixEnd_2245796 768781866629867031014519 := by
  unfold tailWord_2245796
  simp only [CollatzResearch.WordTrace]
  refine ⟨40955454685936059132910621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54607272914581412177214161 40955454685936059132910621)
  ·
    refine ⟨15358295507226022174841483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40955454685936059132910621 15358295507226022174841483)
    ·
      refine ⟨23037443260839033262262225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15358295507226022174841483 23037443260839033262262225)
      ·
        refine ⟨17278082445629274946696669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23037443260839033262262225 17278082445629274946696669)
        ·
          refine ⟨6479280917110978105011251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17278082445629274946696669 6479280917110978105011251)
          ·
            refine ⟨9718921375666467157516877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6479280917110978105011251 9718921375666467157516877)
            ·
              refine ⟨3644595515874925184068829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9718921375666467157516877 3644595515874925184068829)
              ·
                refine ⟨1366723318453096944025811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3644595515874925184068829 1366723318453096944025811)
                ·
                  refine ⟨2050084977679645416038717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366723318453096944025811 2050084977679645416038717)
                  ·
                    refine ⟨768781866629867031014519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2050084977679645416038717 768781866629867031014519)
                    ·
                      rfl

theorem cell22_2245796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_2245796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245796 prefixEnd_2245796 := by exact prefixLift 2245796
  have htrace : WordTrace (prefixWord ++ tailWord_2245796) baseStart_2245796 baseEnd_2245796 := by
    simpa [prefixWord, tailWord_2245796, baseEnd_2245796] using wordTrace_append hprefix tailTrace_2245796
  have hstable : (prefixWord ++ tailWord_2245796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245796).length < 2 ^ (prefixWord ++ tailWord_2245796).sum := by decide
  have hdescent : baseEnd_2245796 < baseStart_2245796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245867 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 2, 4]
def baseStart_2245867 : Nat := 118140960795 + 2245867 * 2 ^ 59
def prefixEnd_2245867 : Nat := 4983230072969 + 3 ^ 40 * 2245867 * 2
def baseEnd_2245867 : Nat := 768806171380846512489301

theorem tailTrace_2245867 : CollatzResearch.WordTrace tailWord_2245867 prefixEnd_2245867 768806171380846512489301 := by
  unfold tailWord_2245867
  simp only [CollatzResearch.WordTrace]
  refine ⟨81913498954614897391655855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54608999303076598261103903 81913498954614897391655855)
  ·
    refine ⟨122870248431922346087483783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81913498954614897391655855 122870248431922346087483783)
    ·
      refine ⟨184305372647883519131225675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122870248431922346087483783 184305372647883519131225675)
      ·
        refine ⟨276458058971825278696838513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184305372647883519131225675 276458058971825278696838513)
        ·
          refine ⟨207343544228868959022628885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276458058971825278696838513 207343544228868959022628885)
          ·
            refine ⟨9719228635728232454185729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 207343544228868959022628885 9719228635728232454185729)
            ·
              refine ⟨7289421476796174340639297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9719228635728232454185729 7289421476796174340639297)
              ·
                refine ⟨5467066107597130755479473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7289421476796174340639297 5467066107597130755479473)
                ·
                  refine ⟨4100299580697848066609605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5467066107597130755479473 4100299580697848066609605)
                  ·
                    refine ⟨768806171380846512489301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4100299580697848066609605 768806171380846512489301)
                    ·
                      rfl

theorem cell22_2245867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 4].length) (baseStart_2245867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245867 prefixEnd_2245867 := by exact prefixLift 2245867
  have htrace : WordTrace (prefixWord ++ tailWord_2245867) baseStart_2245867 baseEnd_2245867 := by
    simpa [prefixWord, tailWord_2245867, baseEnd_2245867] using wordTrace_append hprefix tailTrace_2245867
  have hstable : (prefixWord ++ tailWord_2245867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245867).length < 2 ^ (prefixWord ++ tailWord_2245867).sum := by decide
  have hdescent : baseEnd_2245867 < baseStart_2245867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245880 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 4, 7]
def baseStart_2245880 : Nat := 118140960795 + 2245880 * 2 ^ 59
def prefixEnd_2245880 : Nat := 4983230072969 + 3 ^ 40 * 2245880 * 2
def baseEnd_2245880 : Nat := 768810621546518811914261

theorem tailTrace_2245880 : CollatzResearch.WordTrace tailWord_2245880 prefixEnd_2245880 768810621546518811914261 := by
  unfold tailWord_2245880
  simp only [CollatzResearch.WordTrace]
  refine ⟨40956986551783900305939547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54609315402378533741252729 40956986551783900305939547)
  ·
    refine ⟨61435479827675850458909321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40956986551783900305939547 61435479827675850458909321)
    ·
      refine ⟨46076609870756887844181991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61435479827675850458909321 46076609870756887844181991)
      ·
        refine ⟨69114914806135331766272987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46076609870756887844181991 69114914806135331766272987)
        ·
          refine ⟨103672372209202997649409481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69114914806135331766272987 103672372209202997649409481)
          ·
            refine ⟨77754279156902248237057111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103672372209202997649409481 77754279156902248237057111)
            ·
              refine ⟨116631418735353372355585667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77754279156902248237057111 116631418735353372355585667)
              ·
                refine ⟨174947128103030058533378501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116631418735353372355585667 174947128103030058533378501)
                ·
                  refine ⟨32802586519318135975008469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 174947128103030058533378501 32802586519318135975008469)
                  ·
                    refine ⟨768810621546518811914261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32802586519318135975008469 768810621546518811914261)
                    ·
                      rfl

theorem cell22_2245880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_2245880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245880 prefixEnd_2245880 := by exact prefixLift 2245880
  have htrace : WordTrace (prefixWord ++ tailWord_2245880) baseStart_2245880 baseEnd_2245880 := by
    simpa [prefixWord, tailWord_2245880, baseEnd_2245880] using wordTrace_append hprefix tailTrace_2245880
  have hstable : (prefixWord ++ tailWord_2245880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245880).length < 2 ^ (prefixWord ++ tailWord_2245880).sum := by decide
  have hdescent : baseEnd_2245880 < baseStart_2245880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245886 : List Nat := [4, 2, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_2245886 : Nat := 118140960795 + 2245886 * 2 ^ 59
def prefixEnd_2245886 : Nat := 4983230072969 + 3 ^ 40 * 2245886 * 2
def baseEnd_2245886 : Nat := 768812675469136796264243

theorem tailTrace_2245886 : CollatzResearch.WordTrace tailWord_2245886 prefixEnd_2245886 768812675469136796264243 := by
  unfold tailWord_2245886
  simp only [CollatzResearch.WordTrace]
  refine ⟨10239273992693257954574689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54609461294364042424398341 10239273992693257954574689)
  ·
    refine ⟨7679455494519943465931017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10239273992693257954574689 7679455494519943465931017)
    ·
      refine ⟨5759591620889957599448263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7679455494519943465931017 5759591620889957599448263)
      ·
        refine ⟨8639387431334936399172395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5759591620889957599448263 8639387431334936399172395)
        ·
          refine ⟨12959081147002404598758593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8639387431334936399172395 12959081147002404598758593)
          ·
            refine ⟨9719310860251803449068945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12959081147002404598758593 9719310860251803449068945)
            ·
              refine ⟨7289483145188852586801709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9719310860251803449068945 7289483145188852586801709)
              ·
                refine ⟨2733556179445819720050641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7289483145188852586801709 2733556179445819720050641)
                ·
                  refine ⟨2050167134584364790037981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2733556179445819720050641 2050167134584364790037981)
                  ·
                    refine ⟨768812675469136796264243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2050167134584364790037981 768812675469136796264243)
                    ·
                      rfl

theorem cell22_2245886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_2245886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245886 prefixEnd_2245886 := by exact prefixLift 2245886
  have htrace : WordTrace (prefixWord ++ tailWord_2245886) baseStart_2245886 baseEnd_2245886 := by
    simpa [prefixWord, tailWord_2245886, baseEnd_2245886] using wordTrace_append hprefix tailTrace_2245886
  have hstable : (prefixWord ++ tailWord_2245886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245886).length < 2 ^ (prefixWord ++ tailWord_2245886).sum := by decide
  have hdescent : baseEnd_2245886 < baseStart_2245886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245957 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 3, 4]
def baseStart_2245957 : Nat := 118140960795 + 2245957 * 2 ^ 59
def prefixEnd_2245957 : Nat := 4983230072969 + 3 ^ 40 * 2245957 * 2
def baseEnd_2245957 : Nat := 768836980220116277739025

theorem tailTrace_2245957 : CollatzResearch.WordTrace tailWord_2245957 prefixEnd_2245957 768836980220116277739025 := by
  unfold tailWord_2245957
  simp only [CollatzResearch.WordTrace]
  refine ⟨81916781524288842762432125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54611187682859228508288083 81916781524288842762432125)
  ·
    refine ⟨30718793071608316035912047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81916781524288842762432125 30718793071608316035912047)
    ·
      refine ⟨46078189607412474053868071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30718793071608316035912047 46078189607412474053868071)
      ·
        refine ⟨69117284411118711080802107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46078189607412474053868071 69117284411118711080802107)
        ·
          refine ⟨103675926616678066621203161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69117284411118711080802107 103675926616678066621203161)
          ·
            refine ⟨77756944962508549965902371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103675926616678066621203161 77756944962508549965902371)
            ·
              refine ⟨116635417443762824948853557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77756944962508549965902371 116635417443762824948853557)
              ·
                refine ⟨10934570385352764838955021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116635417443762824948853557 10934570385352764838955021)
                ·
                  refine ⟨4100463894507286814608133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10934570385352764838955021 4100463894507286814608133)
                  ·
                    refine ⟨768836980220116277739025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4100463894507286814608133 768836980220116277739025)
                    ·
                      rfl

theorem cell22_2245957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_2245957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2245957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2245957 prefixEnd_2245957 := by exact prefixLift 2245957
  have htrace : WordTrace (prefixWord ++ tailWord_2245957) baseStart_2245957 baseEnd_2245957 := by
    simpa [prefixWord, tailWord_2245957, baseEnd_2245957] using wordTrace_append hprefix tailTrace_2245957
  have hstable : (prefixWord ++ tailWord_2245957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245957).length < 2 ^ (prefixWord ++ tailWord_2245957).sum := by decide
  have hdescent : baseEnd_2245957 < baseStart_2245957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246019 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 2, 4]
def baseStart_2246019 : Nat := 118140960795 + 2246019 * 2 ^ 59
def prefixEnd_2246019 : Nat := 4983230072969 + 3 ^ 40 * 2246019 * 2
def baseEnd_2246019 : Nat := 768858204087168782688835

theorem tailTrace_2246019 : CollatzResearch.WordTrace tailWord_2246019 prefixEnd_2246019 768858204087168782688835 := by
  unfold tailWord_2246019
  simp only [CollatzResearch.WordTrace]
  refine ⟨81919042850064227351189111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54612695233376151567459407 81919042850064227351189111)
  ·
    refine ⟨122878564275096341026783667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81919042850064227351189111 122878564275096341026783667)
    ·
      refine ⟨184317846412644511540175501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122878564275096341026783667 184317846412644511540175501)
      ·
        refine ⟨69119192404741691827565813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184317846412644511540175501 69119192404741691827565813)
        ·
          refine ⟨6479924287944533608834295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69119192404741691827565813 6479924287944533608834295)
          ·
            refine ⟨9719886431916800413251443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6479924287944533608834295 9719886431916800413251443)
            ·
              refine ⟨14579829647875200619877165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9719886431916800413251443 14579829647875200619877165)
              ·
                refine ⟨5467436117953200232453937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14579829647875200619877165 5467436117953200232453937)
                ·
                  refine ⟨4100577088464900174340453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5467436117953200232453937 4100577088464900174340453)
                  ·
                    refine ⟨768858204087168782688835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4100577088464900174340453 768858204087168782688835)
                    ·
                      rfl

theorem cell22_2246019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 4].length) (baseStart_2246019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246019 prefixEnd_2246019 := by exact prefixLift 2246019
  have htrace : WordTrace (prefixWord ++ tailWord_2246019) baseStart_2246019 baseEnd_2246019 := by
    simpa [prefixWord, tailWord_2246019, baseEnd_2246019] using wordTrace_append hprefix tailTrace_2246019
  have hstable : (prefixWord ++ tailWord_2246019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246019).length < 2 ^ (prefixWord ++ tailWord_2246019).sum := by decide
  have hdescent : baseEnd_2246019 < baseStart_2246019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246034 : List Nat := [3, 2, 3, 3, 11]
def baseStart_2246034 : Nat := 118140960795 + 2246034 * 2 ^ 59
def prefixEnd_2246034 : Nat := 4983230072969 + 3 ^ 40 * 2246034 * 2
def baseEnd_2246034 : Nat := 3164046662114048327423

theorem tailTrace_2246034 : CollatzResearch.WordTrace tailWord_2246034 prefixEnd_2246034 3164046662114048327423 := by
  unfold tailWord_2246034
  simp only [CollatzResearch.WordTrace]
  refine ⟨20479897486252471228246289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54613059963339923275323437 20479897486252471228246289)
  ·
    refine ⟨15359923114689353421184717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20479897486252471228246289 15359923114689353421184717)
    ·
      refine ⟨5759971168008507532944269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15359923114689353421184717 5759971168008507532944269)
      ·
        refine ⟨2159989188003190324854101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5759971168008507532944269 2159989188003190324854101)
        ·
          refine ⟨3164046662114048327423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2159989188003190324854101 3164046662114048327423)
          ·
            rfl

theorem cell22_2246034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 11].length) (baseStart_2246034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246034 prefixEnd_2246034 := by exact prefixLift 2246034
  have htrace : WordTrace (prefixWord ++ tailWord_2246034) baseStart_2246034 baseEnd_2246034 := by
    simpa [prefixWord, tailWord_2246034, baseEnd_2246034] using wordTrace_append hprefix tailTrace_2246034
  have hstable : (prefixWord ++ tailWord_2246034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246034).length < 2 ^ (prefixWord ++ tailWord_2246034).sum := by decide
  have hdescent : baseEnd_2246034 < baseStart_2246034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246036 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2246036 : Nat := 118140960795 + 2246036 * 2 ^ 59
def prefixEnd_2246036 : Nat := 4983230072969 + 3 ^ 40 * 2246036 * 2
def baseEnd_2246036 : Nat := 768864023534586405013783

theorem tailTrace_2246036 : CollatzResearch.WordTrace tailWord_2246036 prefixEnd_2246036 768864023534586405013783 := by
  unfold tailWord_2246036
  simp only [CollatzResearch.WordTrace]
  refine ⟨40959831445501319627278981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54613108594001759503038641 40959831445501319627278981)
  ·
    refine ⟨7679968396031497430114809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40959831445501319627278981 7679968396031497430114809)
    ·
      refine ⟨5759976297023623072586107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7679968396031497430114809 5759976297023623072586107)
      ·
        refine ⟨8639964445535434608879161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5759976297023623072586107 8639964445535434608879161)
        ·
          refine ⟨6479973334151575956659371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8639964445535434608879161 6479973334151575956659371)
          ·
            refine ⟨9719960001227363934989057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6479973334151575956659371 9719960001227363934989057)
            ·
              refine ⟨7289970000920522951241793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9719960001227363934989057 7289970000920522951241793)
              ·
                refine ⟨5467477500690392213431345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7289970000920522951241793 5467477500690392213431345)
                ·
                  refine ⟨4100608125517794160073509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5467477500690392213431345 4100608125517794160073509)
                  ·
                    refine ⟨768864023534586405013783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4100608125517794160073509 768864023534586405013783)
                    ·
                      rfl

theorem cell22_2246036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2246036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246036 prefixEnd_2246036 := by exact prefixLift 2246036
  have htrace : WordTrace (prefixWord ++ tailWord_2246036) baseStart_2246036 baseEnd_2246036 := by
    simpa [prefixWord, tailWord_2246036, baseEnd_2246036] using wordTrace_append hprefix tailTrace_2246036
  have hstable : (prefixWord ++ tailWord_2246036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246036).length < 2 ^ (prefixWord ++ tailWord_2246036).sum := by decide
  have hdescent : baseEnd_2246036 < baseStart_2246036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246040 : List Nat := [2, 1, 2, 5, 2, 2, 2, 2, 4]
def baseStart_2246040 : Nat := 118140960795 + 2246040 * 2 ^ 59
def prefixEnd_2246040 : Nat := 4983230072969 + 3 ^ 40 * 2246040 * 2
def baseEnd_2246040 : Nat := 256288464272110575971257

theorem tailTrace_2246040 : CollatzResearch.WordTrace tailWord_2246040 prefixEnd_2246040 256288464272110575971257 := by
  unfold tailWord_2246040
  simp only [CollatzResearch.WordTrace]
  refine ⟨40959904391494073968851787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54613205855325431958469049 40959904391494073968851787)
  ·
    refine ⟨61439856587241110953277681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40959904391494073968851787 61439856587241110953277681)
    ·
      refine ⟨46079892440430833214958261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61439856587241110953277681 46079892440430833214958261)
      ·
        refine ⟨4319989916290390613902337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46079892440430833214958261 4319989916290390613902337)
        ·
          refine ⟨3239992437217792960426753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4319989916290390613902337 3239992437217792960426753)
          ·
            refine ⟨2429994327913344720320065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3239992437217792960426753 2429994327913344720320065)
            ·
              refine ⟨1822495745935008540240049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2429994327913344720320065 1822495745935008540240049)
              ·
                refine ⟨1366871809451256405180037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1822495745935008540240049 1366871809451256405180037)
                ·
                  refine ⟨256288464272110575971257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1366871809451256405180037 256288464272110575971257)
                  ·
                    rfl

theorem cell22_2246040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 4].length) (baseStart_2246040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246040 prefixEnd_2246040 := by exact prefixLift 2246040
  have htrace : WordTrace (prefixWord ++ tailWord_2246040) baseStart_2246040 baseEnd_2246040 := by
    simpa [prefixWord, tailWord_2246040, baseEnd_2246040] using wordTrace_append hprefix tailTrace_2246040
  have hstable : (prefixWord ++ tailWord_2246040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246040).length < 2 ^ (prefixWord ++ tailWord_2246040).sum := by decide
  have hdescent : baseEnd_2246040 < baseStart_2246040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246094 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_2246094 : Nat := 118140960795 + 2246094 * 2 ^ 59
def prefixEnd_2246094 : Nat := 4983230072969 + 3 ^ 40 * 2246094 * 2
def baseEnd_2246094 : Nat := 768883878119893587063605

theorem tailTrace_2246094 : CollatzResearch.WordTrace tailWord_2246094 prefixEnd_2246094 768883878119893587063605 := by
  unfold tailWord_2246094
  simp only [CollatzResearch.WordTrace]
  refine ⟨10240222290599064395021167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54614518883195010106779557 10240222290599064395021167)
  ·
    refine ⟨15360333435898596592531751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10240222290599064395021167 15360333435898596592531751)
    ·
      refine ⟨23040500153847894888797627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15360333435898596592531751 23040500153847894888797627)
      ·
        refine ⟨34560750230771842333196441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23040500153847894888797627 34560750230771842333196441)
        ·
          refine ⟨25920562673078881749897331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34560750230771842333196441 25920562673078881749897331)
          ·
            refine ⟨38880844009618322624845997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25920562673078881749897331 38880844009618322624845997)
            ·
              refine ⟨14580316503606870984317249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38880844009618322624845997 14580316503606870984317249)
              ·
                refine ⟨10935237377705153238237937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14580316503606870984317249 10935237377705153238237937)
                ·
                  refine ⟨8201428033278864928678453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10935237377705153238237937 8201428033278864928678453)
                  ·
                    refine ⟨768883878119893587063605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8201428033278864928678453 768883878119893587063605)
                    ·
                      rfl

theorem cell22_2246094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_2246094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246094 prefixEnd_2246094 := by exact prefixLift 2246094
  have htrace : WordTrace (prefixWord ++ tailWord_2246094) baseStart_2246094 baseEnd_2246094 := by
    simpa [prefixWord, tailWord_2246094, baseEnd_2246094] using wordTrace_append hprefix tailTrace_2246094
  have hstable : (prefixWord ++ tailWord_2246094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246094).length < 2 ^ (prefixWord ++ tailWord_2246094).sum := by decide
  have hdescent : baseEnd_2246094 < baseStart_2246094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246158 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 6]
def baseStart_2246158 : Nat := 118140960795 + 2246158 * 2 ^ 59
def prefixEnd_2246158 : Nat := 4983230072969 + 3 ^ 40 * 2246158 * 2
def baseEnd_2246158 : Nat := 256301928875939584487803

theorem tailTrace_2246158 : CollatzResearch.WordTrace tailWord_2246158 prefixEnd_2246158 256301928875939584487803 := by
  unfold tailWord_2246158
  simp only [CollatzResearch.WordTrace]
  refine ⟨10240514074570081761312391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54616075064373769393666085 10240514074570081761312391)
  ·
    refine ⟨15360771111855122641968587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10240514074570081761312391 15360771111855122641968587)
    ·
      refine ⟨23041156667782683962952881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15360771111855122641968587 23041156667782683962952881)
      ·
        refine ⟨17280867500837012972214661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23041156667782683962952881 17280867500837012972214661)
        ·
          refine ⟨3240162656406939932290249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17280867500837012972214661 3240162656406939932290249)
          ·
            refine ⟨2430121992305204949217687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3240162656406939932290249 2430121992305204949217687)
            ·
              refine ⟨3645182988457807423826531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2430121992305204949217687 3645182988457807423826531)
              ·
                refine ⟨5467774482686711135739797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3645182988457807423826531 5467774482686711135739797)
                ·
                  refine ⟨256301928875939584487803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5467774482686711135739797 256301928875939584487803)
                  ·
                    rfl

theorem cell22_2246158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_2246158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246158 prefixEnd_2246158 := by exact prefixLift 2246158
  have htrace : WordTrace (prefixWord ++ tailWord_2246158) baseStart_2246158 baseEnd_2246158 := by
    simpa [prefixWord, tailWord_2246158, baseEnd_2246158] using wordTrace_append hprefix tailTrace_2246158
  have hstable : (prefixWord ++ tailWord_2246158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246158).length < 2 ^ (prefixWord ++ tailWord_2246158).sum := by decide
  have hdescent : baseEnd_2246158 < baseStart_2246158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246173 : List Nat := [1, 4, 2, 2, 1, 1, 3, 3, 2, 3]
def baseStart_2246173 : Nat := 118140960795 + 2246173 * 2 ^ 59
def prefixEnd_2246173 : Nat := 4983230072969 + 3 ^ 40 * 2246173 * 2
def baseEnd_2246173 : Nat := 768910921434363714338363

theorem tailTrace_2246173 : CollatzResearch.WordTrace tailWord_2246173 prefixEnd_2246173 768910921434363714338363 := by
  unfold tailWord_2246173
  simp only [CollatzResearch.WordTrace]
  refine ⟨81924659691506311652295173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54616439794337541101530115 81924659691506311652295173)
  ·
    refine ⟨15360873692157433434805345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81924659691506311652295173 15360873692157433434805345)
    ·
      refine ⟨11520655269118075076104009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15360873692157433434805345 11520655269118075076104009)
      ·
        refine ⟨8640491451838556307078007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11520655269118075076104009 8640491451838556307078007)
        ·
          refine ⟨12960737177757834460617011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8640491451838556307078007 12960737177757834460617011)
          ·
            refine ⟨19441105766636751690925517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12960737177757834460617011 19441105766636751690925517)
            ·
              refine ⟨7290414662488781884097069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19441105766636751690925517 7290414662488781884097069)
              ·
                refine ⟨2733905498433293206536401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7290414662488781884097069 2733905498433293206536401)
                ·
                  refine ⟨2050429123824969904902301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2733905498433293206536401 2050429123824969904902301)
                  ·
                    refine ⟨768910921434363714338363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2050429123824969904902301 768910921434363714338363)
                    ·
                      rfl

theorem cell22_2246173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_2246173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246173 prefixEnd_2246173 := by exact prefixLift 2246173
  have htrace : WordTrace (prefixWord ++ tailWord_2246173) baseStart_2246173 baseEnd_2246173 := by
    simpa [prefixWord, tailWord_2246173, baseEnd_2246173] using wordTrace_append hprefix tailTrace_2246173
  have hstable : (prefixWord ++ tailWord_2246173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246173).length < 2 ^ (prefixWord ++ tailWord_2246173).sum := by decide
  have hdescent : baseEnd_2246173 < baseStart_2246173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246231 : List Nat := [1, 1, 3, 2, 2, 3, 2, 3, 5]
def baseStart_2246231 : Nat := 118140960795 + 2246231 * 2 ^ 59
def prefixEnd_2246231 : Nat := 4983230072969 + 3 ^ 40 * 2246231 * 2
def baseEnd_2246231 : Nat := 256310258673223632129395

theorem tailTrace_2246231 : CollatzResearch.WordTrace tailWord_2246231 prefixEnd_2246231 256310258673223632129395 := by
  unfold tailWord_2246231
  simp only [CollatzResearch.WordTrace]
  refine ⟨81926775125296187557906547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54617850083530791705271031 81926775125296187557906547)
  ·
    refine ⟨122890162687944281336859821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81926775125296187557906547 122890162687944281336859821)
    ·
      refine ⟨46083811007979105501322433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122890162687944281336859821 46083811007979105501322433)
      ·
        refine ⟨34562858255984329125991825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46083811007979105501322433 34562858255984329125991825)
        ·
          refine ⟨25922143691988246844493869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34562858255984329125991825 25922143691988246844493869)
          ·
            refine ⟨9720803884495592566685201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25922143691988246844493869 9720803884495592566685201)
            ·
              refine ⟨7290602913371694425013901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9720803884495592566685201 7290602913371694425013901)
              ·
                refine ⟨2733976092514385409380213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7290602913371694425013901 2733976092514385409380213)
                ·
                  refine ⟨256310258673223632129395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2733976092514385409380213 256310258673223632129395)
                  ·
                    rfl

theorem cell22_2246231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 5].length) (baseStart_2246231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246231 prefixEnd_2246231 := by exact prefixLift 2246231
  have htrace : WordTrace (prefixWord ++ tailWord_2246231) baseStart_2246231 baseEnd_2246231 := by
    simpa [prefixWord, tailWord_2246231, baseEnd_2246231] using wordTrace_append hprefix tailTrace_2246231
  have hstable : (prefixWord ++ tailWord_2246231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246231).length < 2 ^ (prefixWord ++ tailWord_2246231).sum := by decide
  have hdescent : baseEnd_2246231 < baseStart_2246231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246291 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 8, 3]
def baseStart_2246291 : Nat := 118140960795 + 2246291 * 2 ^ 59
def prefixEnd_2246291 : Nat := 4983230072969 + 3 ^ 40 * 2246291 * 2
def baseEnd_2246291 : Nat := 768951315245850739888001

theorem tailTrace_2246291 : CollatzResearch.WordTrace tailWord_2246291 prefixEnd_2246291 768951315245850739888001 := by
  unfold tailWord_2246291
  simp only [CollatzResearch.WordTrace]
  refine ⟨81928963505078817805090727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54619309003385878536727151 81928963505078817805090727)
  ·
    refine ⟨122893445257618226707636091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81928963505078817805090727 122893445257618226707636091)
    ·
      refine ⟨184340167886427340061454137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122893445257618226707636091 184340167886427340061454137)
      ·
        refine ⟨138255125914820505046090603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184340167886427340061454137 138255125914820505046090603)
        ·
          refine ⟨207382688872230757569135905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138255125914820505046090603 207382688872230757569135905)
          ·
            refine ⟨155537016654173068176851929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207382688872230757569135905 155537016654173068176851929)
            ·
              refine ⟨116652762490629801132638947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155537016654173068176851929 116652762490629801132638947)
              ·
                refine ⟨174979143735944701698958421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116652762490629801132638947 174979143735944701698958421)
                ·
                  refine ⟨2050536840655601973034669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 174979143735944701698958421 2050536840655601973034669)
                  ·
                    refine ⟨768951315245850739888001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2050536840655601973034669 768951315245850739888001)
                    ·
                      rfl

theorem cell22_2246291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 3].length) (baseStart_2246291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246291 prefixEnd_2246291 := by exact prefixLift 2246291
  have htrace : WordTrace (prefixWord ++ tailWord_2246291) baseStart_2246291 baseEnd_2246291 := by
    simpa [prefixWord, tailWord_2246291, baseEnd_2246291] using wordTrace_append hprefix tailTrace_2246291
  have hstable : (prefixWord ++ tailWord_2246291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246291).length < 2 ^ (prefixWord ++ tailWord_2246291).sum := by decide
  have hdescent : baseEnd_2246291 < baseStart_2246291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246308 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 4, 3]
def baseStart_2246308 : Nat := 118140960795 + 2246308 * 2 ^ 59
def prefixEnd_2246308 : Nat := 4983230072969 + 3 ^ 40 * 2246308 * 2
def baseEnd_2246308 : Nat := 768957134693268362212949

theorem tailTrace_2246308 : CollatzResearch.WordTrace tailWord_2246308 prefixEnd_2246308 768957134693268362212949 := by
  unfold tailWord_2246308
  simp only [CollatzResearch.WordTrace]
  refine ⟨40964791773008614854229789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54619722364011486472306385 40964791773008614854229789)
  ·
    refine ⟨15361796914878230570336171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40964791773008614854229789 15361796914878230570336171)
    ·
      refine ⟨23042695372317345855504257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15361796914878230570336171 23042695372317345855504257)
      ·
        refine ⟨17282021529238009391628193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23042695372317345855504257 17282021529238009391628193)
        ·
          refine ⟨12961516146928507043721145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17282021529238009391628193 12961516146928507043721145)
          ·
            refine ⟨9721137110196380282790859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12961516146928507043721145 9721137110196380282790859)
            ·
              refine ⟨14581705665294570424186289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9721137110196380282790859 14581705665294570424186289)
              ·
                refine ⟨10936279248970927818139717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14581705665294570424186289 10936279248970927818139717)
                ·
                  refine ⟨2050552359182048965901197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10936279248970927818139717 2050552359182048965901197)
                  ·
                    refine ⟨768957134693268362212949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2050552359182048965901197 768957134693268362212949)
                    ·
                      rfl

theorem cell22_2246308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_2246308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246308 prefixEnd_2246308 := by exact prefixLift 2246308
  have htrace : WordTrace (prefixWord ++ tailWord_2246308) baseStart_2246308 baseEnd_2246308 := by
    simpa [prefixWord, tailWord_2246308, baseEnd_2246308] using wordTrace_append hprefix tailTrace_2246308
  have hstable : (prefixWord ++ tailWord_2246308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246308).length < 2 ^ (prefixWord ++ tailWord_2246308).sum := by decide
  have hdescent : baseEnd_2246308 < baseStart_2246308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246383 : List Nat := [1, 1, 2, 1, 5, 1, 4, 2, 5]
def baseStart_2246383 : Nat := 118140960795 + 2246383 * 2 ^ 59
def prefixEnd_2246383 : Nat := 4983230072969 + 3 ^ 40 * 2246383 * 2
def baseEnd_2246383 : Nat := 256327602908664388862573

theorem tailTrace_2246383 : CollatzResearch.WordTrace tailWord_2246383 prefixEnd_2246383 256327602908664388862573 := by
  unfold tailWord_2246383
  simp only [CollatzResearch.WordTrace]
  refine ⟨81932319020745517517439803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54621546013830345011626535 81932319020745517517439803)
  ·
    refine ⟨122898478531118276276159705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81932319020745517517439803 122898478531118276276159705)
    ·
      refine ⟨92173858898338707207119779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122898478531118276276159705 92173858898338707207119779)
      ·
        refine ⟨138260788347508060810679669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92173858898338707207119779 138260788347508060810679669)
        ·
          refine ⟨12961948907578880701001219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138260788347508060810679669 12961948907578880701001219)
          ·
            refine ⟨19442923361368321051501829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12961948907578880701001219 19442923361368321051501829)
            ·
              refine ⟨3645548130256560197156593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19442923361368321051501829 3645548130256560197156593)
              ·
                refine ⟨2734161097692420147867445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3645548130256560197156593 2734161097692420147867445)
                ·
                  refine ⟨256327602908664388862573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2734161097692420147867445 256327602908664388862573)
                  ·
                    rfl

theorem cell22_2246383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 5].length) (baseStart_2246383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246383 prefixEnd_2246383 := by exact prefixLift 2246383
  have htrace : WordTrace (prefixWord ++ tailWord_2246383) baseStart_2246383 baseEnd_2246383 := by
    simpa [prefixWord, tailWord_2246383, baseEnd_2246383] using wordTrace_append hprefix tailTrace_2246383
  have hstable : (prefixWord ++ tailWord_2246383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246383).length < 2 ^ (prefixWord ++ tailWord_2246383).sum := by decide
  have hdescent : baseEnd_2246383 < baseStart_2246383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246387 : List Nat := [1, 1, 1, 2, 2, 3, 6, 2, 1, 3]
def baseStart_2246387 : Nat := 118140960795 + 2246387 * 2 ^ 59
def prefixEnd_2246387 : Nat := 4983230072969 + 3 ^ 40 * 2246387 * 2
def baseEnd_2246387 : Nat := 768984178007738489487707

theorem tailTrace_2246387 : CollatzResearch.WordTrace tailWord_2246387 prefixEnd_2246387 768984178007738489487707 := by
  unfold tailWord_2246387
  simp only [CollatzResearch.WordTrace]
  refine ⟨81932464912731026200585415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54621643275154017467056943 81932464912731026200585415)
  ·
    refine ⟨122898697369096539300878123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81932464912731026200585415 122898697369096539300878123)
    ·
      refine ⟨184348046053644808951317185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122898697369096539300878123 184348046053644808951317185)
      ·
        refine ⟨138261034540233606713487889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184348046053644808951317185 138261034540233606713487889)
        ·
          refine ⟨103695775905175205035115917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138261034540233606713487889 103695775905175205035115917)
          ·
            refine ⟨38885915964440701888168469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103695775905175205035115917 38885915964440701888168469)
            ·
              refine ⟨1822777310833157901007897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38885915964440701888168469 1822777310833157901007897)
              ·
                refine ⟨1367082983124868425755923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1822777310833157901007897 1367082983124868425755923)
                ·
                  refine ⟨2050624474687302638633885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367082983124868425755923 2050624474687302638633885)
                  ·
                    refine ⟨768984178007738489487707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2050624474687302638633885 768984178007738489487707)
                    ·
                      rfl

theorem cell22_2246387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 1, 3].length) (baseStart_2246387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246387 prefixEnd_2246387 := by exact prefixLift 2246387
  have htrace : WordTrace (prefixWord ++ tailWord_2246387) baseStart_2246387 baseEnd_2246387 := by
    simpa [prefixWord, tailWord_2246387, baseEnd_2246387] using wordTrace_append hprefix tailTrace_2246387
  have hstable : (prefixWord ++ tailWord_2246387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246387).length < 2 ^ (prefixWord ++ tailWord_2246387).sum := by decide
  have hdescent : baseEnd_2246387 < baseStart_2246387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246411 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 8]
def baseStart_2246411 : Nat := 118140960795 + 2246411 * 2 ^ 59
def prefixEnd_2246411 : Nat := 4983230072969 + 3 ^ 40 * 2246411 * 2
def baseEnd_2246411 : Nat := 256330797899403475629211

theorem tailTrace_2246411 : CollatzResearch.WordTrace tailWord_2246411 prefixEnd_2246411 256330797899403475629211 := by
  unfold tailWord_2246411
  simp only [CollatzResearch.WordTrace]
  refine ⟨81933340264644078299459087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54622226843096052199639391 81933340264644078299459087)
  ·
    refine ⟨122900010396966117449188631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81933340264644078299459087 122900010396966117449188631)
    ·
      refine ⟨184350015595449176173782947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122900010396966117449188631 184350015595449176173782947)
      ·
        refine ⟨276525023393173764260674421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184350015595449176173782947 276525023393173764260674421)
        ·
          refine ⟨25924220943110040399438227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 276525023393173764260674421 25924220943110040399438227)
          ·
            refine ⟨38886331414665060599157341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25924220943110040399438227 38886331414665060599157341)
            ·
              refine ⟨14582374280499397724684003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38886331414665060599157341 14582374280499397724684003)
              ·
                refine ⟨21873561420749096587026005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14582374280499397724684003 21873561420749096587026005)
                ·
                  refine ⟨256330797899403475629211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21873561420749096587026005 256330797899403475629211)
                  ·
                    rfl

theorem cell22_2246411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 8].length) (baseStart_2246411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246411 prefixEnd_2246411 := by exact prefixLift 2246411
  have htrace : WordTrace (prefixWord ++ tailWord_2246411) baseStart_2246411 baseEnd_2246411 := by
    simpa [prefixWord, tailWord_2246411, baseEnd_2246411] using wordTrace_append hprefix tailTrace_2246411
  have hstable : (prefixWord ++ tailWord_2246411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246411).length < 2 ^ (prefixWord ++ tailWord_2246411).sum := by decide
  have hdescent : baseEnd_2246411 < baseStart_2246411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246441 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 5, 6]
def baseStart_2246441 : Nat := 118140960795 + 2246441 * 2 ^ 59
def prefixEnd_2246441 : Nat := 4983230072969 + 3 ^ 40 * 2246441 * 2
def baseEnd_2246441 : Nat := 769002663311300348637541

theorem tailTrace_2246441 : CollatzResearch.WordTrace tailWord_2246441 prefixEnd_2246441 769002663311300348637541 := by
  unfold tailWord_2246441
  simp only [CollatzResearch.WordTrace]
  refine ⟨81934434454535393423051177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54622956303023595615367451 81934434454535393423051177)
  ·
    refine ⟨61450825840901545067288383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81934434454535393423051177 61450825840901545067288383)
    ·
      refine ⟨92176238761352317600932575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61450825840901545067288383 92176238761352317600932575)
      ·
        refine ⟨138264358142028476401398863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92176238761352317600932575 138264358142028476401398863)
        ·
          refine ⟨207396537213042714602098295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138264358142028476401398863 207396537213042714602098295)
          ·
            refine ⟨311094805819564071903147443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207396537213042714602098295 311094805819564071903147443)
            ·
              refine ⟨466642208729346107854721165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311094805819564071903147443 466642208729346107854721165)
              ·
                refine ⟨174990828273504790445520437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 466642208729346107854721165 174990828273504790445520437)
                ·
                  refine ⟨16405390150641074104267541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 174990828273504790445520437 16405390150641074104267541)
                  ·
                    refine ⟨769002663311300348637541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16405390150641074104267541 769002663311300348637541)
                    ·
                      rfl

theorem cell22_2246441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_2246441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246441 prefixEnd_2246441 := by exact prefixLift 2246441
  have htrace : WordTrace (prefixWord ++ tailWord_2246441) baseStart_2246441 baseEnd_2246441 := by
    simpa [prefixWord, tailWord_2246441, baseEnd_2246441] using wordTrace_append hprefix tailTrace_2246441
  have hstable : (prefixWord ++ tailWord_2246441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246441).length < 2 ^ (prefixWord ++ tailWord_2246441).sum := by decide
  have hdescent : baseEnd_2246441 < baseStart_2246441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246458 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 1, 6]
def baseStart_2246458 : Nat := 118140960795 + 2246458 * 2 ^ 59
def prefixEnd_2246458 : Nat := 4983230072969 + 3 ^ 40 * 2246458 * 2
def baseEnd_2246458 : Nat := 769008482758717970962489

theorem tailTrace_2246458 : CollatzResearch.WordTrace tailWord_2246458 prefixEnd_2246458 769008482758717970962489 := by
  unfold tailWord_2246458
  simp only [CollatzResearch.WordTrace]
  refine ⟨20483763623868451331605007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54623369663649203550946685 20483763623868451331605007)
  ·
    refine ⟨30725645435802676997407511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20483763623868451331605007 30725645435802676997407511)
    ·
      refine ⟨46088468153704015496111267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30725645435802676997407511 46088468153704015496111267)
      ·
        refine ⟨69132702230556023244166901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46088468153704015496111267 69132702230556023244166901)
        ·
          refine ⟨6481190834114627179140647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69132702230556023244166901 6481190834114627179140647)
          ·
            refine ⟨9721786251171940768710971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6481190834114627179140647 9721786251171940768710971)
            ·
              refine ⟨14582679376757911153066457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9721786251171940768710971 14582679376757911153066457)
              ·
                refine ⟨10937009532568433364799843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14582679376757911153066457 10937009532568433364799843)
                ·
                  refine ⟨16405514298852650047199765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10937009532568433364799843 16405514298852650047199765)
                  ·
                    refine ⟨769008482758717970962489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16405514298852650047199765 769008482758717970962489)
                    ·
                      rfl

theorem cell22_2246458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_2246458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246458 prefixEnd_2246458 := by exact prefixLift 2246458
  have htrace : WordTrace (prefixWord ++ tailWord_2246458) baseStart_2246458 baseEnd_2246458 := by
    simpa [prefixWord, tailWord_2246458, baseEnd_2246458] using wordTrace_append hprefix tailTrace_2246458
  have hstable : (prefixWord ++ tailWord_2246458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246458).length < 2 ^ (prefixWord ++ tailWord_2246458).sum := by decide
  have hdescent : baseEnd_2246458 < baseStart_2246458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246460 : List Nat := [2, 2, 2, 2, 1, 1, 2, 5, 2, 3]
def baseStart_2246460 : Nat := 118140960795 + 2246460 * 2 ^ 59
def prefixEnd_2246460 : Nat := 4983230072969 + 3 ^ 40 * 2246460 * 2
def baseEnd_2246460 : Nat := 769009167399590632412483

theorem tailTrace_2246460 : CollatzResearch.WordTrace tailWord_2246460 prefixEnd_2246460 769009167399590632412483 := by
  unfold tailWord_2246460
  simp only [CollatzResearch.WordTrace]
  refine ⟨40967563720733279833996417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54623418294311039778661889 40967563720733279833996417)
  ·
    refine ⟨30725672790549959875497313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40967563720733279833996417 30725672790549959875497313)
    ·
      refine ⟨23044254592912469906622985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30725672790549959875497313 23044254592912469906622985)
      ·
        refine ⟨17283190944684352429967239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23044254592912469906622985 17283190944684352429967239)
        ·
          refine ⟨25924786417026528644950859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17283190944684352429967239 25924786417026528644950859)
          ·
            refine ⟨38887179625539792967426289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25924786417026528644950859 38887179625539792967426289)
            ·
              refine ⟨29165384719154844725569717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38887179625539792967426289 29165384719154844725569717)
              ·
                refine ⟨2734254817420766693022161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29165384719154844725569717 2734254817420766693022161)
                ·
                  refine ⟨2050691113065575019766621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2734254817420766693022161 2050691113065575019766621)
                  ·
                    refine ⟨769009167399590632412483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2050691113065575019766621 769009167399590632412483)
                    ·
                      rfl

theorem cell22_2246460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_2246460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246460 prefixEnd_2246460 := by exact prefixLift 2246460
  have htrace : WordTrace (prefixWord ++ tailWord_2246460) baseStart_2246460 baseEnd_2246460 := by
    simpa [prefixWord, tailWord_2246460, baseEnd_2246460] using wordTrace_append hprefix tailTrace_2246460
  have hstable : (prefixWord ++ tailWord_2246460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246460).length < 2 ^ (prefixWord ++ tailWord_2246460).sum := by decide
  have hdescent : baseEnd_2246460 < baseStart_2246460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246477 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_2246477 : Nat := 118140960795 + 2246477 * 2 ^ 59
def prefixEnd_2246477 : Nat := 4983230072969 + 3 ^ 40 * 2246477 * 2
def baseEnd_2246477 : Nat := 769014986847008254737431

theorem tailTrace_2246477 : CollatzResearch.WordTrace tailWord_2246477 prefixEnd_2246477 769014986847008254737431 := by
  unfold tailWord_2246477
  simp only [CollatzResearch.WordTrace]
  refine ⟨81935747482404971571361685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54623831654936647714241123 81935747482404971571361685)
  ·
    refine ⟨3840738163237733042407579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81935747482404971571361685 3840738163237733042407579)
    ·
      refine ⟨5761107244856599563611369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3840738163237733042407579 5761107244856599563611369)
      ·
        refine ⟨4320830433642449672708527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5761107244856599563611369 4320830433642449672708527)
        ·
          refine ⟨6481245650463674509062791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4320830433642449672708527 6481245650463674509062791)
          ·
            refine ⟨9721868475695511763594187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6481245650463674509062791 9721868475695511763594187)
            ·
              refine ⟨14582802713543267645391281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9721868475695511763594187 14582802713543267645391281)
              ·
                refine ⟨10937102035157450734043461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14582802713543267645391281 10937102035157450734043461)
                ·
                  refine ⟨2050706631592022012633149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10937102035157450734043461 2050706631592022012633149)
                  ·
                    refine ⟨769014986847008254737431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2050706631592022012633149 769014986847008254737431)
                    ·
                      rfl

theorem cell22_2246477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_2246477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246477 prefixEnd_2246477 := by exact prefixLift 2246477
  have htrace : WordTrace (prefixWord ++ tailWord_2246477) baseStart_2246477 baseEnd_2246477 := by
    simpa [prefixWord, tailWord_2246477, baseEnd_2246477] using wordTrace_append hprefix tailTrace_2246477
  have hstable : (prefixWord ++ tailWord_2246477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246477).length < 2 ^ (prefixWord ++ tailWord_2246477).sum := by decide
  have hdescent : baseEnd_2246477 < baseStart_2246477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246492 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 2, 4]
def baseStart_2246492 : Nat := 118140960795 + 2246492 * 2 ^ 59
def prefixEnd_2246492 : Nat := 4983230072969 + 3 ^ 40 * 2246492 * 2
def baseEnd_2246492 : Nat := 769020121653553215612385

theorem tailTrace_2246492 : CollatzResearch.WordTrace tailWord_2246492 prefixEnd_2246492 769020121653553215612385 := by
  unfold tailWord_2246492
  simp only [CollatzResearch.WordTrace]
  refine ⟨40968147288675314566578865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54624196384900419422105153 40968147288675314566578865)
  ·
    refine ⟨30726110466506485924934149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40968147288675314566578865 30726110466506485924934149)
    ·
      refine ⟨5761145712469966110925153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30726110466506485924934149 5761145712469966110925153)
      ·
        refine ⟨4320859284352474583193865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5761145712469966110925153 4320859284352474583193865)
        ·
          refine ⟨3240644463264355937395399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4320859284352474583193865 3240644463264355937395399)
          ·
            refine ⟨4860966694896533906093099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3240644463264355937395399 4860966694896533906093099)
            ·
              refine ⟨7291450042344800859139649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4860966694896533906093099 7291450042344800859139649)
              ·
                refine ⟨5468587531758600644354737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7291450042344800859139649 5468587531758600644354737)
                ·
                  refine ⟨4101440648818950483266053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5468587531758600644354737 4101440648818950483266053)
                  ·
                    refine ⟨769020121653553215612385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4101440648818950483266053 769020121653553215612385)
                    ·
                      rfl

theorem cell22_2246492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_2246492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246492 prefixEnd_2246492 := by exact prefixLift 2246492
  have htrace : WordTrace (prefixWord ++ tailWord_2246492) baseStart_2246492 baseEnd_2246492 := by
    simpa [prefixWord, tailWord_2246492, baseEnd_2246492] using wordTrace_append hprefix tailTrace_2246492
  have hstable : (prefixWord ++ tailWord_2246492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246492).length < 2 ^ (prefixWord ++ tailWord_2246492).sum := by decide
  have hdescent : baseEnd_2246492 < baseStart_2246492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246503 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 2, 6]
def baseStart_2246503 : Nat := 118140960795 + 2246503 * 2 ^ 59
def prefixEnd_2246503 : Nat := 4983230072969 + 3 ^ 40 * 2246503 * 2
def baseEnd_2246503 : Nat := 769023887178352853587351

theorem tailTrace_2246503 : CollatzResearch.WordTrace tailWord_2246503 prefixEnd_2246503 769023887178352853587351 := by
  unfold tailWord_2246503
  simp only [CollatzResearch.WordTrace]
  refine ⟨81936695780310778011808163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54624463853540518674538775 81936695780310778011808163)
  ·
    refine ⟨122905043670466167017712245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81936695780310778011808163 122905043670466167017712245)
    ·
      refine ⟨11522347844106203157910523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122905043670466167017712245 11522347844106203157910523)
      ·
        refine ⟨17283521766159304736865785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11522347844106203157910523 17283521766159304736865785)
        ·
          refine ⟨12962641324619478552649339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17283521766159304736865785 12962641324619478552649339)
          ·
            refine ⟨19443961986929217828974009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12962641324619478552649339 19443961986929217828974009)
            ·
              refine ⟨14582971490196913371730507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19443961986929217828974009 14582971490196913371730507)
              ·
                refine ⟨21874457235295370057595761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14582971490196913371730507 21874457235295370057595761)
                ·
                  refine ⟨16405842926471527543196821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21874457235295370057595761 16405842926471527543196821)
                  ·
                    refine ⟨769023887178352853587351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16405842926471527543196821 769023887178352853587351)
                    ·
                      rfl

theorem cell22_2246503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_2246503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246503 prefixEnd_2246503 := by exact prefixLift 2246503
  have htrace : WordTrace (prefixWord ++ tailWord_2246503) baseStart_2246503 baseEnd_2246503 := by
    simpa [prefixWord, tailWord_2246503, baseEnd_2246503] using wordTrace_append hprefix tailTrace_2246503
  have hstable : (prefixWord ++ tailWord_2246503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246503).length < 2 ^ (prefixWord ++ tailWord_2246503).sum := by decide
  have hdescent : baseEnd_2246503 < baseStart_2246503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246556 : List Nat := [2, 2, 3, 3, 1, 1, 4, 2, 1, 3]
def baseStart_2246556 : Nat := 118140960795 + 2246556 * 2 ^ 59
def prefixEnd_2246556 : Nat := 4983230072969 + 3 ^ 40 * 2246556 * 2
def baseEnd_2246556 : Nat := 769042030161478382012189

theorem tailTrace_2246556 : CollatzResearch.WordTrace tailWord_2246556 prefixEnd_2246556 769042030161478382012189 := by
  unfold tailWord_2246556
  simp only [CollatzResearch.WordTrace]
  refine ⟨40969314424559384031743761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54625752566079178708991681 40969314424559384031743761)
  ·
    refine ⟨30726985818419538023807821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40969314424559384031743761 30726985818419538023807821)
    ·
      refine ⟨11522619681907326758927933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30726985818419538023807821 11522619681907326758927933)
      ·
        refine ⟨4320982380715247534597975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11522619681907326758927933 4320982380715247534597975)
        ·
          refine ⟨6481473571072871301896963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4320982380715247534597975 6481473571072871301896963)
          ·
            refine ⟨9722210356609306952845445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6481473571072871301896963 9722210356609306952845445)
            ·
              refine ⟨1822914441864245053658521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9722210356609306952845445 1822914441864245053658521)
              ·
                refine ⟨1367185831398183790243891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1822914441864245053658521 1367185831398183790243891)
                ·
                  refine ⟨2050778747097275685365837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367185831398183790243891 2050778747097275685365837)
                  ·
                    refine ⟨769042030161478382012189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2050778747097275685365837 769042030161478382012189)
                    ·
                      rfl

theorem cell22_2246556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_2246556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246556 prefixEnd_2246556 := by exact prefixLift 2246556
  have htrace : WordTrace (prefixWord ++ tailWord_2246556) baseStart_2246556 baseEnd_2246556 := by
    simpa [prefixWord, tailWord_2246556, baseEnd_2246556] using wordTrace_append hprefix tailTrace_2246556
  have hstable : (prefixWord ++ tailWord_2246556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246556).length < 2 ^ (prefixWord ++ tailWord_2246556).sum := by decide
  have hdescent : baseEnd_2246556 < baseStart_2246556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246563 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 6]
def baseStart_2246563 : Nat := 118140960795 + 2246563 * 2 ^ 59
def prefixEnd_2246563 : Nat := 4983230072969 + 3 ^ 40 * 2246563 * 2
def baseEnd_2246563 : Nat := 256348142134844232362389

theorem tailTrace_2246563 : CollatzResearch.WordTrace tailWord_2246563 prefixEnd_2246563 256348142134844232362389 := by
  unfold tailWord_2246563
  simp only [CollatzResearch.WordTrace]
  refine ⟨81938884160093408258992343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54625922773395605505994895 81938884160093408258992343)
  ·
    refine ⟨122908326240140112388488515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81938884160093408258992343 122908326240140112388488515)
    ·
      refine ⟨184362489360210168582732773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122908326240140112388488515 184362489360210168582732773)
      ·
        refine ⟨34567966755039406609262395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184362489360210168582732773 34567966755039406609262395)
        ·
          refine ⟨51851950132559109913893593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34567966755039406609262395 51851950132559109913893593)
          ·
            refine ⟨38888962599419332435420195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51851950132559109913893593 38888962599419332435420195)
            ·
              refine ⟨58333443899128998653130293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38888962599419332435420195 58333443899128998653130293)
              ·
                refine ⟨5468760365543343623730965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58333443899128998653130293 5468760365543343623730965)
                ·
                  refine ⟨256348142134844232362389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5468760365543343623730965 256348142134844232362389)
                  ·
                    rfl

theorem cell22_2246563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 6].length) (baseStart_2246563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246563 prefixEnd_2246563 := by exact prefixLift 2246563
  have htrace : WordTrace (prefixWord ++ tailWord_2246563) baseStart_2246563 baseEnd_2246563 := by
    simpa [prefixWord, tailWord_2246563, baseEnd_2246563] using wordTrace_append hprefix tailTrace_2246563
  have hstable : (prefixWord ++ tailWord_2246563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246563).length < 2 ^ (prefixWord ++ tailWord_2246563).sum := by decide
  have hdescent : baseEnd_2246563 < baseStart_2246563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246612 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_2246612 : Nat := 118140960795 + 2246612 * 2 ^ 59
def prefixEnd_2246612 : Nat := 4983230072969 + 3 ^ 40 * 2246612 * 2
def baseEnd_2246612 : Nat := 769061200105912902612017

theorem tailTrace_2246612 : CollatzResearch.WordTrace tailWord_2246612 prefixEnd_2246612 769061200105912902612017 := by
  unfold tailWord_2246612
  simp only [CollatzResearch.WordTrace]
  refine ⟨40970335668457944813763045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54627114224610593085017393 40970335668457944813763045)
  ·
    refine ⟨7681937937835864652580571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40970335668457944813763045 7681937937835864652580571)
    ·
      refine ⟨11522906906753796978870857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7681937937835864652580571 11522906906753796978870857)
      ·
        refine ⟨8642180180065347734153143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11522906906753796978870857 8642180180065347734153143)
        ·
          refine ⟨12963270270098021601229715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8642180180065347734153143 12963270270098021601229715)
          ·
            refine ⟨19444905405147032401844573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12963270270098021601229715 19444905405147032401844573)
            ·
              refine ⟨7291839526930137150691715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19444905405147032401844573 7291839526930137150691715)
              ·
                refine ⟨10937759290395205726037573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7291839526930137150691715 10937759290395205726037573)
                ·
                  refine ⟨2050829866949101073632045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10937759290395205726037573 2050829866949101073632045)
                  ·
                    refine ⟨769061200105912902612017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2050829866949101073632045 769061200105912902612017)
                    ·
                      rfl

theorem cell22_2246612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_2246612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246612 prefixEnd_2246612 := by exact prefixLift 2246612
  have htrace : WordTrace (prefixWord ++ tailWord_2246612) baseStart_2246612 baseEnd_2246612 := by
    simpa [prefixWord, tailWord_2246612, baseEnd_2246612] using wordTrace_append hprefix tailTrace_2246612
  have hstable : (prefixWord ++ tailWord_2246612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246612).length < 2 ^ (prefixWord ++ tailWord_2246612).sum := by decide
  have hdescent : baseEnd_2246612 < baseStart_2246612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246614 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_2246614 : Nat := 118140960795 + 2246614 * 2 ^ 59
def prefixEnd_2246614 : Nat := 4983230072969 + 3 ^ 40 * 2246614 * 2
def baseEnd_2246614 : Nat := 256353961582261854687337

theorem tailTrace_2246614 : CollatzResearch.WordTrace tailWord_2246614 prefixEnd_2246614 256353961582261854687337 := by
  unfold tailWord_2246614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5121296517681790248068681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54627162855272429312732597 5121296517681790248068681)
  ·
    refine ⟨3840972388261342686051511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5121296517681790248068681 3840972388261342686051511)
    ·
      refine ⟨5761458582392014029077267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3840972388261342686051511 5761458582392014029077267)
      ·
        refine ⟨8642187873588021043615901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5761458582392014029077267 8642187873588021043615901)
        ·
          refine ⟨3240820452595507891355963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8642187873588021043615901 3240820452595507891355963)
          ·
            refine ⟨4861230678893261837033945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3240820452595507891355963 4861230678893261837033945)
            ·
              refine ⟨3645923009169946377775459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4861230678893261837033945 3645923009169946377775459)
              ·
                refine ⟨5468884513754919566663189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3645923009169946377775459 5468884513754919566663189)
                ·
                  refine ⟨256353961582261854687337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5468884513754919566663189 256353961582261854687337)
                  ·
                    rfl

theorem cell22_2246614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_2246614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246614 prefixEnd_2246614 := by exact prefixLift 2246614
  have htrace : WordTrace (prefixWord ++ tailWord_2246614) baseStart_2246614 baseEnd_2246614 := by
    simpa [prefixWord, tailWord_2246614, baseEnd_2246614] using wordTrace_append hprefix tailTrace_2246614
  have hstable : (prefixWord ++ tailWord_2246614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246614).length < 2 ^ (prefixWord ++ tailWord_2246614).sum := by decide
  have hdescent : baseEnd_2246614 < baseStart_2246614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246670 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 7]
def baseStart_2246670 : Nat := 118140960795 + 2246670 * 2 ^ 59
def prefixEnd_2246670 : Nat := 4983230072969 + 3 ^ 40 * 2246670 * 2
def baseEnd_2246670 : Nat := 256360351563740028220613

theorem tailTrace_2246670 : CollatzResearch.WordTrace tailWord_2246670 prefixEnd_2246670 256360351563740028220613 := by
  unfold tailWord_2246670
  simp only [CollatzResearch.WordTrace]
  refine ⟨10242848346338220691642183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54628524513803843688758309 10242848346338220691642183)
  ·
    refine ⟨15364272519507331037463275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10242848346338220691642183 15364272519507331037463275)
    ·
      refine ⟨23046408779260996556194913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15364272519507331037463275 23046408779260996556194913)
      ·
        refine ⟨17284806584445747417146185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23046408779260996556194913 17284806584445747417146185)
        ·
          refine ⟨12963604938334310562859639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17284806584445747417146185 12963604938334310562859639)
          ·
            refine ⟨19445407407501465844289459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12963604938334310562859639 19445407407501465844289459)
            ·
              refine ⟨29168111111252198766434189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19445407407501465844289459 29168111111252198766434189)
              ·
                refine ⟨10938041666719574537412821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29168111111252198766434189 10938041666719574537412821)
                ·
                  refine ⟨256360351563740028220613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10938041666719574537412821 256360351563740028220613)
                  ·
                    rfl

theorem cell22_2246670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_2246670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246670 prefixEnd_2246670 := by exact prefixLift 2246670
  have htrace : WordTrace (prefixWord ++ tailWord_2246670) baseStart_2246670 baseEnd_2246670 := by
    simpa [prefixWord, tailWord_2246670, baseEnd_2246670] using wordTrace_append hprefix tailTrace_2246670
  have hstable : (prefixWord ++ tailWord_2246670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246670).length < 2 ^ (prefixWord ++ tailWord_2246670).sum := by decide
  have hdescent : baseEnd_2246670 < baseStart_2246670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246730 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 5, 5]
def baseStart_2246730 : Nat := 118140960795 + 2246730 * 2 ^ 59
def prefixEnd_2246730 : Nat := 4983230072969 + 3 ^ 40 * 2246730 * 2
def baseEnd_2246730 : Nat := 769101593917399928161655

theorem tailTrace_2246730 : CollatzResearch.WordTrace tailWord_2246730 prefixEnd_2246730 769101593917399928161655 := by
  unfold tailWord_2246730
  simp only [CollatzResearch.WordTrace]
  refine ⟨20486243787622098945080411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54629983433658930520214429 20486243787622098945080411)
  ·
    refine ⟨30729365681433148417620617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20486243787622098945080411 30729365681433148417620617)
    ·
      refine ⟨23047024261074861313215463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30729365681433148417620617 23047024261074861313215463)
      ·
        refine ⟨34570536391612291969823195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23047024261074861313215463 34570536391612291969823195)
        ·
          refine ⟨51855804587418437954734793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34570536391612291969823195 51855804587418437954734793)
          ·
            refine ⟨38891853440563828466051095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51855804587418437954734793 38891853440563828466051095)
            ·
              refine ⟨58337780160845742699076643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38891853440563828466051095 58337780160845742699076643)
              ·
                refine ⟨87506670241268614048614965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58337780160845742699076643 87506670241268614048614965)
                ·
                  refine ⟨8203750335118932567057653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87506670241268614048614965 8203750335118932567057653)
                  ·
                    refine ⟨769101593917399928161655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8203750335118932567057653 769101593917399928161655)
                    ·
                      rfl

theorem cell22_2246730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_2246730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246730 prefixEnd_2246730 := by exact prefixLift 2246730
  have htrace : WordTrace (prefixWord ++ tailWord_2246730) baseStart_2246730 baseEnd_2246730 := by
    simpa [prefixWord, tailWord_2246730, baseEnd_2246730] using wordTrace_append hprefix tailTrace_2246730
  have hstable : (prefixWord ++ tailWord_2246730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246730).length < 2 ^ (prefixWord ++ tailWord_2246730).sum := by decide
  have hdescent : baseEnd_2246730 < baseStart_2246730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246745 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 1, 6]
def baseStart_2246745 : Nat := 118140960795 + 2246745 * 2 ^ 59
def prefixEnd_2246745 : Nat := 4983230072969 + 3 ^ 40 * 2246745 * 2
def baseEnd_2246745 : Nat := 769106728723944889036609

theorem tailTrace_2246745 : CollatzResearch.WordTrace tailWord_2246745 prefixEnd_2246745 769106728723944889036609 := by
  unfold tailWord_2246745
  simp only [CollatzResearch.WordTrace]
  refine ⟨81945522245434053342117689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54630348163622702228078459 81945522245434053342117689)
  ·
    refine ⟨61459141684075540006588267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81945522245434053342117689 61459141684075540006588267)
    ·
      refine ⟨92188712526113310009882401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61459141684075540006588267 92188712526113310009882401)
      ·
        refine ⟨69141534394584982507411801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92188712526113310009882401 69141534394584982507411801)
        ·
          refine ⟨51856150795938736880558851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69141534394584982507411801 51856150795938736880558851)
          ·
            refine ⟨77784226193908105320838277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51856150795938736880558851 77784226193908105320838277)
            ·
              refine ⟨14584542411357769747657177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77784226193908105320838277 14584542411357769747657177)
              ·
                refine ⟨10938406808518327310742883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14584542411357769747657177 10938406808518327310742883)
                ·
                  refine ⟨16407610212777490966114325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10938406808518327310742883 16407610212777490966114325)
                  ·
                    refine ⟨769106728723944889036609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16407610212777490966114325 769106728723944889036609)
                    ·
                      rfl

theorem cell22_2246745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_2246745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246745 prefixEnd_2246745 := by exact prefixLift 2246745
  have htrace : WordTrace (prefixWord ++ tailWord_2246745) baseStart_2246745 baseEnd_2246745 := by
    simpa [prefixWord, tailWord_2246745, baseEnd_2246745] using wordTrace_append hprefix tailTrace_2246745
  have hstable : (prefixWord ++ tailWord_2246745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246745).length < 2 ^ (prefixWord ++ tailWord_2246745).sum := by decide
  have hdescent : baseEnd_2246745 < baseStart_2246745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246749 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 6]
def baseStart_2246749 : Nat := 118140960795 + 2246749 * 2 ^ 59
def prefixEnd_2246749 : Nat := 4983230072969 + 3 ^ 40 * 2246749 * 2
def baseEnd_2246749 : Nat := 256369366001896737312199

theorem tailTrace_2246749 : CollatzResearch.WordTrace tailWord_2246749 prefixEnd_2246749 256369366001896737312199 := by
  unfold tailWord_2246749
  simp only [CollatzResearch.WordTrace]
  refine ⟨81945668137419562025263301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54630445424946374683508867 81945668137419562025263301)
  ·
    refine ⟨15364812775766167879736869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81945668137419562025263301 15364812775766167879736869)
    ·
      refine ⟨2880902395456156477450663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15364812775766167879736869 2880902395456156477450663)
      ·
        refine ⟨4321353593184234716175995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2880902395456156477450663 4321353593184234716175995)
        ·
          refine ⟨6482030389776352074263993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4321353593184234716175995 6482030389776352074263993)
          ·
            refine ⟨4861522792332264055697995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6482030389776352074263993 4861522792332264055697995)
            ·
              refine ⟨7292284188498396083546993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4861522792332264055697995 7292284188498396083546993)
              ·
                refine ⟨5469213141373797062660245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7292284188498396083546993 5469213141373797062660245)
                ·
                  refine ⟨256369366001896737312199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5469213141373797062660245 256369366001896737312199)
                  ·
                    rfl

theorem cell22_2246749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_2246749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246749 prefixEnd_2246749 := by exact prefixLift 2246749
  have htrace : WordTrace (prefixWord ++ tailWord_2246749) baseStart_2246749 baseEnd_2246749 := by
    simpa [prefixWord, tailWord_2246749, baseEnd_2246749] using wordTrace_append hprefix tailTrace_2246749
  have hstable : (prefixWord ++ tailWord_2246749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246749).length < 2 ^ (prefixWord ++ tailWord_2246749).sum := by decide
  have hdescent : baseEnd_2246749 < baseStart_2246749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246781 : List Nat := [1, 4, 1, 1, 3, 4, 1, 2, 2, 3]
def baseStart_2246781 : Nat := 118140960795 + 2246781 * 2 ^ 59
def prefixEnd_2246781 : Nat := 4983230072969 + 3 ^ 40 * 2246781 * 2
def baseEnd_2246781 : Nat := 769119052259652795136499

theorem tailTrace_2246781 : CollatzResearch.WordTrace tailWord_2246781 prefixEnd_2246781 769119052259652795136499 := by
  unfold tailWord_2246781
  simp only [CollatzResearch.WordTrace]
  refine ⟨81946835273303631490428197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54631223515535754326952131 81946835273303631490428197)
  ·
    refine ⟨15365031613744430904455287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81946835273303631490428197 15365031613744430904455287)
    ·
      refine ⟨23047547420616646356682931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15365031613744430904455287 23047547420616646356682931)
      ·
        refine ⟨34571321130924969535024397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23047547420616646356682931 34571321130924969535024397)
        ·
          refine ⟨12964245424096863575634149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34571321130924969535024397 12964245424096863575634149)
          ·
            refine ⟨2430796017018161920431403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12964245424096863575634149 2430796017018161920431403)
            ·
              refine ⟨3646194025527242880647105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2430796017018161920431403 3646194025527242880647105)
              ·
                refine ⟨2734645519145432160485329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3646194025527242880647105 2734645519145432160485329)
                ·
                  refine ⟨2050984139359074120363997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2734645519145432160485329 2050984139359074120363997)
                  ·
                    refine ⟨769119052259652795136499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2050984139359074120363997 769119052259652795136499)
                    ·
                      rfl

theorem cell22_2246781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_2246781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246781 prefixEnd_2246781 := by exact prefixLift 2246781
  have htrace : WordTrace (prefixWord ++ tailWord_2246781) baseStart_2246781 baseEnd_2246781 := by
    simpa [prefixWord, tailWord_2246781, baseEnd_2246781] using wordTrace_append hprefix tailTrace_2246781
  have hstable : (prefixWord ++ tailWord_2246781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246781).length < 2 ^ (prefixWord ++ tailWord_2246781).sum := by decide
  have hdescent : baseEnd_2246781 < baseStart_2246781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246798 : List Nat := [4, 1, 1, 3, 3, 1, 3, 1, 2, 3]
def baseStart_2246798 : Nat := 118140960795 + 2246798 * 2 ^ 59
def prefixEnd_2246798 : Nat := 4983230072969 + 3 ^ 40 * 2246798 * 2
def baseEnd_2246798 : Nat := 769124871707070417461447

theorem tailTrace_2246798 : CollatzResearch.WordTrace tailWord_2246798 prefixEnd_2246798 769124871707070417461447 := by
  unfold tailWord_2246798
  simp only [CollatzResearch.WordTrace]
  refine ⟨10243431914280255424224631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54631636876161362262531365 10243431914280255424224631)
  ·
    refine ⟨15365147871420383136336947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10243431914280255424224631 15365147871420383136336947)
    ·
      refine ⟨23047721807130574704505421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15365147871420383136336947 23047721807130574704505421)
      ·
        refine ⟨8642895677673965514189533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23047721807130574704505421 8642895677673965514189533)
        ·
          refine ⟨3241085879127737067821075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8642895677673965514189533 3241085879127737067821075)
          ·
            refine ⟨4861628818691605601731613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3241085879127737067821075 4861628818691605601731613)
            ·
              refine ⟨1823110807009352100649355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4861628818691605601731613 1823110807009352100649355)
              ·
                refine ⟨2734666210514028150974033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1823110807009352100649355 2734666210514028150974033)
                ·
                  refine ⟨2050999657885521113230525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2734666210514028150974033 2050999657885521113230525)
                  ·
                    refine ⟨769124871707070417461447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2050999657885521113230525 769124871707070417461447)
                    ·
                      rfl

theorem cell22_2246798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_2246798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246798 prefixEnd_2246798 := by exact prefixLift 2246798
  have htrace : WordTrace (prefixWord ++ tailWord_2246798) baseStart_2246798 baseEnd_2246798 := by
    simpa [prefixWord, tailWord_2246798, baseEnd_2246798] using wordTrace_append hprefix tailTrace_2246798
  have hstable : (prefixWord ++ tailWord_2246798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246798).length < 2 ^ (prefixWord ++ tailWord_2246798).sum := by decide
  have hdescent : baseEnd_2246798 < baseStart_2246798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246884 : List Nat := [2, 3, 1, 1, 1, 2, 1, 7, 4]
def baseStart_2246884 : Nat := 118140960795 + 2246884 * 2 ^ 59
def prefixEnd_2246884 : Nat := 4983230072969 + 3 ^ 40 * 2246884 * 2
def baseEnd_2246884 : Nat := 256384770421531619937061

theorem tailTrace_2246884 : CollatzResearch.WordTrace tailWord_2246884 prefixEnd_2246884 256384770421531619937061 := by
  unfold tailWord_2246884
  simp only [CollatzResearch.WordTrace]
  refine ⟨40975295995965240040713853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54633727994620320054285137 40975295995965240040713853)
  ·
    refine ⟨15365735998486965015267695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40975295995965240040713853 15365735998486965015267695)
    ·
      refine ⟨23048603997730447522901543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15365735998486965015267695 23048603997730447522901543)
      ·
        refine ⟨34572905996595671284352315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23048603997730447522901543 34572905996595671284352315)
        ·
          refine ⟨51859358994893506926528473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34572905996595671284352315 51859358994893506926528473)
          ·
            refine ⟨38894519246170130194896355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51859358994893506926528473 38894519246170130194896355)
            ·
              refine ⟨58341778869255195292344533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38894519246170130194896355 58341778869255195292344533)
              ·
                refine ⟨1367385442248168639664325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 58341778869255195292344533 1367385442248168639664325)
                ·
                  refine ⟨256384770421531619937061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1367385442248168639664325 256384770421531619937061)
                  ·
                    rfl

theorem cell22_2246884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_2246884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246884 prefixEnd_2246884 := by exact prefixLift 2246884
  have htrace : WordTrace (prefixWord ++ tailWord_2246884) baseStart_2246884 baseEnd_2246884 := by
    simpa [prefixWord, tailWord_2246884, baseEnd_2246884] using wordTrace_append hprefix tailTrace_2246884
  have hstable : (prefixWord ++ tailWord_2246884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246884).length < 2 ^ (prefixWord ++ tailWord_2246884).sum := by decide
  have hdescent : baseEnd_2246884 < baseStart_2246884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246912 : List Nat := [2, 1, 1, 2, 1, 1, 7, 7]
def baseStart_2246912 : Nat := 118140960795 + 2246912 * 2 ^ 59
def prefixEnd_2246912 : Nat := 4983230072969 + 3 ^ 40 * 2246912 * 2
def baseEnd_2246912 : Nat := 85462655137423568901233

theorem tailTrace_2246912 : CollatzResearch.WordTrace tailWord_2246912 prefixEnd_2246912 85462655137423568901233 := by
  unfold tailWord_2246912
  simp only [CollatzResearch.WordTrace]
  refine ⟨40975806617914520431723495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54634408823886027242297993 40975806617914520431723495)
  ·
    refine ⟨61463709926871780647585243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40975806617914520431723495 61463709926871780647585243)
    ·
      refine ⟨92195564890307670971377865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61463709926871780647585243 92195564890307670971377865)
      ·
        refine ⟨69146673667730753228533399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92195564890307670971377865 69146673667730753228533399)
        ·
          refine ⟨103720010501596129842800099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69146673667730753228533399 103720010501596129842800099)
          ·
            refine ⟨155580015752394194764200149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103720010501596129842800099 155580015752394194764200149)
            ·
              refine ⟨3646406619196738939785941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 155580015752394194764200149 3646406619196738939785941)
              ·
                refine ⟨85462655137423568901233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3646406619196738939785941 85462655137423568901233)
                ·
                  rfl

theorem cell22_2246912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 7].length) (baseStart_2246912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246912 prefixEnd_2246912 := by exact prefixLift 2246912
  have htrace : WordTrace (prefixWord ++ tailWord_2246912) baseStart_2246912 baseEnd_2246912 := by
    simpa [prefixWord, tailWord_2246912, baseEnd_2246912] using wordTrace_append hprefix tailTrace_2246912
  have hstable : (prefixWord ++ tailWord_2246912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246912).length < 2 ^ (prefixWord ++ tailWord_2246912).sum := by decide
  have hdescent : baseEnd_2246912 < baseStart_2246912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246916 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_2246916 : Nat := 118140960795 + 2246916 * 2 ^ 59
def prefixEnd_2246916 : Nat := 4983230072969 + 3 ^ 40 * 2246916 * 2
def baseEnd_2246916 : Nat := 769165265518557443011085

theorem tailTrace_2246916 : CollatzResearch.WordTrace tailWord_2246916 prefixEnd_2246916 769165265518557443011085 := by
  unfold tailWord_2246916
  simp only [CollatzResearch.WordTrace]
  refine ⟨40975879563907274773296301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54634506085209699697728401 40975879563907274773296301)
  ·
    refine ⟨15365954836465228039986113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40975879563907274773296301 15365954836465228039986113)
    ·
      refine ⟨11524466127348921029989585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15365954836465228039986113 11524466127348921029989585)
      ·
        refine ⟨8643349595511690772492189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11524466127348921029989585 8643349595511690772492189)
        ·
          refine ⟨3241256098316884039684571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8643349595511690772492189 3241256098316884039684571)
          ·
            refine ⟨4861884147475326059526857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3241256098316884039684571 4861884147475326059526857)
            ·
              refine ⟨3646413110606494544645143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4861884147475326059526857 3646413110606494544645143)
              ·
                refine ⟨5469619665909741816967715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3646413110606494544645143 5469619665909741816967715)
                ·
                  refine ⟨8204429498864612725451573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5469619665909741816967715 8204429498864612725451573)
                  ·
                    refine ⟨769165265518557443011085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8204429498864612725451573 769165265518557443011085)
                    ·
                      rfl

theorem cell22_2246916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_2246916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246916 prefixEnd_2246916 := by exact prefixLift 2246916
  have htrace : WordTrace (prefixWord ++ tailWord_2246916) baseStart_2246916 baseEnd_2246916 := by
    simpa [prefixWord, tailWord_2246916, baseEnd_2246916] using wordTrace_append hprefix tailTrace_2246916
  have hstable : (prefixWord ++ tailWord_2246916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246916).length < 2 ^ (prefixWord ++ tailWord_2246916).sum := by decide
  have hdescent : baseEnd_2246916 < baseStart_2246916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246929 : List Nat := [1, 2, 2, 1, 1, 6, 3, 6]
def baseStart_2246929 : Nat := 118140960795 + 2246929 * 2 ^ 59
def prefixEnd_2246929 : Nat := 4983230072969 + 3 ^ 40 * 2246929 * 2
def baseEnd_2246929 : Nat := 85463301742692193604005

theorem tailTrace_2246929 : CollatzResearch.WordTrace tailWord_2246929 prefixEnd_2246929 85463301742692193604005 := by
  unfold tailWord_2246929
  simp only [CollatzResearch.WordTrace]
  refine ⟨81952233276767452766815841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54634822184511635177877227 81952233276767452766815841)
  ·
    refine ⟨61464174957575589575111881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81952233276767452766815841 61464174957575589575111881)
    ·
      refine ⟨46098131218181692181333911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61464174957575589575111881 46098131218181692181333911)
      ·
        refine ⟨69147196827272538272000867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46098131218181692181333911 69147196827272538272000867)
        ·
          refine ⟨103720795240908807408001301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69147196827272538272000867 103720795240908807408001301)
          ·
            refine ⟨4861912276917600347250061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103720795240908807408001301 4861912276917600347250061)
            ·
              refine ⟨1823217103844100130218773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4861912276917600347250061 1823217103844100130218773)
              ·
                refine ⟨85463301742692193604005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1823217103844100130218773 85463301742692193604005)
                ·
                  rfl

theorem cell22_2246929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 6].length) (baseStart_2246929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246929 prefixEnd_2246929 := by exact prefixLift 2246929
  have htrace : WordTrace (prefixWord ++ tailWord_2246929) baseStart_2246929 baseEnd_2246929 := by
    simpa [prefixWord, tailWord_2246929, baseEnd_2246929] using wordTrace_append hprefix tailTrace_2246929
  have hstable : (prefixWord ++ tailWord_2246929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246929).length < 2 ^ (prefixWord ++ tailWord_2246929).sum := by decide
  have hdescent : baseEnd_2246929 < baseStart_2246929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246980 : List Nat := [2, 3, 4, 1, 3, 1, 2, 6]
def baseStart_2246980 : Nat := 118140960795 + 2246980 * 2 ^ 59
def prefixEnd_2246980 : Nat := 4983230072969 + 3 ^ 40 * 2246980 * 2
def baseEnd_2246980 : Nat := 85465241558498067712321

theorem tailTrace_2246980 : CollatzResearch.WordTrace tailWord_2246980 prefixEnd_2246980 85465241558498067712321 := by
  unfold tailWord_2246980
  simp only [CollatzResearch.WordTrace]
  refine ⟨40977046699791344238461197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54636062266388458984614929 40977046699791344238461197)
  ·
    refine ⟨15366392512421754089422949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40977046699791344238461197 15366392512421754089422949)
    ·
      refine ⟨2881198596079078891766803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15366392512421754089422949 2881198596079078891766803)
      ·
        refine ⟨4321797894118618337650205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2881198596079078891766803 4321797894118618337650205)
        ·
          refine ⟨1620674210294481876618827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4321797894118618337650205 1620674210294481876618827)
          ·
            refine ⟨2431011315441722814928241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620674210294481876618827 2431011315441722814928241)
            ·
              refine ⟨1823258486581292111196181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2431011315441722814928241 1823258486581292111196181)
              ·
                refine ⟨85465241558498067712321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1823258486581292111196181 85465241558498067712321)
                ·
                  rfl

theorem cell22_2246980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 6].length) (baseStart_2246980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2246980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2246980 prefixEnd_2246980 := by exact prefixLift 2246980
  have htrace : WordTrace (prefixWord ++ tailWord_2246980) baseStart_2246980 baseEnd_2246980 := by
    simpa [prefixWord, tailWord_2246980, baseEnd_2246980] using wordTrace_append hprefix tailTrace_2246980
  have hstable : (prefixWord ++ tailWord_2246980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246980).length < 2 ^ (prefixWord ++ tailWord_2246980).sum := by decide
  have hdescent : baseEnd_2246980 < baseStart_2246980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247064 : List Nat := [2, 1, 2, 5, 1, 11]
def baseStart_2247064 : Nat := 118140960795 + 2247064 * 2 ^ 59
def prefixEnd_2247064 : Nat := 4983230072969 + 3 ^ 40 * 2247064 * 2
def baseEnd_2247064 : Nat := 9496492949915239386551

theorem tailTrace_2247064 : CollatzResearch.WordTrace tailWord_2247064 prefixEnd_2247064 9496492949915239386551 := by
  unfold tailWord_2247064
  simp only [CollatzResearch.WordTrace]
  refine ⟨40978578565639185411490123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54638104754185580548653497 40978578565639185411490123)
  ·
    refine ⟨61467867848458778117235185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40978578565639185411490123 61467867848458778117235185)
    ·
      refine ⟨46100900886344083587926389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61467867848458778117235185 46100900886344083587926389)
      ·
        refine ⟨4321959458094757836368099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46100900886344083587926389 4321959458094757836368099)
        ·
          refine ⟨6482939187142136754552149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4321959458094757836368099 6482939187142136754552149)
          ·
            refine ⟨9496492949915239386551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6482939187142136754552149 9496492949915239386551)
            ·
              rfl

theorem cell22_2247064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 11].length) (baseStart_2247064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247064 prefixEnd_2247064 := by exact prefixLift 2247064
  have htrace : WordTrace (prefixWord ++ tailWord_2247064) baseStart_2247064 baseEnd_2247064 := by
    simpa [prefixWord, tailWord_2247064, baseEnd_2247064] using wordTrace_append hprefix tailTrace_2247064
  have hstable : (prefixWord ++ tailWord_2247064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247064).length < 2 ^ (prefixWord ++ tailWord_2247064).sum := by decide
  have hdescent : baseEnd_2247064 < baseStart_2247064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247066 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 2, 4]
def baseStart_2247066 : Nat := 118140960795 + 2247066 * 2 ^ 59
def prefixEnd_2247066 : Nat := 4983230072969 + 3 ^ 40 * 2247066 * 2
def baseEnd_2247066 : Nat := 769216613584007051760625

theorem tailTrace_2247066 : CollatzResearch.WordTrace tailWord_2247066 prefixEnd_2247066 769216613584007051760625 := by
  unfold tailWord_2247066
  simp only [CollatzResearch.WordTrace]
  refine ⟨20489307519317781291138263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54638153384847416776368701 20489307519317781291138263)
  ·
    refine ⟨30733961278976671936707395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20489307519317781291138263 30733961278976671936707395)
    ·
      refine ⟨46100941918465007905061093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30733961278976671936707395 46100941918465007905061093)
      ·
        refine ⟨8643926609712188982198955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46100941918465007905061093 8643926609712188982198955)
        ·
          refine ⟨12965889914568283473298433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8643926609712188982198955 12965889914568283473298433)
          ·
            refine ⟨9724417435926212604973825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12965889914568283473298433 9724417435926212604973825)
            ·
              refine ⟨7293313076944659453730369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9724417435926212604973825 7293313076944659453730369)
              ·
                refine ⟨5469984807708494590297777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7293313076944659453730369 5469984807708494590297777)
                ·
                  refine ⟨4102488605781370942723333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5469984807708494590297777 4102488605781370942723333)
                  ·
                    refine ⟨769216613584007051760625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4102488605781370942723333 769216613584007051760625)
                    ·
                      rfl

theorem cell22_2247066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_2247066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247066 prefixEnd_2247066 := by exact prefixLift 2247066
  have htrace : WordTrace (prefixWord ++ tailWord_2247066) baseStart_2247066 baseEnd_2247066 := by
    simpa [prefixWord, tailWord_2247066, baseEnd_2247066] using wordTrace_append hprefix tailTrace_2247066
  have hstable : (prefixWord ++ tailWord_2247066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247066).length < 2 ^ (prefixWord ++ tailWord_2247066).sum := by decide
  have hdescent : baseEnd_2247066 < baseStart_2247066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247070 : List Nat := [4, 3, 1, 2, 1, 2, 1, 4, 4]
def baseStart_2247070 : Nat := 118140960795 + 2247070 * 2 ^ 59
def prefixEnd_2247070 : Nat := 4983230072969 + 3 ^ 40 * 2247070 * 2
def baseEnd_2247070 : Nat := 256405994288584124886871

theorem tailTrace_2247070 : CollatzResearch.WordTrace tailWord_2247070 prefixEnd_2247070 256405994288584124886871 := by
  unfold tailWord_2247070
  simp only [CollatzResearch.WordTrace]
  refine ⟨10244671996157079230962333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54638250646171089231799109 10244671996157079230962333)
  ·
    refine ⟨3841751998558904711610875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10244671996157079230962333 3841751998558904711610875)
    ·
      refine ⟨5762627997838357067416313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3841751998558904711610875 5762627997838357067416313)
      ·
        refine ⟨4321970998378767800562235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5762627997838357067416313 4321970998378767800562235)
        ·
          refine ⟨6482956497568151700843353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4321970998378767800562235 6482956497568151700843353)
          ·
            refine ⟨4862217373176113775632515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6482956497568151700843353 4862217373176113775632515)
            ·
              refine ⟨7293326059764170663448773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4862217373176113775632515 7293326059764170663448773)
              ·
                refine ⟨1367498636205781999396645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7293326059764170663448773 1367498636205781999396645)
                ·
                  refine ⟨256405994288584124886871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1367498636205781999396645 256405994288584124886871)
                  ·
                    rfl

theorem cell22_2247070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_2247070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247070 prefixEnd_2247070 := by exact prefixLift 2247070
  have htrace : WordTrace (prefixWord ++ tailWord_2247070) baseStart_2247070 baseEnd_2247070 := by
    simpa [prefixWord, tailWord_2247070, baseEnd_2247070] using wordTrace_append hprefix tailTrace_2247070
  have hstable : (prefixWord ++ tailWord_2247070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247070).length < 2 ^ (prefixWord ++ tailWord_2247070).sum := by decide
  have hdescent : baseEnd_2247070 < baseStart_2247070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247113 : List Nat := [1, 2, 1, 1, 2, 1, 5, 5, 1, 3]
def baseStart_2247113 : Nat := 118140960795 + 2247113 * 2 ^ 59
def prefixEnd_2247113 : Nat := 4983230072969 + 3 ^ 40 * 2247113 * 2
def baseEnd_2247113 : Nat := 769232702644514595835481

theorem tailTrace_2247113 : CollatzResearch.WordTrace tailWord_2247113 prefixEnd_2247113 769232702644514595835481 := by
  unfold tailWord_2247113
  simp only [CollatzResearch.WordTrace]
  refine ⟨81958944308100852191513993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54639296205400568127675995 81958944308100852191513993)
  ·
    refine ⟨61469208231075639143635495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81958944308100852191513993 61469208231075639143635495)
    ·
      refine ⟨92203812346613458715453243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61469208231075639143635495 92203812346613458715453243)
      ·
        refine ⟨138305718519920188073179865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92203812346613458715453243 138305718519920188073179865)
        ·
          refine ⟨103729288889940141054884899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138305718519920188073179865 103729288889940141054884899)
          ·
            refine ⟨155593933334910211582327349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103729288889940141054884899 155593933334910211582327349)
            ·
              refine ⟨14586931250147832335843189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 155593933334910211582327349 14586931250147832335843189)
              ·
                refine ⟨1367524804701359281485299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14586931250147832335843189 1367524804701359281485299)
                ·
                  refine ⟨2051287207052038922227949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367524804701359281485299 2051287207052038922227949)
                  ·
                    refine ⟨769232702644514595835481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2051287207052038922227949 769232702644514595835481)
                    ·
                      rfl

theorem cell22_2247113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 1, 3].length) (baseStart_2247113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247113 prefixEnd_2247113 := by exact prefixLift 2247113
  have htrace : WordTrace (prefixWord ++ tailWord_2247113) baseStart_2247113 baseEnd_2247113 := by
    simpa [prefixWord, tailWord_2247113, baseEnd_2247113] using wordTrace_append hprefix tailTrace_2247113
  have hstable : (prefixWord ++ tailWord_2247113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247113).length < 2 ^ (prefixWord ++ tailWord_2247113).sum := by decide
  have hdescent : baseEnd_2247113 < baseStart_2247113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247143 : List Nat := [1, 1, 5, 2, 1, 1, 5, 1, 5]
def baseStart_2247143 : Nat := 118140960795 + 2247143 * 2 ^ 59
def prefixEnd_2247143 : Nat := 4983230072969 + 3 ^ 40 * 2247143 * 2
def baseEnd_2247143 : Nat := 256414324085868172528463

theorem tailTrace_2247143 : CollatzResearch.WordTrace tailWord_2247143 prefixEnd_2247143 256414324085868172528463 := by
  unfold tailWord_2247143
  simp only [CollatzResearch.WordTrace]
  refine ⟨81960038497992167315106083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54640025665328111543404055 81960038497992167315106083)
  ·
    refine ⟨122940057746988250972659125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81960038497992167315106083 122940057746988250972659125)
    ·
      refine ⟨11525630413780148528686793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122940057746988250972659125 11525630413780148528686793)
      ·
        refine ⟨8644222810335111396515095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11525630413780148528686793 8644222810335111396515095)
        ·
          refine ⟨12966334215502667094772643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8644222810335111396515095 12966334215502667094772643)
          ·
            refine ⟨19449501323254000642158965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12966334215502667094772643 19449501323254000642158965)
            ·
              refine ⟨1823390749055062560202403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19449501323254000642158965 1823390749055062560202403)
              ·
                refine ⟨2735086123582593840303605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1823390749055062560202403 2735086123582593840303605)
                ·
                  refine ⟨256414324085868172528463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2735086123582593840303605 256414324085868172528463)
                  ·
                    rfl

theorem cell22_2247143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 5].length) (baseStart_2247143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247143 prefixEnd_2247143 := by exact prefixLift 2247143
  have htrace : WordTrace (prefixWord ++ tailWord_2247143) baseStart_2247143 baseEnd_2247143 := by
    simpa [prefixWord, tailWord_2247143, baseEnd_2247143] using wordTrace_append hprefix tailTrace_2247143
  have hstable : (prefixWord ++ tailWord_2247143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247143).length < 2 ^ (prefixWord ++ tailWord_2247143).sum := by decide
  have hdescent : baseEnd_2247143 < baseStart_2247143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
