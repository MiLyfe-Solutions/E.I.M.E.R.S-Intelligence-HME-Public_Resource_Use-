import V185TrunkScan21Chunk041

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_508818 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 5]
def baseStart_508818 : Nat := 118140960795 + 508818 * 2 ^ 59
def prefixEnd_508818 : Nat := 4983230072969 + 3 ^ 40 * 508818 * 2
def baseEnd_508818 : Nat := 116119199848664658193331

theorem tailTrace_508818 : CollatzResearch.WordTrace tailWord_508818 prefixEnd_508818 116119199848664658193331 := by
  unfold tailWord_508818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4639529267661690010277777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12372078047097840027407405 4639529267661690010277777)
  ·
    refine ⟨3479646950746267507708333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4639529267661690010277777 3479646950746267507708333)
    ·
      refine ⟨1304867606529850315390625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3479646950746267507708333 1304867606529850315390625)
      ·
        refine ⟨978650704897387736542969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1304867606529850315390625 978650704897387736542969)
        ·
          refine ⟨733988028673040802407227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 978650704897387736542969 733988028673040802407227)
          ·
            refine ⟨1100982043009561203610841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733988028673040802407227 1100982043009561203610841)
            ·
              refine ⟨825736532257170902708131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100982043009561203610841 825736532257170902708131)
              ·
                refine ⟨1238604798385756354062197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825736532257170902708131 1238604798385756354062197)
                ·
                  refine ⟨116119199848664658193331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1238604798385756354062197 116119199848664658193331)
                  ·
                    rfl

theorem cell21_508818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_508818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_508818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_508818 prefixEnd_508818 := by exact prefixLift 508818
  have htrace : WordTrace (prefixWord ++ tailWord_508818) baseStart_508818 baseEnd_508818 := by
    simpa [prefixWord, tailWord_508818, baseEnd_508818] using wordTrace_append hprefix tailTrace_508818
  have hstable : (prefixWord ++ tailWord_508818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508818).length < 2 ^ (prefixWord ++ tailWord_508818).sum := by decide
  have hdescent : baseEnd_508818 < baseStart_508818 := by decide
  rcases family_descends (prefixWord ++ tailWord_508818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508829 : List Nat := [1, 4, 2, 1, 2, 1, 2, 8]
def baseStart_508829 : Nat := 118140960795 + 508829 * 2 ^ 59
def prefixEnd_508829 : Nat := 4983230072969 + 3 ^ 40 * 508829 * 2
def baseEnd_508829 : Nat := 38707236732843694503325

theorem tailTrace_508829 : CollatzResearch.WordTrace tailWord_508829 prefixEnd_508829 38707236732843694503325 := by
  unfold tailWord_508829
  simp only [CollatzResearch.WordTrace]
  refine ⟨18558518273606908919761541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12372345515737939279841027 18558518273606908919761541)
  ·
    refine ⟨3479722176301295422455289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18558518273606908919761541 3479722176301295422455289)
    ·
      refine ⟨2609791632225971566841467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3479722176301295422455289 2609791632225971566841467)
      ·
        refine ⟨3914687448338957350262201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609791632225971566841467 3914687448338957350262201)
        ·
          refine ⟨2936015586254218012696651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3914687448338957350262201 2936015586254218012696651)
          ·
            refine ⟨4404023379381327019044977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936015586254218012696651 4404023379381327019044977)
            ·
              refine ⟨3303017534535995264283733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4404023379381327019044977 3303017534535995264283733)
              ·
                refine ⟨38707236732843694503325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3303017534535995264283733 38707236732843694503325)
                ·
                  rfl

theorem cell21_508829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 8].length) (baseStart_508829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_508829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_508829 prefixEnd_508829 := by exact prefixLift 508829
  have htrace : WordTrace (prefixWord ++ tailWord_508829) baseStart_508829 baseEnd_508829 := by
    simpa [prefixWord, tailWord_508829, baseEnd_508829] using wordTrace_append hprefix tailTrace_508829
  have hstable : (prefixWord ++ tailWord_508829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508829).length < 2 ^ (prefixWord ++ tailWord_508829).sum := by decide
  have hdescent : baseEnd_508829 < baseStart_508829 := by decide
  rcases family_descends (prefixWord ++ tailWord_508829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508852 : List Nat := [2, 5, 2, 1, 1, 3, 1, 3, 3]
def baseStart_508852 : Nat := 118140960795 + 508852 * 2 ^ 59
def prefixEnd_508852 : Nat := 4983230072969 + 3 ^ 40 * 508852 * 2
def baseEnd_508852 : Nat := 116126959111888154626595

theorem tailTrace_508852 : CollatzResearch.WordTrace tailWord_508852 prefixEnd_508852 116126959111888154626595 := by
  unfold tailWord_508852
  simp only [CollatzResearch.WordTrace]
  refine ⟨9279678576261791923924405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12372904768349055898565873 9279678576261791923924405)
  ·
    refine ⟨869969866524542992867913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9279678576261791923924405 869969866524542992867913)
    ·
      refine ⟨652477399893407244650935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 869969866524542992867913 652477399893407244650935)
      ·
        refine ⟨978716099840110866976403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652477399893407244650935 978716099840110866976403)
        ·
          refine ⟨1468074149760166300464605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 978716099840110866976403 1468074149760166300464605)
          ·
            refine ⟨550527806160062362674227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1468074149760166300464605 550527806160062362674227)
            ·
              refine ⟨825791709240093544011341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550527806160062362674227 825791709240093544011341)
              ·
                refine ⟨309671890965035079004253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 825791709240093544011341 309671890965035079004253)
                ·
                  refine ⟨116126959111888154626595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309671890965035079004253 116126959111888154626595)
                  ·
                    rfl

theorem cell21_508852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_508852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_508852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_508852 prefixEnd_508852 := by exact prefixLift 508852
  have htrace : WordTrace (prefixWord ++ tailWord_508852) baseStart_508852 baseEnd_508852 := by
    simpa [prefixWord, tailWord_508852, baseEnd_508852] using wordTrace_append hprefix tailTrace_508852
  have hstable : (prefixWord ++ tailWord_508852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508852).length < 2 ^ (prefixWord ++ tailWord_508852).sum := by decide
  have hdescent : baseEnd_508852 < baseStart_508852 := by decide
  rcases family_descends (prefixWord ++ tailWord_508852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508984 : List Nat := [2, 1, 2, 1, 5, 3, 1, 2, 4]
def baseStart_508984 : Nat := 118140960795 + 508984 * 2 ^ 59
def prefixEnd_508984 : Nat := 4983230072969 + 3 ^ 40 * 508984 * 2
def baseEnd_508984 : Nat := 116157083310285258426325

theorem tailTrace_508984 : CollatzResearch.WordTrace tailWord_508984 prefixEnd_508984 116157083310285258426325 := by
  unfold tailWord_508984
  simp only [CollatzResearch.WordTrace]
  refine ⟨9282085794022685195827003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12376114392030246927769337 9282085794022685195827003)
  ·
    refine ⟨13923128691034027793740505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9282085794022685195827003 13923128691034027793740505)
    ·
      refine ⟨10442346518275520845305379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13923128691034027793740505 10442346518275520845305379)
      ·
        refine ⟨15663519777413281267958069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10442346518275520845305379 15663519777413281267958069)
        ·
          refine ⟨1468454979132495118871069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15663519777413281267958069 1468454979132495118871069)
          ·
            refine ⟨550670617174685669576651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1468454979132495118871069 550670617174685669576651)
            ·
              refine ⟨826005925762028504364977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550670617174685669576651 826005925762028504364977)
              ·
                refine ⟨619504444321521378273733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826005925762028504364977 619504444321521378273733)
                ·
                  refine ⟨116157083310285258426325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 619504444321521378273733 116157083310285258426325)
                  ·
                    rfl

theorem cell21_508984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 4].length) (baseStart_508984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_508984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_508984 prefixEnd_508984 := by exact prefixLift 508984
  have htrace : WordTrace (prefixWord ++ tailWord_508984) baseStart_508984 baseEnd_508984 := by
    simpa [prefixWord, tailWord_508984, baseEnd_508984] using wordTrace_append hprefix tailTrace_508984
  have hstable : (prefixWord ++ tailWord_508984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508984).length < 2 ^ (prefixWord ++ tailWord_508984).sum := by decide
  have hdescent : baseEnd_508984 < baseStart_508984 := by decide
  rcases family_descends (prefixWord ++ tailWord_508984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509012 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 5]
def baseStart_509012 : Nat := 118140960795 + 509012 * 2 ^ 59
def prefixEnd_509012 : Nat := 4983230072969 + 3 ^ 40 * 509012 * 2
def baseEnd_509012 : Nat := 116163473291763431959601

theorem tailTrace_509012 : CollatzResearch.WordTrace tailWord_509012 prefixEnd_509012 116163473291763431959601 := by
  unfold tailWord_509012
  simp only [CollatzResearch.WordTrace]
  refine ⟨9282596415971965586836645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12376795221295954115782193 9282596415971965586836645)
  ·
    refine ⟨1740486827994743547531871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9282596415971965586836645 1740486827994743547531871)
    ·
      refine ⟨2610730241992115321297807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1740486827994743547531871 2610730241992115321297807)
      ·
        refine ⟨3916095362988172981946711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2610730241992115321297807 3916095362988172981946711)
        ·
          refine ⟨5874143044482259472920067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3916095362988172981946711 5874143044482259472920067)
          ·
            refine ⟨8811214566723389209380101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5874143044482259472920067 8811214566723389209380101)
            ·
              refine ⟨1652102731260635476758769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8811214566723389209380101 1652102731260635476758769)
              ·
                refine ⟨1239077048445476607569077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1652102731260635476758769 1239077048445476607569077)
                ·
                  refine ⟨116163473291763431959601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1239077048445476607569077 116163473291763431959601)
                  ·
                    rfl

theorem cell21_509012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_509012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509012 prefixEnd_509012 := by exact prefixLift 509012
  have htrace : WordTrace (prefixWord ++ tailWord_509012) baseStart_509012 baseEnd_509012 := by
    simpa [prefixWord, tailWord_509012, baseEnd_509012] using wordTrace_append hprefix tailTrace_509012
  have hstable : (prefixWord ++ tailWord_509012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509012).length < 2 ^ (prefixWord ++ tailWord_509012).sum := by decide
  have hdescent : baseEnd_509012 < baseStart_509012 := by decide
  rcases family_descends (prefixWord ++ tailWord_509012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509057 : List Nat := [1, 2, 4, 2, 2, 1, 1, 8]
def baseStart_509057 : Nat := 118140960795 + 509057 * 2 ^ 59
def prefixEnd_509057 : Nat := 4983230072969 + 3 ^ 40 * 509057 * 2
def baseEnd_509057 : Nat := 38724580968284451236503

theorem tailTrace_509057 : CollatzResearch.WordTrace tailWord_509057 prefixEnd_509057 38724580968284451236503 := by
  unfold tailWord_509057
  simp only [CollatzResearch.WordTrace]
  refine ⟨18566834116780903859061425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12377889411187269239374283 18566834116780903859061425)
  ·
    refine ⟨13925125587585677894296069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18566834116780903859061425 13925125587585677894296069)
    ·
      refine ⟨2610961047672314605180513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13925125587585677894296069 2610961047672314605180513)
      ·
        refine ⟨1958220785754235953885385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2610961047672314605180513 1958220785754235953885385)
        ·
          refine ⟨1468665589315676965414039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1958220785754235953885385 1468665589315676965414039)
          ·
            refine ⟨2202998383973515448121059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468665589315676965414039 2202998383973515448121059)
            ·
              refine ⟨3304497575960273172181589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2202998383973515448121059 3304497575960273172181589)
              ·
                refine ⟨38724580968284451236503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3304497575960273172181589 38724580968284451236503)
                ·
                  rfl

theorem cell21_509057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 8].length) (baseStart_509057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509057 prefixEnd_509057 := by exact prefixLift 509057
  have htrace : WordTrace (prefixWord ++ tailWord_509057) baseStart_509057 baseEnd_509057 := by
    simpa [prefixWord, tailWord_509057, baseEnd_509057] using wordTrace_append hprefix tailTrace_509057
  have hstable : (prefixWord ++ tailWord_509057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509057).length < 2 ^ (prefixWord ++ tailWord_509057).sum := by decide
  have hdescent : baseEnd_509057 < baseStart_509057 := by decide
  rcases family_descends (prefixWord ++ tailWord_509057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509060 : List Nat := [2, 3, 2, 1, 2, 2, 4, 1, 4]
def baseStart_509060 : Nat := 118140960795 + 509060 * 2 ^ 59
def prefixEnd_509060 : Nat := 4983230072969 + 3 ^ 40 * 509060 * 2
def baseEnd_509060 : Nat := 116174427545726015159503

theorem tailTrace_509060 : CollatzResearch.WordTrace tailWord_509060 prefixEnd_509060 116174427545726015159503 := by
  unfold tailWord_509060
  simp only [CollatzResearch.WordTrace]
  refine ⟨9283471767885017685710317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12377962357180023580947089 9283471767885017685710317)
  ·
    refine ⟨3481301912956881632141369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9283471767885017685710317 3481301912956881632141369)
    ·
      refine ⟨2610976434717661224106027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3481301912956881632141369 2610976434717661224106027)
      ·
        refine ⟨3916464652076491836159041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2610976434717661224106027 3916464652076491836159041)
        ·
          refine ⟨2937348489057368877119281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3916464652076491836159041 2937348489057368877119281)
          ·
            refine ⟨2203011366793026657839461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2937348489057368877119281 2203011366793026657839461)
            ·
              refine ⟨413064631273692498344899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2203011366793026657839461 413064631273692498344899)
              ·
                refine ⟨619596946910538747517349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413064631273692498344899 619596946910538747517349)
                ·
                  refine ⟨116174427545726015159503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 619596946910538747517349 116174427545726015159503)
                  ·
                    rfl

theorem cell21_509060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_509060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509060 prefixEnd_509060 := by exact prefixLift 509060
  have htrace : WordTrace (prefixWord ++ tailWord_509060) baseStart_509060 baseEnd_509060 := by
    simpa [prefixWord, tailWord_509060, baseEnd_509060] using wordTrace_append hprefix tailTrace_509060
  have hstable : (prefixWord ++ tailWord_509060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509060).length < 2 ^ (prefixWord ++ tailWord_509060).sum := by decide
  have hdescent : baseEnd_509060 < baseStart_509060 := by decide
  rcases family_descends (prefixWord ++ tailWord_509060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509164 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 5]
def baseStart_509164 : Nat := 118140960795 + 509164 * 2 ^ 59
def prefixEnd_509164 : Nat := 4983230072969 + 3 ^ 40 * 509164 * 2
def baseEnd_509164 : Nat := 116198161762644945425957

theorem tailTrace_509164 : CollatzResearch.WordTrace tailWord_509164 prefixEnd_509164 116198161762644945425957 := by
  unfold tailWord_509164
  simp only [CollatzResearch.WordTrace]
  refine ⟨9285368363696630566603273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12380491151595507422137697 9285368363696630566603273)
  ·
    refine ⟨6964026272772472924952455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9285368363696630566603273 6964026272772472924952455)
    ·
      refine ⟨10446039409158709387428683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6964026272772472924952455 10446039409158709387428683)
      ·
        refine ⟨15669059113738064081143025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10446039409158709387428683 15669059113738064081143025)
        ·
          refine ⟨11751794335303548060857269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15669059113738064081143025 11751794335303548060857269)
          ·
            refine ⟨1101730718934707630705369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11751794335303548060857269 1101730718934707630705369)
            ·
              refine ⟨826298039201030723029027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1101730718934707630705369 826298039201030723029027)
              ·
                refine ⟨1239447058801546084543541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826298039201030723029027 1239447058801546084543541)
                ·
                  refine ⟨116198161762644945425957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1239447058801546084543541 116198161762644945425957)
                  ·
                    rfl

theorem cell21_509164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_509164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509164 prefixEnd_509164 := by exact prefixLift 509164
  have htrace : WordTrace (prefixWord ++ tailWord_509164) baseStart_509164 baseEnd_509164 := by
    simpa [prefixWord, tailWord_509164, baseEnd_509164] using wordTrace_append hprefix tailTrace_509164
  have hstable : (prefixWord ++ tailWord_509164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509164).length < 2 ^ (prefixWord ++ tailWord_509164).sum := by decide
  have hdescent : baseEnd_509164 < baseStart_509164 := by decide
  rcases family_descends (prefixWord ++ tailWord_509164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509198 : List Nat := [4, 1, 1, 2, 1, 5, 1, 3, 3]
def baseStart_509198 : Nat := 118140960795 + 509198 * 2 ^ 59
def prefixEnd_509198 : Nat := 4983230072969 + 3 ^ 40 * 509198 * 2
def baseEnd_509198 : Nat := 116205921025868441859221

theorem tailTrace_509198 : CollatzResearch.WordTrace tailWord_509198 prefixEnd_509198 116205921025868441859221 := by
  unfold tailWord_509198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2321497101158760617493031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12381317872846723293296165 2321497101158760617493031)
  ·
    refine ⟨3482245651738140926239547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2321497101158760617493031 3482245651738140926239547)
    ·
      refine ⟨5223368477607211389359321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3482245651738140926239547 5223368477607211389359321)
      ·
        refine ⟨3917526358205408542019491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5223368477607211389359321 3917526358205408542019491)
        ·
          refine ⟨5876289537308112813029237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3917526358205408542019491 5876289537308112813029237)
          ·
            refine ⟨550902144122635576221491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5876289537308112813029237 550902144122635576221491)
            ·
              refine ⟨826353216183953364332237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550902144122635576221491 826353216183953364332237)
              ·
                refine ⟨309882456068982511624589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 826353216183953364332237 309882456068982511624589)
                ·
                  refine ⟨116205921025868441859221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309882456068982511624589 116205921025868441859221)
                  ·
                    rfl

theorem cell21_509198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_509198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509198 prefixEnd_509198 := by exact prefixLift 509198
  have htrace : WordTrace (prefixWord ++ tailWord_509198) baseStart_509198 baseEnd_509198 := by
    simpa [prefixWord, tailWord_509198, baseEnd_509198] using wordTrace_append hprefix tailTrace_509198
  have hstable : (prefixWord ++ tailWord_509198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509198).length < 2 ^ (prefixWord ++ tailWord_509198).sum := by decide
  have hdescent : baseEnd_509198 < baseStart_509198 := by decide
  rcases family_descends (prefixWord ++ tailWord_509198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509226 : List Nat := [3, 1, 4, 2, 1, 2, 2, 6]
def baseStart_509226 : Nat := 118140960795 + 509226 * 2 ^ 59
def prefixEnd_509226 : Nat := 4983230072969 + 3 ^ 40 * 509226 * 2
def baseEnd_509226 : Nat := 38737437002448871797499

theorem tailTrace_509226 : CollatzResearch.WordTrace tailWord_509226 prefixEnd_509226 38737437002448871797499 := by
  unfold tailWord_509226
  simp only [CollatzResearch.WordTrace]
  refine ⟨4643249513292161430490883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12381998702112430481309021 4643249513292161430490883)
  ·
    refine ⟨6964874269938242145736325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4643249513292161430490883 6964874269938242145736325)
    ·
      refine ⟨1305913925613420402325561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6964874269938242145736325 1305913925613420402325561)
      ·
        refine ⟨979435444210065301744171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1305913925613420402325561 979435444210065301744171)
        ·
          refine ⟨1469153166315097952616257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979435444210065301744171 1469153166315097952616257)
          ·
            refine ⟨1101864874736323464462193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1469153166315097952616257 1101864874736323464462193)
            ·
              refine ⟨826398656052242598346645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1101864874736323464462193 826398656052242598346645)
              ·
                refine ⟨38737437002448871797499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 826398656052242598346645 38737437002448871797499)
                ·
                  rfl

theorem cell21_509226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_509226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509226 prefixEnd_509226 := by exact prefixLift 509226
  have htrace : WordTrace (prefixWord ++ tailWord_509226) baseStart_509226 baseEnd_509226 := by
    simpa [prefixWord, tailWord_509226, baseEnd_509226] using wordTrace_append hprefix tailTrace_509226
  have hstable : (prefixWord ++ tailWord_509226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509226).length < 2 ^ (prefixWord ++ tailWord_509226).sum := by decide
  have hdescent : baseEnd_509226 < baseStart_509226 := by decide
  rcases family_descends (prefixWord ++ tailWord_509226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509229 : List Nat := [1, 5, 3, 1, 1, 1, 4, 1, 4]
def baseStart_509229 : Nat := 118140960795 + 509229 * 2 ^ 59
def prefixEnd_509229 : Nat := 4983230072969 + 3 ^ 40 * 509229 * 2
def baseEnd_509229 : Nat := 116212995648219276842491

theorem tailTrace_509229 : CollatzResearch.WordTrace tailWord_509229 prefixEnd_509229 116212995648219276842491 := by
  unfold tailWord_509229
  simp only [CollatzResearch.WordTrace]
  refine ⟨18573107472157777234322741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12382071648105184822881827 18573107472157777234322741)
  ·
    refine ⟨1741228825514791615717757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18573107472157777234322741 1741228825514791615717757)
    ·
      refine ⟨652960809568046855894159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1741228825514791615717757 652960809568046855894159)
      ·
        refine ⟨979441214352070283841239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652960809568046855894159 979441214352070283841239)
        ·
          refine ⟨1469161821528105425761859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979441214352070283841239 1469161821528105425761859)
          ·
            refine ⟨2203742732292158138642789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469161821528105425761859 2203742732292158138642789)
            ·
              refine ⟨413201762304779650995523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2203742732292158138642789 413201762304779650995523)
              ·
                refine ⟨619802643457169476493285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413201762304779650995523 619802643457169476493285)
                ·
                  refine ⟨116212995648219276842491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 619802643457169476493285 116212995648219276842491)
                  ·
                    rfl

theorem cell21_509229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_509229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509229 prefixEnd_509229 := by exact prefixLift 509229
  have htrace : WordTrace (prefixWord ++ tailWord_509229) baseStart_509229 baseEnd_509229 := by
    simpa [prefixWord, tailWord_509229, baseEnd_509229] using wordTrace_append hprefix tailTrace_509229
  have hstable : (prefixWord ++ tailWord_509229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509229).length < 2 ^ (prefixWord ++ tailWord_509229).sum := by decide
  have hdescent : baseEnd_509229 < baseStart_509229 := by decide
  rcases family_descends (prefixWord ++ tailWord_509229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509271 : List Nat := [1, 1, 3, 2, 3, 3, 2, 2, 4]
def baseStart_509271 : Nat := 118140960795 + 509271 * 2 ^ 59
def prefixEnd_509271 : Nat := 4983230072969 + 3 ^ 40 * 509271 * 2
def baseEnd_509271 : Nat := 116222580620436537142405

theorem tailTrace_509271 : CollatzResearch.WordTrace tailWord_509271 prefixEnd_509271 116222580620436537142405 := by
  unfold tailWord_509271
  simp only [CollatzResearch.WordTrace]
  refine ⟨18574639338005618407351667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12383092892003745604901111 18574639338005618407351667)
  ·
    refine ⟨27861959007008427611027501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18574639338005618407351667 27861959007008427611027501)
    ·
      refine ⟨10448234627628160354135313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27861959007008427611027501 10448234627628160354135313)
      ·
        refine ⟨7836175970721120265601485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10448234627628160354135313 7836175970721120265601485)
        ·
          refine ⟨2938565989020420099600557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7836175970721120265601485 2938565989020420099600557)
          ·
            refine ⟨1101962245882657537350209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2938565989020420099600557 1101962245882657537350209)
            ·
              refine ⟨826471684411993153012657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1101962245882657537350209 826471684411993153012657)
              ·
                refine ⟨619853763308994864759493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826471684411993153012657 619853763308994864759493)
                ·
                  refine ⟨116222580620436537142405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 619853763308994864759493 116222580620436537142405)
                  ·
                    rfl

theorem cell21_509271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 4].length) (baseStart_509271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509271 prefixEnd_509271 := by exact prefixLift 509271
  have htrace : WordTrace (prefixWord ++ tailWord_509271) baseStart_509271 baseEnd_509271 := by
    simpa [prefixWord, tailWord_509271, baseEnd_509271] using wordTrace_append hprefix tailTrace_509271
  have hstable : (prefixWord ++ tailWord_509271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509271).length < 2 ^ (prefixWord ++ tailWord_509271).sum := by decide
  have hdescent : baseEnd_509271 < baseStart_509271 := by decide
  rcases family_descends (prefixWord ++ tailWord_509271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509277 : List Nat := [1, 4, 5, 1, 2, 1, 1, 6]
def baseStart_509277 : Nat := 118140960795 + 509277 * 2 ^ 59
def prefixEnd_509277 : Nat := 4983230072969 + 3 ^ 40 * 509277 * 2
def baseEnd_509277 : Nat := 38741316634060620014131

theorem tailTrace_509277 : CollatzResearch.WordTrace tailWord_509277 prefixEnd_509277 38741316634060620014131 := by
  unfold tailWord_509277
  simp only [CollatzResearch.WordTrace]
  refine ⟨18574858175983881432070085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12383238783989254288046723 18574858175983881432070085)
  ·
    refine ⟨3482785907996977768513141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18574858175983881432070085 3482785907996977768513141)
    ·
      refine ⟨326511178874716665798107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3482785907996977768513141 326511178874716665798107)
      ·
        refine ⟨489766768312074998697161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326511178874716665798107 489766768312074998697161)
        ·
          refine ⟨367325076234056249022871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489766768312074998697161 367325076234056249022871)
          ·
            refine ⟨550987614351084373534307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367325076234056249022871 550987614351084373534307)
            ·
              refine ⟨826481421526626560301461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550987614351084373534307 826481421526626560301461)
              ·
                refine ⟨38741316634060620014131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 826481421526626560301461 38741316634060620014131)
                ·
                  rfl

theorem cell21_509277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 6].length) (baseStart_509277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509277 prefixEnd_509277 := by exact prefixLift 509277
  have htrace : WordTrace (prefixWord ++ tailWord_509277) baseStart_509277 baseEnd_509277 := by
    simpa [prefixWord, tailWord_509277, baseEnd_509277] using wordTrace_append hprefix tailTrace_509277
  have hstable : (prefixWord ++ tailWord_509277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509277).length < 2 ^ (prefixWord ++ tailWord_509277).sum := by decide
  have hdescent : baseEnd_509277 < baseStart_509277 := by decide
  rcases family_descends (prefixWord ++ tailWord_509277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509344 : List Nat := [2, 1, 1, 4, 1, 2, 2, 8]
def baseStart_509344 : Nat := 118140960795 + 509344 * 2 ^ 59
def prefixEnd_509344 : Nat := 4983230072969 + 3 ^ 40 * 509344 * 2
def baseEnd_509344 : Nat := 38746413405001544141863

theorem tailTrace_509344 : CollatzResearch.WordTrace tailWord_509344 prefixEnd_509344 38746413405001544141863 := by
  unfold tailWord_509344
  simp only [CollatzResearch.WordTrace]
  refine ⟨9288650933370575937379543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12384867911160767916506057 9288650933370575937379543)
  ·
    refine ⟨13932976400055863906069315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9288650933370575937379543 13932976400055863906069315)
    ·
      refine ⟨20899464600083795859103973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13932976400055863906069315 20899464600083795859103973)
      ·
        refine ⟨3918649612515711723581995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20899464600083795859103973 3918649612515711723581995)
        ·
          refine ⟨5877974418773567585372993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3918649612515711723581995 5877974418773567585372993)
          ·
            refine ⟨4408480814080175689029745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5877974418773567585372993 4408480814080175689029745)
            ·
              refine ⟨3306360610560131766772309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4408480814080175689029745 3306360610560131766772309)
              ·
                refine ⟨38746413405001544141863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3306360610560131766772309 38746413405001544141863)
                ·
                  rfl

theorem cell21_509344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 8].length) (baseStart_509344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509344 prefixEnd_509344 := by exact prefixLift 509344
  have htrace : WordTrace (prefixWord ++ tailWord_509344) baseStart_509344 baseEnd_509344 := by
    simpa [prefixWord, tailWord_509344, baseEnd_509344] using wordTrace_append hprefix tailTrace_509344
  have hstable : (prefixWord ++ tailWord_509344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509344).length < 2 ^ (prefixWord ++ tailWord_509344).sum := by decide
  have hdescent : baseEnd_509344 < baseStart_509344 := by decide
  rcases family_descends (prefixWord ++ tailWord_509344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509347 : List Nat := [1, 1, 1, 4, 1, 3, 5, 1, 4]
def baseStart_509347 : Nat := 118140960795 + 509347 * 2 ^ 59
def prefixEnd_509347 : Nat := 4983230072969 + 3 ^ 40 * 509347 * 2
def baseEnd_509347 : Nat := 116239924855877293875583

theorem tailTrace_509347 : CollatzResearch.WordTrace tailWord_509347 prefixEnd_509347 116239924855877293875583 := by
  unfold tailWord_509347
  simp only [CollatzResearch.WordTrace]
  refine ⟨18577411285730283387118295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12384940857153522258078863 18577411285730283387118295)
  ·
    refine ⟨27866116928595425080677443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18577411285730283387118295 27866116928595425080677443)
    ·
      refine ⟨41799175392893137621016165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27866116928595425080677443 41799175392893137621016165)
      ·
        refine ⟨7837345386167463303940531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41799175392893137621016165 7837345386167463303940531)
        ·
          refine ⟨11756018079251194955910797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7837345386167463303940531 11756018079251194955910797)
          ·
            refine ⟨4408506779719198108466549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11756018079251194955910797 4408506779719198108466549)
            ·
              refine ⟨413297510598674822668739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4408506779719198108466549 413297510598674822668739)
              ·
                refine ⟨619946265898012234003109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413297510598674822668739 619946265898012234003109)
                ·
                  refine ⟨116239924855877293875583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 619946265898012234003109 116239924855877293875583)
                  ·
                    rfl

theorem cell21_509347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 4].length) (baseStart_509347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509347 prefixEnd_509347 := by exact prefixLift 509347
  have htrace : WordTrace (prefixWord ++ tailWord_509347) baseStart_509347 baseEnd_509347 := by
    simpa [prefixWord, tailWord_509347, baseEnd_509347] using wordTrace_append hprefix tailTrace_509347
  have hstable : (prefixWord ++ tailWord_509347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509347).length < 2 ^ (prefixWord ++ tailWord_509347).sum := by decide
  have hdescent : baseEnd_509347 < baseStart_509347 := by decide
  rcases family_descends (prefixWord ++ tailWord_509347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509454 : List Nat := [4, 1, 1, 2, 4, 2, 1, 6]
def baseStart_509454 : Nat := 118140960795 + 509454 * 2 ^ 59
def prefixEnd_509454 : Nat := 4983230072969 + 3 ^ 40 * 509454 * 2
def baseEnd_509454 : Nat := 38754781237889628530677

theorem tailTrace_509454 : CollatzResearch.WordTrace tailWord_509454 prefixEnd_509454 38754781237889628530677 := by
  unfold tailWord_509454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2322664237042830082657927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12387542597561760440842277 2322664237042830082657927)
  ·
    refine ⟨3483996355564245123986891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2322664237042830082657927 3483996355564245123986891)
    ·
      refine ⟨5225994533346367685980337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3483996355564245123986891 5225994533346367685980337)
      ·
        refine ⟨3919495900009775764485253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5225994533346367685980337 3919495900009775764485253)
        ·
          refine ⟨734905481251832955840985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3919495900009775764485253 734905481251832955840985)
          ·
            refine ⟨551179110938874716880739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 734905481251832955840985 551179110938874716880739)
            ·
              refine ⟨826768666408312075321109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551179110938874716880739 826768666408312075321109)
              ·
                refine ⟨38754781237889628530677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 826768666408312075321109 38754781237889628530677)
                ·
                  rfl

theorem cell21_509454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_509454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509454 prefixEnd_509454 := by exact prefixLift 509454
  have htrace : WordTrace (prefixWord ++ tailWord_509454) baseStart_509454 baseEnd_509454 := by
    simpa [prefixWord, tailWord_509454, baseEnd_509454] using wordTrace_append hprefix tailTrace_509454
  have hstable : (prefixWord ++ tailWord_509454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509454).length < 2 ^ (prefixWord ++ tailWord_509454).sum := by decide
  have hdescent : baseEnd_509454 < baseStart_509454 := by decide
  rcases family_descends (prefixWord ++ tailWord_509454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509482 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 6]
def baseStart_509482 : Nat := 118140960795 + 509482 * 2 ^ 59
def prefixEnd_509482 : Nat := 4983230072969 + 3 ^ 40 * 509482 * 2
def baseEnd_509482 : Nat := 116270733695147059125307

theorem tailTrace_509482 : CollatzResearch.WordTrace tailWord_509482 prefixEnd_509482 116270733695147059125307 := by
  unfold tailWord_509482
  simp only [CollatzResearch.WordTrace]
  refine ⟨4645583785060300360820675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12388223426827467628855133 4645583785060300360820675)
  ·
    refine ⟨6968375677590450541231013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4645583785060300360820675 6968375677590450541231013)
    ·
      refine ⟨1306570439548209476480815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6968375677590450541231013 1306570439548209476480815)
      ·
        refine ⟨1959855659322314214721223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1306570439548209476480815 1959855659322314214721223)
        ·
          refine ⟨2939783488983471322081835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1959855659322314214721223 2939783488983471322081835)
          ·
            refine ⟨4409675233475206983122753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2939783488983471322081835 4409675233475206983122753)
            ·
              refine ⟨3307256425106405237342065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4409675233475206983122753 3307256425106405237342065)
              ·
                refine ⟨2480442318829803928006549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3307256425106405237342065 2480442318829803928006549)
                ·
                  refine ⟨116270733695147059125307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2480442318829803928006549 116270733695147059125307)
                  ·
                    rfl

theorem cell21_509482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_509482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509482 prefixEnd_509482 := by exact prefixLift 509482
  have htrace : WordTrace (prefixWord ++ tailWord_509482) baseStart_509482 baseEnd_509482 := by
    simpa [prefixWord, tailWord_509482, baseEnd_509482] using wordTrace_append hprefix tailTrace_509482
  have hstable : (prefixWord ++ tailWord_509482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509482).length < 2 ^ (prefixWord ++ tailWord_509482).sum := by decide
  have hdescent : baseEnd_509482 < baseStart_509482 := by decide
  rcases family_descends (prefixWord ++ tailWord_509482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509496 : List Nat := [2, 1, 2, 1, 4, 3, 8]
def baseStart_509496 : Nat := 118140960795 + 509496 * 2 ^ 59
def prefixEnd_509496 : Nat := 4983230072969 + 3 ^ 40 * 509496 * 2
def baseEnd_509496 : Nat := 12919325409542905099105

theorem tailTrace_509496 : CollatzResearch.WordTrace tailWord_509496 prefixEnd_509496 12919325409542905099105 := by
  unfold tailWord_509496
  simp only [CollatzResearch.WordTrace]
  refine ⟨9291422881095240917146171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12388563841460321222861561 9291422881095240917146171)
  ·
    refine ⟨13937134321642861375719257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9291422881095240917146171 13937134321642861375719257)
    ·
      refine ⟨10452850741232146031789443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13937134321642861375719257 10452850741232146031789443)
      ·
        refine ⟨15679276111848219047684165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10452850741232146031789443 15679276111848219047684165)
        ·
          refine ⟨2939864270971541071440781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15679276111848219047684165 2939864270971541071440781)
          ·
            refine ⟨1102449101614327901790293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2939864270971541071440781 1102449101614327901790293)
            ·
              refine ⟨12919325409542905099105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1102449101614327901790293 12919325409542905099105)
              ·
                rfl

theorem cell21_509496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 8].length) (baseStart_509496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509496 prefixEnd_509496 := by exact prefixLift 509496
  have htrace : WordTrace (prefixWord ++ tailWord_509496) baseStart_509496 baseEnd_509496 := by
    simpa [prefixWord, tailWord_509496, baseEnd_509496] using wordTrace_append hprefix tailTrace_509496
  have hstable : (prefixWord ++ tailWord_509496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509496).length < 2 ^ (prefixWord ++ tailWord_509496).sum := by decide
  have hdescent : baseEnd_509496 < baseStart_509496 := by decide
  rcases family_descends (prefixWord ++ tailWord_509496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509527 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 5]
def baseStart_509527 : Nat := 118140960795 + 509527 * 2 ^ 59
def prefixEnd_509527 : Nat := 4983230072969 + 3 ^ 40 * 509527 * 2
def baseEnd_509527 : Nat := 116281003308236980875215

theorem tailTrace_509527 : CollatzResearch.WordTrace tailWord_509527 prefixEnd_509527 116281003308236980875215 := by
  unfold tailWord_509527
  simp only [CollatzResearch.WordTrace]
  refine ⟨18583976425078174128670835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12389317616718782752447223 18583976425078174128670835)
  ·
    refine ⟨27875964637617261193006253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18583976425078174128670835 27875964637617261193006253)
    ·
      refine ⟨10453486739106472947377345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27875964637617261193006253 10453486739106472947377345)
      ·
        refine ⟨7840115054329854710533009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10453486739106472947377345 7840115054329854710533009)
        ·
          refine ⟨5880086290747391032899757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7840115054329854710533009 5880086290747391032899757)
          ·
            refine ⟨2205032359030271637337409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5880086290747391032899757 2205032359030271637337409)
            ·
              refine ⟨1653774269272703728003057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2205032359030271637337409 1653774269272703728003057)
              ·
                refine ⟨1240330701954527796002293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1653774269272703728003057 1240330701954527796002293)
                ·
                  refine ⟨116281003308236980875215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1240330701954527796002293 116281003308236980875215)
                  ·
                    rfl

theorem cell21_509527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 5].length) (baseStart_509527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509527 prefixEnd_509527 := by exact prefixLift 509527
  have htrace : WordTrace (prefixWord ++ tailWord_509527) baseStart_509527 baseEnd_509527 := by
    simpa [prefixWord, tailWord_509527, baseEnd_509527] using wordTrace_append hprefix tailTrace_509527
  have hstable : (prefixWord ++ tailWord_509527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509527).length < 2 ^ (prefixWord ++ tailWord_509527).sum := by decide
  have hdescent : baseEnd_509527 < baseStart_509527 := by decide
  rcases family_descends (prefixWord ++ tailWord_509527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509561 : List Nat := [1, 2, 1, 3, 3, 1, 5, 2, 3]
def baseStart_509561 : Nat := 118140960795 + 509561 * 2 ^ 59
def prefixEnd_509561 : Nat := 4983230072969 + 3 ^ 40 * 509561 * 2
def baseEnd_509561 : Nat := 116288762571460477308479

theorem tailTrace_509561 : CollatzResearch.WordTrace tailWord_509561 prefixEnd_509561 116288762571460477308479 := by
  unfold tailWord_509561
  simp only [CollatzResearch.WordTrace]
  refine ⟨18585216506954997935408537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12390144337969998623605691 18585216506954997935408537)
  ·
    refine ⟨13938912380216248451556403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18585216506954997935408537 13938912380216248451556403)
    ·
      refine ⟨20908368570324372677334605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13938912380216248451556403 20908368570324372677334605)
      ·
        refine ⟨7840638213871639754000477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20908368570324372677334605 7840638213871639754000477)
        ·
          refine ⟨2940239330201864907750179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7840638213871639754000477 2940239330201864907750179)
          ·
            refine ⟨4410358995302797361625269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940239330201864907750179 4410358995302797361625269)
            ·
              refine ⟨413471155809637252652369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4410358995302797361625269 413471155809637252652369)
              ·
                refine ⟨310103366857227939489277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413471155809637252652369 310103366857227939489277)
                ·
                  refine ⟨116288762571460477308479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310103366857227939489277 116288762571460477308479)
                  ·
                    rfl

theorem cell21_509561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 3].length) (baseStart_509561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509561 prefixEnd_509561 := by exact prefixLift 509561
  have htrace : WordTrace (prefixWord ++ tailWord_509561) baseStart_509561 baseEnd_509561 := by
    simpa [prefixWord, tailWord_509561, baseEnd_509561] using wordTrace_append hprefix tailTrace_509561
  have hstable : (prefixWord ++ tailWord_509561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509561).length < 2 ^ (prefixWord ++ tailWord_509561).sum := by decide
  have hdescent : baseEnd_509561 < baseStart_509561 := by decide
  rcases family_descends (prefixWord ++ tailWord_509561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509575 : List Nat := [1, 1, 4, 2, 1, 3, 4, 1, 4]
def baseStart_509575 : Nat := 118140960795 + 509575 * 2 ^ 59
def prefixEnd_509575 : Nat := 4983230072969 + 3 ^ 40 * 509575 * 2
def baseEnd_509575 : Nat := 116291957562199564075117

theorem tailTrace_509575 : CollatzResearch.WordTrace tailWord_509575 prefixEnd_509575 116291957562199564075117 := by
  unfold tailWord_509575
  simp only [CollatzResearch.WordTrace]
  refine ⟨18585727128904278326418179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12390484752602852217612119 18585727128904278326418179)
  ·
    refine ⟨27878590693356417489627269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18585727128904278326418179 27878590693356417489627269)
    ·
      refine ⟨5227235755004328279305113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27878590693356417489627269 5227235755004328279305113)
      ·
        refine ⟨3920426816253246209478835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5227235755004328279305113 3920426816253246209478835)
        ·
          refine ⟨5880640224379869314218253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3920426816253246209478835 5880640224379869314218253)
          ·
            refine ⟨2205240084142450992831845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5880640224379869314218253 2205240084142450992831845)
            ·
              refine ⟨413482515776709561155971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2205240084142450992831845 413482515776709561155971)
              ·
                refine ⟨620223773665064341733957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413482515776709561155971 620223773665064341733957)
                ·
                  refine ⟨116291957562199564075117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 620223773665064341733957 116291957562199564075117)
                  ·
                    rfl

theorem cell21_509575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 4].length) (baseStart_509575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509575 prefixEnd_509575 := by exact prefixLift 509575
  have htrace : WordTrace (prefixWord ++ tailWord_509575) baseStart_509575 baseEnd_509575 := by
    simpa [prefixWord, tailWord_509575, baseEnd_509575] using wordTrace_append hprefix tailTrace_509575
  have hstable : (prefixWord ++ tailWord_509575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509575).length < 2 ^ (prefixWord ++ tailWord_509575).sum := by decide
  have hdescent : baseEnd_509575 < baseStart_509575 := by decide
  rcases family_descends (prefixWord ++ tailWord_509575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509679 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 5]
def baseStart_509679 : Nat := 118140960795 + 509679 * 2 ^ 59
def prefixEnd_509679 : Nat := 4983230072969 + 3 ^ 40 * 509679 * 2
def baseEnd_509679 : Nat := 116315691779118494341571

theorem tailTrace_509679 : CollatzResearch.WordTrace tailWord_509679 prefixEnd_509679 116315691779118494341571 := by
  unfold tailWord_509679
  simp only [CollatzResearch.WordTrace]
  refine ⟨18589520320527504088204091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12393013547018336058802727 18589520320527504088204091)
  ·
    refine ⟨27884280480791256132306137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18589520320527504088204091 27884280480791256132306137)
    ·
      refine ⟨20913210360593442099229603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27884280480791256132306137 20913210360593442099229603)
      ·
        refine ⟨31369815540890163148844405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20913210360593442099229603 31369815540890163148844405)
        ·
          refine ⟨2940920206958452795204163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31369815540890163148844405 2940920206958452795204163)
          ·
            refine ⟨4411380310437679192806245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940920206958452795204163 4411380310437679192806245)
            ·
              refine ⟨827133808207064848651171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4411380310437679192806245 827133808207064848651171)
              ·
                refine ⟨1240700712310597272976757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827133808207064848651171 1240700712310597272976757)
                ·
                  refine ⟨116315691779118494341571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1240700712310597272976757 116315691779118494341571)
                  ·
                    rfl

theorem cell21_509679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 5].length) (baseStart_509679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509679 prefixEnd_509679 := by exact prefixLift 509679
  have htrace : WordTrace (prefixWord ++ tailWord_509679) baseStart_509679 baseEnd_509679 := by
    simpa [prefixWord, tailWord_509679, baseEnd_509679] using wordTrace_append hprefix tailTrace_509679
  have hstable : (prefixWord ++ tailWord_509679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509679).length < 2 ^ (prefixWord ++ tailWord_509679).sum := by decide
  have hdescent : baseEnd_509679 < baseStart_509679 := by decide
  rcases family_descends (prefixWord ++ tailWord_509679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509716 : List Nat := [2, 4, 4, 1, 2, 1, 7]
def baseStart_509716 : Nat := 118140960795 + 509716 * 2 ^ 59
def prefixEnd_509716 : Nat := 4983230072969 + 3 ^ 40 * 509716 * 2
def baseEnd_509716 : Nat := 12924903964801628024981

theorem tailTrace_509716 : CollatzResearch.WordTrace tailWord_509716 prefixEnd_509716 12924903964801628024981 := by
  unfold tailWord_509716
  simp only [CollatzResearch.WordTrace]
  refine ⟨9295434910696729703650501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12393913214262306271534001 9295434910696729703650501)
  ·
    refine ⟨1742894045755636819434469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9295434910696729703650501 1742894045755636819434469)
    ·
      refine ⟨326792633579181903643963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1742894045755636819434469 326792633579181903643963)
      ·
        refine ⟨490188950368772855465945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326792633579181903643963 490188950368772855465945)
        ·
          refine ⟨367641712776579641599459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490188950368772855465945 367641712776579641599459)
          ·
            refine ⟨551462569164869462399189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367641712776579641599459 551462569164869462399189)
            ·
              refine ⟨12924903964801628024981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 551462569164869462399189 12924903964801628024981)
              ·
                rfl

theorem cell21_509716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 7].length) (baseStart_509716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509716 prefixEnd_509716 := by exact prefixLift 509716
  have htrace : WordTrace (prefixWord ++ tailWord_509716) baseStart_509716 baseEnd_509716 := by
    simpa [prefixWord, tailWord_509716, baseEnd_509716] using wordTrace_append hprefix tailTrace_509716
  have hstable : (prefixWord ++ tailWord_509716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509716).length < 2 ^ (prefixWord ++ tailWord_509716).sum := by decide
  have hdescent : baseEnd_509716 < baseStart_509716 := by decide
  rcases family_descends (prefixWord ++ tailWord_509716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509783 : List Nat := [1, 1, 3, 2, 14]
def baseStart_509783 : Nat := 118140960795 + 509783 * 2 ^ 59
def prefixEnd_509783 : Nat := 4983230072969 + 3 ^ 40 * 509783 * 2
def baseEnd_509783 : Nat := 1436289209827622526025

theorem tailTrace_509783 : CollatzResearch.WordTrace tailWord_509783 prefixEnd_509783 1436289209827622526025 := by
  unfold tailWord_509783
  simp only [CollatzResearch.WordTrace]
  refine ⟨18593313512150729849990003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12395542341433819899993335 18593313512150729849990003)
  ·
    refine ⟨27889970268226094774985005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18593313512150729849990003 27889970268226094774985005)
    ·
      refine ⟨10458738850584785540619377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27889970268226094774985005 10458738850584785540619377)
      ·
        refine ⟨7844054137938589155464533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10458738850584785540619377 7844054137938589155464533)
        ·
          refine ⟨1436289209827622526025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 7844054137938589155464533 1436289209827622526025)
          ·
            rfl

theorem cell21_509783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 14].length) (baseStart_509783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509783 prefixEnd_509783 := by exact prefixLift 509783
  have htrace : WordTrace (prefixWord ++ tailWord_509783) baseStart_509783 baseEnd_509783 := by
    simpa [prefixWord, tailWord_509783, baseEnd_509783] using wordTrace_append hprefix tailTrace_509783
  have hstable : (prefixWord ++ tailWord_509783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509783).length < 2 ^ (prefixWord ++ tailWord_509783).sum := by decide
  have hdescent : baseEnd_509783 < baseStart_509783 := by decide
  rcases family_descends (prefixWord ++ tailWord_509783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509786 : List Nat := [3, 1, 1, 2, 1, 3, 4, 2, 4]
def baseStart_509786 : Nat := 118140960795 + 509786 * 2 ^ 59
def prefixEnd_509786 : Nat := 4983230072969 + 3 ^ 40 * 509786 * 2
def baseEnd_509786 : Nat := 116340110636910086058019

theorem tailTrace_509786 : CollatzResearch.WordTrace tailWord_509786 prefixEnd_509786 116340110636910086058019 := by
  unfold tailWord_509786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4648355732784965340587303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12395615287426574241566141 4648355732784965340587303)
  ·
    refine ⟨6972533599177448010880955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4648355732784965340587303 6972533599177448010880955)
    ·
      refine ⟨10458800398766172016321433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6972533599177448010880955 10458800398766172016321433)
      ·
        refine ⟨7844100299074629012241075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10458800398766172016321433 7844100299074629012241075)
        ·
          refine ⟨11766150448611943518361613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7844100299074629012241075 11766150448611943518361613)
          ·
            refine ⟨4412306418229478819385605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11766150448611943518361613 4412306418229478819385605)
            ·
              refine ⟨827307453418027278634801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4412306418229478819385605 827307453418027278634801)
              ·
                refine ⟨620480590063520458976101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827307453418027278634801 620480590063520458976101)
                ·
                  refine ⟨116340110636910086058019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 620480590063520458976101 116340110636910086058019)
                  ·
                    rfl

theorem cell21_509786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_509786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509786 prefixEnd_509786 := by exact prefixLift 509786
  have htrace : WordTrace (prefixWord ++ tailWord_509786) baseStart_509786 baseEnd_509786 := by
    simpa [prefixWord, tailWord_509786, baseEnd_509786] using wordTrace_append hprefix tailTrace_509786
  have hstable : (prefixWord ++ tailWord_509786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509786).length < 2 ^ (prefixWord ++ tailWord_509786).sum := by decide
  have hdescent : baseEnd_509786 < baseStart_509786 := by decide
  rcases family_descends (prefixWord ++ tailWord_509786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509845 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 6]
def baseStart_509845 : Nat := 118140960795 + 509845 * 2 ^ 59
def prefixEnd_509845 : Nat := 4983230072969 + 3 ^ 40 * 509845 * 2
def baseEnd_509845 : Nat := 116353575240739094574565

theorem tailTrace_509845 : CollatzResearch.WordTrace tailWord_509845 prefixEnd_509845 116353575240739094574565 := by
  unfold tailWord_509845
  simp only [CollatzResearch.WordTrace]
  refine ⟨18595574837926114438746989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12397049891950742959164659 18595574837926114438746989)
  ·
    refine ⟨6973340564222292914530121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18595574837926114438746989 6973340564222292914530121)
    ·
      refine ⟨5230005423166719685897591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6973340564222292914530121 5230005423166719685897591)
      ·
        refine ⟨7845008134750079528846387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5230005423166719685897591 7845008134750079528846387)
        ·
          refine ⟨11767512202125119293269581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7845008134750079528846387 11767512202125119293269581)
          ·
            refine ⟨4412817075796919734976093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11767512202125119293269581 4412817075796919734976093)
            ·
              refine ⟨1654806403423844900616035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4412817075796919734976093 1654806403423844900616035)
              ·
                refine ⟨2482209605135767350924053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1654806403423844900616035 2482209605135767350924053)
                ·
                  refine ⟨116353575240739094574565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2482209605135767350924053 116353575240739094574565)
                  ·
                    rfl

theorem cell21_509845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_509845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509845 prefixEnd_509845 := by exact prefixLift 509845
  have htrace : WordTrace (prefixWord ++ tailWord_509845) baseStart_509845 baseEnd_509845 := by
    simpa [prefixWord, tailWord_509845, baseEnd_509845] using wordTrace_append hprefix tailTrace_509845
  have hstable : (prefixWord ++ tailWord_509845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509845).length < 2 ^ (prefixWord ++ tailWord_509845).sum := by decide
  have hdescent : baseEnd_509845 < baseStart_509845 := by decide
  rcases family_descends (prefixWord ++ tailWord_509845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509859 : List Nat := [1, 1, 1, 4, 1, 2, 1, 10]
def baseStart_509859 : Nat := 118140960795 + 509859 * 2 ^ 59
def prefixEnd_509859 : Nat := 4983230072969 + 3 ^ 40 * 509859 * 2
def baseEnd_509859 : Nat := 38785590077159393780401

theorem tailTrace_509859 : CollatzResearch.WordTrace tailWord_509859 prefixEnd_509859 38785590077159393780401 := by
  unfold tailWord_509859
  simp only [CollatzResearch.WordTrace]
  refine ⟨18596085459875394829756631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12397390306583596553171087 18596085459875394829756631)
  ·
    refine ⟨27894128189813092244634947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18596085459875394829756631 27894128189813092244634947)
    ·
      refine ⟨41841192284719638366952421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27894128189813092244634947 41841192284719638366952421)
      ·
        refine ⟨7845223553384932193803579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41841192284719638366952421 7845223553384932193803579)
        ·
          refine ⟨11767835330077398290705369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7845223553384932193803579 11767835330077398290705369)
          ·
            refine ⟨8825876497558048718029027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11767835330077398290705369 8825876497558048718029027)
            ·
              refine ⟨13238814746337073077043541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8825876497558048718029027 13238814746337073077043541)
              ·
                refine ⟨38785590077159393780401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13238814746337073077043541 38785590077159393780401)
                ·
                  rfl

theorem cell21_509859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 10].length) (baseStart_509859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509859 prefixEnd_509859 := by exact prefixLift 509859
  have htrace : WordTrace (prefixWord ++ tailWord_509859) baseStart_509859 baseEnd_509859 := by
    simpa [prefixWord, tailWord_509859, baseEnd_509859] using wordTrace_append hprefix tailTrace_509859
  have hstable : (prefixWord ++ tailWord_509859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509859).length < 2 ^ (prefixWord ++ tailWord_509859).sum := by decide
  have hdescent : baseEnd_509859 < baseStart_509859 := by decide
  rcases family_descends (prefixWord ++ tailWord_509859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509910 : List Nat := [5, 2, 1, 1, 3, 1, 2, 6]
def baseStart_509910 : Nat := 118140960795 + 509910 * 2 ^ 59
def prefixEnd_509910 : Nat := 4983230072969 + 3 ^ 40 * 509910 * 2
def baseEnd_509910 : Nat := 38789469708771141997033

theorem tailTrace_509910 : CollatzResearch.WordTrace tailWord_509910 prefixEnd_509910 38789469708771141997033 := by
  unfold tailWord_509910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1162371598918164408741449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12398630388460420359908789 1162371598918164408741449)
  ·
    refine ⟨871778699188623306556087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1162371598918164408741449 871778699188623306556087)
    ·
      refine ⟨1307668048782934959834131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 871778699188623306556087 1307668048782934959834131)
      ·
        refine ⟨1961502073174402439751197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1307668048782934959834131 1961502073174402439751197)
        ·
          refine ⟨735563277440400914906699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1961502073174402439751197 735563277440400914906699)
          ·
            refine ⟨1103344916160601372360049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735563277440400914906699 1103344916160601372360049)
            ·
              refine ⟨827508687120451029270037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103344916160601372360049 827508687120451029270037)
              ·
                refine ⟨38789469708771141997033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 827508687120451029270037 38789469708771141997033)
                ·
                  rfl

theorem cell21_509910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_509910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509910 prefixEnd_509910 := by exact prefixLift 509910
  have htrace : WordTrace (prefixWord ++ tailWord_509910) baseStart_509910 baseEnd_509910 := by
    simpa [prefixWord, tailWord_509910, baseEnd_509910] using wordTrace_append hprefix tailTrace_509910
  have hstable : (prefixWord ++ tailWord_509910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509910).length < 2 ^ (prefixWord ++ tailWord_509910).sum := by decide
  have hdescent : baseEnd_509910 < baseStart_509910 := by decide
  rcases family_descends (prefixWord ++ tailWord_509910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509935 : List Nat := [1, 1, 2, 1, 4, 2, 1, 9]
def baseStart_509935 : Nat := 118140960795 + 509935 * 2 ^ 59
def prefixEnd_509935 : Nat := 4983230072969 + 3 ^ 40 * 509935 * 2
def baseEnd_509935 : Nat := 38791371488972979358127

theorem tailTrace_509935 : CollatzResearch.WordTrace tailWord_509935 prefixEnd_509935 38791371488972979358127 := by
  unfold tailWord_509935
  simp only [CollatzResearch.WordTrace]
  refine ⟨18598857407600059809523259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12399238271733373206348839 18598857407600059809523259)
  ·
    refine ⟨27898286111400089714284889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18598857407600059809523259 27898286111400089714284889)
    ·
      refine ⟨20923714583550067285713667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27898286111400089714284889 20923714583550067285713667)
      ·
        refine ⟨31385571875325100928570501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20923714583550067285713667 31385571875325100928570501)
        ·
          refine ⟨5884794726623456424106969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31385571875325100928570501 5884794726623456424106969)
          ·
            refine ⟨4413596044967592318080227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5884794726623456424106969 4413596044967592318080227)
            ·
              refine ⟨6620394067451388477120341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4413596044967592318080227 6620394067451388477120341)
              ·
                refine ⟨38791371488972979358127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6620394067451388477120341 38791371488972979358127)
                ·
                  rfl

theorem cell21_509935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 9].length) (baseStart_509935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_509935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_509935 prefixEnd_509935 := by exact prefixLift 509935
  have htrace : WordTrace (prefixWord ++ tailWord_509935) baseStart_509935 baseEnd_509935 := by
    simpa [prefixWord, tailWord_509935, baseEnd_509935] using wordTrace_append hprefix tailTrace_509935
  have hstable : (prefixWord ++ tailWord_509935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509935).length < 2 ^ (prefixWord ++ tailWord_509935).sum := by decide
  have hdescent : baseEnd_509935 < baseStart_509935 := by decide
  rcases family_descends (prefixWord ++ tailWord_509935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510000 : List Nat := [2, 1, 1, 1, 2, 6, 2, 3, 3]
def baseStart_510000 : Nat := 118140960795 + 510000 * 2 ^ 59
def prefixEnd_510000 : Nat := 4983230072969 + 3 ^ 40 * 510000 * 2
def baseEnd_510000 : Nat := 116388948352493269490915

theorem tailTrace_510000 : CollatzResearch.WordTrace tailWord_510000 prefixEnd_510000 116388948352493269490915 := by
  unfold tailWord_510000
  simp only [CollatzResearch.WordTrace]
  refine ⟨9300614076182287955319727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12400818768243050607092969 9300614076182287955319727)
  ·
    refine ⟨13950921114273431932979591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9300614076182287955319727 13950921114273431932979591)
    ·
      refine ⟨20926381671410147899469387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13950921114273431932979591 20926381671410147899469387)
      ·
        refine ⟨31389572507115221849204081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20926381671410147899469387 31389572507115221849204081)
        ·
          refine ⟨23542179380336416386903061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31389572507115221849204081 23542179380336416386903061)
          ·
            refine ⟨1103539658453269518136081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23542179380336416386903061 1103539658453269518136081)
            ·
              refine ⟨827654743839952138602061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103539658453269518136081 827654743839952138602061)
              ·
                refine ⟨310370528939982051975773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 827654743839952138602061 310370528939982051975773)
                ·
                  refine ⟨116388948352493269490915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310370528939982051975773 116388948352493269490915)
                  ·
                    rfl

theorem cell21_510000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 3].length) (baseStart_510000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510000 prefixEnd_510000 := by exact prefixLift 510000
  have htrace : WordTrace (prefixWord ++ tailWord_510000) baseStart_510000 baseEnd_510000 := by
    simpa [prefixWord, tailWord_510000, baseEnd_510000] using wordTrace_append hprefix tailTrace_510000
  have hstable : (prefixWord ++ tailWord_510000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510000).length < 2 ^ (prefixWord ++ tailWord_510000).sum := by decide
  have hdescent : baseEnd_510000 < baseStart_510000 := by decide
  rcases family_descends (prefixWord ++ tailWord_510000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510042 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 5]
def baseStart_510042 : Nat := 118140960795 + 510042 * 2 ^ 59
def prefixEnd_510042 : Nat := 4983230072969 + 3 ^ 40 * 510042 * 2
def baseEnd_510042 : Nat := 116398533324710529790829

theorem tailTrace_510042 : CollatzResearch.WordTrace tailWord_510042 prefixEnd_510042 116398533324710529790829 := by
  unfold tailWord_510042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4650690004553104270917095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12401840012141611389112253 4650690004553104270917095)
  ·
    refine ⟨6976035006829656406375643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4650690004553104270917095 6976035006829656406375643)
    ·
      refine ⟨10464052510244484609563465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6976035006829656406375643 10464052510244484609563465)
      ·
        refine ⟨7848039382683363457172599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10464052510244484609563465 7848039382683363457172599)
        ·
          refine ⟨11772059074025045185758899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7848039382683363457172599 11772059074025045185758899)
          ·
            refine ⟨17658088611037567778638349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11772059074025045185758899 17658088611037567778638349)
            ·
              refine ⟨6621783229139087916989381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17658088611037567778638349 6621783229139087916989381)
              ·
                refine ⟨1241584355463578984435509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6621783229139087916989381 1241584355463578984435509)
                ·
                  refine ⟨116398533324710529790829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1241584355463578984435509 116398533324710529790829)
                  ·
                    rfl

theorem cell21_510042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_510042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510042 prefixEnd_510042 := by exact prefixLift 510042
  have htrace : WordTrace (prefixWord ++ tailWord_510042) baseStart_510042 baseEnd_510042 := by
    simpa [prefixWord, tailWord_510042, baseEnd_510042] using wordTrace_append hprefix tailTrace_510042
  have hstable : (prefixWord ++ tailWord_510042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510042).length < 2 ^ (prefixWord ++ tailWord_510042).sum := by decide
  have hdescent : baseEnd_510042 < baseStart_510042 := by decide
  rcases family_descends (prefixWord ++ tailWord_510042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510045 : List Nat := [1, 4, 4, 1, 1, 2, 1, 7]
def baseStart_510045 : Nat := 118140960795 + 510045 * 2 ^ 59
def prefixEnd_510045 : Nat := 4983230072969 + 3 ^ 40 * 510045 * 2
def baseEnd_510045 : Nat := 38799739321861063746941

theorem tailTrace_510045 : CollatzResearch.WordTrace tailWord_510045 prefixEnd_510045 38799739321861063746941 := by
  unfold tailWord_510045
  simp only [CollatzResearch.WordTrace]
  refine ⟨18602869437201548596027589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12401912958134365730685059 18602869437201548596027589)
  ·
    refine ⟨3488038019475290361755173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18602869437201548596027589 3488038019475290361755173)
    ·
      refine ⟨654007128651616942829095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3488038019475290361755173 654007128651616942829095)
      ·
        refine ⟨981010692977425414243643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654007128651616942829095 981010692977425414243643)
        ·
          refine ⟨1471516039466138121365465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 981010692977425414243643 1471516039466138121365465)
          ·
            refine ⟨1103637029599603591024099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1471516039466138121365465 1103637029599603591024099)
            ·
              refine ⟨1655455544399405386536149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103637029599603591024099 1655455544399405386536149)
              ·
                refine ⟨38799739321861063746941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1655455544399405386536149 38799739321861063746941)
                ·
                  rfl

theorem cell21_510045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 7].length) (baseStart_510045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510045 prefixEnd_510045 := by exact prefixLift 510045
  have htrace : WordTrace (prefixWord ++ tailWord_510045) baseStart_510045 baseEnd_510045 := by
    simpa [prefixWord, tailWord_510045, baseEnd_510045] using wordTrace_append hprefix tailTrace_510045
  have hstable : (prefixWord ++ tailWord_510045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510045).length < 2 ^ (prefixWord ++ tailWord_510045).sum := by decide
  have hdescent : baseEnd_510045 < baseStart_510045 := by decide
  rcases family_descends (prefixWord ++ tailWord_510045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510073 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 6]
def baseStart_510073 : Nat := 118140960795 + 510073 * 2 ^ 59
def prefixEnd_510073 : Nat := 4983230072969 + 3 ^ 40 * 510073 * 2
def baseEnd_510073 : Nat := 116405607947061364774099

theorem tailTrace_510073 : CollatzResearch.WordTrace tailWord_510073 prefixEnd_510073 116405607947061364774099 := by
  unfold tailWord_510073
  simp only [CollatzResearch.WordTrace]
  refine ⟨18603890681100109378046873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12402593787400072918697915 18603890681100109378046873)
  ·
    refine ⟨13952918010825082033535155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18603890681100109378046873 13952918010825082033535155)
    ·
      refine ⟨20929377016237623050302733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13952918010825082033535155 20929377016237623050302733)
      ·
        refine ⟨7848516381089108643863525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20929377016237623050302733 7848516381089108643863525)
        ·
          refine ⟨1471596821454207870724411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7848516381089108643863525 1471596821454207870724411)
          ·
            refine ⟨2207395232181311806086617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471596821454207870724411 2207395232181311806086617)
            ·
              refine ⟨1655546424135983854564963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2207395232181311806086617 1655546424135983854564963)
              ·
                refine ⟨2483319636203975781847445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655546424135983854564963 2483319636203975781847445)
                ·
                  refine ⟨116405607947061364774099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2483319636203975781847445 116405607947061364774099)
                  ·
                    rfl

theorem cell21_510073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_510073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510073 prefixEnd_510073 := by exact prefixLift 510073
  have htrace : WordTrace (prefixWord ++ tailWord_510073) baseStart_510073 baseEnd_510073 := by
    simpa [prefixWord, tailWord_510073, baseEnd_510073] using wordTrace_append hprefix tailTrace_510073
  have hstable : (prefixWord ++ tailWord_510073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510073).length < 2 ^ (prefixWord ++ tailWord_510073).sum := by decide
  have hdescent : baseEnd_510073 < baseStart_510073 := by decide
  rcases family_descends (prefixWord ++ tailWord_510073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510087 : List Nat := [1, 1, 4, 2, 1, 1, 3, 8]
def baseStart_510087 : Nat := 118140960795 + 510087 * 2 ^ 59
def prefixEnd_510087 : Nat := 4983230072969 + 3 ^ 40 * 510087 * 2
def baseEnd_510087 : Nat := 38802934312600150513579

theorem tailTrace_510087 : CollatzResearch.WordTrace tailWord_510087 prefixEnd_510087 38802934312600150513579 := by
  unfold tailWord_510087
  simp only [CollatzResearch.WordTrace]
  refine ⟨18604401303049389769056515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12402934202032926512704343 18604401303049389769056515)
  ·
    refine ⟨27906601954574084653584773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18604401303049389769056515 27906601954574084653584773)
    ·
      refine ⟨5232487866482640872547145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27906601954574084653584773 5232487866482640872547145)
      ·
        refine ⟨3924365899861980654410359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5232487866482640872547145 3924365899861980654410359)
        ·
          refine ⟨5886548849792970981615539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3924365899861980654410359 5886548849792970981615539)
          ·
            refine ⟨8829823274689456472423309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5886548849792970981615539 8829823274689456472423309)
            ·
              refine ⟨3311183728008546177158741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8829823274689456472423309 3311183728008546177158741)
              ·
                refine ⟨38802934312600150513579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3311183728008546177158741 38802934312600150513579)
                ·
                  rfl

theorem cell21_510087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 8].length) (baseStart_510087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510087 prefixEnd_510087 := by exact prefixLift 510087
  have htrace : WordTrace (prefixWord ++ tailWord_510087) baseStart_510087 baseEnd_510087 := by
    simpa [prefixWord, tailWord_510087, baseEnd_510087] using wordTrace_append hprefix tailTrace_510087
  have hstable : (prefixWord ++ tailWord_510087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510087).length < 2 ^ (prefixWord ++ tailWord_510087).sum := by decide
  have hdescent : baseEnd_510087 < baseStart_510087 := by decide
  rcases family_descends (prefixWord ++ tailWord_510087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510090 : List Nat := [3, 1, 2, 3, 1, 3, 1, 3, 4]
def baseStart_510090 : Nat := 118140960795 + 510090 * 2 ^ 59
def prefixEnd_510090 : Nat := 4983230072969 + 3 ^ 40 * 510090 * 2
def baseEnd_510090 : Nat := 116409487578673112990731

theorem tailTrace_510090 : CollatzResearch.WordTrace tailWord_510090 prefixEnd_510090 116409487578673112990731 := by
  unfold tailWord_510090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4651127680509630320353931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12403007148025680854277149 4651127680509630320353931)
  ·
    refine ⟨6976691520764445480530897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4651127680509630320353931 6976691520764445480530897)
    ·
      refine ⟨5232518640573334110398173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6976691520764445480530897 5232518640573334110398173)
      ·
        refine ⟨1962194490215000291399315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5232518640573334110398173 1962194490215000291399315)
        ·
          refine ⟨2943291735322500437098973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1962194490215000291399315 2943291735322500437098973)
          ·
            refine ⟨1103734400745937663912115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2943291735322500437098973 1103734400745937663912115)
            ·
              refine ⟨1655601601118906495868173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103734400745937663912115 1655601601118906495868173)
              ·
                refine ⟨620850600419589935950565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1655601601118906495868173 620850600419589935950565)
                ·
                  refine ⟨116409487578673112990731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 620850600419589935950565 116409487578673112990731)
                  ·
                    rfl

theorem cell21_510090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_510090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510090 prefixEnd_510090 := by exact prefixLift 510090
  have htrace : WordTrace (prefixWord ++ tailWord_510090) baseStart_510090 baseEnd_510090 := by
    simpa [prefixWord, tailWord_510090, baseEnd_510090] using wordTrace_append hprefix tailTrace_510090
  have hstable : (prefixWord ++ tailWord_510090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510090).length < 2 ^ (prefixWord ++ tailWord_510090).sum := by decide
  have hdescent : baseEnd_510090 < baseStart_510090 := by decide
  rcases family_descends (prefixWord ++ tailWord_510090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510149 : List Nat := [1, 3, 1, 1, 1, 1, 6, 3, 4]
def baseStart_510149 : Nat := 118140960795 + 510149 * 2 ^ 59
def prefixEnd_510149 : Nat := 4983230072969 + 3 ^ 40 * 510149 * 2
def baseEnd_510149 : Nat := 116422952182502121507277

theorem tailTrace_510149 : CollatzResearch.WordTrace tailWord_510149 prefixEnd_510149 116422952182502121507277 := by
  unfold tailWord_510149
  simp only [CollatzResearch.WordTrace]
  refine ⟨18606662628824774357813501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12404441752549849571875667 18606662628824774357813501)
  ·
    refine ⟨6977498485809290384180063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18606662628824774357813501 6977498485809290384180063)
    ·
      refine ⟨10466247728713935576270095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6977498485809290384180063 10466247728713935576270095)
      ·
        refine ⟨15699371593070903364405143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10466247728713935576270095 15699371593070903364405143)
        ·
          refine ⟨23549057389606355046607715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15699371593070903364405143 23549057389606355046607715)
          ·
            refine ⟨35323586084409532569911573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23549057389606355046607715 35323586084409532569911573)
            ·
              refine ⟨1655793097706696839214605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35323586084409532569911573 1655793097706696839214605)
              ·
                refine ⟨620922411640011314705477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1655793097706696839214605 620922411640011314705477)
                ·
                  refine ⟨116422952182502121507277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 620922411640011314705477 116422952182502121507277)
                  ·
                    rfl

theorem cell21_510149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_510149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510149 prefixEnd_510149 := by exact prefixLift 510149
  have htrace : WordTrace (prefixWord ++ tailWord_510149) baseStart_510149 baseEnd_510149 := by
    simpa [prefixWord, tailWord_510149, baseEnd_510149] using wordTrace_append hprefix tailTrace_510149
  have hstable : (prefixWord ++ tailWord_510149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510149).length < 2 ^ (prefixWord ++ tailWord_510149).sum := by decide
  have hdescent : baseEnd_510149 < baseStart_510149 := by decide
  rcases family_descends (prefixWord ++ tailWord_510149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510183 : List Nat := [1, 1, 5, 3, 1, 3, 1, 2, 4]
def baseStart_510183 : Nat := 118140960795 + 510183 * 2 ^ 59
def prefixEnd_510183 : Nat := 4983230072969 + 3 ^ 40 * 510183 * 2
def baseEnd_510183 : Nat := 116430711445725617940541

theorem tailTrace_510183 : CollatzResearch.WordTrace tailWord_510183 prefixEnd_510183 116430711445725617940541 := by
  unfold tailWord_510183
  simp only [CollatzResearch.WordTrace]
  refine ⟨18607902710701598164551203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12405268473801065443034135 18607902710701598164551203)
  ·
    refine ⟨27911854066052397246826805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18607902710701598164551203 27911854066052397246826805)
    ·
      refine ⟨2616736318692412241890013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27911854066052397246826805 2616736318692412241890013)
      ·
        refine ⟨981276119509654590708755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2616736318692412241890013 981276119509654590708755)
        ·
          refine ⟨1471914179264481886063133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 981276119509654590708755 1471914179264481886063133)
          ·
            refine ⟨551967817224180707273675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1471914179264481886063133 551967817224180707273675)
            ·
              refine ⟨827951725836271060910513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551967817224180707273675 827951725836271060910513)
              ·
                refine ⟨620963794377203295682885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827951725836271060910513 620963794377203295682885)
                ·
                  refine ⟨116430711445725617940541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 620963794377203295682885 116430711445725617940541)
                  ·
                    rfl

theorem cell21_510183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 4].length) (baseStart_510183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510183 prefixEnd_510183 := by exact prefixLift 510183
  have htrace : WordTrace (prefixWord ++ tailWord_510183) baseStart_510183 baseEnd_510183 := by
    simpa [prefixWord, tailWord_510183, baseEnd_510183] using wordTrace_append hprefix tailTrace_510183
  have hstable : (prefixWord ++ tailWord_510183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510183).length < 2 ^ (prefixWord ++ tailWord_510183).sum := by decide
  have hdescent : baseEnd_510183 < baseStart_510183 := by decide
  rcases family_descends (prefixWord ++ tailWord_510183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510239 : List Nat := [1, 1, 2, 4, 3, 1, 9]
def baseStart_510239 : Nat := 118140960795 + 510239 * 2 ^ 59
def prefixEnd_510239 : Nat := 4983230072969 + 3 ^ 40 * 510239 * 2
def baseEnd_510239 : Nat := 12938165712075773889677

theorem tailTrace_510239 : CollatzResearch.WordTrace tailWord_510239 prefixEnd_510239 12938165712075773889677 := by
  unfold tailWord_510239
  simp only [CollatzResearch.WordTrace]
  refine ⟨18609945198498719728589771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12406630132332479819059847 18609945198498719728589771)
  ·
    refine ⟨27914917797748079592884657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18609945198498719728589771 27914917797748079592884657)
    ·
      refine ⟨20936188348311059694663493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27914917797748079592884657 20936188348311059694663493)
      ·
        refine ⟨3925535315308323692749405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20936188348311059694663493 3925535315308323692749405)
        ·
          refine ⟨1472075743240621384781027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3925535315308323692749405 1472075743240621384781027)
          ·
            refine ⟨2208113614860932077171541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1472075743240621384781027 2208113614860932077171541)
            ·
              refine ⟨12938165712075773889677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2208113614860932077171541 12938165712075773889677)
              ·
                rfl

theorem cell21_510239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 9].length) (baseStart_510239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510239 prefixEnd_510239 := by exact prefixLift 510239
  have htrace : WordTrace (prefixWord ++ tailWord_510239) baseStart_510239 baseEnd_510239 := by
    simpa [prefixWord, tailWord_510239, baseEnd_510239] using wordTrace_append hprefix tailTrace_510239
  have hstable : (prefixWord ++ tailWord_510239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510239).length < 2 ^ (prefixWord ++ tailWord_510239).sum := by decide
  have hdescent : baseEnd_510239 < baseStart_510239 := by decide
  rcases family_descends (prefixWord ++ tailWord_510239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510245 : List Nat := [1, 3, 1, 2, 5, 1, 3, 2, 3]
def baseStart_510245 : Nat := 118140960795 + 510245 * 2 ^ 59
def prefixEnd_510245 : Nat := 4983230072969 + 3 ^ 40 * 510245 * 2
def baseEnd_510245 : Nat := 116444860690427287907081

theorem tailTrace_510245 : CollatzResearch.WordTrace tailWord_510245 prefixEnd_510245 116444860690427287907081 := by
  unfold tailWord_510245
  simp only [CollatzResearch.WordTrace]
  refine ⟨18610164036476982753308189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12406776024317988502205459 18610164036476982753308189)
  ·
    refine ⟨6978811513678868532490571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18610164036476982753308189 6978811513678868532490571)
    ·
      refine ⟨10468217270518302798735857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6978811513678868532490571 10468217270518302798735857)
      ·
        refine ⟨7851162952888727099051893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10468217270518302798735857 7851162952888727099051893)
        ·
          refine ⟨736046526833318165536115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7851162952888727099051893 736046526833318165536115)
          ·
            refine ⟨1104069790249977248304173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736046526833318165536115 1104069790249977248304173)
            ·
              refine ⟨414026171343741468114065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1104069790249977248304173 414026171343741468114065)
              ·
                refine ⟨310519628507806101085549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414026171343741468114065 310519628507806101085549)
                ·
                  refine ⟨116444860690427287907081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310519628507806101085549 116444860690427287907081)
                  ·
                    rfl

theorem cell21_510245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_510245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510245 prefixEnd_510245 := by exact prefixLift 510245
  have htrace : WordTrace (prefixWord ++ tailWord_510245) baseStart_510245 baseEnd_510245 := by
    simpa [prefixWord, tailWord_510245, baseEnd_510245] using wordTrace_append hprefix tailTrace_510245
  have hstable : (prefixWord ++ tailWord_510245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510245).length < 2 ^ (prefixWord ++ tailWord_510245).sum := by decide
  have hdescent : baseEnd_510245 < baseStart_510245 := by decide
  rcases family_descends (prefixWord ++ tailWord_510245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510304 : List Nat := [2, 1, 1, 3, 5, 1, 1, 4, 3]
def baseStart_510304 : Nat := 118140960795 + 510304 * 2 ^ 59
def prefixEnd_510304 : Nat := 4983230072969 + 3 ^ 40 * 510304 * 2
def baseEnd_510304 : Nat := 116458325294256296423627

theorem tailTrace_510304 : CollatzResearch.WordTrace tailWord_510304 prefixEnd_510304 116458325294256296423627 := by
  unfold tailWord_510304
  simp only [CollatzResearch.WordTrace]
  refine ⟨9306157971631617914852983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12408210628842157219803977 9306157971631617914852983)
  ·
    refine ⟨13959236957447426872279475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9306157971631617914852983 13959236957447426872279475)
    ·
      refine ⟨20938855436171140308419213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13959236957447426872279475 20938855436171140308419213)
      ·
        refine ⟨7852070788564177615657205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20938855436171140308419213 7852070788564177615657205)
        ·
          refine ⟨736131636427891651467863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7852070788564177615657205 736131636427891651467863)
          ·
            refine ⟨1104197454641837477201795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736131636427891651467863 1104197454641837477201795)
            ·
              refine ⟨1656296181962756215802693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104197454641837477201795 1656296181962756215802693)
              ·
                refine ⟨310555534118016790463005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1656296181962756215802693 310555534118016790463005)
                ·
                  refine ⟨116458325294256296423627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310555534118016790463005 116458325294256296423627)
                  ·
                    rfl

theorem cell21_510304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 3].length) (baseStart_510304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510304 prefixEnd_510304 := by exact prefixLift 510304
  have htrace : WordTrace (prefixWord ++ tailWord_510304) baseStart_510304 baseEnd_510304 := by
    simpa [prefixWord, tailWord_510304, baseEnd_510304] using wordTrace_append hprefix tailTrace_510304
  have hstable : (prefixWord ++ tailWord_510304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510304).length < 2 ^ (prefixWord ++ tailWord_510304).sum := by decide
  have hdescent : baseEnd_510304 < baseStart_510304 := by decide
  rcases family_descends (prefixWord ++ tailWord_510304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510338 : List Nat := [3, 4, 2, 1, 2, 1, 2, 3, 3]
def baseStart_510338 : Nat := 118140960795 + 510338 * 2 ^ 59
def prefixEnd_510338 : Nat := 4983230072969 + 3 ^ 40 * 510338 * 2
def baseEnd_510338 : Nat := 116466084557479792856891

theorem tailTrace_510338 : CollatzResearch.WordTrace tailWord_510338 prefixEnd_510338 116466084557479792856891 := by
  unfold tailWord_510338
  simp only [CollatzResearch.WordTrace]
  refine ⟨4653389006285014909110917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12409037350093373090962445 4653389006285014909110917)
  ·
    refine ⟨872510438678440295458297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4653389006285014909110917 872510438678440295458297)
    ·
      refine ⟨654382829008830221593723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 872510438678440295458297 654382829008830221593723)
      ·
        refine ⟨981574243513245332390585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654382829008830221593723 981574243513245332390585)
        ·
          refine ⟨736180682634933999292939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 981574243513245332390585 736180682634933999292939)
          ·
            refine ⟨1104271023952400998939409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736180682634933999292939 1104271023952400998939409)
            ·
              refine ⟨828203267964300749204557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104271023952400998939409 828203267964300749204557)
              ·
                refine ⟨310576225486612780951709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 828203267964300749204557 310576225486612780951709)
                ·
                  refine ⟨116466084557479792856891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310576225486612780951709 116466084557479792856891)
                  ·
                    rfl

theorem cell21_510338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_510338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510338 prefixEnd_510338 := by exact prefixLift 510338
  have htrace : WordTrace (prefixWord ++ tailWord_510338) baseStart_510338 baseEnd_510338 := by
    simpa [prefixWord, tailWord_510338, baseEnd_510338] using wordTrace_append hprefix tailTrace_510338
  have hstable : (prefixWord ++ tailWord_510338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510338).length < 2 ^ (prefixWord ++ tailWord_510338).sum := by decide
  have hdescent : baseEnd_510338 < baseStart_510338 := by decide
  rcases family_descends (prefixWord ++ tailWord_510338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510391 : List Nat := [1, 1, 3, 1, 3, 4, 1, 7]
def baseStart_510391 : Nat := 118140960795 + 510391 * 2 ^ 59
def prefixEnd_510391 : Nat := 4983230072969 + 3 ^ 40 * 510391 * 2
def baseEnd_510391 : Nat := 38826059959854492824483

theorem tailTrace_510391 : CollatzResearch.WordTrace tailWord_510391 prefixEnd_510391 38826059959854492824483 := by
  unfold tailWord_510391
  simp only [CollatzResearch.WordTrace]
  refine ⟨18615489093948049688123027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12410326062632033125415351 18615489093948049688123027)
  ·
    refine ⟨27923233640922074532184541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18615489093948049688123027 27923233640922074532184541)
    ·
      refine ⟨10471212615345777949569203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27923233640922074532184541 10471212615345777949569203)
      ·
        refine ⟨15706818923018666924353805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10471212615345777949569203 15706818923018666924353805)
        ·
          refine ⟨5890057096132000096632677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15706818923018666924353805 5890057096132000096632677)
          ·
            refine ⟨1104385705524750018118627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5890057096132000096632677 1104385705524750018118627)
            ·
              refine ⟨1656578558287125027177941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104385705524750018118627 1656578558287125027177941)
              ·
                refine ⟨38826059959854492824483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1656578558287125027177941 38826059959854492824483)
                ·
                  rfl

theorem cell21_510391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 7].length) (baseStart_510391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510391 prefixEnd_510391 := by exact prefixLift 510391
  have htrace : WordTrace (prefixWord ++ tailWord_510391) baseStart_510391 baseEnd_510391 := by
    simpa [prefixWord, tailWord_510391, baseEnd_510391] using wordTrace_append hprefix tailTrace_510391
  have hstable : (prefixWord ++ tailWord_510391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510391).length < 2 ^ (prefixWord ++ tailWord_510391).sum := by decide
  have hdescent : baseEnd_510391 < baseStart_510391 := by decide
  rcases family_descends (prefixWord ++ tailWord_510391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510515 : List Nat := [1, 1, 1, 2, 4, 2, 4, 3, 3]
def baseStart_510515 : Nat := 118140960795 + 510515 * 2 ^ 59
def prefixEnd_510515 : Nat := 4983230072969 + 3 ^ 40 * 510515 * 2
def baseEnd_510515 : Nat := 116506478368966818406529

theorem tailTrace_510515 : CollatzResearch.WordTrace tailWord_510515 prefixEnd_510515 116506478368966818406529 := by
  unfold tailWord_510515
  simp only [CollatzResearch.WordTrace]
  refine ⟨18620011745498818865636999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12413341163665879243757999 18620011745498818865636999)
  ·
    refine ⟨27930017618248228298455499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18620011745498818865636999 27930017618248228298455499)
    ·
      refine ⟨41895026427372342447683249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27930017618248228298455499 41895026427372342447683249)
      ·
        refine ⟨31421269820529256835762437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41895026427372342447683249 31421269820529256835762437)
        ·
          refine ⟨5891488091349235656705457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31421269820529256835762437 5891488091349235656705457)
          ·
            refine ⟨4418616068511926742529093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5891488091349235656705457 4418616068511926742529093)
            ·
              refine ⟨828490512845986264224205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4418616068511926742529093 828490512845986264224205)
              ·
                refine ⟨310683942317244849084077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 828490512845986264224205 310683942317244849084077)
                ·
                  refine ⟨116506478368966818406529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310683942317244849084077 116506478368966818406529)
                  ·
                    rfl

theorem cell21_510515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 3].length) (baseStart_510515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510515 prefixEnd_510515 := by exact prefixLift 510515
  have htrace : WordTrace (prefixWord ++ tailWord_510515) baseStart_510515 baseEnd_510515 := by
    simpa [prefixWord, tailWord_510515, baseEnd_510515] using wordTrace_append hprefix tailTrace_510515
  have hstable : (prefixWord ++ tailWord_510515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510515).length < 2 ^ (prefixWord ++ tailWord_510515).sum := by decide
  have hdescent : baseEnd_510515 < baseStart_510515 := by decide
  rcases family_descends (prefixWord ++ tailWord_510515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510529 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 6]
def baseStart_510529 : Nat := 118140960795 + 510529 * 2 ^ 59
def prefixEnd_510529 : Nat := 4983230072969 + 3 ^ 40 * 510529 * 2
def baseEnd_510529 : Nat := 116509673359705905173167

theorem tailTrace_510529 : CollatzResearch.WordTrace tailWord_510529 prefixEnd_510529 116509673359705905173167 := by
  unfold tailWord_510529
  simp only [CollatzResearch.WordTrace]
  refine ⟨18620522367448099256646641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12413681578298732837764427 18620522367448099256646641)
  ·
    refine ⟨13965391775586074442484981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18620522367448099256646641 13965391775586074442484981)
    ·
      refine ⟨1309255478961194478982967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13965391775586074442484981 1309255478961194478982967)
      ·
        refine ⟨1963883218441791718474451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1309255478961194478982967 1963883218441791718474451)
        ·
          refine ⟨2945824827662687577711677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1963883218441791718474451 2945824827662687577711677)
          ·
            refine ⟨1104684310373507841641879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2945824827662687577711677 1104684310373507841641879)
            ·
              refine ⟨1657026465560261762462819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104684310373507841641879 1657026465560261762462819)
              ·
                refine ⟨2485539698340392643694229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657026465560261762462819 2485539698340392643694229)
                ·
                  refine ⟨116509673359705905173167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2485539698340392643694229 116509673359705905173167)
                  ·
                    rfl

theorem cell21_510529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_510529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510529 prefixEnd_510529 := by exact prefixLift 510529
  have htrace : WordTrace (prefixWord ++ tailWord_510529) baseStart_510529 baseEnd_510529 := by
    simpa [prefixWord, tailWord_510529, baseEnd_510529] using wordTrace_append hprefix tailTrace_510529
  have hstable : (prefixWord ++ tailWord_510529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510529).length < 2 ^ (prefixWord ++ tailWord_510529).sum := by decide
  have hdescent : baseEnd_510529 < baseStart_510529 := by decide
  rcases family_descends (prefixWord ++ tailWord_510529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510546 : List Nat := [3, 2, 2, 1, 2, 1, 5, 1, 4]
def baseStart_510546 : Nat := 118140960795 + 510546 * 2 ^ 59
def prefixEnd_510546 : Nat := 4983230072969 + 3 ^ 40 * 510546 * 2
def baseEnd_510546 : Nat := 116513552991317653389799

theorem tailTrace_510546 : CollatzResearch.WordTrace tailWord_510546 prefixEnd_510546 116513552991317653389799 := by
  unfold tailWord_510546
  simp only [CollatzResearch.WordTrace]
  refine ⟨4655285602096627790003873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12414094938924340773343661 4655285602096627790003873)
  ·
    refine ⟨3491464201572470842502905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4655285602096627790003873 3491464201572470842502905)
    ·
      refine ⟨2618598151179353131877179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3491464201572470842502905 2618598151179353131877179)
      ·
        refine ⟨3927897226769029697815769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2618598151179353131877179 3927897226769029697815769)
        ·
          refine ⟨2945922920076772273361827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3927897226769029697815769 2945922920076772273361827)
          ·
            refine ⟨4418884380115158410042741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945922920076772273361827 4418884380115158410042741)
            ·
              refine ⟨414270410635796100941507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4418884380115158410042741 414270410635796100941507)
              ·
                refine ⟨621405615953694151412261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414270410635796100941507 621405615953694151412261)
                ·
                  refine ⟨116513552991317653389799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 621405615953694151412261 116513552991317653389799)
                  ·
                    rfl

theorem cell21_510546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_510546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510546 prefixEnd_510546 := by exact prefixLift 510546
  have htrace : WordTrace (prefixWord ++ tailWord_510546) baseStart_510546 baseEnd_510546 := by
    simpa [prefixWord, tailWord_510546, baseEnd_510546] using wordTrace_append hprefix tailTrace_510546
  have hstable : (prefixWord ++ tailWord_510546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510546).length < 2 ^ (prefixWord ++ tailWord_510546).sum := by decide
  have hdescent : baseEnd_510546 < baseStart_510546 := by decide
  rcases family_descends (prefixWord ++ tailWord_510546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510588 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 6]
def baseStart_510588 : Nat := 118140960795 + 510588 * 2 ^ 59
def prefixEnd_510588 : Nat := 4983230072969 + 3 ^ 40 * 510588 * 2
def baseEnd_510588 : Nat := 116523137963534913689713

theorem tailTrace_510588 : CollatzResearch.WordTrace tailWord_510588 prefixEnd_510588 116523137963534913689713 := by
  unfold tailWord_510588
  simp only [CollatzResearch.WordTrace]
  refine ⟨9311337137117176166522209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12415116182822901555362945 9311337137117176166522209)
  ·
    refine ⟨6983502852837882124891657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9311337137117176166522209 6983502852837882124891657)
    ·
      refine ⟨5237627139628411593668743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6983502852837882124891657 5237627139628411593668743)
      ·
        refine ⟨7856440709442617390503115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5237627139628411593668743 7856440709442617390503115)
        ·
          refine ⟨11784661064163926085754673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7856440709442617390503115 11784661064163926085754673)
          ·
            refine ⟨8838495798122944564316005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11784661064163926085754673 8838495798122944564316005)
            ·
              refine ⟨1657217962148052105809251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8838495798122944564316005 1657217962148052105809251)
              ·
                refine ⟨2485826943222078158713877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657217962148052105809251 2485826943222078158713877)
                ·
                  refine ⟨116523137963534913689713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2485826943222078158713877 116523137963534913689713)
                  ·
                    rfl

theorem cell21_510588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_510588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510588 prefixEnd_510588 := by exact prefixLift 510588
  have htrace : WordTrace (prefixWord ++ tailWord_510588) baseStart_510588 baseEnd_510588 := by
    simpa [prefixWord, tailWord_510588, baseEnd_510588] using wordTrace_append hprefix tailTrace_510588
  have hstable : (prefixWord ++ tailWord_510588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510588).length < 2 ^ (prefixWord ++ tailWord_510588).sum := by decide
  have hdescent : baseEnd_510588 < baseStart_510588 := by decide
  rcases family_descends (prefixWord ++ tailWord_510588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510684 : List Nat := [2, 2, 5, 1, 1, 1, 1, 5, 3]
def baseStart_510684 : Nat := 118140960795 + 510684 * 2 ^ 59
def prefixEnd_510684 : Nat := 4983230072969 + 3 ^ 40 * 510684 * 2
def baseEnd_510684 : Nat := 116545046471460080089517

theorem tailTrace_510684 : CollatzResearch.WordTrace tailWord_510684 prefixEnd_510684 116545046471460080089517 := by
  unfold tailWord_510684
  simp only [CollatzResearch.WordTrace]
  refine ⟨9313087840943280364269553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12417450454591040485692737 9313087840943280364269553)
  ·
    refine ⟨6984815880707460273202165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9313087840943280364269553 6984815880707460273202165)
    ·
      refine ⟨654826488816324400612703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6984815880707460273202165 654826488816324400612703)
      ·
        refine ⟨982239733224486600919055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654826488816324400612703 982239733224486600919055)
        ·
          refine ⟨1473359599836729901378583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982239733224486600919055 1473359599836729901378583)
          ·
            refine ⟨2210039399755094852067875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473359599836729901378583 2210039399755094852067875)
            ·
              refine ⟨3315059099632642278101813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2210039399755094852067875 3315059099632642278101813)
              ·
                refine ⟨310786790590560213572045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3315059099632642278101813 310786790590560213572045)
                ·
                  refine ⟨116545046471460080089517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310786790590560213572045 116545046471460080089517)
                  ·
                    rfl

theorem cell21_510684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_510684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510684 prefixEnd_510684 := by exact prefixLift 510684
  have htrace : WordTrace (prefixWord ++ tailWord_510684) baseStart_510684 baseEnd_510684 := by
    simpa [prefixWord, tailWord_510684, baseEnd_510684] using wordTrace_append hprefix tailTrace_510684
  have hstable : (prefixWord ++ tailWord_510684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510684).length < 2 ^ (prefixWord ++ tailWord_510684).sum := by decide
  have hdescent : baseEnd_510684 < baseStart_510684 := by decide
  rcases family_descends (prefixWord ++ tailWord_510684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510760 : List Nat := [2, 1, 5, 1, 1, 1, 5, 2, 3]
def baseStart_510760 : Nat := 118140960795 + 510760 * 2 ^ 59
def prefixEnd_510760 : Nat := 4983230072969 + 3 ^ 40 * 510760 * 2
def baseEnd_510760 : Nat := 116562390706900836822695

theorem tailTrace_510760 : CollatzResearch.WordTrace tailWord_510760 prefixEnd_510760 116562390706900836822695 := by
  unfold tailWord_510760
  simp only [CollatzResearch.WordTrace]
  refine ⟨9314473814805612854152867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12419298419740817138870489 9314473814805612854152867)
  ·
    refine ⟨13971710722208419281229301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9314473814805612854152867 13971710722208419281229301)
    ·
      refine ⟨1309847880207039307615247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13971710722208419281229301 1309847880207039307615247)
      ·
        refine ⟨1964771820310558961422871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1309847880207039307615247 1964771820310558961422871)
        ·
          refine ⟨2947157730465838442134307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1964771820310558961422871 2947157730465838442134307)
          ·
            refine ⟨4420736595698757663201461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2947157730465838442134307 4420736595698757663201461)
            ·
              refine ⟨414444055846758530925137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4420736595698757663201461 414444055846758530925137)
              ·
                refine ⟨310833041885068898193853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414444055846758530925137 310833041885068898193853)
                ·
                  refine ⟨116562390706900836822695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310833041885068898193853 116562390706900836822695)
                  ·
                    rfl

theorem cell21_510760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 3].length) (baseStart_510760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510760 prefixEnd_510760 := by exact prefixLift 510760
  have htrace : WordTrace (prefixWord ++ tailWord_510760) baseStart_510760 baseEnd_510760 := by
    simpa [prefixWord, tailWord_510760, baseEnd_510760] using wordTrace_append hprefix tailTrace_510760
  have hstable : (prefixWord ++ tailWord_510760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510760).length < 2 ^ (prefixWord ++ tailWord_510760).sum := by decide
  have hdescent : baseEnd_510760 < baseStart_510760 := by decide
  rcases family_descends (prefixWord ++ tailWord_510760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510771 : List Nat := [1, 1, 1, 2, 6, 2, 2, 6]
def baseStart_510771 : Nat := 118140960795 + 510771 * 2 ^ 59
def prefixEnd_510771 : Nat := 4983230072969 + 3 ^ 40 * 510771 * 2
def baseEnd_510771 : Nat := 38854967018922420713113

theorem tailTrace_510771 : CollatzResearch.WordTrace tailWord_510771 prefixEnd_510771 38854967018922420713113 := by
  unfold tailWord_510771
  simp only [CollatzResearch.WordTrace]
  refine ⟨18629348832571374586956167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12419565888380916391304111 18629348832571374586956167)
  ·
    refine ⟨27944023248857061880434251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18629348832571374586956167 27944023248857061880434251)
    ·
      refine ⟨41916034873285592820651377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27944023248857061880434251 41916034873285592820651377)
      ·
        refine ⟨31437026154964194615488533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41916034873285592820651377 31437026154964194615488533)
        ·
          refine ⟨1473610601013946622601025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31437026154964194615488533 1473610601013946622601025)
          ·
            refine ⟨1105207950760459966950769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1473610601013946622601025 1105207950760459966950769)
            ·
              refine ⟨828905963070344975213077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1105207950760459966950769 828905963070344975213077)
              ·
                refine ⟨38854967018922420713113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 828905963070344975213077 38854967018922420713113)
                ·
                  rfl

theorem cell21_510771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 6].length) (baseStart_510771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510771 prefixEnd_510771 := by exact prefixLift 510771
  have htrace : WordTrace (prefixWord ++ tailWord_510771) baseStart_510771 baseEnd_510771 := by
    simpa [prefixWord, tailWord_510771, baseEnd_510771] using wordTrace_append hprefix tailTrace_510771
  have hstable : (prefixWord ++ tailWord_510771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510771).length < 2 ^ (prefixWord ++ tailWord_510771).sum := by decide
  have hdescent : baseEnd_510771 < baseStart_510771 := by decide
  rcases family_descends (prefixWord ++ tailWord_510771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510819 : List Nat := [1, 1, 1, 5, 3, 2, 1, 4, 3]
def baseStart_510819 : Nat := 118140960795 + 510819 * 2 ^ 59
def prefixEnd_510819 : Nat := 4983230072969 + 3 ^ 40 * 510819 * 2
def baseEnd_510819 : Nat := 116575855310729845339241

theorem tailTrace_510819 : CollatzResearch.WordTrace tailWord_510819 prefixEnd_510819 116575855310729845339241 := by
  unfold tailWord_510819
  simp only [CollatzResearch.WordTrace]
  refine ⟨18631099536397478784703511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12420733024264985856469007 18631099536397478784703511)
  ·
    refine ⟨27946649304596218177055267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18631099536397478784703511 27946649304596218177055267)
    ·
      refine ⟨41919973956894327265582901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27946649304596218177055267 41919973956894327265582901)
      ·
        refine ⟨3929997558458843181148397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41919973956894327265582901 3929997558458843181148397)
        ·
          refine ⟨1473749084422066192930649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3929997558458843181148397 1473749084422066192930649)
          ·
            refine ⟨1105311813316549644697987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1473749084422066192930649 1105311813316549644697987)
            ·
              refine ⟨1657967719974824467046981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105311813316549644697987 1657967719974824467046981)
              ·
                refine ⟨310868947495279587571309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1657967719974824467046981 310868947495279587571309)
                ·
                  refine ⟨116575855310729845339241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310868947495279587571309 116575855310729845339241)
                  ·
                    rfl

theorem cell21_510819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 3].length) (baseStart_510819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510819 prefixEnd_510819 := by exact prefixLift 510819
  have htrace : WordTrace (prefixWord ++ tailWord_510819) baseStart_510819 baseEnd_510819 := by
    simpa [prefixWord, tailWord_510819, baseEnd_510819] using wordTrace_append hprefix tailTrace_510819
  have hstable : (prefixWord ++ tailWord_510819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510819).length < 2 ^ (prefixWord ++ tailWord_510819).sum := by decide
  have hdescent : baseEnd_510819 < baseStart_510819 := by decide
  rcases family_descends (prefixWord ++ tailWord_510819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510906 : List Nat := [3, 1, 1, 1, 2, 1, 5, 7]
def baseStart_510906 : Nat := 118140960795 + 510906 * 2 ^ 59
def prefixEnd_510906 : Nat := 4983230072969 + 3 ^ 40 * 510906 * 2
def baseEnd_510906 : Nat := 38865236632012342463021

theorem tailTrace_510906 : CollatzResearch.WordTrace tailWord_510906 prefixEnd_510906 38865236632012342463021 := by
  unfold tailWord_510906
  simp only [CollatzResearch.WordTrace]
  refine ⟨4658568171770573160780143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12422848458054861762080381 4658568171770573160780143)
  ·
    refine ⟨6987852257655859741170215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4658568171770573160780143 6987852257655859741170215)
    ·
      refine ⟨10481778386483789611755323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6987852257655859741170215 10481778386483789611755323)
      ·
        refine ⟨15722667579725684417632985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10481778386483789611755323 15722667579725684417632985)
        ·
          refine ⟨11792000684794263313224739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15722667579725684417632985 11792000684794263313224739)
          ·
            refine ⟨17688001027191394969837109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11792000684794263313224739 17688001027191394969837109)
            ·
              refine ⟨1658250096299193278422229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17688001027191394969837109 1658250096299193278422229)
              ·
                refine ⟨38865236632012342463021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1658250096299193278422229 38865236632012342463021)
                ·
                  rfl

theorem cell21_510906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_510906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510906 prefixEnd_510906 := by exact prefixLift 510906
  have htrace : WordTrace (prefixWord ++ tailWord_510906) baseStart_510906 baseEnd_510906 := by
    simpa [prefixWord, tailWord_510906, baseEnd_510906] using wordTrace_append hprefix tailTrace_510906
  have hstable : (prefixWord ++ tailWord_510906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510906).length < 2 ^ (prefixWord ++ tailWord_510906).sum := by decide
  have hdescent : baseEnd_510906 < baseStart_510906 := by decide
  rcases family_descends (prefixWord ++ tailWord_510906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510943 : List Nat := [1, 1, 2, 3, 6, 1, 2, 1, 4]
def baseStart_510943 : Nat := 118140960795 + 510943 * 2 ^ 59
def prefixEnd_510943 : Nat := 4983230072969 + 3 ^ 40 * 510943 * 2
def baseEnd_510943 : Nat := 116604153800133185272321

theorem tailTrace_510943 : CollatzResearch.WordTrace tailWord_510943 prefixEnd_510943 116604153800133185272321 := by
  unfold tailWord_510943
  simp only [CollatzResearch.WordTrace]
  refine ⟨18635622187948247962217483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12423748125298831974811655 18635622187948247962217483)
  ·
    refine ⟨27953433281922371943326225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18635622187948247962217483 27953433281922371943326225)
    ·
      refine ⟨20965074961441778957494669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27953433281922371943326225 20965074961441778957494669)
      ·
        refine ⟨7861903110540667109060501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20965074961441778957494669 7861903110540667109060501)
        ·
          refine ⟨368526708306593770737211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7861903110540667109060501 368526708306593770737211)
          ·
            refine ⟨552790062459890656105817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368526708306593770737211 552790062459890656105817)
            ·
              refine ⟨414592546844917992079363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552790062459890656105817 414592546844917992079363)
              ·
                refine ⟨621888820267376988119045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414592546844917992079363 621888820267376988119045)
                ·
                  refine ⟨116604153800133185272321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 621888820267376988119045 116604153800133185272321)
                  ·
                    rfl

theorem cell21_510943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 4].length) (baseStart_510943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510943 prefixEnd_510943 := by exact prefixLift 510943
  have htrace : WordTrace (prefixWord ++ tailWord_510943) baseStart_510943 baseEnd_510943 := by
    simpa [prefixWord, tailWord_510943, baseEnd_510943] using wordTrace_append hprefix tailTrace_510943
  have hstable : (prefixWord ++ tailWord_510943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510943).length < 2 ^ (prefixWord ++ tailWord_510943).sum := by decide
  have hdescent : baseEnd_510943 < baseStart_510943 := by decide
  rcases family_descends (prefixWord ++ tailWord_510943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510988 : List Nat := [2, 2, 1, 2, 3, 4, 2, 2, 3]
def baseStart_510988 : Nat := 118140960795 + 510988 * 2 ^ 59
def prefixEnd_510988 : Nat := 4983230072969 + 3 ^ 40 * 510988 * 2
def baseEnd_510988 : Nat := 116614423413223107022229

theorem tailTrace_510988 : CollatzResearch.WordTrace tailWord_510988 prefixEnd_510988 116614423413223107022229 := by
  unfold tailWord_510988
  simp only [CollatzResearch.WordTrace]
  refine ⟨9318631736392610323802809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12424842315190147098403745 9318631736392610323802809)
  ·
    refine ⟨6988973802294457742852107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9318631736392610323802809 6988973802294457742852107)
    ·
      refine ⟨10483460703441686614278161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6988973802294457742852107 10483460703441686614278161)
      ·
        refine ⟨7862595527581264960708621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10483460703441686614278161 7862595527581264960708621)
        ·
          refine ⟨2948473322842974360265733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7862595527581264960708621 2948473322842974360265733)
          ·
            refine ⟨552838748033057692549825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2948473322842974360265733 552838748033057692549825)
            ·
              refine ⟨414629061024793269412369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552838748033057692549825 414629061024793269412369)
              ·
                refine ⟨310971795768594952059277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414629061024793269412369 310971795768594952059277)
                ·
                  refine ⟨116614423413223107022229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310971795768594952059277 116614423413223107022229)
                  ·
                    rfl

theorem cell21_510988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_510988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510988 prefixEnd_510988 := by exact prefixLift 510988
  have htrace : WordTrace (prefixWord ++ tailWord_510988) baseStart_510988 baseEnd_510988 := by
    simpa [prefixWord, tailWord_510988, baseEnd_510988] using wordTrace_append hprefix tailTrace_510988
  have hstable : (prefixWord ++ tailWord_510988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510988).length < 2 ^ (prefixWord ++ tailWord_510988).sum := by decide
  have hdescent : baseEnd_510988 < baseStart_510988 := by decide
  rcases family_descends (prefixWord ++ tailWord_510988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510999 : List Nat := [1, 1, 3, 5, 1, 1, 3, 6]
def baseStart_510999 : Nat := 118140960795 + 510999 * 2 ^ 59
def prefixEnd_510999 : Nat := 4983230072969 + 3 ^ 40 * 510999 * 2
def baseEnd_510999 : Nat := 38872311254363177446291

theorem tailTrace_510999 : CollatzResearch.WordTrace tailWord_510999 prefixEnd_510999 38872311254363177446291 := by
  unfold tailWord_510999
  simp only [CollatzResearch.WordTrace]
  refine ⟨18637664675745369526256051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12425109783830246350837367 18637664675745369526256051)
  ·
    refine ⟨27956497013618054289384077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18637664675745369526256051 27956497013618054289384077)
    ·
      refine ⟨10483686380106770358519029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27956497013618054289384077 10483686380106770358519029)
      ·
        refine ⟨982845598135009721111159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10483686380106770358519029 982845598135009721111159)
        ·
          refine ⟨1474268397202514581666739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982845598135009721111159 1474268397202514581666739)
          ·
            refine ⟨2211402595803771872500109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474268397202514581666739 2211402595803771872500109)
            ·
              refine ⟨829275973426414452187541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2211402595803771872500109 829275973426414452187541)
              ·
                refine ⟨38872311254363177446291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 829275973426414452187541 38872311254363177446291)
                ·
                  rfl

theorem cell21_510999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 6].length) (baseStart_510999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_510999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_510999 prefixEnd_510999 := by exact prefixLift 510999
  have htrace : WordTrace (prefixWord ++ tailWord_510999) baseStart_510999 baseEnd_510999 := by
    simpa [prefixWord, tailWord_510999, baseEnd_510999] using wordTrace_append hprefix tailTrace_510999
  have hstable : (prefixWord ++ tailWord_510999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510999).length < 2 ^ (prefixWord ++ tailWord_510999).sum := by decide
  have hdescent : baseEnd_510999 < baseStart_510999 := by decide
  rcases family_descends (prefixWord ++ tailWord_510999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511013 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 5]
def baseStart_511013 : Nat := 118140960795 + 511013 * 2 ^ 59
def prefixEnd_511013 : Nat := 4983230072969 + 3 ^ 40 * 511013 * 2
def baseEnd_511013 : Nat := 116620128753828619105511

theorem tailTrace_511013 : CollatzResearch.WordTrace tailWord_511013 prefixEnd_511013 116620128753828619105511 := by
  unfold tailWord_511013
  simp only [CollatzResearch.WordTrace]
  refine ⟨18638175297694649917265693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12425450198463099944843795 18638175297694649917265693)
  ·
    refine ⟨6989315736635493718974635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18638175297694649917265693 6989315736635493718974635)
    ·
      refine ⟨10483973604953240578461953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6989315736635493718974635 10483973604953240578461953)
      ·
        refine ⟨7862980203714930433846465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10483973604953240578461953 7862980203714930433846465)
        ·
          refine ⟨5897235152786197825384849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7862980203714930433846465 5897235152786197825384849)
          ·
            refine ⟨4422926364589648369038637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5897235152786197825384849 4422926364589648369038637)
            ·
              refine ⟨1658597386721118138389489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4422926364589648369038637 1658597386721118138389489)
              ·
                refine ⟨1243948040040838603792117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1658597386721118138389489 1243948040040838603792117)
                ·
                  refine ⟨116620128753828619105511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1243948040040838603792117 116620128753828619105511)
                  ·
                    rfl

theorem cell21_511013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_511013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511013 prefixEnd_511013 := by exact prefixLift 511013
  have htrace : WordTrace (prefixWord ++ tailWord_511013) baseStart_511013 baseEnd_511013 := by
    simpa [prefixWord, tailWord_511013, baseEnd_511013] using wordTrace_append hprefix tailTrace_511013
  have hstable : (prefixWord ++ tailWord_511013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511013).length < 2 ^ (prefixWord ++ tailWord_511013).sum := by decide
  have hdescent : baseEnd_511013 < baseStart_511013 := by decide
  rcases family_descends (prefixWord ++ tailWord_511013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511027 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 6]
def baseStart_511027 : Nat := 118140960795 + 511027 * 2 ^ 59
def prefixEnd_511027 : Nat := 4983230072969 + 3 ^ 40 * 511027 * 2
def baseEnd_511027 : Nat := 116623323744567705872149

theorem tailTrace_511027 : CollatzResearch.WordTrace tailWord_511027 prefixEnd_511027 116623323744567705872149 := by
  unfold tailWord_511027
  simp only [CollatzResearch.WordTrace]
  refine ⟨18638685919643930308275335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12425790613095953538850223 18638685919643930308275335)
  ·
    refine ⟨27958028879465895462413003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18638685919643930308275335 27958028879465895462413003)
    ·
      refine ⟨41937043319198843193619505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27958028879465895462413003 41937043319198843193619505)
      ·
        refine ⟨31452782489399132395214629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41937043319198843193619505 31452782489399132395214629)
        ·
          refine ⟨5897396716762337324102743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31452782489399132395214629 5897396716762337324102743)
          ·
            refine ⟨8846095075143505986154115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5897396716762337324102743 8846095075143505986154115)
            ·
              refine ⟨13269142612715258979231173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8846095075143505986154115 13269142612715258979231173)
              ·
                refine ⟨2487964239884111058605845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13269142612715258979231173 2487964239884111058605845)
                ·
                  refine ⟨116623323744567705872149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2487964239884111058605845 116623323744567705872149)
                  ·
                    rfl

theorem cell21_511027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 6].length) (baseStart_511027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511027 prefixEnd_511027 := by exact prefixLift 511027
  have htrace : WordTrace (prefixWord ++ tailWord_511027) baseStart_511027 baseEnd_511027 := by
    simpa [prefixWord, tailWord_511027, baseEnd_511027] using wordTrace_append hprefix tailTrace_511027
  have hstable : (prefixWord ++ tailWord_511027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511027).length < 2 ^ (prefixWord ++ tailWord_511027).sum := by decide
  have hdescent : baseEnd_511027 < baseStart_511027 := by decide
  rcases family_descends (prefixWord ++ tailWord_511027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511061 : List Nat := [1, 3, 2, 2, 1, 2, 5, 1, 4]
def baseStart_511061 : Nat := 118140960795 + 511061 * 2 ^ 59
def prefixEnd_511061 : Nat := 4983230072969 + 3 ^ 40 * 511061 * 2
def baseEnd_511061 : Nat := 116631083007791202305413

theorem tailTrace_511061 : CollatzResearch.WordTrace tailWord_511061 prefixEnd_511061 116631083007791202305413 := by
  unfold tailWord_511061
  simp only [CollatzResearch.WordTrace]
  refine ⟨18639926001520754115013037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12426617334347169410008691 18639926001520754115013037)
  ·
    refine ⟨6989972250570282793129889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18639926001520754115013037 6989972250570282793129889)
    ·
      refine ⟨5242479187927712094847417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6989972250570282793129889 5242479187927712094847417)
      ·
        refine ⟨3931859390945784071135563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5242479187927712094847417 3931859390945784071135563)
        ·
          refine ⟨5897789086418676106703345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3931859390945784071135563 5897789086418676106703345)
          ·
            refine ⟨4423341814814007080027509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5897789086418676106703345 4423341814814007080027509)
            ·
              refine ⟨414688295138813163752579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4423341814814007080027509 414688295138813163752579)
              ·
                refine ⟨622032442708219745628869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414688295138813163752579 622032442708219745628869)
                ·
                  refine ⟨116631083007791202305413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 622032442708219745628869 116631083007791202305413)
                  ·
                    rfl

theorem cell21_511061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_511061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511061 prefixEnd_511061 := by exact prefixLift 511061
  have htrace : WordTrace (prefixWord ++ tailWord_511061) baseStart_511061 baseEnd_511061 := by
    simpa [prefixWord, tailWord_511061, baseEnd_511061] using wordTrace_append hprefix tailTrace_511061
  have hstable : (prefixWord ++ tailWord_511061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511061).length < 2 ^ (prefixWord ++ tailWord_511061).sum := by decide
  have hdescent : baseEnd_511061 < baseStart_511061 := by decide
  rcases family_descends (prefixWord ++ tailWord_511061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511148 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 9]
def baseStart_511148 : Nat := 118140960795 + 511148 * 2 ^ 59
def prefixEnd_511148 : Nat := 4983230072969 + 3 ^ 40 * 511148 * 2
def baseEnd_511148 : Nat := 116650937593098384355235

theorem tailTrace_511148 : CollatzResearch.WordTrace tailWord_511148 prefixEnd_511148 116650937593098384355235 := by
  unfold tailWord_511148
  simp only [CollatzResearch.WordTrace]
  refine ⟨9321549576102783986715049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12428732768137045315620065 9321549576102783986715049)
  ·
    refine ⟨6991162182077087990036287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9321549576102783986715049 6991162182077087990036287)
    ·
      refine ⟨10486743273115631985054431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6991162182077087990036287 10486743273115631985054431)
      ·
        refine ⟨15730114909673447977581647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10486743273115631985054431 15730114909673447977581647)
        ·
          refine ⟨23595172364510171966372471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15730114909673447977581647 23595172364510171966372471)
          ·
            refine ⟨35392758546765257949558707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23595172364510171966372471 35392758546765257949558707)
            ·
              refine ⟨53089137820147886924338061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35392758546765257949558707 53089137820147886924338061)
              ·
                refine ⟨19908426682555457596626773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53089137820147886924338061 19908426682555457596626773)
                ·
                  refine ⟨116650937593098384355235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19908426682555457596626773 116650937593098384355235)
                  ·
                    rfl

theorem cell21_511148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_511148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511148 prefixEnd_511148 := by exact prefixLift 511148
  have htrace : WordTrace (prefixWord ++ tailWord_511148) baseStart_511148 baseEnd_511148 := by
    simpa [prefixWord, tailWord_511148, baseEnd_511148] using wordTrace_append hprefix tailTrace_511148
  have hstable : (prefixWord ++ tailWord_511148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511148).length < 2 ^ (prefixWord ++ tailWord_511148).sum := by decide
  have hdescent : baseEnd_511148 < baseStart_511148 := by decide
  rcases family_descends (prefixWord ++ tailWord_511148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511168 : List Nat := [2, 1, 1, 2, 7, 1, 1, 6]
def baseStart_511168 : Nat := 118140960795 + 511168 * 2 ^ 59
def prefixEnd_511168 : Nat := 4983230072969 + 3 ^ 40 * 511168 * 2
def baseEnd_511168 : Nat := 38885167288527598007287

theorem tailTrace_511168 : CollatzResearch.WordTrace tailWord_511168 prefixEnd_511168 38885167288527598007287 := by
  unfold tailWord_511168
  simp only [CollatzResearch.WordTrace]
  refine ⟨9321914306066555694579079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12429219074755407592772105 9321914306066555694579079)
  ·
    refine ⟨13982871459099833541868619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9321914306066555694579079 13982871459099833541868619)
    ·
      refine ⟨20974307188649750312802929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13982871459099833541868619 20974307188649750312802929)
      ·
        refine ⟨15730730391487312734602197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20974307188649750312802929 15730730391487312734602197)
        ·
          refine ⟨368688993550483892217239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15730730391487312734602197 368688993550483892217239)
          ·
            refine ⟨553033490325725838325859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368688993550483892217239 553033490325725838325859)
            ·
              refine ⟨829550235488588757488789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553033490325725838325859 829550235488588757488789)
              ·
                refine ⟨38885167288527598007287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 829550235488588757488789 38885167288527598007287)
                ·
                  rfl

theorem cell21_511168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 6].length) (baseStart_511168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511168 prefixEnd_511168 := by exact prefixLift 511168
  have htrace : WordTrace (prefixWord ++ tailWord_511168) baseStart_511168 baseEnd_511168 := by
    simpa [prefixWord, tailWord_511168, baseEnd_511168] using wordTrace_append hprefix tailTrace_511168
  have hstable : (prefixWord ++ tailWord_511168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511168).length < 2 ^ (prefixWord ++ tailWord_511168).sum := by decide
  have hdescent : baseEnd_511168 < baseStart_511168 := by decide
  rcases family_descends (prefixWord ++ tailWord_511168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511182 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_511182 : Nat := 118140960795 + 511182 * 2 ^ 59
def prefixEnd_511182 : Nat := 4983230072969 + 3 ^ 40 * 511182 * 2
def baseEnd_511182 : Nat := 116658696856321880788499

theorem tailTrace_511182 : CollatzResearch.WordTrace tailWord_511182 prefixEnd_511182 116658696856321880788499 := by
  unfold tailWord_511182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330542404260298972520975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12429559489388261186778533 2330542404260298972520975)
  ·
    refine ⟨3495813606390448458781463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2330542404260298972520975 3495813606390448458781463)
    ·
      refine ⟨5243720409585672688172195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3495813606390448458781463 5243720409585672688172195)
      ·
        refine ⟨7865580614378509032258293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5243720409585672688172195 7865580614378509032258293)
        ·
          refine ⟨737398182597985221774215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7865580614378509032258293 737398182597985221774215)
          ·
            refine ⟨1106097273896977832661323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737398182597985221774215 1106097273896977832661323)
            ·
              refine ⟨1659145910845466748991985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1106097273896977832661323 1659145910845466748991985)
              ·
                refine ⟨1244359433134100061743989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1659145910845466748991985 1244359433134100061743989)
                ·
                  refine ⟨116658696856321880788499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1244359433134100061743989 116658696856321880788499)
                  ·
                    rfl

theorem cell21_511182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_511182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511182 prefixEnd_511182 := by exact prefixLift 511182
  have htrace : WordTrace (prefixWord ++ tailWord_511182) baseStart_511182 baseEnd_511182 := by
    simpa [prefixWord, tailWord_511182, baseEnd_511182] using wordTrace_append hprefix tailTrace_511182
  have hstable : (prefixWord ++ tailWord_511182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511182).length < 2 ^ (prefixWord ++ tailWord_511182).sum := by decide
  have hdescent : baseEnd_511182 < baseStart_511182 := by decide
  rcases family_descends (prefixWord ++ tailWord_511182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511210 : List Nat := [3, 1, 3, 1, 1, 4, 8]
def baseStart_511210 : Nat := 118140960795 + 511210 * 2 ^ 59
def prefixEnd_511210 : Nat := 4983230072969 + 3 ^ 40 * 511210 * 2
def baseEnd_511210 : Nat := 12962787426422228257975

theorem tailTrace_511210 : CollatzResearch.WordTrace tailWord_511210 prefixEnd_511210 12962787426422228257975 := by
  unfold tailWord_511210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4661340119495238140546771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12430240318653968374791389 4661340119495238140546771)
  ·
    refine ⟨6992010179242857210820157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4661340119495238140546771 6992010179242857210820157)
    ·
      refine ⟨2622003817216071454057559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6992010179242857210820157 2622003817216071454057559)
      ·
        refine ⟨3933005725824107181086339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2622003817216071454057559 3933005725824107181086339)
        ·
          refine ⟨5899508588736160771629509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3933005725824107181086339 5899508588736160771629509)
          ·
            refine ⟨1106157860388030144680533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5899508588736160771629509 1106157860388030144680533)
            ·
              refine ⟨12962787426422228257975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1106157860388030144680533 12962787426422228257975)
              ·
                rfl

theorem cell21_511210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 8].length) (baseStart_511210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511210 prefixEnd_511210 := by exact prefixLift 511210
  have htrace : WordTrace (prefixWord ++ tailWord_511210) baseStart_511210 baseEnd_511210 := by
    simpa [prefixWord, tailWord_511210, baseEnd_511210] using wordTrace_append hprefix tailTrace_511210
  have hstable : (prefixWord ++ tailWord_511210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511210).length < 2 ^ (prefixWord ++ tailWord_511210).sum := by decide
  have hdescent : baseEnd_511210 < baseStart_511210 := by decide
  rcases family_descends (prefixWord ++ tailWord_511210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511213 : List Nat := [1, 5, 1, 2, 2, 1, 3, 2, 4]
def baseStart_511213 : Nat := 118140960795 + 511213 * 2 ^ 59
def prefixEnd_511213 : Nat := 4983230072969 + 3 ^ 40 * 511213 * 2
def baseEnd_511213 : Nat := 116665771478672715771769

theorem tailTrace_511213 : CollatzResearch.WordTrace tailWord_511213 prefixEnd_511213 116665771478672715771769 := by
  unfold tailWord_511213
  simp only [CollatzResearch.WordTrace]
  refine ⟨18645469896970084074546293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12430313264646722716364195 18645469896970084074546293)
  ·
    refine ⟨1748012802840945381988715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18645469896970084074546293 1748012802840945381988715)
    ·
      refine ⟨2622019204261418072983073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1748012802840945381988715 2622019204261418072983073)
      ·
        refine ⟨1966514403196063554737305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2622019204261418072983073 1966514403196063554737305)
        ·
          refine ⟨1474885802397047666052979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1966514403196063554737305 1474885802397047666052979)
          ·
            refine ⟨2212328703595571499079469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474885802397047666052979 2212328703595571499079469)
            ·
              refine ⟨829623263848339312154801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2212328703595571499079469 829623263848339312154801)
              ·
                refine ⟨622217447886254484116101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 829623263848339312154801 622217447886254484116101)
                ·
                  refine ⟨116665771478672715771769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 622217447886254484116101 116665771478672715771769)
                  ·
                    rfl

theorem cell21_511213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_511213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511213 prefixEnd_511213 := by exact prefixLift 511213
  have htrace : WordTrace (prefixWord ++ tailWord_511213) baseStart_511213 baseEnd_511213 := by
    simpa [prefixWord, tailWord_511213, baseEnd_511213] using wordTrace_append hprefix tailTrace_511213
  have hstable : (prefixWord ++ tailWord_511213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511213).length < 2 ^ (prefixWord ++ tailWord_511213).sum := by decide
  have hdescent : baseEnd_511213 < baseStart_511213 := by decide
  rcases family_descends (prefixWord ++ tailWord_511213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511230 : List Nat := [4, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_511230 : Nat := 118140960795 + 511230 * 2 ^ 59
def prefixEnd_511230 : Nat := 4983230072969 + 3 ^ 40 * 511230 * 2
def baseEnd_511230 : Nat := 116669651110284463988401

theorem tailTrace_511230 : CollatzResearch.WordTrace tailWord_511230 prefixEnd_511230 116669651110284463988401 := by
  unfold tailWord_511230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330761242238561997239393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12430726625272330651943429 2330761242238561997239393)
  ·
    refine ⟨1748070931678921497929545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2330761242238561997239393 1748070931678921497929545)
    ·
      refine ⟨1311053198759191123447159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1748070931678921497929545 1311053198759191123447159)
      ·
        refine ⟨1966579798138786685170739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311053198759191123447159 1966579798138786685170739)
        ·
          refine ⟨2949869697208180027756109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966579798138786685170739 2949869697208180027756109)
          ·
            refine ⟨1106201136453067510408541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2949869697208180027756109 1106201136453067510408541)
            ·
              refine ⟨414825426169900316403203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1106201136453067510408541 414825426169900316403203)
              ·
                refine ⟨622238139254850474604805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414825426169900316403203 622238139254850474604805)
                ·
                  refine ⟨116669651110284463988401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 622238139254850474604805 116669651110284463988401)
                  ·
                    rfl

theorem cell21_511230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_511230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511230 prefixEnd_511230 := by exact prefixLift 511230
  have htrace : WordTrace (prefixWord ++ tailWord_511230) baseStart_511230 baseEnd_511230 := by
    simpa [prefixWord, tailWord_511230, baseEnd_511230] using wordTrace_append hprefix tailTrace_511230
  have hstable : (prefixWord ++ tailWord_511230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511230).length < 2 ^ (prefixWord ++ tailWord_511230).sum := by decide
  have hdescent : baseEnd_511230 < baseStart_511230 := by decide
  rcases family_descends (prefixWord ++ tailWord_511230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511250 : List Nat := [3, 2, 4, 2, 2, 1, 1, 3, 3]
def baseStart_511250 : Nat := 118140960795 + 511250 * 2 ^ 59
def prefixEnd_511250 : Nat := 4983230072969 + 3 ^ 40 * 511250 * 2
def baseEnd_511250 : Nat := 116674215382768873655027

theorem tailTrace_511250 : CollatzResearch.WordTrace tailWord_511250 prefixEnd_511250 116674215382768873655027 := by
  unfold tailWord_511250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4661704849459009848410801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12431212931890692929095469 4661704849459009848410801)
  ·
    refine ⟨3496278637094257386308101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4661704849459009848410801 3496278637094257386308101)
    ·
      refine ⟨655552244455173259932769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3496278637094257386308101 655552244455173259932769)
      ·
        refine ⟨491664183341379944949577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 655552244455173259932769 491664183341379944949577)
        ·
          refine ⟨368748137506034958712183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491664183341379944949577 368748137506034958712183)
          ·
            refine ⟨553122206259052438068275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368748137506034958712183 553122206259052438068275)
            ·
              refine ⟨829683309388578657102413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553122206259052438068275 829683309388578657102413)
              ·
                refine ⟨311131241020716996413405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 829683309388578657102413 311131241020716996413405)
                ·
                  refine ⟨116674215382768873655027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311131241020716996413405 116674215382768873655027)
                  ·
                    rfl

theorem cell21_511250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_511250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511250 prefixEnd_511250 := by exact prefixLift 511250
  have htrace : WordTrace (prefixWord ++ tailWord_511250) baseStart_511250 baseEnd_511250 := by
    simpa [prefixWord, tailWord_511250, baseEnd_511250] using wordTrace_append hprefix tailTrace_511250
  have hstable : (prefixWord ++ tailWord_511250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511250).length < 2 ^ (prefixWord ++ tailWord_511250).sum := by decide
  have hdescent : baseEnd_511250 < baseStart_511250 := by decide
  rcases family_descends (prefixWord ++ tailWord_511250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511255 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 8]
def baseStart_511255 : Nat := 118140960795 + 511255 * 2 ^ 59
def prefixEnd_511255 : Nat := 4983230072969 + 3 ^ 40 * 511255 * 2
def baseEnd_511255 : Nat := 116675356450889976071683

theorem tailTrace_511255 : CollatzResearch.WordTrace tailWord_511255 prefixEnd_511255 116675356450889976071683 := by
  unfold tailWord_511255
  simp only [CollatzResearch.WordTrace]
  refine ⟨18647001762817925247575219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12431334508545283498383479 18647001762817925247575219)
  ·
    refine ⟨27970502644226887871362829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18647001762817925247575219 27970502644226887871362829)
    ·
      refine ⟨10488938491585082951761061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27970502644226887871362829 10488938491585082951761061)
      ·
        refine ⟨1966675967172203053455199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10488938491585082951761061 1966675967172203053455199)
        ·
          refine ⟨2950013950758304580182799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966675967172203053455199 2950013950758304580182799)
          ·
            refine ⟨4425020926137456870274199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2950013950758304580182799 4425020926137456870274199)
            ·
              refine ⟨6637531389206185305411299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4425020926137456870274199 6637531389206185305411299)
              ·
                refine ⟨9956297083809277958116949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6637531389206185305411299 9956297083809277958116949)
                ·
                  refine ⟨116675356450889976071683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9956297083809277958116949 116675356450889976071683)
                  ·
                    rfl

theorem cell21_511255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 8].length) (baseStart_511255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511255 prefixEnd_511255 := by exact prefixLift 511255
  have htrace : WordTrace (prefixWord ++ tailWord_511255) baseStart_511255 baseEnd_511255 := by
    simpa [prefixWord, tailWord_511255, baseEnd_511255] using wordTrace_append hprefix tailTrace_511255
  have hstable : (prefixWord ++ tailWord_511255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511255).length < 2 ^ (prefixWord ++ tailWord_511255).sum := by decide
  have hdescent : baseEnd_511255 < baseStart_511255 := by decide
  rcases family_descends (prefixWord ++ tailWord_511255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511272 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 6]
def baseStart_511272 : Nat := 118140960795 + 511272 * 2 ^ 59
def prefixEnd_511272 : Nat := 4983230072969 + 3 ^ 40 * 511272 * 2
def baseEnd_511272 : Nat := 116679236082501724288315

theorem tailTrace_511272 : CollatzResearch.WordTrace tailWord_511272 prefixEnd_511272 116679236082501724288315 := by
  unfold tailWord_511272
  simp only [CollatzResearch.WordTrace]
  refine ⟨9323810901878168575472035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12431747869170891433962713 9323810901878168575472035)
  ·
    refine ⟨13985716352817252863208053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9323810901878168575472035 13985716352817252863208053)
    ·
      refine ⟨1311160908076617455925755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13985716352817252863208053 1311160908076617455925755)
      ·
        refine ⟨1966741362114926183888633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311160908076617455925755 1966741362114926183888633)
        ·
          refine ⟨1475056021586194637916475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1966741362114926183888633 1475056021586194637916475)
          ·
            refine ⟨2212584032379291956874713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475056021586194637916475 2212584032379291956874713)
            ·
              refine ⟨1659438024284468967656035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2212584032379291956874713 1659438024284468967656035)
              ·
                refine ⟨2489157036426703451484053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659438024284468967656035 2489157036426703451484053)
                ·
                  refine ⟨116679236082501724288315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2489157036426703451484053 116679236082501724288315)
                  ·
                    rfl

theorem cell21_511272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_511272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511272 prefixEnd_511272 := by exact prefixLift 511272
  have htrace : WordTrace (prefixWord ++ tailWord_511272) baseStart_511272 baseEnd_511272 := by
    simpa [prefixWord, tailWord_511272, baseEnd_511272] using wordTrace_append hprefix tailTrace_511272
  have hstable : (prefixWord ++ tailWord_511272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511272).length < 2 ^ (prefixWord ++ tailWord_511272).sum := by decide
  have hdescent : baseEnd_511272 < baseStart_511272 := by decide
  rcases family_descends (prefixWord ++ tailWord_511272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511289 : List Nat := [1, 2, 1, 6, 2, 1, 1, 3, 4]
def baseStart_511289 : Nat := 118140960795 + 511289 * 2 ^ 59
def prefixEnd_511289 : Nat := 4983230072969 + 3 ^ 40 * 511289 * 2
def baseEnd_511289 : Nat := 116683115714113472504947

theorem tailTrace_511289 : CollatzResearch.WordTrace tailWord_511289 prefixEnd_511289 116683115714113472504947 := by
  unfold tailWord_511289
  simp only [CollatzResearch.WordTrace]
  refine ⟨18648241844694749054312921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12432161229796499369541947 18648241844694749054312921)
  ·
    refine ⟨13986181383521061790734691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18648241844694749054312921 13986181383521061790734691)
    ·
      refine ⟨20979272075281592686102037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13986181383521061790734691 20979272075281592686102037)
      ·
        refine ⟨983403378528824657161033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20979272075281592686102037 983403378528824657161033)
        ·
          refine ⟨737552533896618492870775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 983403378528824657161033 737552533896618492870775)
          ·
            refine ⟨1106328800844927739306163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737552533896618492870775 1106328800844927739306163)
            ·
              refine ⟨1659493201267391608959245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1106328800844927739306163 1659493201267391608959245)
              ·
                refine ⟨622309950475271853359717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1659493201267391608959245 622309950475271853359717)
                ·
                  refine ⟨116683115714113472504947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 622309950475271853359717 116683115714113472504947)
                  ·
                    rfl

theorem cell21_511289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_511289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511289 prefixEnd_511289 := by exact prefixLift 511289
  have htrace : WordTrace (prefixWord ++ tailWord_511289) baseStart_511289 baseEnd_511289 := by
    simpa [prefixWord, tailWord_511289, baseEnd_511289] using wordTrace_append hprefix tailTrace_511289
  have hstable : (prefixWord ++ tailWord_511289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511289).length < 2 ^ (prefixWord ++ tailWord_511289).sum := by decide
  have hdescent : baseEnd_511289 < baseStart_511289 := by decide
  rcases family_descends (prefixWord ++ tailWord_511289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511407 : List Nat := [1, 1, 2, 1, 2, 2, 1, 7, 4]
def baseStart_511407 : Nat := 118140960795 + 511407 * 2 ^ 59
def prefixEnd_511407 : Nat := 4983230072969 + 3 ^ 40 * 511407 * 2
def baseEnd_511407 : Nat := 116710044921771489538039

theorem tailTrace_511407 : CollatzResearch.WordTrace tailWord_511407 prefixEnd_511407 116710044921771489538039 := by
  unfold tailWord_511407
  simp only [CollatzResearch.WordTrace]
  refine ⟨18652545658267255207108475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12435030438844836804738983 18652545658267255207108475)
  ·
    refine ⟨27978818487400882810662713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18652545658267255207108475 27978818487400882810662713)
    ·
      refine ⟨20984113865550662107997035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27978818487400882810662713 20984113865550662107997035)
      ·
        refine ⟨31476170798325993161995553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20984113865550662107997035 31476170798325993161995553)
        ·
          refine ⟨23607128098744494871496665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31476170798325993161995553 23607128098744494871496665)
          ·
            refine ⟨17705346074058371153622499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23607128098744494871496665 17705346074058371153622499)
            ·
              refine ⟨26558019111087556730433749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17705346074058371153622499 26558019111087556730433749)
              ·
                refine ⟨622453572916114610869541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26558019111087556730433749 622453572916114610869541)
                ·
                  refine ⟨116710044921771489538039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 622453572916114610869541 116710044921771489538039)
                  ·
                    rfl

theorem cell21_511407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 4].length) (baseStart_511407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511407 prefixEnd_511407 := by exact prefixLift 511407
  have htrace : WordTrace (prefixWord ++ tailWord_511407) baseStart_511407 baseEnd_511407 := by
    simpa [prefixWord, tailWord_511407, baseEnd_511407] using wordTrace_append hprefix tailTrace_511407
  have hstable : (prefixWord ++ tailWord_511407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511407).length < 2 ^ (prefixWord ++ tailWord_511407).sum := by decide
  have hdescent : baseEnd_511407 < baseStart_511407 := by decide
  rcases family_descends (prefixWord ++ tailWord_511407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511444 : List Nat := [2, 4, 1, 2, 3, 1, 3, 2, 3]
def baseStart_511444 : Nat := 118140960795 + 511444 * 2 ^ 59
def prefixEnd_511444 : Nat := 4983230072969 + 3 ^ 40 * 511444 * 2
def baseEnd_511444 : Nat := 116718488825867647421297

theorem tailTrace_511444 : CollatzResearch.WordTrace tailWord_511444 prefixEnd_511444 116718488825867647421297 := by
  unfold tailWord_511444
  simp only [CollatzResearch.WordTrace]
  refine ⟨9326947579566605263102693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12435930106088807017470257 9326947579566605263102693)
  ·
    refine ⟨1748802671168738486831755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9326947579566605263102693 1748802671168738486831755)
    ·
      refine ⟨2623204006753107730247633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1748802671168738486831755 2623204006753107730247633)
      ·
        refine ⟨1967403005064830797685725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2623204006753107730247633 1967403005064830797685725)
        ·
          refine ⟨737776126899311549132147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1967403005064830797685725 737776126899311549132147)
          ·
            refine ⟨1106664190348967323698221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737776126899311549132147 1106664190348967323698221)
            ·
              refine ⟨414999071380862746386833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1106664190348967323698221 414999071380862746386833)
              ·
                refine ⟨311249303535647059790125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414999071380862746386833 311249303535647059790125)
                ·
                  refine ⟨116718488825867647421297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311249303535647059790125 116718488825867647421297)
                  ·
                    rfl

theorem cell21_511444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_511444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511444 prefixEnd_511444 := by exact prefixLift 511444
  have htrace : WordTrace (prefixWord ++ tailWord_511444) baseStart_511444 baseEnd_511444 := by
    simpa [prefixWord, tailWord_511444, baseEnd_511444] using wordTrace_append hprefix tailTrace_511444
  have hstable : (prefixWord ++ tailWord_511444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511444).length < 2 ^ (prefixWord ++ tailWord_511444).sum := by decide
  have hdescent : baseEnd_511444 < baseStart_511444 := by decide
  rcases family_descends (prefixWord ++ tailWord_511444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511573 : List Nat := [1, 3, 2, 2, 1, 1, 1, 10]
def baseStart_511573 : Nat := 118140960795 + 511573 * 2 ^ 59
def prefixEnd_511573 : Nat := 4983230072969 + 3 ^ 40 * 511573 * 2
def baseEnd_511573 : Nat := 38915976127797363257011

theorem tailTrace_511573 : CollatzResearch.WordTrace tailWord_511573 prefixEnd_511573 38915976127797363257011 := by
  unfold tailWord_511573
  simp only [CollatzResearch.WordTrace]
  refine ⟨18658600175665865557651373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12439066783777243705100915 18658600175665865557651373)
  ·
    refine ⟨6996975065874699584119265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18658600175665865557651373 6996975065874699584119265)
    ·
      refine ⟨5247731299406024688089449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6996975065874699584119265 5247731299406024688089449)
      ·
        refine ⟨3935798474554518516067087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5247731299406024688089449 3935798474554518516067087)
        ·
          refine ⟨5903697711831777774100631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3935798474554518516067087 5903697711831777774100631)
          ·
            refine ⟨8855546567747666661150947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5903697711831777774100631 8855546567747666661150947)
            ·
              refine ⟨13283319851621499991726421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8855546567747666661150947 13283319851621499991726421)
              ·
                refine ⟨38915976127797363257011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13283319851621499991726421 38915976127797363257011)
                ·
                  rfl

theorem cell21_511573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 10].length) (baseStart_511573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511573 prefixEnd_511573 := by exact prefixLift 511573
  have htrace : WordTrace (prefixWord ++ tailWord_511573) baseStart_511573 baseEnd_511573 := by
    simpa [prefixWord, tailWord_511573, baseEnd_511573] using wordTrace_append hprefix tailTrace_511573
  have hstable : (prefixWord ++ tailWord_511573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511573).length < 2 ^ (prefixWord ++ tailWord_511573).sum := by decide
  have hdescent : baseEnd_511573 < baseStart_511573 := by decide
  rcases family_descends (prefixWord ++ tailWord_511573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511669 : List Nat := [1, 3, 3, 3, 2, 1, 2, 2, 4]
def baseStart_511669 : Nat := 118140960795 + 511669 * 2 ^ 59
def prefixEnd_511669 : Nat := 4983230072969 + 3 ^ 40 * 511669 * 2
def baseEnd_511669 : Nat := 116769836891317256170837

theorem tailTrace_511669 : CollatzResearch.WordTrace tailWord_511669 prefixEnd_511669 116769836891317256170837 := by
  unfold tailWord_511669
  simp only [CollatzResearch.WordTrace]
  refine ⟨18662101583318073953146061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12441401055545382635430707 18662101583318073953146061)
  ·
    refine ⟨6998288093744277732429773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18662101583318073953146061 6998288093744277732429773)
    ·
      refine ⟨2624358035154104149661165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6998288093744277732429773 2624358035154104149661165)
      ·
        refine ⟨984134263182789056122937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2624358035154104149661165 984134263182789056122937)
        ·
          refine ⟨738100697387091792092203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 984134263182789056122937 738100697387091792092203)
          ·
            refine ⟨1107151046080637688138305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738100697387091792092203 1107151046080637688138305)
            ·
              refine ⟨830363284560478266103729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1107151046080637688138305 830363284560478266103729)
              ·
                refine ⟨622772463420358699577797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 830363284560478266103729 622772463420358699577797)
                ·
                  refine ⟨116769836891317256170837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 622772463420358699577797 116769836891317256170837)
                  ·
                    rfl

theorem cell21_511669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_511669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511669 prefixEnd_511669 := by exact prefixLift 511669
  have htrace : WordTrace (prefixWord ++ tailWord_511669) baseStart_511669 baseEnd_511669 := by
    simpa [prefixWord, tailWord_511669, baseEnd_511669] using wordTrace_append hprefix tailTrace_511669
  have hstable : (prefixWord ++ tailWord_511669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511669).length < 2 ^ (prefixWord ++ tailWord_511669).sum := by decide
  have hdescent : baseEnd_511669 < baseStart_511669 := by decide
  rcases family_descends (prefixWord ++ tailWord_511669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511680 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 5]
def baseStart_511680 : Nat := 118140960795 + 511680 * 2 ^ 59
def prefixEnd_511680 : Nat := 4983230072969 + 3 ^ 40 * 511680 * 2
def baseEnd_511680 : Nat := 116772347241183681487481

theorem tailTrace_511680 : CollatzResearch.WordTrace tailWord_511680 prefixEnd_511680 116772347241183681487481 := by
  unfold tailWord_511680
  simp only [CollatzResearch.WordTrace]
  refine ⟨9331251393139111415898247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12441668524185481887864329 9331251393139111415898247)
  ·
    refine ⟨13996877089708667123847371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9331251393139111415898247 13996877089708667123847371)
    ·
      refine ⟨20995315634563000685771057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13996877089708667123847371 20995315634563000685771057)
      ·
        refine ⟨15746486725922250514328293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20995315634563000685771057 15746486725922250514328293)
        ·
          refine ⟨2952466261110421971436555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15746486725922250514328293 2952466261110421971436555)
          ·
            refine ⟨4428699391665632957154833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2952466261110421971436555 4428699391665632957154833)
            ·
              refine ⟨3321524543749224717866125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4428699391665632957154833 3321524543749224717866125)
              ·
                refine ⟨1245571703905959269199797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3321524543749224717866125 1245571703905959269199797)
                ·
                  refine ⟨116772347241183681487481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1245571703905959269199797 116772347241183681487481)
                  ·
                    rfl

theorem cell21_511680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_511680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511680 prefixEnd_511680 := by exact prefixLift 511680
  have htrace : WordTrace (prefixWord ++ tailWord_511680) baseStart_511680 baseEnd_511680 := by
    simpa [prefixWord, tailWord_511680, baseEnd_511680] using wordTrace_append hprefix tailTrace_511680
  have hstable : (prefixWord ++ tailWord_511680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511680).length < 2 ^ (prefixWord ++ tailWord_511680).sum := by decide
  have hdescent : baseEnd_511680 < baseStart_511680 := by decide
  rcases family_descends (prefixWord ++ tailWord_511680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511686 : List Nat := [6, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_511686 : Nat := 118140960795 + 511686 * 2 ^ 59
def prefixEnd_511686 : Nat := 4983230072969 + 3 ^ 40 * 511686 * 2
def baseEnd_511686 : Nat := 116773716522929004387469

theorem tailTrace_511686 : CollatzResearch.WordTrace tailWord_511686 prefixEnd_511686 116773716522929004387469 := by
  unfold tailWord_511686
  simp only [CollatzResearch.WordTrace]
  refine ⟨583210050758015183016091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12441814416170990571009941 583210050758015183016091)
  ·
    refine ⟨874815076137022774524137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 583210050758015183016091 874815076137022774524137)
    ·
      refine ⟨656111307102767080893103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 874815076137022774524137 656111307102767080893103)
      ·
        refine ⟨984166960654150621339655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656111307102767080893103 984166960654150621339655)
        ·
          refine ⟨1476250440981225932009483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984166960654150621339655 1476250440981225932009483)
          ·
            refine ⟨2214375661471838898014225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476250440981225932009483 2214375661471838898014225)
            ·
              refine ⟨1660781746103879173510669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2214375661471838898014225 1660781746103879173510669)
              ·
                refine ⟨622793154788954690066501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1660781746103879173510669 622793154788954690066501)
                ·
                  refine ⟨116773716522929004387469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 622793154788954690066501 116773716522929004387469)
                  ·
                    rfl

theorem cell21_511686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_511686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511686 prefixEnd_511686 := by exact prefixLift 511686
  have htrace : WordTrace (prefixWord ++ tailWord_511686) baseStart_511686 baseEnd_511686 := by
    simpa [prefixWord, tailWord_511686, baseEnd_511686] using wordTrace_append hprefix tailTrace_511686
  have hstable : (prefixWord ++ tailWord_511686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511686).length < 2 ^ (prefixWord ++ tailWord_511686).sum := by decide
  have hdescent : baseEnd_511686 < baseStart_511686 := by decide
  rcases family_descends (prefixWord ++ tailWord_511686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511756 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 5]
def baseStart_511756 : Nat := 118140960795 + 511756 * 2 ^ 59
def prefixEnd_511756 : Nat := 4983230072969 + 3 ^ 40 * 511756 * 2
def baseEnd_511756 : Nat := 116789691476624438220659

theorem tailTrace_511756 : CollatzResearch.WordTrace tailWord_511756 prefixEnd_511756 116789691476624438220659 := by
  unfold tailWord_511756
  simp only [CollatzResearch.WordTrace]
  refine ⟨9332637367001443905781561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12443516489335258541042081 9332637367001443905781561)
  ·
    refine ⟨6999478025251082929336171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9332637367001443905781561 6999478025251082929336171)
    ·
      refine ⟨10499217037876624394004257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6999478025251082929336171 10499217037876624394004257)
      ·
        refine ⟨7874412778407468295503193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10499217037876624394004257 7874412778407468295503193)
        ·
          refine ⟨5905809583805601221627395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7874412778407468295503193 5905809583805601221627395)
          ·
            refine ⟨8858714375708401832441093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5905809583805601221627395 8858714375708401832441093)
            ·
              refine ⟨1661008945445325343582705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8858714375708401832441093 1661008945445325343582705)
              ·
                refine ⟨1245756709083994007687029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1661008945445325343582705 1245756709083994007687029)
                ·
                  refine ⟨116789691476624438220659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1245756709083994007687029 116789691476624438220659)
                  ·
                    rfl

theorem cell21_511756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_511756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511756 prefixEnd_511756 := by exact prefixLift 511756
  have htrace : WordTrace (prefixWord ++ tailWord_511756) baseStart_511756 baseEnd_511756 := by
    simpa [prefixWord, tailWord_511756, baseEnd_511756] using wordTrace_append hprefix tailTrace_511756
  have hstable : (prefixWord ++ tailWord_511756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511756).length < 2 ^ (prefixWord ++ tailWord_511756).sum := by decide
  have hdescent : baseEnd_511756 < baseStart_511756 := by decide
  rcases family_descends (prefixWord ++ tailWord_511756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511804 : List Nat := [2, 2, 2, 2, 1, 1, 6, 1, 4]
def baseStart_511804 : Nat := 118140960795 + 511804 * 2 ^ 59
def prefixEnd_511804 : Nat := 4983230072969 + 3 ^ 40 * 511804 * 2
def baseEnd_511804 : Nat := 116800645730587021420561

theorem tailTrace_511804 : CollatzResearch.WordTrace tailWord_511804 prefixEnd_511804 116800645730587021420561 := by
  unfold tailWord_511804
  simp only [CollatzResearch.WordTrace]
  refine ⟨9333512718914496004655233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12444683625219328006206977 9333512718914496004655233)
  ·
    refine ⟨7000134539185872003491425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9333512718914496004655233 7000134539185872003491425)
    ·
      refine ⟨5250100904389404002618569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7000134539185872003491425 5250100904389404002618569)
      ·
        refine ⟨3937575678292053001963927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5250100904389404002618569 3937575678292053001963927)
        ·
          refine ⟨5906363517438079502945891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3937575678292053001963927 5906363517438079502945891)
          ·
            refine ⟨8859545276157119254418837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5906363517438079502945891 8859545276157119254418837)
            ·
              refine ⟨415291184819864965050883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8859545276157119254418837 415291184819864965050883)
              ·
                refine ⟨622936777229797447576325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415291184819864965050883 622936777229797447576325)
                ·
                  refine ⟨116800645730587021420561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 622936777229797447576325 116800645730587021420561)
                  ·
                    rfl

theorem cell21_511804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_511804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511804 prefixEnd_511804 := by exact prefixLift 511804
  have htrace : WordTrace (prefixWord ++ tailWord_511804) baseStart_511804 baseEnd_511804 := by
    simpa [prefixWord, tailWord_511804, baseEnd_511804] using wordTrace_append hprefix tailTrace_511804
  have hstable : (prefixWord ++ tailWord_511804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511804).length < 2 ^ (prefixWord ++ tailWord_511804).sum := by decide
  have hdescent : baseEnd_511804 < baseStart_511804 := by decide
  rcases family_descends (prefixWord ++ tailWord_511804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511908 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 5]
def baseStart_511908 : Nat := 118140960795 + 511908 * 2 ^ 59
def prefixEnd_511908 : Nat := 4983230072969 + 3 ^ 40 * 511908 * 2
def baseEnd_511908 : Nat := 116824379947505951687015

theorem tailTrace_511908 : CollatzResearch.WordTrace tailWord_511908 prefixEnd_511908 116824379947505951687015 := by
  unfold tailWord_511908
  simp only [CollatzResearch.WordTrace]
  refine ⟨9335409314726108885548189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12447212419634811847397585 9335409314726108885548189)
  ·
    refine ⟨3500778493022290832080571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9335409314726108885548189 3500778493022290832080571)
    ·
      refine ⟨5251167739533436248120857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3500778493022290832080571 5251167739533436248120857)
      ·
        refine ⟨3938375804650077186090643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5251167739533436248120857 3938375804650077186090643)
        ·
          refine ⟨5907563706975115779135965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3938375804650077186090643 5907563706975115779135965)
          ·
            refine ⟨2215336390115668417175987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5907563706975115779135965 2215336390115668417175987)
            ·
              refine ⟨3323004585173502625763981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215336390115668417175987 3323004585173502625763981)
              ·
                refine ⟨1246126719440063484661493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3323004585173502625763981 1246126719440063484661493)
                ·
                  refine ⟨116824379947505951687015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1246126719440063484661493 116824379947505951687015)
                  ·
                    rfl

theorem cell21_511908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_511908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_511908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_511908 prefixEnd_511908 := by exact prefixLift 511908
  have htrace : WordTrace (prefixWord ++ tailWord_511908) baseStart_511908 baseEnd_511908 := by
    simpa [prefixWord, tailWord_511908, baseEnd_511908] using wordTrace_append hprefix tailTrace_511908
  have hstable : (prefixWord ++ tailWord_511908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511908).length < 2 ^ (prefixWord ++ tailWord_511908).sum := by decide
  have hdescent : baseEnd_511908 < baseStart_511908 := by decide
  rcases family_descends (prefixWord ++ tailWord_511908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512001 : List Nat := [1, 2, 4, 1, 2, 1, 2, 5, 3]
def baseStart_512001 : Nat := 118140960795 + 512001 * 2 ^ 59
def prefixEnd_512001 : Nat := 4983230072969 + 3 ^ 40 * 512001 * 2
def baseEnd_512001 : Nat := 116845603814558456636825

theorem tailTrace_512001 : CollatzResearch.WordTrace tailWord_512001 prefixEnd_512001 116845603814558456636825 := by
  unfold tailWord_512001
  simp only [CollatzResearch.WordTrace]
  refine ⟨18674210618115294654231857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12449473745410196436154571 18674210618115294654231857)
  ·
    refine ⟨14005657963586470990673893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18674210618115294654231857 14005657963586470990673893)
    ·
      refine ⟨2626060868172463310751355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14005657963586470990673893 2626060868172463310751355)
      ·
        refine ⟨3939091302258694966127033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2626060868172463310751355 3939091302258694966127033)
        ·
          refine ⟨2954318476694021224595275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3939091302258694966127033 2954318476694021224595275)
          ·
            refine ⟨4431477715041031836892913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2954318476694021224595275 4431477715041031836892913)
            ·
              refine ⟨3323608286280773877669685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4431477715041031836892913 3323608286280773877669685)
              ·
                refine ⟨311588276838822551031533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3323608286280773877669685 311588276838822551031533)
                ·
                  refine ⟨116845603814558456636825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311588276838822551031533 116845603814558456636825)
                  ·
                    rfl

theorem cell21_512001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 3].length) (baseStart_512001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_512001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_512001 prefixEnd_512001 := by exact prefixLift 512001
  have htrace : WordTrace (prefixWord ++ tailWord_512001) baseStart_512001 baseEnd_512001 := by
    simpa [prefixWord, tailWord_512001, baseEnd_512001] using wordTrace_append hprefix tailTrace_512001
  have hstable : (prefixWord ++ tailWord_512001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512001).length < 2 ^ (prefixWord ++ tailWord_512001).sum := by decide
  have hdescent : baseEnd_512001 < baseStart_512001 := by decide
  rcases family_descends (prefixWord ++ tailWord_512001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512077 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 5]
def baseStart_512077 : Nat := 118140960795 + 512077 * 2 ^ 59
def prefixEnd_512077 : Nat := 4983230072969 + 3 ^ 40 * 512077 * 2
def baseEnd_512077 : Nat := 116862948049999213370003

theorem tailTrace_512077 : CollatzResearch.WordTrace tailWord_512077 prefixEnd_512077 116862948049999213370003 := by
  unfold tailWord_512077
  simp only [CollatzResearch.WordTrace]
  refine ⟨18676982565839959633998485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12451321710559973089332323 18676982565839959633998485)
  ·
    refine ⟨875483557773748107843679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18676982565839959633998485 875483557773748107843679)
    ·
      refine ⟨1313225336660622161765519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 875483557773748107843679 1313225336660622161765519)
      ·
        refine ⟨1969838004990933242648279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1313225336660622161765519 1969838004990933242648279)
        ·
          refine ⟨2954757007486399863972419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1969838004990933242648279 2954757007486399863972419)
          ·
            refine ⟨4432135511229599795958629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2954757007486399863972419 4432135511229599795958629)
            ·
              refine ⟨831025408355549961742243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4432135511229599795958629 831025408355549961742243)
              ·
                refine ⟨1246538112533324942613365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831025408355549961742243 1246538112533324942613365)
                ·
                  refine ⟨116862948049999213370003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1246538112533324942613365 116862948049999213370003)
                  ·
                    rfl

theorem cell21_512077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_512077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_512077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_512077 prefixEnd_512077 := by exact prefixLift 512077
  have htrace : WordTrace (prefixWord ++ tailWord_512077) baseStart_512077 baseEnd_512077 := by
    simpa [prefixWord, tailWord_512077, baseEnd_512077] using wordTrace_append hprefix tailTrace_512077
  have hstable : (prefixWord ++ tailWord_512077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512077).length < 2 ^ (prefixWord ++ tailWord_512077).sum := by decide
  have hdescent : baseEnd_512077 < baseStart_512077 := by decide
  rcases family_descends (prefixWord ++ tailWord_512077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512142 : List Nat := [4, 1, 1, 3, 4, 1, 2, 1, 4]
def baseStart_512142 : Nat := 118140960795 + 512142 * 2 ^ 59
def prefixEnd_512142 : Nat := 4983230072969 + 3 ^ 40 * 512142 * 2
def baseEnd_512142 : Nat := 116877781935573544786537

theorem tailTrace_512142 : CollatzResearch.WordTrace tailWord_512142 prefixEnd_512142 116877781935573544786537 := by
  unfold tailWord_512142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2334919163825559466889335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12452902207069650490076453 2334919163825559466889335)
  ·
    refine ⟨3502378745738339200334003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2334919163825559466889335 3502378745738339200334003)
    ·
      refine ⟨5253568118607508800501005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3502378745738339200334003 5253568118607508800501005)
      ·
        refine ⟨1970088044477815800187877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5253568118607508800501005 1970088044477815800187877)
        ·
          refine ⟨369391508339590462535227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1970088044477815800187877 369391508339590462535227)
          ·
            refine ⟨554087262509385693802841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369391508339590462535227 554087262509385693802841)
            ·
              refine ⟨415565446882039270352131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554087262509385693802841 415565446882039270352131)
              ·
                refine ⟨623348170323058905528197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415565446882039270352131 623348170323058905528197)
                ·
                  refine ⟨116877781935573544786537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 623348170323058905528197 116877781935573544786537)
                  ·
                    rfl

theorem cell21_512142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_512142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_512142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_512142 prefixEnd_512142 := by exact prefixLift 512142
  have htrace : WordTrace (prefixWord ++ tailWord_512142) baseStart_512142 baseEnd_512142 := by
    simpa [prefixWord, tailWord_512142, baseEnd_512142] using wordTrace_append hprefix tailTrace_512142
  have hstable : (prefixWord ++ tailWord_512142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512142).length < 2 ^ (prefixWord ++ tailWord_512142).sum := by decide
  have hdescent : baseEnd_512142 < baseStart_512142 := by decide
  rcases family_descends (prefixWord ++ tailWord_512142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512181 : List Nat := [1, 3, 3, 4, 10]
def baseStart_512181 : Nat := 118140960795 + 512181 * 2 ^ 59
def prefixEnd_512181 : Nat := 4983230072969 + 3 ^ 40 * 512181 * 2
def baseEnd_512181 : Nat := 1443045460085409180697

theorem tailTrace_512181 : CollatzResearch.WordTrace tailWord_512181 prefixEnd_512181 1443045460085409180697 := by
  unfold tailWord_512181
  simp only [CollatzResearch.WordTrace]
  refine ⟨18680775757463185395784397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12453850504975456930522931 18680775757463185395784397)
  ·
    refine ⟨7005290909048694523419149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18680775757463185395784397 7005290909048694523419149)
    ·
      refine ⟨2626984090893260446282181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7005290909048694523419149 2626984090893260446282181)
      ·
        refine ⟨492559517042486333677909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2626984090893260446282181 492559517042486333677909)
        ·
          refine ⟨1443045460085409180697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 492559517042486333677909 1443045460085409180697)
          ·
            rfl

theorem cell21_512181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 10].length) (baseStart_512181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_512181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_512181 prefixEnd_512181 := by exact prefixLift 512181
  have htrace : WordTrace (prefixWord ++ tailWord_512181) baseStart_512181 baseEnd_512181 := by
    simpa [prefixWord, tailWord_512181, baseEnd_512181] using wordTrace_append hprefix tailTrace_512181
  have hstable : (prefixWord ++ tailWord_512181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512181).length < 2 ^ (prefixWord ++ tailWord_512181).sum := by decide
  have hdescent : baseEnd_512181 < baseStart_512181 := by decide
  rcases family_descends (prefixWord ++ tailWord_512181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512229 : List Nat := [1, 3, 1, 4, 2, 1, 1, 5, 3]
def baseStart_512229 : Nat := 118140960795 + 512229 * 2 ^ 59
def prefixEnd_512229 : Nat := 4983230072969 + 3 ^ 40 * 512229 * 2
def baseEnd_512229 : Nat := 116897636520880726836359

theorem tailTrace_512229 : CollatzResearch.WordTrace tailWord_512229 prefixEnd_512229 116897636520880726836359 := by
  unfold tailWord_512229
  simp only [CollatzResearch.WordTrace]
  refine ⟨18682526461289289593531741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12455017640859526395687827 18682526461289289593531741)
  ·
    refine ⟨7005947422983483597574403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18682526461289289593531741 7005947422983483597574403)
    ·
      refine ⟨10508921134475225396361605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7005947422983483597574403 10508921134475225396361605)
      ·
        refine ⟨1970422712714104761817801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10508921134475225396361605 1970422712714104761817801)
        ·
          refine ⟨1477817034535578571363351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1970422712714104761817801 1477817034535578571363351)
          ·
            refine ⟨2216725551803367857045027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477817034535578571363351 2216725551803367857045027)
            ·
              refine ⟨3325088327705051785567541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2216725551803367857045027 3325088327705051785567541)
              ·
                refine ⟨311727030722348604896957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3325088327705051785567541 311727030722348604896957)
                ·
                  refine ⟨116897636520880726836359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311727030722348604896957 116897636520880726836359)
                  ·
                    rfl

theorem cell21_512229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_512229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_512229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_512229 prefixEnd_512229 := by exact prefixLift 512229
  have htrace : WordTrace (prefixWord ++ tailWord_512229) baseStart_512229 baseEnd_512229 := by
    simpa [prefixWord, tailWord_512229, baseEnd_512229] using wordTrace_append hprefix tailTrace_512229
  have hstable : (prefixWord ++ tailWord_512229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512229).length < 2 ^ (prefixWord ++ tailWord_512229).sum := by decide
  have hdescent : baseEnd_512229 < baseStart_512229 := by decide
  rcases family_descends (prefixWord ++ tailWord_512229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512305 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 5]
def baseStart_512305 : Nat := 118140960795 + 512305 * 2 ^ 59
def prefixEnd_512305 : Nat := 4983230072969 + 3 ^ 40 * 512305 * 2
def baseEnd_512305 : Nat := 116914980756321483569537

theorem tailTrace_512305 : CollatzResearch.WordTrace tailWord_512305 prefixEnd_512305 116914980756321483569537 := by
  unfold tailWord_512305
  simp only [CollatzResearch.WordTrace]
  refine ⟨18685298409013954573298369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12456865606009303048865579 18685298409013954573298369)
  ·
    refine ⟨14013973806760465929973777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18685298409013954573298369 14013973806760465929973777)
    ·
      refine ⟨10510480355070349447480333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14013973806760465929973777 10510480355070349447480333)
      ·
        refine ⟨3941430133151381042805125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10510480355070349447480333 3941430133151381042805125)
        ·
          refine ⟨739018149965883945525961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3941430133151381042805125 739018149965883945525961)
          ·
            refine ⟨554263612474412959144471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 739018149965883945525961 554263612474412959144471)
            ·
              refine ⟨831395418711619438716707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554263612474412959144471 831395418711619438716707)
              ·
                refine ⟨1247093128067429158075061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831395418711619438716707 1247093128067429158075061)
                ·
                  refine ⟨116914980756321483569537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1247093128067429158075061 116914980756321483569537)
                  ·
                    rfl

theorem cell21_512305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 5].length) (baseStart_512305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_512305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_512305 prefixEnd_512305 := by exact prefixLift 512305
  have htrace : WordTrace (prefixWord ++ tailWord_512305) baseStart_512305 baseEnd_512305 := by
    simpa [prefixWord, tailWord_512305, baseEnd_512305] using wordTrace_append hprefix tailTrace_512305
  have hstable : (prefixWord ++ tailWord_512305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512305).length < 2 ^ (prefixWord ++ tailWord_512305).sum := by decide
  have hdescent : baseEnd_512305 < baseStart_512305 := by decide
  rcases family_descends (prefixWord ++ tailWord_512305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512398 : List Nat := [4, 1, 1, 4, 1, 2, 2, 3, 3]
def baseStart_512398 : Nat := 118140960795 + 512398 * 2 ^ 59
def prefixEnd_512398 : Nat := 4983230072969 + 3 ^ 40 * 512398 * 2
def baseEnd_512398 : Nat := 116936204623373988519347

theorem tailTrace_512398 : CollatzResearch.WordTrace tailWord_512398 prefixEnd_512398 116936204623373988519347 := by
  unfold tailWord_512398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2336086299709628932054231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12459126931784687637622565 2336086299709628932054231)
  ·
    refine ⟨3504129449564443398081347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2336086299709628932054231 3504129449564443398081347)
    ·
      refine ⟨5256194174346665097122021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3504129449564443398081347 5256194174346665097122021)
      ·
        refine ⟨985536407689999705710379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5256194174346665097122021 985536407689999705710379)
        ·
          refine ⟨1478304611534999558565569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985536407689999705710379 1478304611534999558565569)
          ·
            refine ⟨1108728458651249668924177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1478304611534999558565569 1108728458651249668924177)
            ·
              refine ⟨831546343988437251693133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1108728458651249668924177 831546343988437251693133)
              ·
                refine ⟨311829878995663969384925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 831546343988437251693133 311829878995663969384925)
                ·
                  refine ⟨116936204623373988519347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311829878995663969384925 116936204623373988519347)
                  ·
                    rfl

theorem cell21_512398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_512398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_512398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_512398 prefixEnd_512398 := by exact prefixLift 512398
  have htrace : WordTrace (prefixWord ++ tailWord_512398) baseStart_512398 baseEnd_512398 := by
    simpa [prefixWord, tailWord_512398, baseEnd_512398] using wordTrace_append hprefix tailTrace_512398
  have hstable : (prefixWord ++ tailWord_512398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512398).length < 2 ^ (prefixWord ++ tailWord_512398).sum := by decide
  have hdescent : baseEnd_512398 < baseStart_512398 := by decide
  rcases family_descends (prefixWord ++ tailWord_512398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512429 : List Nat := [1, 5, 2, 2, 2, 1, 3, 1, 4]
def baseStart_512429 : Nat := 118140960795 + 512429 * 2 ^ 59
def prefixEnd_512429 : Nat := 4983230072969 + 3 ^ 40 * 512429 * 2
def baseEnd_512429 : Nat := 116943279245724823502617

theorem tailTrace_512429 : CollatzResearch.WordTrace tailWord_512429 prefixEnd_512429 116943279245724823502617 := by
  unfold tailWord_512429
  simp only [CollatzResearch.WordTrace]
  refine ⟨18689821060564723750812341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12459880707043149167208227 18689821060564723750812341)
  ·
    refine ⟨1752170724427942851638657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18689821060564723750812341 1752170724427942851638657)
    ·
      refine ⟨1314128043320957138728993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1752170724427942851638657 1314128043320957138728993)
      ·
        refine ⟨985596032490717854046745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1314128043320957138728993 985596032490717854046745)
        ·
          refine ⟨739197024368038390535059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 985596032490717854046745 739197024368038390535059)
          ·
            refine ⟨1108795536552057585802589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739197024368038390535059 1108795536552057585802589)
            ·
              refine ⟨415798326207021594675971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1108795536552057585802589 415798326207021594675971)
              ·
                refine ⟨623697489310532392013957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415798326207021594675971 623697489310532392013957)
                ·
                  refine ⟨116943279245724823502617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 623697489310532392013957 116943279245724823502617)
                  ·
                    rfl

theorem cell21_512429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_512429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_512429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_512429 prefixEnd_512429 := by exact prefixLift 512429
  have htrace : WordTrace (prefixWord ++ tailWord_512429) baseStart_512429 baseEnd_512429 := by
    simpa [prefixWord, tailWord_512429, baseEnd_512429] using wordTrace_append hprefix tailTrace_512429
  have hstable : (prefixWord ++ tailWord_512429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512429).length < 2 ^ (prefixWord ++ tailWord_512429).sum := by decide
  have hdescent : baseEnd_512429 < baseStart_512429 := by decide
  rcases family_descends (prefixWord ++ tailWord_512429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512449 : List Nat := [1, 2, 7, 1, 2, 1, 1, 3, 3]
def baseStart_512449 : Nat := 118140960795 + 512449 * 2 ^ 59
def prefixEnd_512449 : Nat := 4983230072969 + 3 ^ 40 * 512449 * 2
def baseEnd_512449 : Nat := 116947843518209233169243

theorem tailTrace_512449 : CollatzResearch.WordTrace tailWord_512449 prefixEnd_512449 116947843518209233169243 := by
  unfold tailWord_512449
  simp only [CollatzResearch.WordTrace]
  refine ⟨18690550520492267166540401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12460367013661511444360267 18690550520492267166540401)
  ·
    refine ⟨14017912890369200374905301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18690550520492267166540401 14017912890369200374905301)
    ·
      refine ⟨328544833368028133786843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 14017912890369200374905301 328544833368028133786843)
      ·
        refine ⟨492817250052042200680265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328544833368028133786843 492817250052042200680265)
        ·
          refine ⟨369612937539031650510199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492817250052042200680265 369612937539031650510199)
          ·
            refine ⟨554419406308547475765299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369612937539031650510199 554419406308547475765299)
            ·
              refine ⟨831629109462821213647949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554419406308547475765299 831629109462821213647949)
              ·
                refine ⟨311860916048557955117981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 831629109462821213647949 311860916048557955117981)
                ·
                  refine ⟨116947843518209233169243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311860916048557955117981 116947843518209233169243)
                  ·
                    rfl

theorem cell21_512449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 3].length) (baseStart_512449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_512449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_512449 prefixEnd_512449 := by exact prefixLift 512449
  have htrace : WordTrace (prefixWord ++ tailWord_512449) baseStart_512449 baseEnd_512449 := by
    simpa [prefixWord, tailWord_512449, baseEnd_512449] using wordTrace_append hprefix tailTrace_512449
  have hstable : (prefixWord ++ tailWord_512449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512449).length < 2 ^ (prefixWord ++ tailWord_512449).sum := by decide
  have hdescent : baseEnd_512449 < baseStart_512449 := by decide
  rcases family_descends (prefixWord ++ tailWord_512449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512488 : List Nat := [2, 1, 4, 1, 1, 5, 2, 1, 4]
def baseStart_512488 : Nat := 118140960795 + 512488 * 2 ^ 59
def prefixEnd_512488 : Nat := 4983230072969 + 3 ^ 40 * 512488 * 2
def baseEnd_512488 : Nat := 116956743849553832019163

theorem tailTrace_512488 : CollatzResearch.WordTrace tailWord_512488 prefixEnd_512488 116956743849553832019163 := by
  unfold tailWord_512488
  simp only [CollatzResearch.WordTrace]
  refine ⟨9345986483675488413605059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12461315311567317884806745 9345986483675488413605059)
  ·
    refine ⟨14018979725513232620407589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9345986483675488413605059 14018979725513232620407589)
    ·
      refine ⟨2628558698533731116326423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14018979725513232620407589 2628558698533731116326423)
      ·
        refine ⟨3942838047800596674489635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2628558698533731116326423 3942838047800596674489635)
        ·
          refine ⟨5914257071700895011734453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3942838047800596674489635 5914257071700895011734453)
          ·
            refine ⟨554461600471958907350105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5914257071700895011734453 554461600471958907350105)
            ·
              refine ⟨415846200353969180512579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554461600471958907350105 415846200353969180512579)
              ·
                refine ⟨623769300530953770768869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415846200353969180512579 623769300530953770768869)
                ·
                  refine ⟨116956743849553832019163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 623769300530953770768869 116956743849553832019163)
                  ·
                    rfl

theorem cell21_512488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 4].length) (baseStart_512488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_512488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_512488 prefixEnd_512488 := by exact prefixLift 512488
  have htrace : WordTrace (prefixWord ++ tailWord_512488) baseStart_512488 baseEnd_512488 := by
    simpa [prefixWord, tailWord_512488, baseEnd_512488] using wordTrace_append hprefix tailTrace_512488
  have hstable : (prefixWord ++ tailWord_512488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512488).length < 2 ^ (prefixWord ++ tailWord_512488).sum := by decide
  have hdescent : baseEnd_512488 < baseStart_512488 := by decide
  rcases family_descends (prefixWord ++ tailWord_512488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512626 : List Nat := [3, 2, 1, 2, 4, 2, 1, 3, 3]
def baseStart_512626 : Nat := 118140960795 + 512626 * 2 ^ 59
def prefixEnd_512626 : Nat := 4983230072969 + 3 ^ 40 * 512626 * 2
def baseEnd_512626 : Nat := 116988237329696258718881

theorem tailTrace_512626 : CollatzResearch.WordTrace tailWord_512626 prefixEnd_512626 116988237329696258718881 := by
  unfold tailWord_512626
  simp only [CollatzResearch.WordTrace]
  refine ⟨4674251560212756598933433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12464670827234017597155821 4674251560212756598933433)
  ·
    refine ⟨3505688670159567449200075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4674251560212756598933433 3505688670159567449200075)
    ·
      refine ⟨5258533005239351173800113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3505688670159567449200075 5258533005239351173800113)
      ·
        refine ⟨3943899753929513380350085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5258533005239351173800113 3943899753929513380350085)
        ·
          refine ⟨739481203861783758815641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3943899753929513380350085 739481203861783758815641)
          ·
            refine ⟨554610902896337819111731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 739481203861783758815641 554610902896337819111731)
            ·
              refine ⟨831916354344506728667597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554610902896337819111731 831916354344506728667597)
              ·
                refine ⟨311968632879190023250349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 831916354344506728667597 311968632879190023250349)
                ·
                  refine ⟨116988237329696258718881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311968632879190023250349 116988237329696258718881)
                  ·
                    rfl

theorem cell21_512626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_512626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_512626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_512626 prefixEnd_512626 := by exact prefixLift 512626
  have htrace : WordTrace (prefixWord ++ tailWord_512626) baseStart_512626 baseEnd_512626 := by
    simpa [prefixWord, tailWord_512626, baseEnd_512626] using wordTrace_append hprefix tailTrace_512626
  have hstable : (prefixWord ++ tailWord_512626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512626).length < 2 ^ (prefixWord ++ tailWord_512626).sum := by decide
  have hdescent : baseEnd_512626 < baseStart_512626 := by decide
  rcases family_descends (prefixWord ++ tailWord_512626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512637 : List Nat := [1, 4, 1, 1, 5, 2, 7]
def baseStart_512637 : Nat := 118140960795 + 512637 * 2 ^ 59
def prefixEnd_512637 : Nat := 4983230072969 + 3 ^ 40 * 512637 * 2
def baseEnd_512637 : Nat := 12998971964395853781725

theorem tailTrace_512637 : CollatzResearch.WordTrace tailWord_512637 prefixEnd_512637 12998971964395853781725 := by
  unfold tailWord_512637
  simp only [CollatzResearch.WordTrace]
  refine ⟨18697407443811175274384165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12464938295874116849589443 18697407443811175274384165)
  ·
    refine ⟨3505763895714595363947031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18697407443811175274384165 3505763895714595363947031)
    ·
      refine ⟨5258645843571893045920547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3505763895714595363947031 5258645843571893045920547)
      ·
        refine ⟨7887968765357839568880821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5258645843571893045920547 7887968765357839568880821)
        ·
          refine ⟨739497071752297459582577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7887968765357839568880821 739497071752297459582577)
          ·
            refine ⟨554622803814223094686933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 739497071752297459582577 554622803814223094686933)
            ·
              refine ⟨12998971964395853781725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 554622803814223094686933 12998971964395853781725)
              ·
                rfl

theorem cell21_512637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 7].length) (baseStart_512637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_512637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_512637 prefixEnd_512637 := by exact prefixLift 512637
  have htrace : WordTrace (prefixWord ++ tailWord_512637) baseStart_512637 baseEnd_512637 := by
    simpa [prefixWord, tailWord_512637, baseEnd_512637] using wordTrace_append hprefix tailTrace_512637
  have hstable : (prefixWord ++ tailWord_512637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512637).length < 2 ^ (prefixWord ++ tailWord_512637).sum := by decide
  have hdescent : baseEnd_512637 < baseStart_512637 := by decide
  rcases family_descends (prefixWord ++ tailWord_512637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512727 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 5]
def baseStart_512727 : Nat := 118140960795 + 512727 * 2 ^ 59
def prefixEnd_512727 : Nat := 4983230072969 + 3 ^ 40 * 512727 * 2
def baseEnd_512727 : Nat := 117011286905742527535341

theorem tailTrace_512727 : CollatzResearch.WordTrace tailWord_512727 prefixEnd_512727 117011286905742527535341 := by
  unfold tailWord_512727
  simp only [CollatzResearch.WordTrace]
  refine ⟨18700690013485120645160435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12467126675656747096773623 18700690013485120645160435)
  ·
    refine ⟨28051035020227680967740653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18700690013485120645160435 28051035020227680967740653)
    ·
      refine ⟨10519138132585380362902745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28051035020227680967740653 10519138132585380362902745)
      ·
        refine ⟨7889353599439035272177059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10519138132585380362902745 7889353599439035272177059)
        ·
          refine ⟨11834030399158552908265589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7889353599439035272177059 11834030399158552908265589)
          ·
            refine ⟨1109440349921114335149899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11834030399158552908265589 1109440349921114335149899)
            ·
              refine ⟨1664160524881671502724849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109440349921114335149899 1664160524881671502724849)
              ·
                refine ⟨1248120393661253627043637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1664160524881671502724849 1248120393661253627043637)
                ·
                  refine ⟨117011286905742527535341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1248120393661253627043637 117011286905742527535341)
                  ·
                    rfl

theorem cell21_512727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 5].length) (baseStart_512727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_512727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_512727 prefixEnd_512727 := by exact prefixLift 512727
  have htrace : WordTrace (prefixWord ++ tailWord_512727) baseStart_512727 baseEnd_512727 := by
    simpa [prefixWord, tailWord_512727, baseEnd_512727] using wordTrace_append hprefix tailTrace_512727
  have hstable : (prefixWord ++ tailWord_512727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512727).length < 2 ^ (prefixWord ++ tailWord_512727).sum := by decide
  have hdescent : baseEnd_512727 < baseStart_512727 := by decide
  rcases family_descends (prefixWord ++ tailWord_512727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512758 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_512758 : Nat := 118140960795 + 512758 * 2 ^ 59
def prefixEnd_512758 : Nat := 4983230072969 + 3 ^ 40 * 512758 * 2
def baseEnd_512758 : Nat := 117018361528093362518611

theorem tailTrace_512758 : CollatzResearch.WordTrace tailWord_512758 prefixEnd_512758 117018361528093362518611 := by
  unfold tailWord_512758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1168863792273300808721183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12467880450915208626359285 1168863792273300808721183)
  ·
    refine ⟨1753295688409951213081775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1168863792273300808721183 1753295688409951213081775)
    ·
      refine ⟨2629943532614926819622663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1753295688409951213081775 2629943532614926819622663)
      ·
        refine ⟨3944915298922390229433995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2629943532614926819622663 3944915298922390229433995)
        ·
          refine ⟨5917372948383585344150993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3944915298922390229433995 5917372948383585344150993)
          ·
            refine ⟨4438029711287689008113245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5917372948383585344150993 4438029711287689008113245)
            ·
              refine ⟨1664261141732883378042467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4438029711287689008113245 1664261141732883378042467)
              ·
                refine ⟨2496391712599325067063701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1664261141732883378042467 2496391712599325067063701)
                ·
                  refine ⟨117018361528093362518611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2496391712599325067063701 117018361528093362518611)
                  ·
                    rfl

theorem cell21_512758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_512758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_512758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_512758 prefixEnd_512758 := by exact prefixLift 512758
  have htrace : WordTrace (prefixWord ++ tailWord_512758) baseStart_512758 baseEnd_512758 := by
    simpa [prefixWord, tailWord_512758, baseEnd_512758] using wordTrace_append hprefix tailTrace_512758
  have hstable : (prefixWord ++ tailWord_512758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512758).length < 2 ^ (prefixWord ++ tailWord_512758).sum := by decide
  have hdescent : baseEnd_512758 < baseStart_512758 := by decide
  rcases family_descends (prefixWord ++ tailWord_512758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512772 : List Nat := [2, 3, 2, 2, 1, 1, 2, 8]
def baseStart_512772 : Nat := 118140960795 + 512772 * 2 ^ 59
def prefixEnd_512772 : Nat := 4983230072969 + 3 ^ 40 * 512772 * 2
def baseEnd_512772 : Nat := 39007185506277483095083

theorem tailTrace_512772 : CollatzResearch.WordTrace tailWord_512772 prefixEnd_512772 39007185506277483095083 := by
  unfold tailWord_512772
  simp only [CollatzResearch.WordTrace]
  refine ⟨9351165649161046665274285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12468220865548062220365713 9351165649161046665274285)
  ·
    refine ⟨3506687118435392499477857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9351165649161046665274285 3506687118435392499477857)
    ·
      refine ⟨2630015338826544374608393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3506687118435392499477857 2630015338826544374608393)
      ·
        refine ⟨1972511504119908280956295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2630015338826544374608393 1972511504119908280956295)
        ·
          refine ⟨2958767256179862421434443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1972511504119908280956295 2958767256179862421434443)
          ·
            refine ⟨4438150884269793632151665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2958767256179862421434443 4438150884269793632151665)
            ·
              refine ⟨3328613163202345224113749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4438150884269793632151665 3328613163202345224113749)
              ·
                refine ⟨39007185506277483095083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3328613163202345224113749 39007185506277483095083)
                ·
                  rfl

theorem cell21_512772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 8].length) (baseStart_512772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_512772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_512772 prefixEnd_512772 := by exact prefixLift 512772
  have htrace : WordTrace (prefixWord ++ tailWord_512772) baseStart_512772 baseEnd_512772 := by
    simpa [prefixWord, tailWord_512772, baseEnd_512772] using wordTrace_append hprefix tailTrace_512772
  have hstable : (prefixWord ++ tailWord_512772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512772).length < 2 ^ (prefixWord ++ tailWord_512772).sum := by decide
  have hdescent : baseEnd_512772 < baseStart_512772 := by decide
  rcases family_descends (prefixWord ++ tailWord_512772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512817 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 6]
def baseStart_512817 : Nat := 118140960795 + 512817 * 2 ^ 59
def prefixEnd_512817 : Nat := 4983230072969 + 3 ^ 40 * 512817 * 2
def baseEnd_512817 : Nat := 117031826131922371035157

theorem tailTrace_512817 : CollatzResearch.WordTrace tailWord_512817 prefixEnd_512817 117031826131922371035157 := by
  unfold tailWord_512817
  simp only [CollatzResearch.WordTrace]
  refine ⟨18703972583159066015936705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12469315055439377343957803 18703972583159066015936705)
  ·
    refine ⟨14027979437369299511952529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18703972583159066015936705 14027979437369299511952529)
    ·
      refine ⟨10520984578026974633964397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14027979437369299511952529 10520984578026974633964397)
      ·
        refine ⟨3945369216760115487736649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10520984578026974633964397 3945369216760115487736649)
        ·
          refine ⟨2959026912570086615802487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3945369216760115487736649 2959026912570086615802487)
          ·
            refine ⟨4438540368855129923703731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959026912570086615802487 4438540368855129923703731)
            ·
              refine ⟨6657810553282694885555597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438540368855129923703731 6657810553282694885555597)
              ·
                refine ⟨2496678957481010582083349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6657810553282694885555597 2496678957481010582083349)
                ·
                  refine ⟨117031826131922371035157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2496678957481010582083349 117031826131922371035157)
                  ·
                    rfl

theorem cell21_512817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_512817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_512817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_512817 prefixEnd_512817 := by exact prefixLift 512817
  have htrace : WordTrace (prefixWord ++ tailWord_512817) baseStart_512817 baseEnd_512817 := by
    simpa [prefixWord, tailWord_512817, baseEnd_512817] using wordTrace_append hprefix tailTrace_512817
  have hstable : (prefixWord ++ tailWord_512817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512817).length < 2 ^ (prefixWord ++ tailWord_512817).sum := by decide
  have hdescent : baseEnd_512817 < baseStart_512817 := by decide
  rcases family_descends (prefixWord ++ tailWord_512817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512907 : List Nat := [1, 1, 1, 1, 4, 2, 2, 9]
def baseStart_512907 : Nat := 118140960795 + 512907 * 2 ^ 59
def prefixEnd_512907 : Nat := 4983230072969 + 3 ^ 40 * 512907 * 2
def baseEnd_512907 : Nat := 39017455119367404844991

theorem tailTrace_512907 : CollatzResearch.WordTrace tailWord_512907 prefixEnd_512907 39017455119367404844991 := by
  unfold tailWord_512907
  simp only [CollatzResearch.WordTrace]
  refine ⟨18707255152833011386712975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12471503435222007591141983 18707255152833011386712975)
  ·
    refine ⟨28060882729249517080069463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18707255152833011386712975 28060882729249517080069463)
    ·
      refine ⟨42091324093874275620104195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28060882729249517080069463 42091324093874275620104195)
      ·
        refine ⟨63136986140811413430156293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42091324093874275620104195 63136986140811413430156293)
        ·
          refine ⟨11838184901402140018154305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63136986140811413430156293 11838184901402140018154305)
          ·
            refine ⟨8878638676051605013615729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11838184901402140018154305 8878638676051605013615729)
            ·
              refine ⟨6658979007038703760211797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8878638676051605013615729 6658979007038703760211797)
              ·
                refine ⟨39017455119367404844991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6658979007038703760211797 39017455119367404844991)
                ·
                  rfl

theorem cell21_512907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 9].length) (baseStart_512907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_512907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_512907 prefixEnd_512907 := by exact prefixLift 512907
  have htrace : WordTrace (prefixWord ++ tailWord_512907) baseStart_512907 baseEnd_512907 := by
    simpa [prefixWord, tailWord_512907, baseEnd_512907] using wordTrace_append hprefix tailTrace_512907
  have hstable : (prefixWord ++ tailWord_512907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512907).length < 2 ^ (prefixWord ++ tailWord_512907).sum := by decide
  have hdescent : baseEnd_512907 < baseStart_512907 := by decide
  rcases family_descends (prefixWord ++ tailWord_512907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512927 : List Nat := [1, 1, 2, 5, 2, 3, 1, 2, 4]
def baseStart_512927 : Nat := 118140960795 + 512927 * 2 ^ 59
def prefixEnd_512927 : Nat := 4983230072969 + 3 ^ 40 * 512927 * 2
def baseEnd_512927 : Nat := 117056929630586624201599

theorem tailTrace_512927 : CollatzResearch.WordTrace tailWord_512927 prefixEnd_512927 117056929630586624201599 := by
  unfold tailWord_512927
  simp only [CollatzResearch.WordTrace]
  refine ⟨18707984612760554802441035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12471989741840369868294023 18707984612760554802441035)
  ·
    refine ⟨28061976919140832203661553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18707984612760554802441035 28061976919140832203661553)
    ·
      refine ⟨21046482689355624152746165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28061976919140832203661553 21046482689355624152746165)
      ·
        refine ⟨1973107752127089764319953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21046482689355624152746165 1973107752127089764319953)
        ·
          refine ⟨1479830814095317323239965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1973107752127089764319953 1479830814095317323239965)
          ·
            refine ⟨554936555285743996214987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1479830814095317323239965 554936555285743996214987)
            ·
              refine ⟨832404832928615994322481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554936555285743996214987 832404832928615994322481)
              ·
                refine ⟨624303624696461995741861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 832404832928615994322481 624303624696461995741861)
                ·
                  refine ⟨117056929630586624201599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624303624696461995741861 117056929630586624201599)
                  ·
                    rfl

theorem cell21_512927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 4].length) (baseStart_512927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_512927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_512927 prefixEnd_512927 := by exact prefixLift 512927
  have htrace : WordTrace (prefixWord ++ tailWord_512927) baseStart_512927 baseEnd_512927 := by
    simpa [prefixWord, tailWord_512927, baseEnd_512927] using wordTrace_append hprefix tailTrace_512927
  have hstable : (prefixWord ++ tailWord_512927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512927).length < 2 ^ (prefixWord ++ tailWord_512927).sum := by decide
  have hdescent : baseEnd_512927 < baseStart_512927 := by decide
  rcases family_descends (prefixWord ++ tailWord_512927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513048 : List Nat := [2, 1, 2, 3, 2, 3, 1, 4, 3]
def baseStart_513048 : Nat := 118140960795 + 513048 * 2 ^ 59
def prefixEnd_513048 : Nat := 4983230072969 + 3 ^ 40 * 513048 * 2
def baseEnd_513048 : Nat := 117084543479117302684685

theorem tailTrace_513048 : CollatzResearch.WordTrace tailWord_513048 prefixEnd_513048 117084543479117302684685 := by
  unfold tailWord_513048
  simp only [CollatzResearch.WordTrace]
  refine ⟨9356198922661096233797899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12474931896881461645063865 9356198922661096233797899)
  ·
    refine ⟨14034298383991644350696849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9356198922661096233797899 14034298383991644350696849)
    ·
      refine ⟨10525723787993733263022637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14034298383991644350696849 10525723787993733263022637)
      ·
        refine ⟨3947146420497649973633489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10525723787993733263022637 3947146420497649973633489)
        ·
          refine ⟨2960359815373237480225117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3947146420497649973633489 2960359815373237480225117)
          ·
            refine ⟨1110134930764964055084419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2960359815373237480225117 1110134930764964055084419)
            ·
              refine ⟨1665202396147446082626629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110134930764964055084419 1665202396147446082626629)
              ·
                refine ⟨312225449277646140492493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1665202396147446082626629 312225449277646140492493)
                ·
                  refine ⟨117084543479117302684685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312225449277646140492493 117084543479117302684685)
                  ·
                    rfl

theorem cell21_513048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 3].length) (baseStart_513048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513048 prefixEnd_513048 := by exact prefixLift 513048
  have htrace : WordTrace (prefixWord ++ tailWord_513048) baseStart_513048 baseEnd_513048 := by
    simpa [prefixWord, tailWord_513048, baseEnd_513048] using wordTrace_append hprefix tailTrace_513048
  have hstable : (prefixWord ++ tailWord_513048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513048).length < 2 ^ (prefixWord ++ tailWord_513048).sum := by decide
  have hdescent : baseEnd_513048 < baseStart_513048 := by decide
  rcases family_descends (prefixWord ++ tailWord_513048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513121 : List Nat := [1, 2, 3, 1, 1, 2, 2, 5, 4]
def baseStart_513121 : Nat := 118140960795 + 513121 * 2 ^ 59
def prefixEnd_513121 : Nat := 4983230072969 + 3 ^ 40 * 513121 * 2
def baseEnd_513121 : Nat := 117101203073685397967869

theorem tailTrace_513121 : CollatzResearch.WordTrace tailWord_513121 prefixEnd_513121 117101203073685397967869 := by
  unfold tailWord_513121
  simp only [CollatzResearch.WordTrace]
  refine ⟨18715060374057725935003217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12476706916038483956668811 18715060374057725935003217)
  ·
    refine ⟨14036295280543294451252413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18715060374057725935003217 14036295280543294451252413)
    ·
      refine ⟨5263610730203735419219655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14036295280543294451252413 5263610730203735419219655)
      ·
        refine ⟨7895416095305603128829483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5263610730203735419219655 7895416095305603128829483)
        ·
          refine ⟨11843124142958404693244225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7895416095305603128829483 11843124142958404693244225)
          ·
            refine ⟨8882343107218803519933169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11843124142958404693244225 8882343107218803519933169)
            ·
              refine ⟨6661757330414102639949877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8882343107218803519933169 6661757330414102639949877)
              ·
                refine ⟨624539749726322122495301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6661757330414102639949877 624539749726322122495301)
                ·
                  refine ⟨117101203073685397967869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624539749726322122495301 117101203073685397967869)
                  ·
                    rfl

theorem cell21_513121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_513121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513121 prefixEnd_513121 := by exact prefixLift 513121
  have htrace : WordTrace (prefixWord ++ tailWord_513121) baseStart_513121 baseEnd_513121 := by
    simpa [prefixWord, tailWord_513121, baseEnd_513121] using wordTrace_append hprefix tailTrace_513121
  have hstable : (prefixWord ++ tailWord_513121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513121).length < 2 ^ (prefixWord ++ tailWord_513121).sum := by decide
  have hdescent : baseEnd_513121 < baseStart_513121 := by decide
  rcases family_descends (prefixWord ++ tailWord_513121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513135 : List Nat := [1, 1, 2, 1, 3, 3, 3, 7]
def baseStart_513135 : Nat := 118140960795 + 513135 * 2 ^ 59
def prefixEnd_513135 : Nat := 4983230072969 + 3 ^ 40 * 513135 * 2
def baseEnd_513135 : Nat := 39034799354808161578169

theorem tailTrace_513135 : CollatzResearch.WordTrace tailWord_513135 prefixEnd_513135 39034799354808161578169 := by
  unfold tailWord_513135
  simp only [CollatzResearch.WordTrace]
  refine ⟨18715570996007006326012859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12477047330671337550675239 18715570996007006326012859)
  ·
    refine ⟨28073356494010509489019289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18715570996007006326012859 28073356494010509489019289)
    ·
      refine ⟨21055017370507882116764467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28073356494010509489019289 21055017370507882116764467)
      ·
        refine ⟨31582526055761823175146701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21055017370507882116764467 31582526055761823175146701)
        ·
          refine ⟨11843447270910683690680013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31582526055761823175146701 11843447270910683690680013)
          ·
            refine ⟨4441292726591506384005005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11843447270910683690680013 4441292726591506384005005)
            ·
              refine ⟨1665484772471814894001877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4441292726591506384005005 1665484772471814894001877)
              ·
                refine ⟨39034799354808161578169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1665484772471814894001877 39034799354808161578169)
                ·
                  rfl

theorem cell21_513135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 7].length) (baseStart_513135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513135 prefixEnd_513135 := by exact prefixLift 513135
  have htrace : WordTrace (prefixWord ++ tailWord_513135) baseStart_513135 baseEnd_513135 := by
    simpa [prefixWord, tailWord_513135, baseEnd_513135] using wordTrace_append hprefix tailTrace_513135
  have hstable : (prefixWord ++ tailWord_513135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513135).length < 2 ^ (prefixWord ++ tailWord_513135).sum := by decide
  have hdescent : baseEnd_513135 < baseStart_513135 := by decide
  rcases family_descends (prefixWord ++ tailWord_513135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513214 : List Nat := [4, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_513214 : Nat := 118140960795 + 513214 * 2 ^ 59
def prefixEnd_513214 : Nat := 4983230072969 + 3 ^ 40 * 513214 * 2
def baseEnd_513214 : Nat := 117122426940737902917679

theorem tailTrace_513214 : CollatzResearch.WordTrace tailWord_513214 prefixEnd_513214 117122426940737902917679 := by
  unfold tailWord_513214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2339806545340100352267337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12478968241813868545425797 2339806545340100352267337)
  ·
    refine ⟨1754854909005075264200503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2339806545340100352267337 1754854909005075264200503)
    ·
      refine ⟨2632282363507612896300755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1754854909005075264200503 2632282363507612896300755)
      ·
        refine ⟨3948423545261419344451133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2632282363507612896300755 3948423545261419344451133)
        ·
          refine ⟨1480658829473032254169175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3948423545261419344451133 1480658829473032254169175)
          ·
            refine ⟨2220988244209548381253763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480658829473032254169175 2220988244209548381253763)
            ·
              refine ⟨3331482366314322571880645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220988244209548381253763 3331482366314322571880645)
              ·
                refine ⟨624652943683935482227621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3331482366314322571880645 624652943683935482227621)
                ·
                  refine ⟨117122426940737902917679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624652943683935482227621 117122426940737902917679)
                  ·
                    rfl

theorem cell21_513214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_513214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513214 prefixEnd_513214 := by exact prefixLift 513214
  have htrace : WordTrace (prefixWord ++ tailWord_513214) baseStart_513214 baseEnd_513214 := by
    simpa [prefixWord, tailWord_513214, baseEnd_513214] using wordTrace_append hprefix tailTrace_513214
  have hstable : (prefixWord ++ tailWord_513214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513214).length < 2 ^ (prefixWord ++ tailWord_513214).sum := by decide
  have hdescent : baseEnd_513214 < baseStart_513214 := by decide
  rcases family_descends (prefixWord ++ tailWord_513214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513217 : List Nat := [1, 2, 6, 1, 1, 2, 1, 4, 3]
def baseStart_513217 : Nat := 118140960795 + 513217 * 2 ^ 59
def prefixEnd_513217 : Nat := 4983230072969 + 3 ^ 40 * 513217 * 2
def baseEnd_513217 : Nat := 117123111581610564367673

theorem tailTrace_513217 : CollatzResearch.WordTrace tailWord_513217 prefixEnd_513217 117123111581610564367673 := by
  unfold tailWord_513217
  simp only [CollatzResearch.WordTrace]
  refine ⟨18718561781709934330497905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12479041187806622886998603 18718561781709934330497905)
  ·
    refine ⟨14038921336282450747873429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18718561781709934330497905 14038921336282450747873429)
    ·
      refine ⟨658074437638239878806567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14038921336282450747873429 658074437638239878806567)
      ·
        refine ⟨987111656457359818209851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658074437638239878806567 987111656457359818209851)
        ·
          refine ⟨1480667484686039727314777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987111656457359818209851 1480667484686039727314777)
          ·
            refine ⟨1110500613514529795486083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1480667484686039727314777 1110500613514529795486083)
            ·
              refine ⟨1665750920271794693229125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110500613514529795486083 1665750920271794693229125)
              ·
                refine ⟨312328297550961504980461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1665750920271794693229125 312328297550961504980461)
                ·
                  refine ⟨117123111581610564367673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312328297550961504980461 117123111581610564367673)
                  ·
                    rfl

theorem cell21_513217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 3].length) (baseStart_513217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513217 prefixEnd_513217 := by exact prefixLift 513217
  have htrace : WordTrace (prefixWord ++ tailWord_513217) baseStart_513217 baseEnd_513217 := by
    simpa [prefixWord, tailWord_513217, baseEnd_513217] using wordTrace_append hprefix tailTrace_513217
  have hstable : (prefixWord ++ tailWord_513217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513217).length < 2 ^ (prefixWord ++ tailWord_513217).sum := by decide
  have hdescent : baseEnd_513217 < baseStart_513217 := by decide
  rcases family_descends (prefixWord ++ tailWord_513217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513259 : List Nat := [1, 1, 1, 1, 2, 6, 1, 5, 3]
def baseStart_513259 : Nat := 118140960795 + 513259 * 2 ^ 59
def prefixEnd_513259 : Nat := 4983230072969 + 3 ^ 40 * 513259 * 2
def baseEnd_513259 : Nat := 117132696553827824667587

theorem tailTrace_513259 : CollatzResearch.WordTrace tailWord_513259 prefixEnd_513259 117132696553827824667587 := by
  unfold tailWord_513259
  simp only [CollatzResearch.WordTrace]
  refine ⟨18720093647557775503526831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12480062431705183669017887 18720093647557775503526831)
  ·
    refine ⟨28080140471336663255290247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18720093647557775503526831 28080140471336663255290247)
    ·
      refine ⟨42120210707004994882935371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28080140471336663255290247 42120210707004994882935371)
      ·
        refine ⟨63180316060507492324403057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42120210707004994882935371 63180316060507492324403057)
        ·
          refine ⟨47385237045380619243302293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63180316060507492324403057 47385237045380619243302293)
          ·
            refine ⟨2221182986502216527029795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47385237045380619243302293 2221182986502216527029795)
            ·
              refine ⟨3331774479753324790544693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2221182986502216527029795 3331774479753324790544693)
              ·
                refine ⟨312353857476874199113565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3331774479753324790544693 312353857476874199113565)
                ·
                  refine ⟨117132696553827824667587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312353857476874199113565 117132696553827824667587)
                  ·
                    rfl

theorem cell21_513259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 3].length) (baseStart_513259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513259 prefixEnd_513259 := by exact prefixLift 513259
  have htrace : WordTrace (prefixWord ++ tailWord_513259) baseStart_513259 baseEnd_513259 := by
    simpa [prefixWord, tailWord_513259, baseEnd_513259] using wordTrace_append hprefix tailTrace_513259
  have hstable : (prefixWord ++ tailWord_513259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513259).length < 2 ^ (prefixWord ++ tailWord_513259).sum := by decide
  have hdescent : baseEnd_513259 < baseStart_513259 := by decide
  rcases family_descends (prefixWord ++ tailWord_513259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513304 : List Nat := [2, 1, 2, 3, 1, 3, 4, 5]
def baseStart_513304 : Nat := 118140960795 + 513304 * 2 ^ 59
def prefixEnd_513304 : Nat := 4983230072969 + 3 ^ 40 * 513304 * 2
def baseEnd_513304 : Nat := 39047655388972582139165

theorem tailTrace_513304 : CollatzResearch.WordTrace tailWord_513304 prefixEnd_513304 39047655388972582139165 := by
  unfold tailWord_513304
  simp only [CollatzResearch.WordTrace]
  refine ⟨9360867466197374094457483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12481156621596498792609977 9360867466197374094457483)
  ·
    refine ⟨14041301199296061141686225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9360867466197374094457483 14041301199296061141686225)
    ·
      refine ⟨10530975899472045856264669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14041301199296061141686225 10530975899472045856264669)
      ·
        refine ⟨3949115962302017196099251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10530975899472045856264669 3949115962302017196099251)
        ·
          refine ⟨5923673943453025794148877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3949115962302017196099251 5923673943453025794148877)
          ·
            refine ⟨2221377728794884672805829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5923673943453025794148877 2221377728794884672805829)
            ·
              refine ⟨416508324149040876151093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2221377728794884672805829 416508324149040876151093)
              ·
                refine ⟨39047655388972582139165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 416508324149040876151093 39047655388972582139165)
                ·
                  rfl

theorem cell21_513304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 5].length) (baseStart_513304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513304 prefixEnd_513304 := by exact prefixLift 513304
  have htrace : WordTrace (prefixWord ++ tailWord_513304) baseStart_513304 baseEnd_513304 := by
    simpa [prefixWord, tailWord_513304, baseEnd_513304] using wordTrace_append hprefix tailTrace_513304
  have hstable : (prefixWord ++ tailWord_513304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513304).length < 2 ^ (prefixWord ++ tailWord_513304).sum := by decide
  have hdescent : baseEnd_513304 < baseStart_513304 := by decide
  rcases family_descends (prefixWord ++ tailWord_513304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513341 : List Nat := [1, 4, 1, 5, 2, 1, 2, 1, 4]
def baseStart_513341 : Nat := 118140960795 + 513341 * 2 ^ 59
def prefixEnd_513341 : Nat := 4983230072969 + 3 ^ 40 * 513341 * 2
def baseEnd_513341 : Nat := 117151410071013904300753

theorem tailTrace_513341 : CollatzResearch.WordTrace tailWord_513341 prefixEnd_513341 117151410071013904300753 := by
  unfold tailWord_513341
  simp only [CollatzResearch.WordTrace]
  refine ⟨18723084433260703508011877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12482056288840469005341251 18723084433260703508011877)
  ·
    refine ⟨3510578331236381907752227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18723084433260703508011877 3510578331236381907752227)
    ·
      refine ⟨5265867496854572861628341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3510578331236381907752227 5265867496854572861628341)
      ·
        refine ⟨493675077830116205777657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5265867496854572861628341 493675077830116205777657)
        ·
          refine ⟨370256308372587154333243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493675077830116205777657 370256308372587154333243)
          ·
            refine ⟨555384462558880731499865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370256308372587154333243 555384462558880731499865)
            ·
              refine ⟨416538346919160548624899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555384462558880731499865 416538346919160548624899)
              ·
                refine ⟨624807520378740822937349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416538346919160548624899 624807520378740822937349)
                ·
                  refine ⟨117151410071013904300753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624807520378740822937349 117151410071013904300753)
                  ·
                    rfl

theorem cell21_513341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_513341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513341 prefixEnd_513341 := by exact prefixLift 513341
  have htrace : WordTrace (prefixWord ++ tailWord_513341) baseStart_513341 baseEnd_513341 := by
    simpa [prefixWord, tailWord_513341, baseEnd_513341] using wordTrace_append hprefix tailTrace_513341
  have hstable : (prefixWord ++ tailWord_513341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513341).length < 2 ^ (prefixWord ++ tailWord_513341).sum := by decide
  have hdescent : baseEnd_513341 < baseStart_513341 := by decide
  rcases family_descends (prefixWord ++ tailWord_513341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513386 : List Nat := [3, 1, 3, 3, 2, 2, 2, 2, 3]
def baseStart_513386 : Nat := 118140960795 + 513386 * 2 ^ 59
def prefixEnd_513386 : Nat := 4983230072969 + 3 ^ 40 * 513386 * 2
def baseEnd_513386 : Nat := 117161679684103826050661

theorem tailTrace_513386 : CollatzResearch.WordTrace tailWord_513386 prefixEnd_513386 117161679684103826050661 := by
  unfold tailWord_513386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4681181429524419048350003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12483150478731784128933341 4681181429524419048350003)
  ·
    refine ⟨7021772144286628572525005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4681181429524419048350003 7021772144286628572525005)
    ·
      refine ⟨2633164554107485714696877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7021772144286628572525005 2633164554107485714696877)
      ·
        refine ⟨987436707790307143011329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2633164554107485714696877 987436707790307143011329)
        ·
          refine ⟨740577530842730357258497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 987436707790307143011329 740577530842730357258497)
          ·
            refine ⟨555433148132047767943873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740577530842730357258497 555433148132047767943873)
            ·
              refine ⟨416574861099035825957905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555433148132047767943873 416574861099035825957905)
              ·
                refine ⟨312431145824276869468429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416574861099035825957905 312431145824276869468429)
                ·
                  refine ⟨117161679684103826050661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312431145824276869468429 117161679684103826050661)
                  ·
                    rfl

theorem cell21_513386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_513386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513386 prefixEnd_513386 := by exact prefixLift 513386
  have htrace : WordTrace (prefixWord ++ tailWord_513386) baseStart_513386 baseEnd_513386 := by
    simpa [prefixWord, tailWord_513386, baseEnd_513386] using wordTrace_append hprefix tailTrace_513386
  have hstable : (prefixWord ++ tailWord_513386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513386).length < 2 ^ (prefixWord ++ tailWord_513386).sum := by decide
  have hdescent : baseEnd_513386 < baseStart_513386 := by decide
  rcases family_descends (prefixWord ++ tailWord_513386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513394 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 5]
def baseStart_513394 : Nat := 118140960795 + 513394 * 2 ^ 59
def prefixEnd_513394 : Nat := 4983230072969 + 3 ^ 40 * 513394 * 2
def baseEnd_513394 : Nat := 117163505393097589917311

theorem tailTrace_513394 : CollatzResearch.WordTrace tailWord_513394 prefixEnd_513394 117163505393097589917311 := by
  unfold tailWord_513394
  simp only [CollatzResearch.WordTrace]
  refine ⟨4681254375517173389922809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12483345001379129039794157 4681254375517173389922809)
  ·
    refine ⟨3510940781637880042442107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4681254375517173389922809 3510940781637880042442107)
    ·
      refine ⟨5266411172456820063663161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3510940781637880042442107 5266411172456820063663161)
      ·
        refine ⟨3949808379342615047747371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5266411172456820063663161 3949808379342615047747371)
        ·
          refine ⟨5924712569013922571621057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3949808379342615047747371 5924712569013922571621057)
          ·
            refine ⟨4443534426760441928715793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5924712569013922571621057 4443534426760441928715793)
            ·
              refine ⟨3332650820070331446536845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4443534426760441928715793 3332650820070331446536845)
              ·
                refine ⟨1249744057526374292451317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3332650820070331446536845 1249744057526374292451317)
                ·
                  refine ⟨117163505393097589917311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1249744057526374292451317 117163505393097589917311)
                  ·
                    rfl

theorem cell21_513394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_513394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513394 prefixEnd_513394 := by exact prefixLift 513394
  have htrace : WordTrace (prefixWord ++ tailWord_513394) baseStart_513394 baseEnd_513394 := by
    simpa [prefixWord, tailWord_513394, baseEnd_513394] using wordTrace_append hprefix tailTrace_513394
  have hstable : (prefixWord ++ tailWord_513394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513394).length < 2 ^ (prefixWord ++ tailWord_513394).sum := by decide
  have hdescent : baseEnd_513394 < baseStart_513394 := by decide
  rcases family_descends (prefixWord ++ tailWord_513394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513397 : List Nat := [1, 3, 4, 1, 3, 2, 1, 6]
def baseStart_513397 : Nat := 118140960795 + 513397 * 2 ^ 59
def prefixEnd_513397 : Nat := 4983230072969 + 3 ^ 40 * 513397 * 2
def baseEnd_513397 : Nat := 39054730011323417122435

theorem tailTrace_513397 : CollatzResearch.WordTrace tailWord_513397 prefixEnd_513397 39054730011323417122435 := by
  unfold tailWord_513397
  simp only [CollatzResearch.WordTrace]
  refine ⟨18725126921057825072050445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12483417947371883381366963 18725126921057825072050445)
  ·
    refine ⟨7021922595396684402018917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18725126921057825072050445 7021922595396684402018917)
    ·
      refine ⟨1316610486636878325378547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7021922595396684402018917 1316610486636878325378547)
      ·
        refine ⟨1974915729955317488067821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316610486636878325378547 1974915729955317488067821)
        ·
          refine ⟨740593398733244058025433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1974915729955317488067821 740593398733244058025433)
          ·
            refine ⟨555445049049933043519075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740593398733244058025433 555445049049933043519075)
            ·
              refine ⟨833167573574899565278613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555445049049933043519075 833167573574899565278613)
              ·
                refine ⟨39054730011323417122435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 833167573574899565278613 39054730011323417122435)
                ·
                  rfl

theorem cell21_513397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 6].length) (baseStart_513397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513397 prefixEnd_513397 := by exact prefixLift 513397
  have htrace : WordTrace (prefixWord ++ tailWord_513397) baseStart_513397 baseEnd_513397 := by
    simpa [prefixWord, tailWord_513397, baseEnd_513397] using wordTrace_append hprefix tailTrace_513397
  have hstable : (prefixWord ++ tailWord_513397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513397).length < 2 ^ (prefixWord ++ tailWord_513397).sum := by decide
  have hdescent : baseEnd_513397 < baseStart_513397 := by decide
  rcases family_descends (prefixWord ++ tailWord_513397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513428 : List Nat := [2, 4, 2, 1, 2, 1, 1, 5, 3]
def baseStart_513428 : Nat := 118140960795 + 513428 * 2 ^ 59
def prefixEnd_513428 : Nat := 4983230072969 + 3 ^ 40 * 513428 * 2
def baseEnd_513428 : Nat := 117171264656321086350575

theorem tailTrace_513428 : CollatzResearch.WordTrace tailWord_513428 prefixEnd_513428 117171264656321086350575 := by
  unfold tailWord_513428
  simp only [CollatzResearch.WordTrace]
  refine ⟨9363128791972758683214469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12484171722630344910952625 9363128791972758683214469)
  ·
    refine ⟨1755586648494892253102713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9363128791972758683214469 1755586648494892253102713)
    ·
      refine ⟨1316689986371169189827035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1755586648494892253102713 1316689986371169189827035)
      ·
        refine ⟨1975034979556753784740553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316689986371169189827035 1975034979556753784740553)
        ·
          refine ⟨1481276234667565338555415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1975034979556753784740553 1481276234667565338555415)
          ·
            refine ⟨2221914352001348007833123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481276234667565338555415 2221914352001348007833123)
            ·
              refine ⟨3332871528002022011749685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2221914352001348007833123 3332871528002022011749685)
              ·
                refine ⟨312456705750189563601533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3332871528002022011749685 312456705750189563601533)
                ·
                  refine ⟨117171264656321086350575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312456705750189563601533 117171264656321086350575)
                  ·
                    rfl

theorem cell21_513428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_513428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513428 prefixEnd_513428 := by exact prefixLift 513428
  have htrace : WordTrace (prefixWord ++ tailWord_513428) baseStart_513428 baseEnd_513428 := by
    simpa [prefixWord, tailWord_513428, baseEnd_513428] using wordTrace_append hprefix tailTrace_513428
  have hstable : (prefixWord ++ tailWord_513428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513428).length < 2 ^ (prefixWord ++ tailWord_513428).sum := by decide
  have hdescent : baseEnd_513428 < baseStart_513428 := by decide
  rcases family_descends (prefixWord ++ tailWord_513428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513439 : List Nat := [1, 1, 2, 5, 1, 3, 8]
def baseStart_513439 : Nat := 118140960795 + 513439 * 2 ^ 59
def prefixEnd_513439 : Nat := 4983230072969 + 3 ^ 40 * 513439 * 2
def baseEnd_513439 : Nat := 13019308334020834629691

theorem tailTrace_513439 : CollatzResearch.WordTrace tailWord_513439 prefixEnd_513439 13019308334020834629691 := by
  unfold tailWord_513439
  simp only [CollatzResearch.WordTrace]
  refine ⟨18726658786905666245079371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12484439191270444163386247 18726658786905666245079371)
  ·
    refine ⟨28089988180358499367619057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18726658786905666245079371 28089988180358499367619057)
    ·
      refine ⟨21067491135268874525714293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28089988180358499367619057 21067491135268874525714293)
      ·
        refine ⟨1975077293931456986785715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21067491135268874525714293 1975077293931456986785715)
        ·
          refine ⟨2962615940897185480178573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1975077293931456986785715 2962615940897185480178573)
          ·
            refine ⟨1110980977836444555066965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2962615940897185480178573 1110980977836444555066965)
            ·
              refine ⟨13019308334020834629691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1110980977836444555066965 13019308334020834629691)
              ·
                rfl

theorem cell21_513439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 8].length) (baseStart_513439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513439 prefixEnd_513439 := by exact prefixLift 513439
  have htrace : WordTrace (prefixWord ++ tailWord_513439) baseStart_513439 baseEnd_513439 := by
    simpa [prefixWord, tailWord_513439, baseEnd_513439] using wordTrace_append hprefix tailTrace_513439
  have hstable : (prefixWord ++ tailWord_513439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513439).length < 2 ^ (prefixWord ++ tailWord_513439).sum := by decide
  have hdescent : baseEnd_513439 < baseStart_513439 := by decide
  rcases family_descends (prefixWord ++ tailWord_513439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513442 : List Nat := [3, 3, 1, 2, 1, 2, 3, 2, 4]
def baseStart_513442 : Nat := 118140960795 + 513442 * 2 ^ 59
def prefixEnd_513442 : Nat := 4983230072969 + 3 ^ 40 * 513442 * 2
def baseEnd_513442 : Nat := 117174459647060173117213

theorem tailTrace_513442 : CollatzResearch.WordTrace tailWord_513442 prefixEnd_513442 117174459647060173117213 := by
  unfold tailWord_513442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4681692051473699439359645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12484512137263198504959053 4681692051473699439359645)
  ·
    refine ⟨1755634519302637289759867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4681692051473699439359645 1755634519302637289759867)
    ·
      refine ⟨2633451778953955934639801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1755634519302637289759867 2633451778953955934639801)
      ·
        refine ⟨1975088834215466950979851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2633451778953955934639801 1975088834215466950979851)
        ·
          refine ⟨2962633251323200426469777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1975088834215466950979851 2962633251323200426469777)
          ·
            refine ⟨2221974938492400319852333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2962633251323200426469777 2221974938492400319852333)
            ·
              refine ⟨833240601934650119944625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2221974938492400319852333 833240601934650119944625)
              ·
                refine ⟨624930451450987589958469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 833240601934650119944625 624930451450987589958469)
                ·
                  refine ⟨117174459647060173117213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624930451450987589958469 117174459647060173117213)
                  ·
                    rfl

theorem cell21_513442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_513442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513442 prefixEnd_513442 := by exact prefixLift 513442
  have htrace : WordTrace (prefixWord ++ tailWord_513442) baseStart_513442 baseEnd_513442 := by
    simpa [prefixWord, tailWord_513442, baseEnd_513442] using wordTrace_append hprefix tailTrace_513442
  have hstable : (prefixWord ++ tailWord_513442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513442).length < 2 ^ (prefixWord ++ tailWord_513442).sum := by decide
  have hdescent : baseEnd_513442 < baseStart_513442 := by decide
  rcases family_descends (prefixWord ++ tailWord_513442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513487 : List Nat := [1, 1, 2, 1, 1, 4, 5, 3, 3]
def baseStart_513487 : Nat := 118140960795 + 513487 * 2 ^ 59
def prefixEnd_513487 : Nat := 4983230072969 + 3 ^ 40 * 513487 * 2
def baseEnd_513487 : Nat := 117184729260150094867121

theorem tailTrace_513487 : CollatzResearch.WordTrace tailWord_513487 prefixEnd_513487 117184729260150094867121 := by
  unfold tailWord_513487
  simp only [CollatzResearch.WordTrace]
  refine ⟨18728409490731770442826715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12485606327154513628551143 18728409490731770442826715)
  ·
    refine ⟨28092614236097655664240073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18728409490731770442826715 28092614236097655664240073)
    ·
      refine ⟨21069460677073241748180055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28092614236097655664240073 21069460677073241748180055)
      ·
        refine ⟨31604191015609862622270083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21069460677073241748180055 31604191015609862622270083)
        ·
          refine ⟨47406286523414793933405125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31604191015609862622270083 47406286523414793933405125)
          ·
            refine ⟨8888678723140273862513461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47406286523414793933405125 8888678723140273862513461)
            ·
              refine ⟨833313630294400674610637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8888678723140273862513461 833313630294400674610637)
              ·
                refine ⟨312492611360400252978989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 833313630294400674610637 312492611360400252978989)
                ·
                  refine ⟨117184729260150094867121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312492611360400252978989 117184729260150094867121)
                  ·
                    rfl

theorem cell21_513487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 3].length) (baseStart_513487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513487 prefixEnd_513487 := by exact prefixLift 513487
  have htrace : WordTrace (prefixWord ++ tailWord_513487) baseStart_513487 baseEnd_513487 := by
    simpa [prefixWord, tailWord_513487, baseEnd_513487] using wordTrace_append hprefix tailTrace_513487
  have hstable : (prefixWord ++ tailWord_513487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513487).length < 2 ^ (prefixWord ++ tailWord_513487).sum := by decide
  have hdescent : baseEnd_513487 < baseStart_513487 := by decide
  rcases family_descends (prefixWord ++ tailWord_513487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513501 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 6]
def baseStart_513501 : Nat := 118140960795 + 513501 * 2 ^ 59
def prefixEnd_513501 : Nat := 4983230072969 + 3 ^ 40 * 513501 * 2
def baseEnd_513501 : Nat := 117187924250889181633759

theorem tailTrace_513501 : CollatzResearch.WordTrace tailWord_513501 prefixEnd_513501 117187924250889181633759 := by
  unfold tailWord_513501
  simp only [CollatzResearch.WordTrace]
  refine ⟨18728920112681050833836357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12485946741787367222557571 18728920112681050833836357)
  ·
    refine ⟨3511672521127697031344317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18728920112681050833836357 3511672521127697031344317)
    ·
      refine ⟨1316877195422886386754119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3511672521127697031344317 1316877195422886386754119)
      ·
        refine ⟨1975315793134329580131179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316877195422886386754119 1975315793134329580131179)
        ·
          refine ⟨2962973689701494370196769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1975315793134329580131179 2962973689701494370196769)
          ·
            refine ⟨2222230267276120777647577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2962973689701494370196769 2222230267276120777647577)
            ·
              refine ⟨1666672700457090583235683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2222230267276120777647577 1666672700457090583235683)
              ·
                refine ⟨2500009050685635874853525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666672700457090583235683 2500009050685635874853525)
                ·
                  refine ⟨117187924250889181633759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2500009050685635874853525 117187924250889181633759)
                  ·
                    rfl

theorem cell21_513501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_513501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513501 prefixEnd_513501 := by exact prefixLift 513501
  have htrace : WordTrace (prefixWord ++ tailWord_513501) baseStart_513501 baseEnd_513501 := by
    simpa [prefixWord, tailWord_513501, baseEnd_513501] using wordTrace_append hprefix tailTrace_513501
  have hstable : (prefixWord ++ tailWord_513501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513501).length < 2 ^ (prefixWord ++ tailWord_513501).sum := by decide
  have hdescent : baseEnd_513501 < baseStart_513501 := by decide
  rcases family_descends (prefixWord ++ tailWord_513501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513529 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 7]
def baseStart_513529 : Nat := 118140960795 + 513529 * 2 ^ 59
def prefixEnd_513529 : Nat := 4983230072969 + 3 ^ 40 * 513529 * 2
def baseEnd_513529 : Nat := 117194314232367355167035

theorem tailTrace_513529 : CollatzResearch.WordTrace tailWord_513529 prefixEnd_513529 117194314232367355167035 := by
  unfold tailWord_513529
  simp only [CollatzResearch.WordTrace]
  refine ⟨18729941356579611615855641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12486627571053074410570427 18729941356579611615855641)
  ·
    refine ⟨14047456017434708711891731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18729941356579611615855641 14047456017434708711891731)
    ·
      refine ⟨21071184026152063067837597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14047456017434708711891731 21071184026152063067837597)
      ·
        refine ⟨7901694009807023650439099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21071184026152063067837597 7901694009807023650439099)
        ·
          refine ⟨11852541014710535475658649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7901694009807023650439099 11852541014710535475658649)
          ·
            refine ⟨8889405761032901606743987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11852541014710535475658649 8889405761032901606743987)
            ·
              refine ⟨13334108641549352410115981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8889405761032901606743987 13334108641549352410115981)
              ·
                refine ⟨5000290740581007153793493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13334108641549352410115981 5000290740581007153793493)
                ·
                  refine ⟨117194314232367355167035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5000290740581007153793493 117194314232367355167035)
                  ·
                    rfl

theorem cell21_513529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_513529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513529 prefixEnd_513529 := by exact prefixLift 513529
  have htrace : WordTrace (prefixWord ++ tailWord_513529) baseStart_513529 baseEnd_513529 := by
    simpa [prefixWord, tailWord_513529, baseEnd_513529] using wordTrace_append hprefix tailTrace_513529
  have hstable : (prefixWord ++ tailWord_513529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513529).length < 2 ^ (prefixWord ++ tailWord_513529).sum := by decide
  have hdescent : baseEnd_513529 < baseStart_513529 := by decide
  rcases family_descends (prefixWord ++ tailWord_513529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513549 : List Nat := [1, 7, 1, 1, 2, 9]
def baseStart_513549 : Nat := 118140960795 + 513549 * 2 ^ 59
def prefixEnd_513549 : Nat := 4983230072969 + 3 ^ 40 * 513549 * 2
def baseEnd_513549 : Nat := 4340699203883398697543

theorem tailTrace_513549 : CollatzResearch.WordTrace tailWord_513549 prefixEnd_513549 4340699203883398697543 := by
  unfold tailWord_513549
  simp only [CollatzResearch.WordTrace]
  refine ⟨18730670816507155031583701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12487113877671436687722467 18730670816507155031583701)
  ·
    refine ⟨439000097261886446052743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 18730670816507155031583701 439000097261886446052743)
    ·
      refine ⟨658500145892829669079115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439000097261886446052743 658500145892829669079115)
      ·
        refine ⟨987750218839244503618673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658500145892829669079115 987750218839244503618673)
        ·
          refine ⟨740812664129433377714005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 987750218839244503618673 740812664129433377714005)
          ·
            refine ⟨4340699203883398697543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 740812664129433377714005 4340699203883398697543)
            ·
              rfl

theorem cell21_513549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 9].length) (baseStart_513549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513549 prefixEnd_513549 := by exact prefixLift 513549
  have htrace : WordTrace (prefixWord ++ tailWord_513549) baseStart_513549 baseEnd_513549 := by
    simpa [prefixWord, tailWord_513549, baseEnd_513549] using wordTrace_append hprefix tailTrace_513549
  have hstable : (prefixWord ++ tailWord_513549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513549).length < 2 ^ (prefixWord ++ tailWord_513549).sum := by decide
  have hdescent : baseEnd_513549 < baseStart_513549 := by decide
  rcases family_descends (prefixWord ++ tailWord_513549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513605 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 7]
def baseStart_513605 : Nat := 118140960795 + 513605 * 2 ^ 59
def prefixEnd_513605 : Nat := 4983230072969 + 3 ^ 40 * 513605 * 2
def baseEnd_513605 : Nat := 117211658467808111900213

theorem tailTrace_513605 : CollatzResearch.WordTrace tailWord_513605 prefixEnd_513605 117211658467808111900213 := by
  unfold tailWord_513605
  simp only [CollatzResearch.WordTrace]
  refine ⟨18732713304304276595622269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12488475536202851063748179 18732713304304276595622269)
  ·
    refine ⟨7024767489114103723358351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18732713304304276595622269 7024767489114103723358351)
    ·
      refine ⟨10537151233671155585037527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7024767489114103723358351 10537151233671155585037527)
      ·
        refine ⟨15805726850506733377556291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10537151233671155585037527 15805726850506733377556291)
        ·
          refine ⟨23708590275760100066334437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15805726850506733377556291 23708590275760100066334437)
          ·
            refine ⟨4445360676705018762437707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23708590275760100066334437 4445360676705018762437707)
            ·
              refine ⟨6668041015057528143656561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4445360676705018762437707 6668041015057528143656561)
              ·
                refine ⟨5001030761293146107742421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6668041015057528143656561 5001030761293146107742421)
                ·
                  refine ⟨117211658467808111900213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5001030761293146107742421 117211658467808111900213)
                  ·
                    rfl

theorem cell21_513605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_513605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513605 prefixEnd_513605 := by exact prefixLift 513605
  have htrace : WordTrace (prefixWord ++ tailWord_513605) baseStart_513605 baseEnd_513605 := by
    simpa [prefixWord, tailWord_513605, baseEnd_513605] using wordTrace_append hprefix tailTrace_513605
  have hstable : (prefixWord ++ tailWord_513605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513605).length < 2 ^ (prefixWord ++ tailWord_513605).sum := by decide
  have hdescent : baseEnd_513605 < baseStart_513605 := by decide
  rcases family_descends (prefixWord ++ tailWord_513605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513653 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 6]
def baseStart_513653 : Nat := 118140960795 + 513653 * 2 ^ 59
def prefixEnd_513653 : Nat := 4983230072969 + 3 ^ 40 * 513653 * 2
def baseEnd_513653 : Nat := 117222612721770695100115

theorem tailTrace_513653 : CollatzResearch.WordTrace tailWord_513653 prefixEnd_513653 117222612721770695100115 := by
  unfold tailWord_513653
  simp only [CollatzResearch.WordTrace]
  refine ⟨18734464008130380793369613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12489642672086920528913075 18734464008130380793369613)
  ·
    refine ⟨7025424003048892797513605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18734464008130380793369613 7025424003048892797513605)
    ·
      refine ⟨1317267000571667399533801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7025424003048892797513605 1317267000571667399533801)
      ·
        refine ⟨987950250428750549650351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1317267000571667399533801 987950250428750549650351)
        ·
          refine ⟨1481925375643125824475527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987950250428750549650351 1481925375643125824475527)
          ·
            refine ⟨2222888063464688736713291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481925375643125824475527 2222888063464688736713291)
            ·
              refine ⟨3334332095197033105069937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2222888063464688736713291 3334332095197033105069937)
              ·
                refine ⟨2500749071397774828802453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3334332095197033105069937 2500749071397774828802453)
                ·
                  refine ⟨117222612721770695100115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2500749071397774828802453 117222612721770695100115)
                  ·
                    rfl

theorem cell21_513653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_513653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513653 prefixEnd_513653 := by exact prefixLift 513653
  have htrace : WordTrace (prefixWord ++ tailWord_513653) baseStart_513653 baseEnd_513653 := by
    simpa [prefixWord, tailWord_513653, baseEnd_513653] using wordTrace_append hprefix tailTrace_513653
  have hstable : (prefixWord ++ tailWord_513653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513653).length < 2 ^ (prefixWord ++ tailWord_513653).sum := by decide
  have hdescent : baseEnd_513653 < baseStart_513653 := by decide
  rcases family_descends (prefixWord ++ tailWord_513653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513681 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 5]
def baseStart_513681 : Nat := 118140960795 + 513681 * 2 ^ 59
def prefixEnd_513681 : Nat := 4983230072969 + 3 ^ 40 * 513681 * 2
def baseEnd_513681 : Nat := 117229002703248868633391

theorem tailTrace_513681 : CollatzResearch.WordTrace tailWord_513681 prefixEnd_513681 117229002703248868633391 := by
  unfold tailWord_513681
  simp only [CollatzResearch.WordTrace]
  refine ⟨18735485252028941575388897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12490323501352627716925931 18735485252028941575388897)
  ·
    refine ⟨14051613939021706181541673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18735485252028941575388897 14051613939021706181541673)
    ·
      refine ⟨10538710454266279636156255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14051613939021706181541673 10538710454266279636156255)
      ·
        refine ⟨15808065681399419454234383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10538710454266279636156255 15808065681399419454234383)
        ·
          refine ⟨23712098522099129181351575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15808065681399419454234383 23712098522099129181351575)
          ·
            refine ⟨35568147783148693772027363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23712098522099129181351575 35568147783148693772027363)
            ·
              refine ⟨53352221674723040658041045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35568147783148693772027363 53352221674723040658041045)
              ·
                refine ⟨1250442695501321265422837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53352221674723040658041045 1250442695501321265422837)
                ·
                  refine ⟨117229002703248868633391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1250442695501321265422837 117229002703248868633391)
                  ·
                    rfl

theorem cell21_513681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_513681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513681 prefixEnd_513681 := by exact prefixLift 513681
  have htrace : WordTrace (prefixWord ++ tailWord_513681) baseStart_513681 baseEnd_513681 := by
    simpa [prefixWord, tailWord_513681, baseEnd_513681] using wordTrace_append hprefix tailTrace_513681
  have hstable : (prefixWord ++ tailWord_513681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513681).length < 2 ^ (prefixWord ++ tailWord_513681).sum := by decide
  have hdescent : baseEnd_513681 < baseStart_513681 := by decide
  rcases family_descends (prefixWord ++ tailWord_513681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513780 : List Nat := [2, 6, 1, 1, 1, 3, 1, 2, 4]
def baseStart_513780 : Nat := 118140960795 + 513780 * 2 ^ 59
def prefixEnd_513780 : Nat := 4983230072969 + 3 ^ 40 * 513780 * 2
def baseEnd_513780 : Nat := 117251595852046696483189

theorem tailTrace_513780 : CollatzResearch.WordTrace tailWord_513780 prefixEnd_513780 117251595852046696483189 := by
  unfold tailWord_513780
  simp only [CollatzResearch.WordTrace]
  refine ⟨9369548039335140741621397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12492730719113520988828529 9369548039335140741621397)
  ·
    refine ⟨439197564343834722263503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9369548039335140741621397 439197564343834722263503)
    ·
      refine ⟨658796346515752083395255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439197564343834722263503 658796346515752083395255)
      ·
        refine ⟨988194519773628125092883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658796346515752083395255 988194519773628125092883)
        ·
          refine ⟨1482291779660442187639325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988194519773628125092883 1482291779660442187639325)
          ·
            refine ⟨555859417372665820364747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1482291779660442187639325 555859417372665820364747)
            ·
              refine ⟨833789126058998730547121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555859417372665820364747 833789126058998730547121)
              ·
                refine ⟨625341844544249047910341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 833789126058998730547121 625341844544249047910341)
                ·
                  refine ⟨117251595852046696483189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 625341844544249047910341 117251595852046696483189)
                  ·
                    rfl

theorem cell21_513780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_513780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513780 prefixEnd_513780 := by exact prefixLift 513780
  have htrace : WordTrace (prefixWord ++ tailWord_513780) baseStart_513780 baseEnd_513780 := by
    simpa [prefixWord, tailWord_513780, baseEnd_513780] using wordTrace_append hprefix tailTrace_513780
  have hstable : (prefixWord ++ tailWord_513780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513780).length < 2 ^ (prefixWord ++ tailWord_513780).sum := by decide
  have hdescent : baseEnd_513780 < baseStart_513780 := by decide
  rcases family_descends (prefixWord ++ tailWord_513780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513788 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 6]
def baseStart_513788 : Nat := 118140960795 + 513788 * 2 ^ 59
def prefixEnd_513788 : Nat := 4983230072969 + 3 ^ 40 * 513788 * 2
def baseEnd_513788 : Nat := 117253421561040460349839

theorem tailTrace_513788 : CollatzResearch.WordTrace tailWord_513788 prefixEnd_513788 117253421561040460349839 := by
  unfold tailWord_513788
  simp only [CollatzResearch.WordTrace]
  refine ⟨9369693931320649424767009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12492925241760865899689345 9369693931320649424767009)
  ·
    refine ⟨7027270448490487068575257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9369693931320649424767009 7027270448490487068575257)
    ·
      refine ⟨5270452836367865301431443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7027270448490487068575257 5270452836367865301431443)
      ·
        refine ⟨7905679254551797952147165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5270452836367865301431443 7905679254551797952147165)
        ·
          refine ⟨2964629720456924232055187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7905679254551797952147165 2964629720456924232055187)
          ·
            refine ⟨4446944580685386348082781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2964629720456924232055187 4446944580685386348082781)
            ·
              refine ⟨1667604217757019880531043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4446944580685386348082781 1667604217757019880531043)
              ·
                refine ⟨2501406326635529820796565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1667604217757019880531043 2501406326635529820796565)
                ·
                  refine ⟨117253421561040460349839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2501406326635529820796565 117253421561040460349839)
                  ·
                    rfl

theorem cell21_513788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_513788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513788 prefixEnd_513788 := by exact prefixLift 513788
  have htrace : WordTrace (prefixWord ++ tailWord_513788) baseStart_513788 baseEnd_513788 := by
    simpa [prefixWord, tailWord_513788, baseEnd_513788] using wordTrace_append hprefix tailTrace_513788
  have hstable : (prefixWord ++ tailWord_513788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513788).length < 2 ^ (prefixWord ++ tailWord_513788).sum := by decide
  have hdescent : baseEnd_513788 < baseStart_513788 := by decide
  rcases family_descends (prefixWord ++ tailWord_513788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513850 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 5]
def baseStart_513850 : Nat := 118140960795 + 513850 * 2 ^ 59
def prefixEnd_513850 : Nat := 4983230072969 + 3 ^ 40 * 513850 * 2
def baseEnd_513850 : Nat := 117267570805742130316379

theorem tailTrace_513850 : CollatzResearch.WordTrace tailWord_513850 prefixEnd_513850 117267570805742130316379 := by
  unfold tailWord_513850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685412297104170859572751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12494432792277788958860669 4685412297104170859572751)
  ·
    refine ⟨7028118445656256289359127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4685412297104170859572751 7028118445656256289359127)
    ·
      refine ⟨10542177668484384434038691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7028118445656256289359127 10542177668484384434038691)
      ·
        refine ⟨15813266502726576651058037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10542177668484384434038691 15813266502726576651058037)
        ·
          refine ⟨1482493734630616561036691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15813266502726576651058037 1482493734630616561036691)
          ·
            refine ⟨2223740601945924841555037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482493734630616561036691 2223740601945924841555037)
            ·
              refine ⟨833902725729721815583139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2223740601945924841555037 833902725729721815583139)
              ·
                refine ⟨1250854088594582723374709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833902725729721815583139 1250854088594582723374709)
                ·
                  refine ⟨117267570805742130316379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1250854088594582723374709 117267570805742130316379)
                  ·
                    rfl

theorem cell21_513850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_513850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513850 prefixEnd_513850 := by exact prefixLift 513850
  have htrace : WordTrace (prefixWord ++ tailWord_513850) baseStart_513850 baseEnd_513850 := by
    simpa [prefixWord, tailWord_513850, baseEnd_513850] using wordTrace_append hprefix tailTrace_513850
  have hstable : (prefixWord ++ tailWord_513850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513850).length < 2 ^ (prefixWord ++ tailWord_513850).sum := by decide
  have hdescent : baseEnd_513850 < baseStart_513850 := by decide
  rcases family_descends (prefixWord ++ tailWord_513850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513943 : List Nat := [1, 1, 3, 3, 1, 4, 2, 3, 3]
def baseStart_513943 : Nat := 118140960795 + 513943 * 2 ^ 59
def prefixEnd_513943 : Nat := 4983230072969 + 3 ^ 40 * 513943 * 2
def baseEnd_513943 : Nat := 117288794672794635266189

theorem tailTrace_513943 : CollatzResearch.WordTrace tailWord_513943 prefixEnd_513943 117288794672794635266189 := by
  unfold tailWord_513943
  simp only [CollatzResearch.WordTrace]
  refine ⟨18745041177079760321426483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12496694118053173547617655 18745041177079760321426483)
  ·
    refine ⟨28117561765619640482139725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18745041177079760321426483 28117561765619640482139725)
    ·
      refine ⟨10544085662107365180802397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28117561765619640482139725 10544085662107365180802397)
      ·
        refine ⟨3954032123290261942800899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10544085662107365180802397 3954032123290261942800899)
        ·
          refine ⟨5931048184935392914201349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3954032123290261942800899 5931048184935392914201349)
          ·
            refine ⟨1112071534675386171412753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5931048184935392914201349 1112071534675386171412753)
            ·
              refine ⟨834053651006539628559565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112071534675386171412753 834053651006539628559565)
              ·
                refine ⟨312770119127452360709837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 834053651006539628559565 312770119127452360709837)
                ·
                  refine ⟨117288794672794635266189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312770119127452360709837 117288794672794635266189)
                  ·
                    rfl

theorem cell21_513943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 3].length) (baseStart_513943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513943 prefixEnd_513943 := by exact prefixLift 513943
  have htrace : WordTrace (prefixWord ++ tailWord_513943) baseStart_513943 baseEnd_513943 := by
    simpa [prefixWord, tailWord_513943, baseEnd_513943] using wordTrace_append hprefix tailTrace_513943
  have hstable : (prefixWord ++ tailWord_513943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513943).length < 2 ^ (prefixWord ++ tailWord_513943).sum := by decide
  have hdescent : baseEnd_513943 < baseStart_513943 := by decide
  rcases family_descends (prefixWord ++ tailWord_513943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513960 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 5]
def baseStart_513960 : Nat := 118140960795 + 513960 * 2 ^ 59
def prefixEnd_513960 : Nat := 4983230072969 + 3 ^ 40 * 513960 * 2
def baseEnd_513960 : Nat := 117292674304406383482821

theorem tailTrace_513960 : CollatzResearch.WordTrace tailWord_513960 prefixEnd_513960 117292674304406383482821 := by
  unfold tailWord_513960
  simp only [CollatzResearch.WordTrace]
  refine ⟨9372830609009086112397667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12497107478678781483196889 9372830609009086112397667)
  ·
    refine ⟨14059245913513629168596501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9372830609009086112397667 14059245913513629168596501)
    ·
      refine ⟨659027152195951367277961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14059245913513629168596501 659027152195951367277961)
      ·
        refine ⟨494270364146963525458471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659027152195951367277961 494270364146963525458471)
        ·
          refine ⟨741405546220445288187707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494270364146963525458471 741405546220445288187707)
          ·
            refine ⟨1112108319330667932281561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741405546220445288187707 1112108319330667932281561)
            ·
              refine ⟨834081239498000949211171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112108319330667932281561 834081239498000949211171)
              ·
                refine ⟨1251121859247001423816757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834081239498000949211171 1251121859247001423816757)
                ·
                  refine ⟨117292674304406383482821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1251121859247001423816757 117292674304406383482821)
                  ·
                    rfl

theorem cell21_513960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 5].length) (baseStart_513960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513960 prefixEnd_513960 := by exact prefixLift 513960
  have htrace : WordTrace (prefixWord ++ tailWord_513960) baseStart_513960 baseEnd_513960 := by
    simpa [prefixWord, tailWord_513960, baseEnd_513960] using wordTrace_append hprefix tailTrace_513960
  have hstable : (prefixWord ++ tailWord_513960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513960).length < 2 ^ (prefixWord ++ tailWord_513960).sum := by decide
  have hdescent : baseEnd_513960 < baseStart_513960 := by decide
  rcases family_descends (prefixWord ++ tailWord_513960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513999 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 8]
def baseStart_513999 : Nat := 118140960795 + 513999 * 2 ^ 59
def prefixEnd_513999 : Nat := 4983230072969 + 3 ^ 40 * 513999 * 2
def baseEnd_513999 : Nat := 117301574635750982332741

theorem tailTrace_513999 : CollatzResearch.WordTrace tailWord_513999 prefixEnd_513999 117301574635750982332741 := by
  unfold tailWord_513999
  simp only [CollatzResearch.WordTrace]
  refine ⟨18747083664876881885465051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12498055776584587923643367 18747083664876881885465051)
  ·
    refine ⟨28120625497315322828197577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18747083664876881885465051 28120625497315322828197577)
    ·
      refine ⟨21090469122986492121148183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28120625497315322828197577 21090469122986492121148183)
      ·
        refine ⟨31635703684479738181722275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21090469122986492121148183 31635703684479738181722275)
        ·
          refine ⟨47453555526719607272583413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31635703684479738181722275 47453555526719607272583413)
          ·
            refine ⟨4448770830629963181804695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47453555526719607272583413 4448770830629963181804695)
            ·
              refine ⟨6673156245944944772707043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448770830629963181804695 6673156245944944772707043)
              ·
                refine ⟨10009734368917417159060565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6673156245944944772707043 10009734368917417159060565)
                ·
                  refine ⟨117301574635750982332741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10009734368917417159060565 117301574635750982332741)
                  ·
                    rfl

theorem cell21_513999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 8].length) (baseStart_513999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_513999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_513999 prefixEnd_513999 := by exact prefixLift 513999
  have htrace : WordTrace (prefixWord ++ tailWord_513999) baseStart_513999 baseEnd_513999 := by
    simpa [prefixWord, tailWord_513999, baseEnd_513999] using wordTrace_append hprefix tailTrace_513999
  have hstable : (prefixWord ++ tailWord_513999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513999).length < 2 ^ (prefixWord ++ tailWord_513999).sum := by decide
  have hdescent : baseEnd_513999 < baseStart_513999 := by decide
  rcases family_descends (prefixWord ++ tailWord_513999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514033 : List Nat := [1, 2, 2, 2, 5, 1, 1, 3, 4]
def baseStart_514033 : Nat := 118140960795 + 514033 * 2 ^ 59
def prefixEnd_514033 : Nat := 4983230072969 + 3 ^ 40 * 514033 * 2
def baseEnd_514033 : Nat := 117309333898974478766005

theorem tailTrace_514033 : CollatzResearch.WordTrace tailWord_514033 prefixEnd_514033 117309333898974478766005 := by
  unfold tailWord_514033
  simp only [CollatzResearch.WordTrace]
  refine ⟨18748323746753705692202753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12498882497835803794801835 18748323746753705692202753)
  ·
    refine ⟨14061242810065279269152065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18748323746753705692202753 14061242810065279269152065)
    ·
      refine ⟨10545932107548959451864049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14061242810065279269152065 10545932107548959451864049)
      ·
        refine ⟨7909449080661719588898037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10545932107548959451864049 7909449080661719588898037)
        ·
          refine ⟨741510851312036211459191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7909449080661719588898037 741510851312036211459191)
          ·
            refine ⟨1112266276968054317188787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741510851312036211459191 1112266276968054317188787)
            ·
              refine ⟨1668399415452081475783181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112266276968054317188787 1668399415452081475783181)
              ·
                refine ⟨625649780794530553418693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1668399415452081475783181 625649780794530553418693)
                ·
                  refine ⟨117309333898974478766005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 625649780794530553418693 117309333898974478766005)
                  ·
                    rfl

theorem cell21_514033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_514033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514033 prefixEnd_514033 := by exact prefixLift 514033
  have htrace : WordTrace (prefixWord ++ tailWord_514033) baseStart_514033 baseEnd_514033 := by
    simpa [prefixWord, tailWord_514033, baseEnd_514033] using wordTrace_append hprefix tailTrace_514033
  have hstable : (prefixWord ++ tailWord_514033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514033).length < 2 ^ (prefixWord ++ tailWord_514033).sum := by decide
  have hdescent : baseEnd_514033 < baseStart_514033 := by decide
  rcases family_descends (prefixWord ++ tailWord_514033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514137 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 5]
def baseStart_514137 : Nat := 118140960795 + 514137 * 2 ^ 59
def prefixEnd_514137 : Nat := 4983230072969 + 3 ^ 40 * 514137 * 2
def baseEnd_514137 : Nat := 117333068115893409032459

theorem tailTrace_514137 : CollatzResearch.WordTrace tailWord_514137 prefixEnd_514137 117333068115893409032459 := by
  unfold tailWord_514137
  simp only [CollatzResearch.WordTrace]
  refine ⟨18752116938376931453988665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12501411292251287635992443 18752116938376931453988665)
  ·
    refine ⟨14064087703782698590491499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18752116938376931453988665 14064087703782698590491499)
    ·
      refine ⟨21096131555674047885737249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14064087703782698590491499 21096131555674047885737249)
      ·
        refine ⟨15822098666755535914302937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21096131555674047885737249 15822098666755535914302937)
        ·
          refine ⟨11866574000066651935727203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15822098666755535914302937 11866574000066651935727203)
          ·
            refine ⟨17799861000099977903590805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11866574000066651935727203 17799861000099977903590805)
            ·
              refine ⟨834368484379686464230819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17799861000099977903590805 834368484379686464230819)
              ·
                refine ⟨1251552726569529696346229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834368484379686464230819 1251552726569529696346229)
                ·
                  refine ⟨117333068115893409032459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1251552726569529696346229 117333068115893409032459)
                  ·
                    rfl

theorem cell21_514137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_514137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514137 prefixEnd_514137 := by exact prefixLift 514137
  have htrace : WordTrace (prefixWord ++ tailWord_514137) baseStart_514137 baseEnd_514137 := by
    simpa [prefixWord, tailWord_514137, baseEnd_514137] using wordTrace_append hprefix tailTrace_514137
  have hstable : (prefixWord ++ tailWord_514137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514137).length < 2 ^ (prefixWord ++ tailWord_514137).sum := by decide
  have hdescent : baseEnd_514137 < baseStart_514137 := by decide
  rcases family_descends (prefixWord ++ tailWord_514137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514199 : List Nat := [1, 1, 3, 3, 4, 1, 2, 6]
def baseStart_514199 : Nat := 118140960795 + 514199 * 2 ^ 59
def prefixEnd_514199 : Nat := 4983230072969 + 3 ^ 40 * 514199 * 2
def baseEnd_514199 : Nat := 39115739120198359666333

theorem tailTrace_514199 : CollatzResearch.WordTrace tailWord_514199 prefixEnd_514199 39115739120198359666333 := by
  unfold tailWord_514199
  simp only [CollatzResearch.WordTrace]
  refine ⟨18754378264152316042745651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12502918842768210695163767 18754378264152316042745651)
  ·
    refine ⟨28131567396228474064118477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18754378264152316042745651 28131567396228474064118477)
    ·
      refine ⟨10549337773585677774044429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28131567396228474064118477 10549337773585677774044429)
      ·
        refine ⟨3956001665094629165266661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10549337773585677774044429 3956001665094629165266661)
        ·
          refine ⟨741750312205242968487499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3956001665094629165266661 741750312205242968487499)
          ·
            refine ⟨1112625468307864452731249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741750312205242968487499 1112625468307864452731249)
            ·
              refine ⟨834469101230898339548437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112625468307864452731249 834469101230898339548437)
              ·
                refine ⟨39115739120198359666333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 834469101230898339548437 39115739120198359666333)
                ·
                  rfl

theorem cell21_514199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 6].length) (baseStart_514199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514199 prefixEnd_514199 := by exact prefixLift 514199
  have htrace : WordTrace (prefixWord ++ tailWord_514199) baseStart_514199 baseEnd_514199 := by
    simpa [prefixWord, tailWord_514199, baseEnd_514199] using wordTrace_append hprefix tailTrace_514199
  have hstable : (prefixWord ++ tailWord_514199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514199).length < 2 ^ (prefixWord ++ tailWord_514199).sum := by decide
  have hdescent : baseEnd_514199 < baseStart_514199 := by decide
  rcases family_descends (prefixWord ++ tailWord_514199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514303 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 6]
def baseStart_514303 : Nat := 118140960795 + 514303 * 2 ^ 59
def prefixEnd_514303 : Nat := 4983230072969 + 3 ^ 40 * 514303 * 2
def baseEnd_514303 : Nat := 117370951577514009265453

theorem tailTrace_514303 : CollatzResearch.WordTrace tailWord_514303 prefixEnd_514303 117370951577514009265453 := by
  unfold tailWord_514303
  simp only [CollatzResearch.WordTrace]
  refine ⟨18758171455775541804531563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12505447637183694536354375 18758171455775541804531563)
  ·
    refine ⟨28137257183663312706797345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18758171455775541804531563 28137257183663312706797345)
    ·
      refine ⟨21102942887747484530098009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28137257183663312706797345 21102942887747484530098009)
      ·
        refine ⟨15827207165810613397573507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21102942887747484530098009 15827207165810613397573507)
        ·
          refine ⟨23740810748715920096360261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15827207165810613397573507 23740810748715920096360261)
          ·
            refine ⟨4451402015384235018067549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23740810748715920096360261 4451402015384235018067549)
            ·
              refine ⟨1669275755769088131775331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4451402015384235018067549 1669275755769088131775331)
              ·
                refine ⟨2503913633653632197662997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669275755769088131775331 2503913633653632197662997)
                ·
                  refine ⟨117370951577514009265453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2503913633653632197662997 117370951577514009265453)
                  ·
                    rfl

theorem cell21_514303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 6].length) (baseStart_514303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514303 prefixEnd_514303 := by exact prefixLift 514303
  have htrace : WordTrace (prefixWord ++ tailWord_514303) baseStart_514303 baseEnd_514303 := by
    simpa [prefixWord, tailWord_514303, baseEnd_514303] using wordTrace_append hprefix tailTrace_514303
  have hstable : (prefixWord ++ tailWord_514303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514303).length < 2 ^ (prefixWord ++ tailWord_514303).sum := by decide
  have hdescent : baseEnd_514303 < baseStart_514303 := by decide
  rcases family_descends (prefixWord ++ tailWord_514303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514306 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 5]
def baseStart_514306 : Nat := 118140960795 + 514306 * 2 ^ 59
def prefixEnd_514306 : Nat := 4983230072969 + 3 ^ 40 * 514306 * 2
def baseEnd_514306 : Nat := 117371636218386670715447

theorem tailTrace_514306 : CollatzResearch.WordTrace tailWord_514306 prefixEnd_514306 117371636218386670715447 := by
  unfold tailWord_514306
  simp only [CollatzResearch.WordTrace]
  refine ⟨4689570218691168329222693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12505520583176448877927181 4689570218691168329222693)
  ·
    refine ⟨879294416004594061729255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4689570218691168329222693 879294416004594061729255)
    ·
      refine ⟨1318941624006891092593883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 879294416004594061729255 1318941624006891092593883)
      ·
        refine ⟨1978412436010336638890825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1318941624006891092593883 1978412436010336638890825)
        ·
          refine ⟨1483809327007752479168119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1978412436010336638890825 1483809327007752479168119)
          ·
            refine ⟨2225713990511628718752179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483809327007752479168119 2225713990511628718752179)
            ·
              refine ⟨3338570985767443078128269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2225713990511628718752179 3338570985767443078128269)
              ·
                refine ⟨1251964119662791154298101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3338570985767443078128269 1251964119662791154298101)
                ·
                  refine ⟨117371636218386670715447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1251964119662791154298101 117371636218386670715447)
                  ·
                    rfl

theorem cell21_514306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_514306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514306 prefixEnd_514306 := by exact prefixLift 514306
  have htrace : WordTrace (prefixWord ++ tailWord_514306) baseStart_514306 baseEnd_514306 := by
    simpa [prefixWord, tailWord_514306, baseEnd_514306] using wordTrace_append hprefix tailTrace_514306
  have hstable : (prefixWord ++ tailWord_514306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514306).length < 2 ^ (prefixWord ++ tailWord_514306).sum := by decide
  have hdescent : baseEnd_514306 < baseStart_514306 := by decide
  rcases family_descends (prefixWord ++ tailWord_514306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514348 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 7]
def baseStart_514348 : Nat := 118140960795 + 514348 * 2 ^ 59
def prefixEnd_514348 : Nat := 4983230072969 + 3 ^ 40 * 514348 * 2
def baseEnd_514348 : Nat := 117381221190603931015361

theorem tailTrace_514348 : CollatzResearch.WordTrace tailWord_514348 prefixEnd_514348 117381221190603931015361 := by
  unfold tailWord_514348
  simp only [CollatzResearch.WordTrace]
  refine ⟨9379906370306257244959849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12506541827075009659946465 9379906370306257244959849)
  ·
    refine ⟨7034929777729692933719887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9379906370306257244959849 7034929777729692933719887)
    ·
      refine ⟨10552394666594539400579831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7034929777729692933719887 10552394666594539400579831)
      ·
        refine ⟨15828591999891809100869747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10552394666594539400579831 15828591999891809100869747)
        ·
          refine ⟨23742887999837713651304621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15828591999891809100869747 23742887999837713651304621)
          ·
            refine ⟨8903582999939142619239233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23742887999837713651304621 8903582999939142619239233)
            ·
              refine ⟨6677687249954356964429425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8903582999939142619239233 6677687249954356964429425)
              ·
                refine ⟨5008265437465767723322069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6677687249954356964429425 5008265437465767723322069)
                ·
                  refine ⟨117381221190603931015361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5008265437465767723322069 117381221190603931015361)
                  ·
                    rfl

theorem cell21_514348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_514348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514348 prefixEnd_514348 := by exact prefixLift 514348
  have htrace : WordTrace (prefixWord ++ tailWord_514348) baseStart_514348 baseEnd_514348 := by
    simpa [prefixWord, tailWord_514348, baseEnd_514348] using wordTrace_append hprefix tailTrace_514348
  have hstable : (prefixWord ++ tailWord_514348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514348).length < 2 ^ (prefixWord ++ tailWord_514348).sum := by decide
  have hdescent : baseEnd_514348 < baseStart_514348 := by decide
  rcases family_descends (prefixWord ++ tailWord_514348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514410 : List Nat := [3, 1, 3, 3, 1, 10]
def baseStart_514410 : Nat := 118140960795 + 514410 * 2 ^ 59
def prefixEnd_514410 : Nat := 4983230072969 + 3 ^ 40 * 514410 * 2
def baseEnd_514410 : Nat := 4347976682789096332663

theorem tailTrace_514410 : CollatzResearch.WordTrace tailWord_514410 prefixEnd_514410 4347976682789096332663 := by
  unfold tailWord_514410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4690518516596974769669171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12508049377591932719117789 4690518516596974769669171)
  ·
    refine ⟨7035777774895462154503757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4690518516596974769669171 7035777774895462154503757)
    ·
      refine ⟨2638416665585798307938909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7035777774895462154503757 2638416665585798307938909)
      ·
        refine ⟨989406249594674365477091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2638416665585798307938909 989406249594674365477091)
        ·
          refine ⟨1484109374392011548215637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989406249594674365477091 1484109374392011548215637)
          ·
            refine ⟨4347976682789096332663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1484109374392011548215637 4347976682789096332663)
            ·
              rfl

theorem cell21_514410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 10].length) (baseStart_514410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514410 prefixEnd_514410 := by exact prefixLift 514410
  have htrace : WordTrace (prefixWord ++ tailWord_514410) baseStart_514410 baseEnd_514410 := by
    simpa [prefixWord, tailWord_514410, baseEnd_514410] using wordTrace_append hprefix tailTrace_514410
  have hstable : (prefixWord ++ tailWord_514410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514410).length < 2 ^ (prefixWord ++ tailWord_514410).sum := by decide
  have hdescent : baseEnd_514410 < baseStart_514410 := by decide
  rcases family_descends (prefixWord ++ tailWord_514410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514441 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 5]
def baseStart_514441 : Nat := 118140960795 + 514441 * 2 ^ 59
def prefixEnd_514441 : Nat := 4983230072969 + 3 ^ 40 * 514441 * 2
def baseEnd_514441 : Nat := 117402445057656435965171

theorem tailTrace_514441 : CollatzResearch.WordTrace tailWord_514441 prefixEnd_514441 117402445057656435965171 := by
  unfold tailWord_514441
  simp only [CollatzResearch.WordTrace]
  refine ⟨18763204729275591373055177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12508803152850394248703451 18763204729275591373055177)
  ·
    refine ⟨14072403546956693529791383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18763204729275591373055177 14072403546956693529791383)
    ·
      refine ⟨21108605320435040294687075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14072403546956693529791383 21108605320435040294687075)
      ·
        refine ⟨31662907980652560442030613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21108605320435040294687075 31662907980652560442030613)
        ·
          refine ⟨1484198811593088770720185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31662907980652560442030613 1484198811593088770720185)
          ·
            refine ⟨1113149108694816578040139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1484198811593088770720185 1113149108694816578040139)
            ·
              refine ⟨1669723663042224867060209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1113149108694816578040139 1669723663042224867060209)
              ·
                refine ⟨1252292747281668650295157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1669723663042224867060209 1252292747281668650295157)
                ·
                  refine ⟨117402445057656435965171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1252292747281668650295157 117402445057656435965171)
                  ·
                    rfl

theorem cell21_514441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_514441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514441 prefixEnd_514441 := by exact prefixLift 514441
  have htrace : WordTrace (prefixWord ++ tailWord_514441) baseStart_514441 baseEnd_514441 := by
    simpa [prefixWord, tailWord_514441, baseEnd_514441] using wordTrace_append hprefix tailTrace_514441
  have hstable : (prefixWord ++ tailWord_514441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514441).length < 2 ^ (prefixWord ++ tailWord_514441).sum := by decide
  have hdescent : baseEnd_514441 < baseStart_514441 := by decide
  rcases family_descends (prefixWord ++ tailWord_514441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514458 : List Nat := [3, 1, 1, 4, 1, 2, 1, 5, 3]
def baseStart_514458 : Nat := 118140960795 + 514458 * 2 ^ 59
def prefixEnd_514458 : Nat := 4983230072969 + 3 ^ 40 * 514458 * 2
def baseEnd_514458 : Nat := 117406324689268184181803

theorem tailTrace_514458 : CollatzResearch.WordTrace tailWord_514458 prefixEnd_514458 117406324689268184181803 := by
  unfold tailWord_514458
  simp only [CollatzResearch.WordTrace]
  refine ⟨4690956192553500819106007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12509216513476002184282685 4690956192553500819106007)
  ·
    refine ⟨7036434288830251228659011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4690956192553500819106007 7036434288830251228659011)
    ·
      refine ⟨10554651433245376842988517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7036434288830251228659011 10554651433245376842988517)
      ·
        refine ⟨1978997143733508158060347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10554651433245376842988517 1978997143733508158060347)
        ·
          refine ⟨2968495715600262237090521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1978997143733508158060347 2968495715600262237090521)
          ·
            refine ⟨2226371786700196677817891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2968495715600262237090521 2226371786700196677817891)
            ·
              refine ⟨3339557680050295016726837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2226371786700196677817891 3339557680050295016726837)
              ·
                refine ⟨313083532504715157818141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3339557680050295016726837 313083532504715157818141)
                ·
                  refine ⟨117406324689268184181803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313083532504715157818141 117406324689268184181803)
                  ·
                    rfl

theorem cell21_514458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_514458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514458 prefixEnd_514458 := by exact prefixLift 514458
  have htrace : WordTrace (prefixWord ++ tailWord_514458) baseStart_514458 baseEnd_514458 := by
    simpa [prefixWord, tailWord_514458, baseEnd_514458] using wordTrace_append hprefix tailTrace_514458
  have hstable : (prefixWord ++ tailWord_514458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514458).length < 2 ^ (prefixWord ++ tailWord_514458).sum := by decide
  have hdescent : baseEnd_514458 < baseStart_514458 := by decide
  rcases family_descends (prefixWord ++ tailWord_514458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514469 : List Nat := [1, 3, 1, 2, 1, 1, 12]
def baseStart_514469 : Nat := 118140960795 + 514469 * 2 ^ 59
def prefixEnd_514469 : Nat := 4983230072969 + 3 ^ 40 * 514469 * 2
def baseEnd_514469 : Nat := 13045426115459401055383

theorem tailTrace_514469 : CollatzResearch.WordTrace tailWord_514469 prefixEnd_514469 13045426115459401055383 := by
  unfold tailWord_514469
  simp only [CollatzResearch.WordTrace]
  refine ⟨18764225973174152155074461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12509483982116101436716307 18764225973174152155074461)
  ·
    refine ⟨7036584739940307058152923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18764225973174152155074461 7036584739940307058152923)
    ·
      refine ⟨10554877109910460587229385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7036584739940307058152923 10554877109910460587229385)
      ·
        refine ⟨7916157832432845440422039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10554877109910460587229385 7916157832432845440422039)
        ·
          refine ⟨11874236748649268160633059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7916157832432845440422039 11874236748649268160633059)
          ·
            refine ⟨17811355122973902240949589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11874236748649268160633059 17811355122973902240949589)
            ·
              refine ⟨13045426115459401055383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 17811355122973902240949589 13045426115459401055383)
              ·
                rfl

theorem cell21_514469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 12].length) (baseStart_514469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514469 prefixEnd_514469 := by exact prefixLift 514469
  have htrace : WordTrace (prefixWord ++ tailWord_514469) baseStart_514469 baseEnd_514469 := by
    simpa [prefixWord, tailWord_514469, baseEnd_514469] using wordTrace_append hprefix tailTrace_514469
  have hstable : (prefixWord ++ tailWord_514469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514469).length < 2 ^ (prefixWord ++ tailWord_514469).sum := by decide
  have hdescent : baseEnd_514469 < baseStart_514469 := by decide
  rcases family_descends (prefixWord ++ tailWord_514469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514489 : List Nat := [1, 2, 1, 4, 3, 2, 3, 1, 4]
def baseStart_514489 : Nat := 118140960795 + 514489 * 2 ^ 59
def prefixEnd_514489 : Nat := 4983230072969 + 3 ^ 40 * 514489 * 2
def baseEnd_514489 : Nat := 117413399311619019165073

theorem tailTrace_514489 : CollatzResearch.WordTrace tailWord_514489 prefixEnd_514489 117413399311619019165073 := by
  unfold tailWord_514489
  simp only [CollatzResearch.WordTrace]
  refine ⟨18764955433101695570802521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12509970288734463713868347 18764955433101695570802521)
  ·
    refine ⟨14073716574826271678101891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18764955433101695570802521 14073716574826271678101891)
    ·
      refine ⟨21110574862239407517152837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14073716574826271678101891 21110574862239407517152837)
      ·
        refine ⟨3958232786669888909466157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21110574862239407517152837 3958232786669888909466157)
        ·
          refine ⟨1484337295001208341049809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3958232786669888909466157 1484337295001208341049809)
          ·
            refine ⟨1113252971250906255787357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1484337295001208341049809 1113252971250906255787357)
            ·
              refine ⟨417469864219089845920259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1113252971250906255787357 417469864219089845920259)
              ·
                refine ⟨626204796328634768880389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417469864219089845920259 626204796328634768880389)
                ·
                  refine ⟨117413399311619019165073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 626204796328634768880389 117413399311619019165073)
                  ·
                    rfl

theorem cell21_514489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 4].length) (baseStart_514489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514489 prefixEnd_514489 := by exact prefixLift 514489
  have htrace : WordTrace (prefixWord ++ tailWord_514489) baseStart_514489 baseEnd_514489 := by
    simpa [prefixWord, tailWord_514489, baseEnd_514489] using wordTrace_append hprefix tailTrace_514489
  have hstable : (prefixWord ++ tailWord_514489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514489).length < 2 ^ (prefixWord ++ tailWord_514489).sum := by decide
  have hdescent : baseEnd_514489 < baseStart_514489 := by decide
  rcases family_descends (prefixWord ++ tailWord_514489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514503 : List Nat := [1, 1, 4, 1, 1, 6, 2, 5]
def baseStart_514503 : Nat := 118140960795 + 514503 * 2 ^ 59
def prefixEnd_514503 : Nat := 4983230072969 + 3 ^ 40 * 514503 * 2
def baseEnd_514503 : Nat := 39138864767452701977237

theorem tailTrace_514503 : CollatzResearch.WordTrace tailWord_514503 prefixEnd_514503 39138864767452701977237 := by
  unfold tailWord_514503
  simp only [CollatzResearch.WordTrace]
  refine ⟨18765466055050975961812163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12510310703367317307874775 18765466055050975961812163)
  ·
    refine ⟨28148199082576463942718245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18765466055050975961812163 28148199082576463942718245)
    ·
      refine ⟨5277787327983086989259671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28148199082576463942718245 5277787327983086989259671)
      ·
        refine ⟨7916680991974630483889507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5277787327983086989259671 7916680991974630483889507)
        ·
          refine ⟨11875021487961945725834261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7916680991974630483889507 11875021487961945725834261)
          ·
            refine ⟨556641632248216205898481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11875021487961945725834261 556641632248216205898481)
            ·
              refine ⟨417481224186162154423861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556641632248216205898481 417481224186162154423861)
              ·
                refine ⟨39138864767452701977237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 417481224186162154423861 39138864767452701977237)
                ·
                  rfl

theorem cell21_514503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 5].length) (baseStart_514503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514503 prefixEnd_514503 := by exact prefixLift 514503
  have htrace : WordTrace (prefixWord ++ tailWord_514503) baseStart_514503 baseEnd_514503 := by
    simpa [prefixWord, tailWord_514503, baseEnd_514503] using wordTrace_append hprefix tailTrace_514503
  have hstable : (prefixWord ++ tailWord_514503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514503).length < 2 ^ (prefixWord ++ tailWord_514503).sum := by decide
  have hdescent : baseEnd_514503 < baseStart_514503 := by decide
  rcases family_descends (prefixWord ++ tailWord_514503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514596 : List Nat := [2, 3, 1, 5, 1, 2, 1, 6]
def baseStart_514596 : Nat := 118140960795 + 514596 * 2 ^ 59
def prefixEnd_514596 : Nat := 4983230072969 + 3 ^ 40 * 514596 * 2
def baseEnd_514596 : Nat := 39145939389803536960507

theorem tailTrace_514596 : CollatzResearch.WordTrace tailWord_514596 prefixEnd_514596 39145939389803536960507 := by
  unfold tailWord_514596
  simp only [CollatzResearch.WordTrace]
  refine ⟨9384429021857026422473821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12512572029142701896631761 9384429021857026422473821)
  ·
    refine ⟨3519160883196384908427683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9384429021857026422473821 3519160883196384908427683)
    ·
      refine ⟨5278741324794577362641525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3519160883196384908427683 5278741324794577362641525)
      ·
        refine ⟨494881999199491627747643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5278741324794577362641525 494881999199491627747643)
        ·
          refine ⟨742322998799237441621465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494881999199491627747643 742322998799237441621465)
          ·
            refine ⟨556742249099428081216099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742322998799237441621465 556742249099428081216099)
            ·
              refine ⟨835113373649142121824149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556742249099428081216099 835113373649142121824149)
              ·
                refine ⟨39145939389803536960507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 835113373649142121824149 39145939389803536960507)
                ·
                  rfl

theorem cell21_514596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 6].length) (baseStart_514596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514596 prefixEnd_514596 := by exact prefixLift 514596
  have htrace : WordTrace (prefixWord ++ tailWord_514596) baseStart_514596 baseEnd_514596 := by
    simpa [prefixWord, tailWord_514596, baseEnd_514596] using wordTrace_append hprefix tailTrace_514596
  have hstable : (prefixWord ++ tailWord_514596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514596).length < 2 ^ (prefixWord ++ tailWord_514596).sum := by decide
  have hdescent : baseEnd_514596 < baseStart_514596 := by decide
  rcases family_descends (prefixWord ++ tailWord_514596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514669 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 5]
def baseStart_514669 : Nat := 118140960795 + 514669 * 2 ^ 59
def prefixEnd_514669 : Nat := 4983230072969 + 3 ^ 40 * 514669 * 2
def baseEnd_514669 : Nat := 117454477763978706164705

theorem tailTrace_514669 : CollatzResearch.WordTrace tailWord_514669 prefixEnd_514669 117454477763978706164705 := by
  unfold tailWord_514669
  simp only [CollatzResearch.WordTrace]
  refine ⟨18771520572449586312355061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12514347048299724208236707 18771520572449586312355061)
  ·
    refine ⟨1759830053667148716783287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18771520572449586312355061 1759830053667148716783287)
    ·
      refine ⟨2639745080500723075174931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1759830053667148716783287 2639745080500723075174931)
      ·
        refine ⟨3959617620751084612762397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2639745080500723075174931 3959617620751084612762397)
        ·
          refine ⟨1484856607781656729785899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3959617620751084612762397 1484856607781656729785899)
          ·
            refine ⟨2227284911672485094678849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1484856607781656729785899 2227284911672485094678849)
            ·
              refine ⟨1670463683754363821009137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227284911672485094678849 1670463683754363821009137)
              ·
                refine ⟨1252847762815772865756853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670463683754363821009137 1252847762815772865756853)
                ·
                  refine ⟨117454477763978706164705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1252847762815772865756853 117454477763978706164705)
                  ·
                    rfl

theorem cell21_514669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_514669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514669 prefixEnd_514669 := by exact prefixLift 514669
  have htrace : WordTrace (prefixWord ++ tailWord_514669) baseStart_514669 baseEnd_514669 := by
    simpa [prefixWord, tailWord_514669, baseEnd_514669] using wordTrace_append hprefix tailTrace_514669
  have hstable : (prefixWord ++ tailWord_514669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514669).length < 2 ^ (prefixWord ++ tailWord_514669).sum := by decide
  have hdescent : baseEnd_514669 < baseStart_514669 := by decide
  rcases family_descends (prefixWord ++ tailWord_514669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514672 : List Nat := [2, 1, 1, 1, 8, 1, 2, 5]
def baseStart_514672 : Nat := 118140960795 + 514672 * 2 ^ 59
def prefixEnd_514672 : Nat := 4983230072969 + 3 ^ 40 * 514672 * 2
def baseEnd_514672 : Nat := 39151720801617122538233

theorem tailTrace_514672 : CollatzResearch.WordTrace tailWord_514672 prefixEnd_514672 39151720801617122538233 := by
  unfold tailWord_514672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9385814995719358912357135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12514419994292478549809513 9385814995719358912357135)
  ·
    refine ⟨14078722493579038368535703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9385814995719358912357135 14078722493579038368535703)
    ·
      refine ⟨21118083740368557552803555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14078722493579038368535703 21118083740368557552803555)
      ·
        refine ⟨31677125610552836329205333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21118083740368557552803555 31677125610552836329205333)
        ·
          refine ⟨371216315748666050732875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 31677125610552836329205333 371216315748666050732875)
          ·
            refine ⟨556824473622999076099313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371216315748666050732875 556824473622999076099313)
            ·
              refine ⟨417618355217249307074485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556824473622999076099313 417618355217249307074485)
              ·
                refine ⟨39151720801617122538233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 417618355217249307074485 39151720801617122538233)
                ·
                  rfl

theorem cell21_514672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 5].length) (baseStart_514672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514672 prefixEnd_514672 := by exact prefixLift 514672
  have htrace : WordTrace (prefixWord ++ tailWord_514672) baseStart_514672 baseEnd_514672 := by
    simpa [prefixWord, tailWord_514672, baseEnd_514672] using wordTrace_append hprefix tailTrace_514672
  have hstable : (prefixWord ++ tailWord_514672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514672).length < 2 ^ (prefixWord ++ tailWord_514672).sum := by decide
  have hdescent : baseEnd_514672 < baseStart_514672 := by decide
  rcases family_descends (prefixWord ++ tailWord_514672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514745 : List Nat := [1, 2, 1, 4, 1, 1, 1, 7, 3]
def baseStart_514745 : Nat := 118140960795 + 514745 * 2 ^ 59
def prefixEnd_514745 : Nat := 4983230072969 + 3 ^ 40 * 514745 * 2
def baseEnd_514745 : Nat := 117471821999419462897883

theorem tailTrace_514745 : CollatzResearch.WordTrace tailWord_514745 prefixEnd_514745 117471821999419462897883 := by
  unfold tailWord_514745
  simp only [CollatzResearch.WordTrace]
  refine ⟨18774292520174251292121689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12516195013449500861414459 18774292520174251292121689)
  ·
    refine ⟨14080719390130688469091267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18774292520174251292121689 14080719390130688469091267)
    ·
      refine ⟨21121079085196032703636901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14080719390130688469091267 21121079085196032703636901)
      ·
        refine ⟨3960202328474256131931919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21121079085196032703636901 3960202328474256131931919)
        ·
          refine ⟨5940303492711384197897879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3960202328474256131931919 5940303492711384197897879)
          ·
            refine ⟨8910455239067076296846819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5940303492711384197897879 8910455239067076296846819)
            ·
              refine ⟨13365682858600614445270229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8910455239067076296846819 13365682858600614445270229)
              ·
                refine ⟨313258191998451901061021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13365682858600614445270229 313258191998451901061021)
                ·
                  refine ⟨117471821999419462897883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313258191998451901061021 117471821999419462897883)
                  ·
                    rfl

theorem cell21_514745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 3].length) (baseStart_514745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514745 prefixEnd_514745 := by exact prefixLift 514745
  have htrace : WordTrace (prefixWord ++ tailWord_514745) baseStart_514745 baseEnd_514745 := by
    simpa [prefixWord, tailWord_514745, baseEnd_514745] using wordTrace_append hprefix tailTrace_514745
  have hstable : (prefixWord ++ tailWord_514745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514745).length < 2 ^ (prefixWord ++ tailWord_514745).sum := by decide
  have hdescent : baseEnd_514745 < baseStart_514745 := by decide
  rcases family_descends (prefixWord ++ tailWord_514745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514762 : List Nat := [3, 1, 2, 1, 4, 2, 1, 4, 3]
def baseStart_514762 : Nat := 118140960795 + 514762 * 2 ^ 59
def prefixEnd_514762 : Nat := 4983230072969 + 3 ^ 40 * 514762 * 2
def baseEnd_514762 : Nat := 117475701631031211114515

theorem tailTrace_514762 : CollatzResearch.WordTrace tailWord_514762 prefixEnd_514762 117475701631031211114515 := by
  unfold tailWord_514762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4693728140278165798872635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12516608374075108796993693 4693728140278165798872635)
  ·
    refine ⟨7040592210417248698308953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4693728140278165798872635 7040592210417248698308953)
    ·
      refine ⟨5280444157812936523731715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7040592210417248698308953 5280444157812936523731715)
      ·
        refine ⟨7920666236719404785597573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5280444157812936523731715 7920666236719404785597573)
        ·
          refine ⟨1485124919384888397299545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7920666236719404785597573 1485124919384888397299545)
          ·
            refine ⟨1113843689538666297974659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1485124919384888397299545 1113843689538666297974659)
            ·
              refine ⟨1670765534307999446961989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1113843689538666297974659 1670765534307999446961989)
              ·
                refine ⟨313268537682749896305373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1670765534307999446961989 313268537682749896305373)
                ·
                  refine ⟨117475701631031211114515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313268537682749896305373 117475701631031211114515)
                  ·
                    rfl

theorem cell21_514762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_514762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514762 prefixEnd_514762 := by exact prefixLift 514762
  have htrace : WordTrace (prefixWord ++ tailWord_514762) baseStart_514762 baseEnd_514762 := by
    simpa [prefixWord, tailWord_514762, baseEnd_514762] using wordTrace_append hprefix tailTrace_514762
  have hstable : (prefixWord ++ tailWord_514762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514762).length < 2 ^ (prefixWord ++ tailWord_514762).sum := by decide
  have hdescent : baseEnd_514762 < baseStart_514762 := by decide
  rcases family_descends (prefixWord ++ tailWord_514762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514765 : List Nat := [1, 6, 2, 1, 3, 1, 1, 6]
def baseStart_514765 : Nat := 118140960795 + 514765 * 2 ^ 59
def prefixEnd_514765 : Nat := 4983230072969 + 3 ^ 40 * 514765 * 2
def baseEnd_514765 : Nat := 39158795423967957521503

theorem tailTrace_514765 : CollatzResearch.WordTrace tailWord_514765 prefixEnd_514765 39158795423967957521503 := by
  unfold tailWord_514765
  simp only [CollatzResearch.WordTrace]
  refine ⟨18775021980101794707849749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12516681320067863138566499 18775021980101794707849749)
  ·
    refine ⟨880079155317271626930457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18775021980101794707849749 880079155317271626930457)
    ·
      refine ⟨660059366487953720197843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 880079155317271626930457 660059366487953720197843)
      ·
        refine ⟨990089049731930580296765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660059366487953720197843 990089049731930580296765)
        ·
          refine ⟨371283393649473967611287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 990089049731930580296765 371283393649473967611287)
          ·
            refine ⟨556925090474210951416931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371283393649473967611287 556925090474210951416931)
            ·
              refine ⟨835387635711316427125397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556925090474210951416931 835387635711316427125397)
              ·
                refine ⟨39158795423967957521503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 835387635711316427125397 39158795423967957521503)
                ·
                  rfl

theorem cell21_514765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 6].length) (baseStart_514765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514765 prefixEnd_514765 := by exact prefixLift 514765
  have htrace : WordTrace (prefixWord ++ tailWord_514765) baseStart_514765 baseEnd_514765 := by
    simpa [prefixWord, tailWord_514765, baseEnd_514765] using wordTrace_append hprefix tailTrace_514765
  have hstable : (prefixWord ++ tailWord_514765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514765).length < 2 ^ (prefixWord ++ tailWord_514765).sum := by decide
  have hdescent : baseEnd_514765 < baseStart_514765 := by decide
  rcases family_descends (prefixWord ++ tailWord_514765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514849 : List Nat := [1, 2, 3, 2, 1, 2, 3, 7]
def baseStart_514849 : Nat := 118140960795 + 514849 * 2 ^ 59
def prefixEnd_514849 : Nat := 4983230072969 + 3 ^ 40 * 514849 * 2
def baseEnd_514849 : Nat := 39165185405446131054779

theorem tailTrace_514849 : CollatzResearch.WordTrace tailWord_514849 prefixEnd_514849 39165185405446131054779 := by
  unfold tailWord_514849
  simp only [CollatzResearch.WordTrace]
  refine ⟨18778085711797477053907601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12518723807864984702605067 18778085711797477053907601)
  ·
    refine ⟨14083564283848107790430701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18778085711797477053907601 14083564283848107790430701)
    ·
      refine ⟨5281336606443040421411513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14083564283848107790430701 5281336606443040421411513)
      ·
        refine ⟨3961002454832280316058635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5281336606443040421411513 3961002454832280316058635)
        ·
          refine ⟨5941503682248420474087953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3961002454832280316058635 5941503682248420474087953)
          ·
            refine ⟨4456127761686315355565965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5941503682248420474087953 4456127761686315355565965)
            ·
              refine ⟨1671047910632368258337237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4456127761686315355565965 1671047910632368258337237)
              ·
                refine ⟨39165185405446131054779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1671047910632368258337237 39165185405446131054779)
                ·
                  rfl

theorem cell21_514849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 7].length) (baseStart_514849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514849 prefixEnd_514849 := by exact prefixLift 514849
  have htrace : WordTrace (prefixWord ++ tailWord_514849) baseStart_514849 baseEnd_514849 := by
    simpa [prefixWord, tailWord_514849, baseEnd_514849] using wordTrace_append hprefix tailTrace_514849
  have hstable : (prefixWord ++ tailWord_514849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514849).length < 2 ^ (prefixWord ++ tailWord_514849).sum := by decide
  have hdescent : baseEnd_514849 < baseStart_514849 := by decide
  rcases family_descends (prefixWord ++ tailWord_514849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514886 : List Nat := [6, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_514886 : Nat := 118140960795 + 514886 * 2 ^ 59
def prefixEnd_514886 : Nat := 4983230072969 + 3 ^ 40 * 514886 * 2
def baseEnd_514886 : Nat := 117504000120434551047595

theorem tailTrace_514886 : CollatzResearch.WordTrace tailWord_514886 prefixEnd_514886 117504000120434551047595 := by
  unfold tailWord_514886
  simp only [CollatzResearch.WordTrace]
  refine ⟨586857350395732261656391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12519623475108954915336341 586857350395732261656391)
  ·
    refine ⟨880286025593598392484587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 586857350395732261656391 880286025593598392484587)
    ·
      refine ⟨1320429038390397588726881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 880286025593598392484587 1320429038390397588726881)
      ·
        refine ⟨990321778792798191545161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1320429038390397588726881 990321778792798191545161)
        ·
          refine ⟨742741334094598643658871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 990321778792798191545161 742741334094598643658871)
          ·
            refine ⟨1114112001141897965488307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742741334094598643658871 1114112001141897965488307)
            ·
              refine ⟨1671168001712846948232461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114112001141897965488307 1671168001712846948232461)
              ·
                refine ⟨626688000642317605587173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1671168001712846948232461 626688000642317605587173)
                ·
                  refine ⟨117504000120434551047595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 626688000642317605587173 117504000120434551047595)
                  ·
                    rfl

theorem cell21_514886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_514886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_514886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_514886 prefixEnd_514886 := by exact prefixLift 514886
  have htrace : WordTrace (prefixWord ++ tailWord_514886) baseStart_514886 baseEnd_514886 := by
    simpa [prefixWord, tailWord_514886, baseEnd_514886] using wordTrace_append hprefix tailTrace_514886
  have hstable : (prefixWord ++ tailWord_514886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514886).length < 2 ^ (prefixWord ++ tailWord_514886).sum := by decide
  have hdescent : baseEnd_514886 < baseStart_514886 := by decide
  rcases family_descends (prefixWord ++ tailWord_514886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515100 : List Nat := [2, 2, 3, 1, 5, 1, 2, 2, 3]
def baseStart_515100 : Nat := 118140960795 + 515100 * 2 ^ 59
def prefixEnd_515100 : Nat := 4983230072969 + 3 ^ 40 * 515100 * 2
def baseEnd_515100 : Nat := 117552837836017734480491

theorem tailTrace_515100 : CollatzResearch.WordTrace tailWord_515100 prefixEnd_515100 117552837836017734480491 := by
  unfold tailWord_515100
  simp only [CollatzResearch.WordTrace]
  refine ⟨9393620216944073460647377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12524826955925431280863169 9393620216944073460647377)
  ·
    refine ⟨7045215162708055095485533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9393620216944073460647377 7045215162708055095485533)
    ·
      refine ⟨2641955686015520660807075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7045215162708055095485533 2641955686015520660807075)
      ·
        refine ⟨3962933529023280991210613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2641955686015520660807075 3962933529023280991210613)
        ·
          refine ⟨371525018345932592925995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3962933529023280991210613 371525018345932592925995)
          ·
            refine ⟨557287527518898889388993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371525018345932592925995 557287527518898889388993)
            ·
              refine ⟨417965645639174167041745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557287527518898889388993 417965645639174167041745)
              ·
                refine ⟨313474234229380625281309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417965645639174167041745 313474234229380625281309)
                ·
                  refine ⟨117552837836017734480491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313474234229380625281309 117552837836017734480491)
                  ·
                    rfl

theorem cell21_515100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_515100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515100 prefixEnd_515100 := by exact prefixLift 515100
  have htrace : WordTrace (prefixWord ++ tailWord_515100) baseStart_515100 baseEnd_515100 := by
    simpa [prefixWord, tailWord_515100, baseEnd_515100] using wordTrace_append hprefix tailTrace_515100
  have hstable : (prefixWord ++ tailWord_515100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515100).length < 2 ^ (prefixWord ++ tailWord_515100).sum := by decide
  have hdescent : baseEnd_515100 < baseStart_515100 := by decide
  rcases family_descends (prefixWord ++ tailWord_515100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515111 : List Nat := [1, 1, 7, 1, 1, 3, 1, 6]
def baseStart_515111 : Nat := 118140960795 + 515111 * 2 ^ 59
def prefixEnd_515111 : Nat := 4983230072969 + 3 ^ 40 * 515111 * 2
def baseEnd_515111 : Nat := 39185116061961386599045

theorem tailTrace_515111 : CollatzResearch.WordTrace tailWord_515111 prefixEnd_515111 39185116061961386599045 := by
  unfold tailWord_515111
  simp only [CollatzResearch.WordTrace]
  refine ⟨18787641636848295799945187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12525094424565530533296791 18787641636848295799945187)
  ·
    refine ⟨28181462455272443699917781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18787641636848295799945187 28181462455272443699917781)
    ·
      refine ⟨660503026295447899216823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 28181462455272443699917781 660503026295447899216823)
      ·
        refine ⟨990754539443171848825235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660503026295447899216823 990754539443171848825235)
        ·
          refine ⟨1486131809164757773237853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990754539443171848825235 1486131809164757773237853)
          ·
            refine ⟨557299428436784164964195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1486131809164757773237853 557299428436784164964195)
            ·
              refine ⟨835949142655176247446293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557299428436784164964195 835949142655176247446293)
              ·
                refine ⟨39185116061961386599045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 835949142655176247446293 39185116061961386599045)
                ·
                  rfl

theorem cell21_515111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 6].length) (baseStart_515111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515111 prefixEnd_515111 := by exact prefixLift 515111
  have htrace : WordTrace (prefixWord ++ tailWord_515111) baseStart_515111 baseEnd_515111 := by
    simpa [prefixWord, tailWord_515111, baseEnd_515111] using wordTrace_append hprefix tailTrace_515111
  have hstable : (prefixWord ++ tailWord_515111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515111).length < 2 ^ (prefixWord ++ tailWord_515111).sum := by decide
  have hdescent : baseEnd_515111 < baseStart_515111 := by decide
  rcases family_descends (prefixWord ++ tailWord_515111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515229 : List Nat := [1, 4, 2, 1, 1, 2, 4, 6]
def baseStart_515229 : Nat := 118140960795 + 515229 * 2 ^ 59
def prefixEnd_515229 : Nat := 4983230072969 + 3 ^ 40 * 515229 * 2
def baseEnd_515229 : Nat := 39194092464514058943409

theorem tailTrace_515229 : CollatzResearch.WordTrace tailWord_515229 prefixEnd_515229 39194092464514058943409 := by
  unfold tailWord_515229
  simp only [CollatzResearch.WordTrace]
  refine ⟨18791945450420801952740741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12527963633613867968493827 18791945450420801952740741)
  ·
    refine ⟨3523489771953900366138889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18791945450420801952740741 3523489771953900366138889)
    ·
      refine ⟨2642617328965425274604167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3523489771953900366138889 2642617328965425274604167)
      ·
        refine ⟨3963925993448137911906251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2642617328965425274604167 3963925993448137911906251)
        ·
          refine ⟨5945888990172206867859377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3963925993448137911906251 5945888990172206867859377)
          ·
            refine ⟨4459416742629155150894533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5945888990172206867859377 4459416742629155150894533)
            ·
              refine ⟨836140639242966590792725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4459416742629155150894533 836140639242966590792725)
              ·
                refine ⟨39194092464514058943409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 836140639242966590792725 39194092464514058943409)
                ·
                  rfl

theorem cell21_515229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 6].length) (baseStart_515229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515229 prefixEnd_515229 := by exact prefixLift 515229
  have htrace : WordTrace (prefixWord ++ tailWord_515229) baseStart_515229 baseEnd_515229 := by
    simpa [prefixWord, tailWord_515229, baseEnd_515229] using wordTrace_append hprefix tailTrace_515229
  have hstable : (prefixWord ++ tailWord_515229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515229).length < 2 ^ (prefixWord ++ tailWord_515229).sum := by decide
  have hdescent : baseEnd_515229 < baseStart_515229 := by decide
  rcases family_descends (prefixWord ++ tailWord_515229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515266 : List Nat := [3, 5, 1, 1, 2, 1, 2, 2, 4]
def baseStart_515266 : Nat := 118140960795 + 515266 * 2 ^ 59
def prefixEnd_515266 : Nat := 4983230072969 + 3 ^ 40 * 515266 * 2
def baseEnd_515266 : Nat := 117590721297638334713485

theorem tailTrace_515266 : CollatzResearch.WordTrace tailWord_515266 prefixEnd_515266 117590721297638334713485 := by
  unfold tailWord_515266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4698323737821689317959413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12528863300857838181225101 4698323737821689317959413)
  ·
    refine ⟨440467850420783373558695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4698323737821689317959413 440467850420783373558695)
    ·
      refine ⟨660701775631175060338043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440467850420783373558695 660701775631175060338043)
      ·
        refine ⟨991052663446762590507065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660701775631175060338043 991052663446762590507065)
        ·
          refine ⟨743289497585071942880299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 991052663446762590507065 743289497585071942880299)
          ·
            refine ⟨1114934246377607914320449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743289497585071942880299 1114934246377607914320449)
            ·
              refine ⟨836200684783205935740337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1114934246377607914320449 836200684783205935740337)
              ·
                refine ⟨627150513587404451805253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 836200684783205935740337 627150513587404451805253)
                ·
                  refine ⟨117590721297638334713485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 627150513587404451805253 117590721297638334713485)
                  ·
                    rfl

theorem cell21_515266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_515266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515266 prefixEnd_515266 := by exact prefixLift 515266
  have htrace : WordTrace (prefixWord ++ tailWord_515266) baseStart_515266 baseEnd_515266 := by
    simpa [prefixWord, tailWord_515266, baseEnd_515266] using wordTrace_append hprefix tailTrace_515266
  have hstable : (prefixWord ++ tailWord_515266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515266).length < 2 ^ (prefixWord ++ tailWord_515266).sum := by decide
  have hdescent : baseEnd_515266 < baseStart_515266 := by decide
  rcases family_descends (prefixWord ++ tailWord_515266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515370 : List Nat := [3, 1, 4, 2, 1, 1, 3, 3, 3]
def baseStart_515370 : Nat := 118140960795 + 515370 * 2 ^ 59
def prefixEnd_515370 : Nat := 4983230072969 + 3 ^ 40 * 515370 * 2
def baseEnd_515370 : Nat := 117614455514557264979939

theorem tailTrace_515370 : CollatzResearch.WordTrace tailWord_515370 prefixEnd_515370 117614455514557264979939 := by
  unfold tailWord_515370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4699272035727495758405891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12531392095273322022415709 4699272035727495758405891)
  ·
    refine ⟨7048908053591243637608837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4699272035727495758405891 7048908053591243637608837)
    ·
      refine ⟨1321670260048358182051657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7048908053591243637608837 1321670260048358182051657)
      ·
        refine ⟨991252695036268636538743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1321670260048358182051657 991252695036268636538743)
        ·
          refine ⟨1486879042554402954808115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991252695036268636538743 1486879042554402954808115)
          ·
            refine ⟨2230318563831604432212173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1486879042554402954808115 2230318563831604432212173)
            ·
              refine ⟨836369461436851662079565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2230318563831604432212173 836369461436851662079565)
              ·
                refine ⟨313638548038819373279837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 836369461436851662079565 313638548038819373279837)
                ·
                  refine ⟨117614455514557264979939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313638548038819373279837 117614455514557264979939)
                  ·
                    rfl

theorem cell21_515370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_515370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515370 prefixEnd_515370 := by exact prefixLift 515370
  have htrace : WordTrace (prefixWord ++ tailWord_515370) baseStart_515370 baseEnd_515370 := by
    simpa [prefixWord, tailWord_515370, baseEnd_515370] using wordTrace_append hprefix tailTrace_515370
  have hstable : (prefixWord ++ tailWord_515370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515370).length < 2 ^ (prefixWord ++ tailWord_515370).sum := by decide
  have hdescent : baseEnd_515370 < baseStart_515370 := by decide
  rcases family_descends (prefixWord ++ tailWord_515370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515381 : List Nat := [1, 3, 3, 1, 2, 4, 7]
def baseStart_515381 : Nat := 118140960795 + 515381 * 2 ^ 59
def prefixEnd_515381 : Nat := 4983230072969 + 3 ^ 40 * 515381 * 2
def baseEnd_515381 : Nat := 13068551762713743366287

theorem tailTrace_515381 : CollatzResearch.WordTrace tailWord_515381 prefixEnd_515381 13068551762713743366287 := by
  unfold tailWord_515381
  simp only [CollatzResearch.WordTrace]
  refine ⟨18797489345870131912273997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12531659563913421274849331 18797489345870131912273997)
  ·
    refine ⟨7049058504701299467102749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18797489345870131912273997 7049058504701299467102749)
    ·
      refine ⟨2643396939262987300163531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7049058504701299467102749 2643396939262987300163531)
      ·
        refine ⟨3965095408894480950245297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2643396939262987300163531 3965095408894480950245297)
        ·
          refine ⟨2973821556670860712683973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3965095408894480950245297 2973821556670860712683973)
          ·
            refine ⟨557591541875786383628245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2973821556670860712683973 557591541875786383628245)
            ·
              refine ⟨13068551762713743366287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 557591541875786383628245 13068551762713743366287)
              ·
                rfl

theorem cell21_515381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 7].length) (baseStart_515381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515381 prefixEnd_515381 := by exact prefixLift 515381
  have htrace : WordTrace (prefixWord ++ tailWord_515381) baseStart_515381 baseEnd_515381 := by
    simpa [prefixWord, tailWord_515381, baseEnd_515381] using wordTrace_append hprefix tailTrace_515381
  have hstable : (prefixWord ++ tailWord_515381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515381).length < 2 ^ (prefixWord ++ tailWord_515381).sum := by decide
  have hdescent : baseEnd_515381 < baseStart_515381 := by decide
  rcases family_descends (prefixWord ++ tailWord_515381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515578 : List Nat := [3, 1, 1, 1, 1, 2, 5, 3, 4]
def baseStart_515578 : Nat := 118140960795 + 515578 * 2 ^ 59
def prefixEnd_515578 : Nat := 4983230072969 + 3 ^ 40 * 515578 * 2
def baseEnd_515578 : Nat := 117661923948395125512847

theorem tailTrace_515578 : CollatzResearch.WordTrace tailWord_515578 prefixEnd_515578 117661923948395125512847 := by
  unfold tailWord_515578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4701168631539108639298847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12536449684104289704796925 4701168631539108639298847)
  ·
    refine ⟨7051752947308662958948271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4701168631539108639298847 7051752947308662958948271)
    ·
      refine ⟨10577629420962994438422407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7051752947308662958948271 10577629420962994438422407)
      ·
        refine ⟨15866444131444491657633611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10577629420962994438422407 15866444131444491657633611)
        ·
          refine ⟨23799666197166737486450417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15866444131444491657633611 23799666197166737486450417)
          ·
            refine ⟨17849749647875053114837813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23799666197166737486450417 17849749647875053114837813)
            ·
              refine ⟨1673414029488286229516045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17849749647875053114837813 1673414029488286229516045)
              ·
                refine ⟨627530261058107336068517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1673414029488286229516045 627530261058107336068517)
                ·
                  refine ⟨117661923948395125512847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 627530261058107336068517 117661923948395125512847)
                  ·
                    rfl

theorem cell21_515578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_515578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515578 prefixEnd_515578 := by exact prefixLift 515578
  have htrace : WordTrace (prefixWord ++ tailWord_515578) baseStart_515578 baseEnd_515578 := by
    simpa [prefixWord, tailWord_515578, baseEnd_515578] using wordTrace_append hprefix tailTrace_515578
  have hstable : (prefixWord ++ tailWord_515578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515578).length < 2 ^ (prefixWord ++ tailWord_515578).sum := by decide
  have hdescent : baseEnd_515578 < baseStart_515578 := by decide
  rcases family_descends (prefixWord ++ tailWord_515578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515592 : List Nat := [2, 1, 3, 2, 1, 1, 4, 7]
def baseStart_515592 : Nat := 118140960795 + 515592 * 2 ^ 59
def prefixEnd_515592 : Nat := 4983230072969 + 3 ^ 40 * 515592 * 2
def baseEnd_515592 : Nat := 39221706313044737426495

theorem tailTrace_515592 : CollatzResearch.WordTrace tailWord_515592 prefixEnd_515592 39221706313044737426495 := by
  unfold tailWord_515592
  simp only [CollatzResearch.WordTrace]
  refine ⟨9402592574052857474102515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12536790098737143298803353 9402592574052857474102515)
  ·
    refine ⟨14103888861079286211153773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9402592574052857474102515 14103888861079286211153773)
    ·
      refine ⟨5288958322904732329182665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14103888861079286211153773 5288958322904732329182665)
      ·
        refine ⟨3966718742178549246886999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5288958322904732329182665 3966718742178549246886999)
        ·
          refine ⟨5950078113267823870330499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3966718742178549246886999 5950078113267823870330499)
          ·
            refine ⟨8925117169901735805495749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5950078113267823870330499 8925117169901735805495749)
            ·
              refine ⟨1673459469356575463530453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8925117169901735805495749 1673459469356575463530453)
              ·
                refine ⟨39221706313044737426495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1673459469356575463530453 39221706313044737426495)
                ·
                  rfl

theorem cell21_515592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 7].length) (baseStart_515592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515592 prefixEnd_515592 := by exact prefixLift 515592
  have htrace : WordTrace (prefixWord ++ tailWord_515592) baseStart_515592 baseEnd_515592 := by
    simpa [prefixWord, tailWord_515592, baseEnd_515592] using wordTrace_append hprefix tailTrace_515592
  have hstable : (prefixWord ++ tailWord_515592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515592).length < 2 ^ (prefixWord ++ tailWord_515592).sum := by decide
  have hdescent : baseEnd_515592 < baseStart_515592 := by decide
  rcases family_descends (prefixWord ++ tailWord_515592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515668 : List Nat := [2, 4, 1, 1, 1, 2, 10]
def baseStart_515668 : Nat := 118140960795 + 515668 * 2 ^ 59
def prefixEnd_515668 : Nat := 4983230072969 + 3 ^ 40 * 515668 * 2
def baseEnd_515668 : Nat := 13075829241619441001407

theorem tailTrace_515668 : CollatzResearch.WordTrace tailWord_515668 prefixEnd_515668 13075829241619441001407 := by
  unfold tailWord_515668
  simp only [CollatzResearch.WordTrace]
  refine ⟨9403978547915189963985829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12538638063886919951981105 9403978547915189963985829)
  ·
    refine ⟨1763245977734098118247343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9403978547915189963985829 1763245977734098118247343)
    ·
      refine ⟨2644868966601147177371015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1763245977734098118247343 2644868966601147177371015)
      ·
        refine ⟨3967303449901720766056523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2644868966601147177371015 3967303449901720766056523)
        ·
          refine ⟨5950955174852581149084785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3967303449901720766056523 5950955174852581149084785)
          ·
            refine ⟨4463216381139435861813589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5950955174852581149084785 4463216381139435861813589)
            ·
              refine ⟨13075829241619441001407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4463216381139435861813589 13075829241619441001407)
              ·
                rfl

theorem cell21_515668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 10].length) (baseStart_515668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515668 prefixEnd_515668 := by exact prefixLift 515668
  have htrace : WordTrace (prefixWord ++ tailWord_515668) baseStart_515668 baseEnd_515668 := by
    simpa [prefixWord, tailWord_515668, baseEnd_515668] using wordTrace_append hprefix tailTrace_515668
  have hstable : (prefixWord ++ tailWord_515668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515668).length < 2 ^ (prefixWord ++ tailWord_515668).sum := by decide
  have hdescent : baseEnd_515668 < baseStart_515668 := by decide
  rcases family_descends (prefixWord ++ tailWord_515668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515671 : List Nat := [1, 1, 3, 2, 2, 5, 1, 2, 4]
def baseStart_515671 : Nat := 118140960795 + 515671 * 2 ^ 59
def prefixEnd_515671 : Nat := 4983230072969 + 3 ^ 40 * 515671 * 2
def baseEnd_515671 : Nat := 117683147815447630462657

theorem tailTrace_515671 : CollatzResearch.WordTrace tailWord_515671 prefixEnd_515671 117683147815447630462657 := by
  unfold tailWord_515671
  simp only [CollatzResearch.WordTrace]
  refine ⟨18808066514819511440330867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12538711009879674293553911 18808066514819511440330867)
  ·
    refine ⟨28212099772229267160496301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18808066514819511440330867 28212099772229267160496301)
    ·
      refine ⟨10579537414585975185186113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28212099772229267160496301 10579537414585975185186113)
      ·
        refine ⟨7934653060939481388889585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10579537414585975185186113 7934653060939481388889585)
        ·
          refine ⟨5950989795704611041667189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7934653060939481388889585 5950989795704611041667189)
          ·
            refine ⟨557905293347307285156299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5950989795704611041667189 557905293347307285156299)
            ·
              refine ⟨836857940020960927734449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557905293347307285156299 836857940020960927734449)
              ·
                refine ⟨627643455015720695800837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 836857940020960927734449 627643455015720695800837)
                ·
                  refine ⟨117683147815447630462657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 627643455015720695800837 117683147815447630462657)
                  ·
                    rfl

theorem cell21_515671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 4].length) (baseStart_515671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515671 prefixEnd_515671 := by exact prefixLift 515671
  have htrace : WordTrace (prefixWord ++ tailWord_515671) baseStart_515671 baseEnd_515671 := by
    simpa [prefixWord, tailWord_515671, baseEnd_515671] using wordTrace_append hprefix tailTrace_515671
  have hstable : (prefixWord ++ tailWord_515671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515671).length < 2 ^ (prefixWord ++ tailWord_515671).sum := by decide
  have hdescent : baseEnd_515671 < baseStart_515671 := by decide
  rcases family_descends (prefixWord ++ tailWord_515671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515688 : List Nat := [2, 1, 4, 3, 1, 2, 3, 1, 4]
def baseStart_515688 : Nat := 118140960795 + 515688 * 2 ^ 59
def prefixEnd_515688 : Nat := 4983230072969 + 3 ^ 40 * 515688 * 2
def baseEnd_515688 : Nat := 117687027447059378679289

theorem tailTrace_515688 : CollatzResearch.WordTrace tailWord_515688 prefixEnd_515688 117687027447059378679289 := by
  unfold tailWord_515688
  simp only [CollatzResearch.WordTrace]
  refine ⟨9404343277878961671849859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12539124370505282229133145 9404343277878961671849859)
  ·
    refine ⟨14106514916818442507774789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9404343277878961671849859 14106514916818442507774789)
    ·
      refine ⟨2644971546903457970207773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14106514916818442507774789 2644971546903457970207773)
      ·
        refine ⟨991864330088796738827915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2644971546903457970207773 991864330088796738827915)
        ·
          refine ⟨1487796495133195108241873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991864330088796738827915 1487796495133195108241873)
          ·
            refine ⟨1115847371349896331181405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1487796495133195108241873 1115847371349896331181405)
            ·
              refine ⟨418442764256211124193027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1115847371349896331181405 418442764256211124193027)
              ·
                refine ⟨627664146384316686289541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418442764256211124193027 627664146384316686289541)
                ·
                  refine ⟨117687027447059378679289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 627664146384316686289541 117687027447059378679289)
                  ·
                    rfl

theorem cell21_515688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 4].length) (baseStart_515688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515688 prefixEnd_515688 := by exact prefixLift 515688
  have htrace : WordTrace (prefixWord ++ tailWord_515688) baseStart_515688 baseEnd_515688 := by
    simpa [prefixWord, tailWord_515688, baseEnd_515688] using wordTrace_append hprefix tailTrace_515688
  have hstable : (prefixWord ++ tailWord_515688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515688).length < 2 ^ (prefixWord ++ tailWord_515688).sum := by decide
  have hdescent : baseEnd_515688 < baseStart_515688 := by decide
  rcases family_descends (prefixWord ++ tailWord_515688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515702 : List Nat := [5, 1, 1, 2, 2, 1, 4, 5]
def baseStart_515702 : Nat := 118140960795 + 515702 * 2 ^ 59
def prefixEnd_515702 : Nat := 4983230072969 + 3 ^ 40 * 515702 * 2
def baseEnd_515702 : Nat := 39230074145932821815309

theorem tailTrace_515702 : CollatzResearch.WordTrace tailWord_515702 prefixEnd_515702 39230074145932821815309 := by
  unfold tailWord_515702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1175574823606700233419335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12539464785138135823139573 1175574823606700233419335)
  ·
    refine ⟨1763362235410050350129003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1175574823606700233419335 1763362235410050350129003)
    ·
      refine ⟨2645043353115075525193505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1763362235410050350129003 2645043353115075525193505)
      ·
        refine ⟨1983782514836306643895129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2645043353115075525193505 1983782514836306643895129)
        ·
          refine ⟨1487836886127229982921347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1983782514836306643895129 1487836886127229982921347)
          ·
            refine ⟨2231755329190844974382021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487836886127229982921347 2231755329190844974382021)
            ·
              refine ⟨418454124223283432696629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2231755329190844974382021 418454124223283432696629)
              ·
                refine ⟨39230074145932821815309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 418454124223283432696629 39230074145932821815309)
                ·
                  rfl

theorem cell21_515702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_515702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515702 prefixEnd_515702 := by exact prefixLift 515702
  have htrace : WordTrace (prefixWord ++ tailWord_515702) baseStart_515702 baseEnd_515702 := by
    simpa [prefixWord, tailWord_515702, baseEnd_515702] using wordTrace_append hprefix tailTrace_515702
  have hstable : (prefixWord ++ tailWord_515702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515702).length < 2 ^ (prefixWord ++ tailWord_515702).sum := by decide
  have hdescent : baseEnd_515702 < baseStart_515702 := by decide
  rcases family_descends (prefixWord ++ tailWord_515702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515744 : List Nat := [2, 1, 1, 4, 3, 1, 1, 8]
def baseStart_515744 : Nat := 118140960795 + 515744 * 2 ^ 59
def prefixEnd_515744 : Nat := 4983230072969 + 3 ^ 40 * 515744 * 2
def baseEnd_515744 : Nat := 39233269136671908581947

theorem tailTrace_515744 : CollatzResearch.WordTrace tailWord_515744 prefixEnd_515744 39233269136671908581947 := by
  unfold tailWord_515744
  simp only [CollatzResearch.WordTrace]
  refine ⟨9405364521777522453869143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12540486029036696605158857 9405364521777522453869143)
  ·
    refine ⟨14108046782666283680803715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9405364521777522453869143 14108046782666283680803715)
    ·
      refine ⟨21162070173999425521205573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14108046782666283680803715 21162070173999425521205573)
      ·
        refine ⟨3967888157624892285226045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21162070173999425521205573 3967888157624892285226045)
        ·
          refine ⟨1487958059109334606959767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3967888157624892285226045 1487958059109334606959767)
          ·
            refine ⟨2231937088664001910439651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487958059109334606959767 2231937088664001910439651)
            ·
              refine ⟨3347905632996002865659477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2231937088664001910439651 3347905632996002865659477)
              ·
                refine ⟨39233269136671908581947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3347905632996002865659477 39233269136671908581947)
                ·
                  rfl

theorem cell21_515744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 8].length) (baseStart_515744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515744 prefixEnd_515744 := by exact prefixLift 515744
  have htrace : WordTrace (prefixWord ++ tailWord_515744) baseStart_515744 baseEnd_515744 := by
    simpa [prefixWord, tailWord_515744, baseEnd_515744] using wordTrace_append hprefix tailTrace_515744
  have hstable : (prefixWord ++ tailWord_515744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515744).length < 2 ^ (prefixWord ++ tailWord_515744).sum := by decide
  have hdescent : baseEnd_515744 < baseStart_515744 := by decide
  rcases family_descends (prefixWord ++ tailWord_515744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515778 : List Nat := [3, 5, 1, 2, 10]
def baseStart_515778 : Nat := 118140960795 + 515778 * 2 ^ 59
def prefixEnd_515778 : Nat := 4983230072969 + 3 ^ 40 * 515778 * 2
def baseEnd_515778 : Nat := 1453179835472089162705

theorem tailTrace_515778 : CollatzResearch.WordTrace tailWord_515778 prefixEnd_515778 1453179835472089162705 := by
  unfold tailWord_515778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4702992281357967178618997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12541312750287912476317325 4702992281357967178618997)
  ·
    refine ⟨440905526377309422995531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4702992281357967178618997 440905526377309422995531)
    ·
      refine ⟨661358289565964134493297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440905526377309422995531 661358289565964134493297)
      ·
        refine ⟨496018717174473100869973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 661358289565964134493297 496018717174473100869973)
        ·
          refine ⟨1453179835472089162705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 496018717174473100869973 1453179835472089162705)
          ·
            rfl

theorem cell21_515778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 10].length) (baseStart_515778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515778 prefixEnd_515778 := by exact prefixLift 515778
  have htrace : WordTrace (prefixWord ++ tailWord_515778) baseStart_515778 baseEnd_515778 := by
    simpa [prefixWord, tailWord_515778, baseEnd_515778] using wordTrace_append hprefix tailTrace_515778
  have hstable : (prefixWord ++ tailWord_515778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515778).length < 2 ^ (prefixWord ++ tailWord_515778).sum := by decide
  have hdescent : baseEnd_515778 < baseStart_515778 := by decide
  rcases family_descends (prefixWord ++ tailWord_515778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515834 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 9]
def baseStart_515834 : Nat := 118140960795 + 515834 * 2 ^ 59
def prefixEnd_515834 : Nat := 4983230072969 + 3 ^ 40 * 515834 * 2
def baseEnd_515834 : Nat := 117720346636195569245657

theorem tailTrace_515834 : CollatzResearch.WordTrace tailWord_515834 prefixEnd_515834 117720346636195569245657 := by
  unfold tailWord_515834
  simp only [CollatzResearch.WordTrace]
  refine ⟨4703502903307247569628639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12542674408819326852343037 4703502903307247569628639)
  ·
    refine ⟨7055254354960871354442959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4703502903307247569628639 7055254354960871354442959)
    ·
      refine ⟨10582881532441307031664439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7055254354960871354442959 10582881532441307031664439)
      ·
        refine ⟨15874322298661960547496659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10582881532441307031664439 15874322298661960547496659)
        ·
          refine ⟨23811483447992940821244989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15874322298661960547496659 23811483447992940821244989)
          ·
            refine ⟨8929306292997352807966871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23811483447992940821244989 8929306292997352807966871)
            ·
              refine ⟨13393959439496029211950307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8929306292997352807966871 13393959439496029211950307)
              ·
                refine ⟨20090939159244043817925461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13393959439496029211950307 20090939159244043817925461)
                ·
                  refine ⟨117720346636195569245657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20090939159244043817925461 117720346636195569245657)
                  ·
                    rfl

theorem cell21_515834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_515834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515834 prefixEnd_515834 := by exact prefixLift 515834
  have htrace : WordTrace (prefixWord ++ tailWord_515834) baseStart_515834 baseEnd_515834 := by
    simpa [prefixWord, tailWord_515834, baseEnd_515834] using wordTrace_append hprefix tailTrace_515834
  have hstable : (prefixWord ++ tailWord_515834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515834).length < 2 ^ (prefixWord ++ tailWord_515834).sum := by decide
  have hdescent : baseEnd_515834 < baseStart_515834 := by decide
  rcases family_descends (prefixWord ++ tailWord_515834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515896 : List Nat := [2, 1, 2, 1, 3, 5, 7]
def baseStart_515896 : Nat := 118140960795 + 515896 * 2 ^ 59
def prefixEnd_515896 : Nat := 4983230072969 + 3 ^ 40 * 515896 * 2
def baseEnd_515896 : Nat := 13081610653433026579133

theorem tailTrace_515896 : CollatzResearch.WordTrace tailWord_515896 prefixEnd_515896 13081610653433026579133 := by
  unfold tailWord_515896
  simp only [CollatzResearch.WordTrace]
  refine ⟨9408136469502187433635771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12544181959336249911514361 9408136469502187433635771)
  ·
    refine ⟨14112204704253281150453657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9408136469502187433635771 14112204704253281150453657)
    ·
      refine ⟨10584153528189960862840243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14112204704253281150453657 10584153528189960862840243)
      ·
        refine ⟨15876230292284941294260365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10584153528189960862840243 15876230292284941294260365)
        ·
          refine ⟨5953586359606852985347637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15876230292284941294260365 5953586359606852985347637)
          ·
            refine ⟨558148721213142467376341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5953586359606852985347637 558148721213142467376341)
            ·
              refine ⟨13081610653433026579133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 558148721213142467376341 13081610653433026579133)
              ·
                rfl

theorem cell21_515896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 7].length) (baseStart_515896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515896 prefixEnd_515896 := by exact prefixLift 515896
  have htrace : WordTrace (prefixWord ++ tailWord_515896) baseStart_515896 baseEnd_515896 := by
    simpa [prefixWord, tailWord_515896, baseEnd_515896] using wordTrace_append hprefix tailTrace_515896
  have hstable : (prefixWord ++ tailWord_515896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515896).length < 2 ^ (prefixWord ++ tailWord_515896).sum := by decide
  have hdescent : baseEnd_515896 < baseStart_515896 := by decide
  rcases family_descends (prefixWord ++ tailWord_515896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515902 : List Nat := [4, 2, 1, 2, 2, 2, 3, 2, 3]
def baseStart_515902 : Nat := 118140960795 + 515902 * 2 ^ 59
def prefixEnd_515902 : Nat := 4983230072969 + 3 ^ 40 * 515902 * 2
def baseEnd_515902 : Nat := 117735865162642562112185

theorem tailTrace_515902 : CollatzResearch.WordTrace tailWord_515902 prefixEnd_515902 117735865162642562112185 := by
  unfold tailWord_515902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2352061472122829736498745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12544327851321758594659973 2352061472122829736498745)
  ·
    refine ⟨1764046104092122302374059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2352061472122829736498745 1764046104092122302374059)
    ·
      refine ⟨2646069156138183453561089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1764046104092122302374059 2646069156138183453561089)
      ·
        refine ⟨1984551867103637590170817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2646069156138183453561089 1984551867103637590170817)
        ·
          refine ⟨1488413900327728192628113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1984551867103637590170817 1488413900327728192628113)
          ·
            refine ⟨1116310425245796144471085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1488413900327728192628113 1116310425245796144471085)
            ·
              refine ⟨418616409467173554176657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1116310425245796144471085 418616409467173554176657)
              ·
                refine ⟨313962307100380165632493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418616409467173554176657 313962307100380165632493)
                ·
                  refine ⟨117735865162642562112185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313962307100380165632493 117735865162642562112185)
                  ·
                    rfl

theorem cell21_515902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_515902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515902 prefixEnd_515902 := by exact prefixLift 515902
  have htrace : WordTrace (prefixWord ++ tailWord_515902) baseStart_515902 baseEnd_515902 := by
    simpa [prefixWord, tailWord_515902, baseEnd_515902] using wordTrace_append hprefix tailTrace_515902
  have hstable : (prefixWord ++ tailWord_515902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515902).length < 2 ^ (prefixWord ++ tailWord_515902).sum := by decide
  have hdescent : baseEnd_515902 < baseStart_515902 := by decide
  rcases family_descends (prefixWord ++ tailWord_515902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515916 : List Nat := [2, 2, 1, 3, 4, 2, 2, 1, 4]
def baseStart_515916 : Nat := 118140960795 + 515916 * 2 ^ 59
def prefixEnd_515916 : Nat := 4983230072969 + 3 ^ 40 * 515916 * 2
def baseEnd_515916 : Nat := 117739060153381648878823

theorem tailTrace_515916 : CollatzResearch.WordTrace tailWord_515916 prefixEnd_515916 117739060153381648878823 := by
  unfold tailWord_515916
  simp only [CollatzResearch.WordTrace]
  refine ⟨9408501199465959141499801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12544668265954612188666401 9408501199465959141499801)
  ·
    refine ⟨7056375899599469356124851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9408501199465959141499801 7056375899599469356124851)
    ·
      refine ⟨10584563849399204034187277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7056375899599469356124851 10584563849399204034187277)
      ·
        refine ⟨3969211443524701512820229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10584563849399204034187277 3969211443524701512820229)
        ·
          refine ⟨744227145660881533653793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3969211443524701512820229 744227145660881533653793)
          ·
            refine ⟨558170359245661150240345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 744227145660881533653793 558170359245661150240345)
            ·
              refine ⟨418627769434245862680259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558170359245661150240345 418627769434245862680259)
              ·
                refine ⟨627941654151368794020389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418627769434245862680259 627941654151368794020389)
                ·
                  refine ⟨117739060153381648878823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 627941654151368794020389 117739060153381648878823)
                  ·
                    rfl

theorem cell21_515916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_515916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515916 prefixEnd_515916 := by exact prefixLift 515916
  have htrace : WordTrace (prefixWord ++ tailWord_515916) baseStart_515916 baseEnd_515916 := by
    simpa [prefixWord, tailWord_515916, baseEnd_515916] using wordTrace_append hprefix tailTrace_515916
  have hstable : (prefixWord ++ tailWord_515916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515916).length < 2 ^ (prefixWord ++ tailWord_515916).sum := by decide
  have hdescent : baseEnd_515916 < baseStart_515916 := by decide
  rcases family_descends (prefixWord ++ tailWord_515916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515944 : List Nat := [2, 1, 4, 2, 1, 1, 2, 5, 3]
def baseStart_515944 : Nat := 118140960795 + 515944 * 2 ^ 59
def prefixEnd_515944 : Nat := 4983230072969 + 3 ^ 40 * 515944 * 2
def baseEnd_515944 : Nat := 117745450134859822412099

theorem tailTrace_515944 : CollatzResearch.WordTrace tailWord_515944 prefixEnd_515944 117745450134859822412099 := by
  unfold tailWord_515944
  simp only [CollatzResearch.WordTrace]
  refine ⟨9409011821415239532509443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12545349095220319376679257 9409011821415239532509443)
  ·
    refine ⟨14113517732122859298764165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9409011821415239532509443 14113517732122859298764165)
    ·
      refine ⟨2646284574773036118518281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14113517732122859298764165 2646284574773036118518281)
      ·
        refine ⟨1984713431079777088888711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2646284574773036118518281 1984713431079777088888711)
        ·
          refine ⟨2977070146619665633333067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1984713431079777088888711 2977070146619665633333067)
          ·
            refine ⟨4465605219929498449999601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977070146619665633333067 4465605219929498449999601)
            ·
              refine ⟨3349203914947123837499701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4465605219929498449999601 3349203914947123837499701)
              ·
                refine ⟨313987867026292859765597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3349203914947123837499701 313987867026292859765597)
                ·
                  refine ⟨117745450134859822412099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313987867026292859765597 117745450134859822412099)
                  ·
                    rfl

theorem cell21_515944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 3].length) (baseStart_515944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515944 prefixEnd_515944 := by exact prefixLift 515944
  have htrace : WordTrace (prefixWord ++ tailWord_515944) baseStart_515944 baseEnd_515944 := by
    simpa [prefixWord, tailWord_515944, baseEnd_515944] using wordTrace_append hprefix tailTrace_515944
  have hstable : (prefixWord ++ tailWord_515944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515944).length < 2 ^ (prefixWord ++ tailWord_515944).sum := by decide
  have hdescent : baseEnd_515944 < baseStart_515944 := by decide
  rcases family_descends (prefixWord ++ tailWord_515944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515972 : List Nat := [2, 3, 2, 1, 1, 1, 5, 6]
def baseStart_515972 : Nat := 118140960795 + 515972 * 2 ^ 59
def prefixEnd_515972 : Nat := 4983230072969 + 3 ^ 40 * 515972 * 2
def baseEnd_515972 : Nat := 39250613372112665315125

theorem tailTrace_515972 : CollatzResearch.WordTrace tailWord_515972 prefixEnd_515972 39250613372112665315125 := by
  unfold tailWord_515972
  simp only [CollatzResearch.WordTrace]
  refine ⟨9409522443364519923519085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12546029924486026564692113 9409522443364519923519085)
  ·
    refine ⟨3528570916261694971319657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9409522443364519923519085 3528570916261694971319657)
    ·
      refine ⟨2646428187196271228489743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3528570916261694971319657 2646428187196271228489743)
      ·
        refine ⟨3969642280794406842734615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2646428187196271228489743 3969642280794406842734615)
        ·
          refine ⟨5954463421191610264101923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3969642280794406842734615 5954463421191610264101923)
          ·
            refine ⟨8931695131787415396152885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5954463421191610264101923 8931695131787415396152885)
            ·
              refine ⟨837346418605070193389333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8931695131787415396152885 837346418605070193389333)
              ·
                refine ⟨39250613372112665315125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 837346418605070193389333 39250613372112665315125)
                ·
                  rfl

theorem cell21_515972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 6].length) (baseStart_515972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_515972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_515972 prefixEnd_515972 := by exact prefixLift 515972
  have htrace : WordTrace (prefixWord ++ tailWord_515972) baseStart_515972 baseEnd_515972 := by
    simpa [prefixWord, tailWord_515972, baseEnd_515972] using wordTrace_append hprefix tailTrace_515972
  have hstable : (prefixWord ++ tailWord_515972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515972).length < 2 ^ (prefixWord ++ tailWord_515972).sum := by decide
  have hdescent : baseEnd_515972 < baseStart_515972 := by decide
  rcases family_descends (prefixWord ++ tailWord_515972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516031 : List Nat := [1, 1, 2, 2, 2, 1, 4, 8]
def baseStart_516031 : Nat := 118140960795 + 516031 * 2 ^ 59
def prefixEnd_516031 : Nat := 4983230072969 + 3 ^ 40 * 516031 * 2
def baseEnd_516031 : Nat := 39255101573389001487307

theorem tailTrace_516031 : CollatzResearch.WordTrace tailWord_516031 prefixEnd_516031 39255101573389001487307 := by
  unfold tailWord_516031
  simp only [CollatzResearch.WordTrace]
  refine ⟨18821196793515292923435947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12547464529010195282290631 18821196793515292923435947)
  ·
    refine ⟨28231795190272939385153921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18821196793515292923435947 28231795190272939385153921)
    ·
      refine ⟨21173846392704704538865441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28231795190272939385153921 21173846392704704538865441)
      ·
        refine ⟨15880384794528528404149081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21173846392704704538865441 15880384794528528404149081)
        ·
          refine ⟨11910288595896396303111811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15880384794528528404149081 11910288595896396303111811)
          ·
            refine ⟨17865432893844594454667717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11910288595896396303111811 17865432893844594454667717)
            ·
              refine ⟨3349768667595861460250197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17865432893844594454667717 3349768667595861460250197)
              ·
                refine ⟨39255101573389001487307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3349768667595861460250197 39255101573389001487307)
                ·
                  rfl

theorem cell21_516031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 8].length) (baseStart_516031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516031 prefixEnd_516031 := by exact prefixLift 516031
  have htrace : WordTrace (prefixWord ++ tailWord_516031) baseStart_516031 baseEnd_516031 := by
    simpa [prefixWord, tailWord_516031, baseEnd_516031] using wordTrace_append hprefix tailTrace_516031
  have hstable : (prefixWord ++ tailWord_516031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516031).length < 2 ^ (prefixWord ++ tailWord_516031).sum := by decide
  have hdescent : baseEnd_516031 < baseStart_516031 := by decide
  rcases family_descends (prefixWord ++ tailWord_516031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516048 : List Nat := [2, 1, 1, 1, 1, 2, 8, 5]
def baseStart_516048 : Nat := 118140960795 + 516048 * 2 ^ 59
def prefixEnd_516048 : Nat := 4983230072969 + 3 ^ 40 * 516048 * 2
def baseEnd_516048 : Nat := 39256394783926250892851

theorem tailTrace_516048 : CollatzResearch.WordTrace tailWord_516048 prefixEnd_516048 39256394783926250892851 := by
  unfold tailWord_516048
  simp only [CollatzResearch.WordTrace]
  refine ⟨9410908417226852413402399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12547877889635803217869865 9410908417226852413402399)
  ·
    refine ⟨14116362625840278620103599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9410908417226852413402399 14116362625840278620103599)
    ·
      refine ⟨21174543938760417930155399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14116362625840278620103599 21174543938760417930155399)
      ·
        refine ⟨31761815908140626895233099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21174543938760417930155399 31761815908140626895233099)
        ·
          refine ⟨47642723862210940342849649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31761815908140626895233099 47642723862210940342849649)
          ·
            refine ⟨35732042896658205257137237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47642723862210940342849649 35732042896658205257137237)
            ·
              refine ⟨418734877695213342857077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 35732042896658205257137237 418734877695213342857077)
              ·
                refine ⟨39256394783926250892851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 418734877695213342857077 39256394783926250892851)
                ·
                  rfl

theorem cell21_516048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 5].length) (baseStart_516048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516048 prefixEnd_516048 := by exact prefixLift 516048
  have htrace : WordTrace (prefixWord ++ tailWord_516048) baseStart_516048 baseEnd_516048 := by
    simpa [prefixWord, tailWord_516048, baseEnd_516048] using wordTrace_append hprefix tailTrace_516048
  have hstable : (prefixWord ++ tailWord_516048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516048).length < 2 ^ (prefixWord ++ tailWord_516048).sum := by decide
  have hdescent : baseEnd_516048 < baseStart_516048 := by decide
  rcases family_descends (prefixWord ++ tailWord_516048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516107 : List Nat := [1, 1, 1, 1, 6, 1, 1, 9]
def baseStart_516107 : Nat := 118140960795 + 516107 * 2 ^ 59
def prefixEnd_516107 : Nat := 4983230072969 + 3 ^ 40 * 516107 * 2
def baseEnd_516107 : Nat := 39260882985202587065033

theorem tailTrace_516107 : CollatzResearch.WordTrace tailWord_516107 prefixEnd_516107 39260882985202587065033 := by
  unfold tailWord_516107
  simp only [CollatzResearch.WordTrace]
  refine ⟨18823968741239957903202575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12549312494159971935468383 18823968741239957903202575)
  ·
    refine ⟨28235953111859936854803863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18823968741239957903202575 28235953111859936854803863)
    ·
      refine ⟨42353929667789905282205795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28235953111859936854803863 42353929667789905282205795)
      ·
        refine ⟨63530894501684857923308693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42353929667789905282205795 63530894501684857923308693)
        ·
          refine ⟨2978010679766477715155095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63530894501684857923308693 2978010679766477715155095)
          ·
            refine ⟨4467016019649716572732643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2978010679766477715155095 4467016019649716572732643)
            ·
              refine ⟨6700524029474574859098965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4467016019649716572732643 6700524029474574859098965)
              ·
                refine ⟨39260882985202587065033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6700524029474574859098965 39260882985202587065033)
                ·
                  rfl

theorem cell21_516107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 9].length) (baseStart_516107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516107 prefixEnd_516107 := by exact prefixLift 516107
  have htrace : WordTrace (prefixWord ++ tailWord_516107) baseStart_516107 baseEnd_516107 := by
    simpa [prefixWord, tailWord_516107, baseEnd_516107] using wordTrace_append hprefix tailTrace_516107
  have hstable : (prefixWord ++ tailWord_516107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516107).length < 2 ^ (prefixWord ++ tailWord_516107).sum := by decide
  have hdescent : baseEnd_516107 < baseStart_516107 := by decide
  rcases family_descends (prefixWord ++ tailWord_516107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516158 : List Nat := [4, 2, 1, 3, 2, 1, 3, 5]
def baseStart_516158 : Nat := 118140960795 + 516158 * 2 ^ 59
def prefixEnd_516158 : Nat := 4983230072969 + 3 ^ 40 * 516158 * 2
def baseEnd_516158 : Nat := 39264762616814335281665

theorem tailTrace_516158 : CollatzResearch.WordTrace tailWord_516158 prefixEnd_516158 39264762616814335281665 := by
  unfold tailWord_516158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2353228608006899201663641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12550552576036795742206085 2353228608006899201663641)
  ·
    refine ⟨1764921456005174401247731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2353228608006899201663641 1764921456005174401247731)
    ·
      refine ⟨2647382184007761601871597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1764921456005174401247731 2647382184007761601871597)
      ·
        refine ⟨992768319002910600701849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2647382184007761601871597 992768319002910600701849)
        ·
          refine ⟨744576239252182950526387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 992768319002910600701849 744576239252182950526387)
          ·
            refine ⟨1116864358878274425789581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744576239252182950526387 1116864358878274425789581)
            ·
              refine ⟨418824134579352909671093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1116864358878274425789581 418824134579352909671093)
              ·
                refine ⟨39264762616814335281665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 418824134579352909671093 39264762616814335281665)
                ·
                  rfl

theorem cell21_516158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_516158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516158 prefixEnd_516158 := by exact prefixLift 516158
  have htrace : WordTrace (prefixWord ++ tailWord_516158) baseStart_516158 baseEnd_516158 := by
    simpa [prefixWord, tailWord_516158, baseEnd_516158] using wordTrace_append hprefix tailTrace_516158
  have hstable : (prefixWord ++ tailWord_516158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516158).length < 2 ^ (prefixWord ++ tailWord_516158).sum := by decide
  have hdescent : baseEnd_516158 < baseStart_516158 := by decide
  rcases family_descends (prefixWord ++ tailWord_516158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516189 : List Nat := [1, 4, 4, 1, 1, 1, 2, 4, 3]
def baseStart_516189 : Nat := 118140960795 + 516189 * 2 ^ 59
def prefixEnd_516189 : Nat := 4983230072969 + 3 ^ 40 * 516189 * 2
def baseEnd_516189 : Nat := 117801362472793840828265

theorem tailTrace_516189 : CollatzResearch.WordTrace tailWord_516189 prefixEnd_516189 117801362472793840828265 := by
  unfold tailWord_516189
  simp only [CollatzResearch.WordTrace]
  refine ⟨18826959526942885907687621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12551306351295257271791747 18826959526942885907687621)
  ·
    refine ⟨3530054911301791107691429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18826959526942885907687621 3530054911301791107691429)
    ·
      refine ⟨661885295869085832692143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3530054911301791107691429 661885295869085832692143)
      ·
        refine ⟨992827943803628749038215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661885295869085832692143 992827943803628749038215)
        ·
          refine ⟨1489241915705443123557323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992827943803628749038215 1489241915705443123557323)
          ·
            refine ⟨2233862873558164685335985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489241915705443123557323 2233862873558164685335985)
            ·
              refine ⟨1675397155168623514001989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2233862873558164685335985 1675397155168623514001989)
              ·
                refine ⟨314136966594116908875373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1675397155168623514001989 314136966594116908875373)
                ·
                  refine ⟨117801362472793840828265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314136966594116908875373 117801362472793840828265)
                  ·
                    rfl

theorem cell21_516189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_516189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516189 prefixEnd_516189 := by exact prefixLift 516189
  have htrace : WordTrace (prefixWord ++ tailWord_516189) baseStart_516189 baseEnd_516189 := by
    simpa [prefixWord, tailWord_516189, baseEnd_516189] using wordTrace_append hprefix tailTrace_516189
  have hstable : (prefixWord ++ tailWord_516189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516189).length < 2 ^ (prefixWord ++ tailWord_516189).sum := by decide
  have hdescent : baseEnd_516189 < baseStart_516189 := by decide
  rcases family_descends (prefixWord ++ tailWord_516189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516217 : List Nat := [1, 2, 1, 3, 4, 3, 2, 5]
def baseStart_516217 : Nat := 118140960795 + 516217 * 2 ^ 59
def prefixEnd_516217 : Nat := 4983230072969 + 3 ^ 40 * 516217 * 2
def baseEnd_516217 : Nat := 39269250818090671453847

theorem tailTrace_516217 : CollatzResearch.WordTrace tailWord_516217 prefixEnd_516217 39269250818090671453847 := by
  unfold tailWord_516217
  simp only [CollatzResearch.WordTrace]
  refine ⟨18827980770841446689706905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12551987180560964459804603 18827980770841446689706905)
  ·
    refine ⟨14120985578131085017280179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18827980770841446689706905 14120985578131085017280179)
    ·
      refine ⟨21181478367196627525920269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14120985578131085017280179 21181478367196627525920269)
      ·
        refine ⟨7943054387698735322220101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21181478367196627525920269 7943054387698735322220101)
        ·
          refine ⟨1489322697693512872916269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7943054387698735322220101 1489322697693512872916269)
          ·
            refine ⟨558496011635067327343601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1489322697693512872916269 558496011635067327343601)
            ·
              refine ⟨418872008726300495507701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558496011635067327343601 418872008726300495507701)
              ·
                refine ⟨39269250818090671453847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 418872008726300495507701 39269250818090671453847)
                ·
                  rfl

theorem cell21_516217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 5].length) (baseStart_516217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516217 prefixEnd_516217 := by exact prefixLift 516217
  have htrace : WordTrace (prefixWord ++ tailWord_516217) baseStart_516217 baseEnd_516217 := by
    simpa [prefixWord, tailWord_516217, baseEnd_516217] using wordTrace_append hprefix tailTrace_516217
  have hstable : (prefixWord ++ tailWord_516217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516217).length < 2 ^ (prefixWord ++ tailWord_516217).sum := by decide
  have hdescent : baseEnd_516217 < baseStart_516217 := by decide
  rcases family_descends (prefixWord ++ tailWord_516217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516245 : List Nat := [1, 3, 2, 1, 1, 1, 4, 4, 4]
def baseStart_516245 : Nat := 118140960795 + 516245 * 2 ^ 59
def prefixEnd_516245 : Nat := 4983230072969 + 3 ^ 40 * 516245 * 2
def baseEnd_516245 : Nat := 117814142435750187894817

theorem tailTrace_516245 : CollatzResearch.WordTrace tailWord_516245 prefixEnd_516245 117814142435750187894817 := by
  unfold tailWord_516245
  simp only [CollatzResearch.WordTrace]
  refine ⟨18829002014740007471726189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12552668009826671647817459 18829002014740007471726189)
  ·
    refine ⟨7060875755527502801897321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18829002014740007471726189 7060875755527502801897321)
    ·
      refine ⟨5295656816645627101422991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7060875755527502801897321 5295656816645627101422991)
      ·
        refine ⟨7943485224968440652134487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5295656816645627101422991 7943485224968440652134487)
        ·
          refine ⟨11915227837452660978201731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7943485224968440652134487 11915227837452660978201731)
          ·
            refine ⟨17872841756178991467302597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11915227837452660978201731 17872841756178991467302597)
            ·
              refine ⟨3351157829283560900119237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17872841756178991467302597 3351157829283560900119237)
              ·
                refine ⟨628342092990667668772357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3351157829283560900119237 628342092990667668772357)
                ·
                  refine ⟨117814142435750187894817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 628342092990667668772357 117814142435750187894817)
                  ·
                    rfl

theorem cell21_516245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_516245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516245 prefixEnd_516245 := by exact prefixLift 516245
  have htrace : WordTrace (prefixWord ++ tailWord_516245) baseStart_516245 baseEnd_516245 := by
    simpa [prefixWord, tailWord_516245, baseEnd_516245] using wordTrace_append hprefix tailTrace_516245
  have hstable : (prefixWord ++ tailWord_516245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516245).length < 2 ^ (prefixWord ++ tailWord_516245).sum := by decide
  have hdescent : baseEnd_516245 < baseStart_516245 := by decide
  rcases family_descends (prefixWord ++ tailWord_516245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516248 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 5]
def baseStart_516248 : Nat := 118140960795 + 516248 * 2 ^ 59
def prefixEnd_516248 : Nat := 4983230072969 + 3 ^ 40 * 516248 * 2
def baseEnd_516248 : Nat := 117814827076622849344811

theorem tailTrace_516248 : CollatzResearch.WordTrace tailWord_516248 prefixEnd_516248 117814827076622849344811 := by
  unfold tailWord_516248
  simp only [CollatzResearch.WordTrace]
  refine ⟨9414555716864569492042699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12552740955819425989390265 9414555716864569492042699)
  ·
    refine ⟨14121833575296854238064049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9414555716864569492042699 14121833575296854238064049)
    ·
      refine ⟨10591375181472640678548037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14121833575296854238064049 10591375181472640678548037)
      ·
        refine ⟨1985882846526120127227757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10591375181472640678548037 1985882846526120127227757)
        ·
          refine ⟨744706067447295047710409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1985882846526120127227757 744706067447295047710409)
          ·
            refine ⟨558529550585471285782807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 744706067447295047710409 558529550585471285782807)
            ·
              refine ⟨837794325878206928674211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558529550585471285782807 837794325878206928674211)
              ·
                refine ⟨1256691488817310393011317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837794325878206928674211 1256691488817310393011317)
                ·
                  refine ⟨117814827076622849344811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1256691488817310393011317 117814827076622849344811)
                  ·
                    rfl

theorem cell21_516248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 5].length) (baseStart_516248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516248 prefixEnd_516248 := by exact prefixLift 516248
  have htrace : WordTrace (prefixWord ++ tailWord_516248) baseStart_516248 baseEnd_516248 := by
    simpa [prefixWord, tailWord_516248, baseEnd_516248] using wordTrace_append hprefix tailTrace_516248
  have hstable : (prefixWord ++ tailWord_516248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516248).length < 2 ^ (prefixWord ++ tailWord_516248).sum := by decide
  have hdescent : baseEnd_516248 < baseStart_516248 := by decide
  rcases family_descends (prefixWord ++ tailWord_516248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516310 : List Nat := [5, 2, 1, 2, 1, 3, 1, 6]
def baseStart_516310 : Nat := 118140960795 + 516310 * 2 ^ 59
def prefixEnd_516310 : Nat := 4983230072969 + 3 ^ 40 * 516310 * 2
def baseEnd_516310 : Nat := 39276325440441506437117

theorem tailTrace_516310 : CollatzResearch.WordTrace tailWord_516310 prefixEnd_516310 39276325440441506437117 := by
  unfold tailWord_516310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1176960797469032723302649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12554248506336349048561589 1176960797469032723302649)
  ·
    refine ⟨882720598101774542476987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1176960797469032723302649 882720598101774542476987)
    ·
      refine ⟨1324080897152661813715481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 882720598101774542476987 1324080897152661813715481)
      ·
        refine ⟨993060672864496360286611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1324080897152661813715481 993060672864496360286611)
        ·
          refine ⟨1489591009296744540429917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993060672864496360286611 1489591009296744540429917)
          ·
            refine ⟨558596628486279202661219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1489591009296744540429917 558596628486279202661219)
            ·
              refine ⟨837894942729418803991829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558596628486279202661219 837894942729418803991829)
              ·
                refine ⟨39276325440441506437117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 837894942729418803991829 39276325440441506437117)
                ·
                  rfl

theorem cell21_516310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_516310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516310 prefixEnd_516310 := by exact prefixLift 516310
  have htrace : WordTrace (prefixWord ++ tailWord_516310) baseStart_516310 baseEnd_516310 := by
    simpa [prefixWord, tailWord_516310, baseEnd_516310] using wordTrace_append hprefix tailTrace_516310
  have hstable : (prefixWord ++ tailWord_516310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516310).length < 2 ^ (prefixWord ++ tailWord_516310).sum := by decide
  have hdescent : baseEnd_516310 < baseStart_516310 := by decide
  rcases family_descends (prefixWord ++ tailWord_516310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516321 : List Nat := [1, 2, 3, 1, 3, 1, 1, 5, 4]
def baseStart_516321 : Nat := 118140960795 + 516321 * 2 ^ 59
def prefixEnd_516321 : Nat := 4983230072969 + 3 ^ 40 * 516321 * 2
def baseEnd_516321 : Nat := 117831486671190944627995

theorem tailTrace_516321 : CollatzResearch.WordTrace tailWord_516321 prefixEnd_516321 117831486671190944627995 := by
  unfold tailWord_516321
  simp only [CollatzResearch.WordTrace]
  refine ⟨18831773962464672451492817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12554515974976448300995211 18831773962464672451492817)
  ·
    refine ⟨14123830471848504338619613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18831773962464672451492817 14123830471848504338619613)
    ·
      refine ⟨5296436426943189126982355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14123830471848504338619613 5296436426943189126982355)
      ·
        refine ⟨7944654640414783690473533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5296436426943189126982355 7944654640414783690473533)
        ·
          refine ⟨2979245490155543883927575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7944654640414783690473533 2979245490155543883927575)
          ·
            refine ⟨4468868235233315825891363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979245490155543883927575 4468868235233315825891363)
            ·
              refine ⟨6703302352849973738837045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4468868235233315825891363 6703302352849973738837045)
              ·
                refine ⟨628434595579685038015973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6703302352849973738837045 628434595579685038015973)
                ·
                  refine ⟨117831486671190944627995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 628434595579685038015973 117831486671190944627995)
                  ·
                    rfl

theorem cell21_516321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_516321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516321 prefixEnd_516321 := by exact prefixLift 516321
  have htrace : WordTrace (prefixWord ++ tailWord_516321) baseStart_516321 baseEnd_516321 := by
    simpa [prefixWord, tailWord_516321, baseEnd_516321] using wordTrace_append hprefix tailTrace_516321
  have hstable : (prefixWord ++ tailWord_516321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516321).length < 2 ^ (prefixWord ++ tailWord_516321).sum := by decide
  have hdescent : baseEnd_516321 < baseStart_516321 := by decide
  rcases family_descends (prefixWord ++ tailWord_516321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516417 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 5]
def baseStart_516417 : Nat := 118140960795 + 516417 * 2 ^ 59
def prefixEnd_516417 : Nat := 4983230072969 + 3 ^ 40 * 516417 * 2
def baseEnd_516417 : Nat := 117853395179116111027799

theorem tailTrace_516417 : CollatzResearch.WordTrace tailWord_516417 prefixEnd_516417 117853395179116111027799 := by
  unfold tailWord_516417
  simp only [CollatzResearch.WordTrace]
  refine ⟨18835275370116880846987505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12556850246744587231325003 18835275370116880846987505)
  ·
    refine ⟨14126456527587660635240629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18835275370116880846987505 14126456527587660635240629)
    ·
      refine ⟨1324355299461343184553809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14126456527587660635240629 1324355299461343184553809)
      ·
        refine ⟨993266474596007388415357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1324355299461343184553809 993266474596007388415357)
        ·
          refine ⟨372474927973502770655759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 993266474596007388415357 372474927973502770655759)
          ·
            refine ⟨558712391960254155983639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372474927973502770655759 558712391960254155983639)
            ·
              refine ⟨838068587940381233975459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558712391960254155983639 838068587940381233975459)
              ·
                refine ⟨1257102881910571850963189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838068587940381233975459 1257102881910571850963189)
                ·
                  refine ⟨117853395179116111027799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1257102881910571850963189 117853395179116111027799)
                  ·
                    rfl

theorem cell21_516417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 5].length) (baseStart_516417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516417 prefixEnd_516417 := by exact prefixLift 516417
  have htrace : WordTrace (prefixWord ++ tailWord_516417) baseStart_516417 baseEnd_516417 := by
    simpa [prefixWord, tailWord_516417, baseEnd_516417] using wordTrace_append hprefix tailTrace_516417
  have hstable : (prefixWord ++ tailWord_516417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516417).length < 2 ^ (prefixWord ++ tailWord_516417).sum := by decide
  have hdescent : baseEnd_516417 < baseStart_516417 := by decide
  rcases family_descends (prefixWord ++ tailWord_516417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516535 : List Nat := [1, 1, 3, 1, 3, 3, 2, 4, 3]
def baseStart_516535 : Nat := 118140960795 + 516535 * 2 ^ 59
def prefixEnd_516535 : Nat := 4983230072969 + 3 ^ 40 * 516535 * 2
def baseEnd_516535 : Nat := 117880324386774128060891

theorem tailTrace_516535 : CollatzResearch.WordTrace tailWord_516535 prefixEnd_516535 117880324386774128060891 := by
  unfold tailWord_516535
  simp only [CollatzResearch.WordTrace]
  refine ⟨18839579183689386999783059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12559719455792924666522039 18839579183689386999783059)
  ·
    refine ⟨28259368775534080499674589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18839579183689386999783059 28259368775534080499674589)
    ·
      refine ⟨10597263290825280187377971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28259368775534080499674589 10597263290825280187377971)
      ·
        refine ⟨15895894936237920281066957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10597263290825280187377971 15895894936237920281066957)
        ·
          refine ⟨5960960601089220105400109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15895894936237920281066957 5960960601089220105400109)
          ·
            refine ⟨2235360225408457539525041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5960960601089220105400109 2235360225408457539525041)
            ·
              refine ⟨1676520169056343154643781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2235360225408457539525041 1676520169056343154643781)
              ·
                refine ⟨314347531698064341495709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1676520169056343154643781 314347531698064341495709)
                ·
                  refine ⟨117880324386774128060891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314347531698064341495709 117880324386774128060891)
                  ·
                    rfl

theorem cell21_516535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 3].length) (baseStart_516535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516535 prefixEnd_516535 := by exact prefixLift 516535
  have htrace : WordTrace (prefixWord ++ tailWord_516535) baseStart_516535 baseEnd_516535 := by
    simpa [prefixWord, tailWord_516535, baseEnd_516535] using wordTrace_append hprefix tailTrace_516535
  have hstable : (prefixWord ++ tailWord_516535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516535).length < 2 ^ (prefixWord ++ tailWord_516535).sum := by decide
  have hdescent : baseEnd_516535 < baseStart_516535 := by decide
  rcases family_descends (prefixWord ++ tailWord_516535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516597 : List Nat := [1, 3, 5, 1, 2, 1, 2, 6]
def baseStart_516597 : Nat := 118140960795 + 516597 * 2 ^ 59
def prefixEnd_516597 : Nat := 4983230072969 + 3 ^ 40 * 516597 * 2
def baseEnd_516597 : Nat := 39298157877158599342477

theorem tailTrace_516597 : CollatzResearch.WordTrace tailWord_516597 prefixEnd_516597 39298157877158599342477 := by
  unfold tailWord_516597
  simp only [CollatzResearch.WordTrace]
  refine ⟨18841840509464771588540045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12561227006309847725693363 18841840509464771588540045)
  ·
    refine ⟨7065690191049289345702517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18841840509464771588540045 7065690191049289345702517)
    ·
      refine ⟨662408455410870876159611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7065690191049289345702517 662408455410870876159611)
      ·
        refine ⟨993612683116306314239417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662408455410870876159611 993612683116306314239417)
        ·
          refine ⟨745209512337229735679563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 993612683116306314239417 745209512337229735679563)
          ·
            refine ⟨1117814268505844603519345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745209512337229735679563 1117814268505844603519345)
            ·
              refine ⟨838360701379383452639509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1117814268505844603519345 838360701379383452639509)
              ·
                refine ⟨39298157877158599342477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 838360701379383452639509 39298157877158599342477)
                ·
                  rfl

theorem cell21_516597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 6].length) (baseStart_516597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516597 prefixEnd_516597 := by exact prefixLift 516597
  have htrace : WordTrace (prefixWord ++ tailWord_516597) baseStart_516597 baseEnd_516597 := by
    simpa [prefixWord, tailWord_516597, baseEnd_516597] using wordTrace_append hprefix tailTrace_516597
  have hstable : (prefixWord ++ tailWord_516597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516597).length < 2 ^ (prefixWord ++ tailWord_516597).sum := by decide
  have hdescent : baseEnd_516597 < baseStart_516597 := by decide
  rcases family_descends (prefixWord ++ tailWord_516597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516614 : List Nat := [6, 2, 1, 1, 1, 1, 2, 7]
def baseStart_516614 : Nat := 118140960795 + 516614 * 2 ^ 59
def prefixEnd_516614 : Nat := 4983230072969 + 3 ^ 40 * 516614 * 2
def baseEnd_516614 : Nat := 39299451087695848748021

theorem tailTrace_516614 : CollatzResearch.WordTrace tailWord_516614 prefixEnd_516614 39299451087695848748021 := by
  unfold tailWord_516614
  simp only [CollatzResearch.WordTrace]
  refine ⟨588826892200099484122153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12561640366935455661272597 588826892200099484122153)
  ·
    refine ⟨441620169150074613091615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 588826892200099484122153 441620169150074613091615)
    ·
      refine ⟨662430253725111919637423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441620169150074613091615 662430253725111919637423)
      ·
        refine ⟨993645380587667879456135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662430253725111919637423 993645380587667879456135)
        ·
          refine ⟨1490468070881501819184203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993645380587667879456135 1490468070881501819184203)
          ·
            refine ⟨2235702106322252728776305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490468070881501819184203 2235702106322252728776305)
            ·
              refine ⟨1676776579741689546582229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2235702106322252728776305 1676776579741689546582229)
              ·
                refine ⟨39299451087695848748021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1676776579741689546582229 39299451087695848748021)
                ·
                  rfl

theorem cell21_516614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_516614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516614 prefixEnd_516614 := by exact prefixLift 516614
  have htrace : WordTrace (prefixWord ++ tailWord_516614) baseStart_516614 baseEnd_516614 := by
    simpa [prefixWord, tailWord_516614, baseEnd_516614] using wordTrace_append hprefix tailTrace_516614
  have hstable : (prefixWord ++ tailWord_516614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516614).length < 2 ^ (prefixWord ++ tailWord_516614).sum := by decide
  have hdescent : baseEnd_516614 < baseStart_516614 := by decide
  rcases family_descends (prefixWord ++ tailWord_516614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516684 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 6]
def baseStart_516684 : Nat := 118140960795 + 516684 * 2 ^ 59
def prefixEnd_516684 : Nat := 4983230072969 + 3 ^ 40 * 516684 * 2
def baseEnd_516684 : Nat := 117914328216782980077253

theorem tailTrace_516684 : CollatzResearch.WordTrace tailWord_516684 prefixEnd_516684 117914328216782980077253 := by
  unfold tailWord_516684
  simp only [CollatzResearch.WordTrace]
  refine ⟨9422506830074792723478553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12563342440099723631304737 9422506830074792723478553)
  ·
    refine ⟨7066880122556094542608915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9422506830074792723478553 7066880122556094542608915)
    ·
      refine ⟨10600320183834141813913373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7066880122556094542608915 10600320183834141813913373)
      ·
        refine ⟨3975120068937803180217515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10600320183834141813913373 3975120068937803180217515)
        ·
          refine ⟨5962680103406704770326273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3975120068937803180217515 5962680103406704770326273)
          ·
            refine ⟨4472010077555028577744705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5962680103406704770326273 4472010077555028577744705)
            ·
              refine ⟨3354007558166271433308529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4472010077555028577744705 3354007558166271433308529)
              ·
                refine ⟨2515505668624703574981397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3354007558166271433308529 2515505668624703574981397)
                ·
                  refine ⟨117914328216782980077253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2515505668624703574981397 117914328216782980077253)
                  ·
                    rfl

theorem cell21_516684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_516684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516684 prefixEnd_516684 := by exact prefixLift 516684
  have htrace : WordTrace (prefixWord ++ tailWord_516684) baseStart_516684 baseEnd_516684 := by
    simpa [prefixWord, tailWord_516684, baseEnd_516684] using wordTrace_append hprefix tailTrace_516684
  have hstable : (prefixWord ++ tailWord_516684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516684).length < 2 ^ (prefixWord ++ tailWord_516684).sum := by decide
  have hdescent : baseEnd_516684 < baseStart_516684 := by decide
  rcases family_descends (prefixWord ++ tailWord_516684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516760 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 6]
def baseStart_516760 : Nat := 118140960795 + 516760 * 2 ^ 59
def prefixEnd_516760 : Nat := 4983230072969 + 3 ^ 40 * 516760 * 2
def baseEnd_516760 : Nat := 117931672452223736810431

theorem tailTrace_516760 : CollatzResearch.WordTrace tailWord_516760 prefixEnd_516760 117931672452223736810431 := by
  unfold tailWord_516760
  simp only [CollatzResearch.WordTrace]
  refine ⟨9423892803937125213361867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12565190405249500284482489 9423892803937125213361867)
  ·
    refine ⟨14135839205905687820042801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9423892803937125213361867 14135839205905687820042801)
    ·
      refine ⟨10601879404429265865032101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14135839205905687820042801 10601879404429265865032101)
      ·
        refine ⟨1987852388330487349693519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10601879404429265865032101 1987852388330487349693519)
        ·
          refine ⟨2981778582495731024540279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987852388330487349693519 2981778582495731024540279)
          ·
            refine ⟨4472667873743596536810419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2981778582495731024540279 4472667873743596536810419)
            ·
              refine ⟨6709001810615394805215629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4472667873743596536810419 6709001810615394805215629)
              ·
                refine ⟨2515875678980773051955861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6709001810615394805215629 2515875678980773051955861)
                ·
                  refine ⟨117931672452223736810431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2515875678980773051955861 117931672452223736810431)
                  ·
                    rfl

theorem cell21_516760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_516760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516760 prefixEnd_516760 := by exact prefixLift 516760
  have htrace : WordTrace (prefixWord ++ tailWord_516760) baseStart_516760 baseEnd_516760 := by
    simpa [prefixWord, tailWord_516760, baseEnd_516760] using wordTrace_append hprefix tailTrace_516760
  have hstable : (prefixWord ++ tailWord_516760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516760).length < 2 ^ (prefixWord ++ tailWord_516760).sum := by decide
  have hdescent : baseEnd_516760 < baseStart_516760 := by decide
  rcases family_descends (prefixWord ++ tailWord_516760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516881 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 5]
def baseStart_516881 : Nat := 118140960795 + 516881 * 2 ^ 59
def prefixEnd_516881 : Nat := 4983230072969 + 3 ^ 40 * 516881 * 2
def baseEnd_516881 : Nat := 117959286300754415293517

theorem tailTrace_516881 : CollatzResearch.WordTrace tailWord_516881 prefixEnd_516881 117959286300754415293517 := by
  unfold tailWord_516881
  simp only [CollatzResearch.WordTrace]
  refine ⟨18852198840435888091878497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12568132560290592061252331 18852198840435888091878497)
  ·
    refine ⟨14139149130326916068908873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18852198840435888091878497 14139149130326916068908873)
    ·
      refine ⟨10604361847745187051681655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14139149130326916068908873 10604361847745187051681655)
      ·
        refine ⟨15906542771617780577522483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10604361847745187051681655 15906542771617780577522483)
        ·
          refine ⟨23859814157426670866283725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15906542771617780577522483 23859814157426670866283725)
          ·
            refine ⟨8947430309035001574856397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23859814157426670866283725 8947430309035001574856397)
            ·
              refine ⟨3355286365888125590571149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8947430309035001574856397 3355286365888125590571149)
              ·
                refine ⟨1258232387208047096464181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3355286365888125590571149 1258232387208047096464181)
                ·
                  refine ⟨117959286300754415293517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1258232387208047096464181 117959286300754415293517)
                  ·
                    rfl

theorem cell21_516881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_516881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516881 prefixEnd_516881 := by exact prefixLift 516881
  have htrace : WordTrace (prefixWord ++ tailWord_516881) baseStart_516881 baseEnd_516881 := by
    simpa [prefixWord, tailWord_516881, baseEnd_516881] using wordTrace_append hprefix tailTrace_516881
  have hstable : (prefixWord ++ tailWord_516881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516881).length < 2 ^ (prefixWord ++ tailWord_516881).sum := by decide
  have hdescent : baseEnd_516881 < baseStart_516881 := by decide
  rcases family_descends (prefixWord ++ tailWord_516881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516898 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 5]
def baseStart_516898 : Nat := 118140960795 + 516898 * 2 ^ 59
def prefixEnd_516898 : Nat := 4983230072969 + 3 ^ 40 * 516898 * 2
def baseEnd_516898 : Nat := 117963165932366163510149

theorem tailTrace_516898 : CollatzResearch.WordTrace tailWord_516898 prefixEnd_516898 117963165932366163510149 := by
  unfold tailWord_516898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4713204720343574998811837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12568545920916199996831565 4713204720343574998811837)
  ·
    refine ⟨1767451770128840624554439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4713204720343574998811837 1767451770128840624554439)
    ·
      refine ⟨2651177655193260936831659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1767451770128840624554439 2651177655193260936831659)
      ·
        refine ⟨3976766482789891405247489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2651177655193260936831659 3976766482789891405247489)
        ·
          refine ⟨2982574862092418553935617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3976766482789891405247489 2982574862092418553935617)
          ·
            refine ⟨2236931146569313915451713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2982574862092418553935617 2236931146569313915451713)
            ·
              refine ⟨1677698359926985436588785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2236931146569313915451713 1677698359926985436588785)
              ·
                refine ⟨1258273769945239077441589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1677698359926985436588785 1258273769945239077441589)
                ·
                  refine ⟨117963165932366163510149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1258273769945239077441589 117963165932366163510149)
                  ·
                    rfl

theorem cell21_516898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_516898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516898 prefixEnd_516898 := by exact prefixLift 516898
  have htrace : WordTrace (prefixWord ++ tailWord_516898) baseStart_516898 baseEnd_516898 := by
    simpa [prefixWord, tailWord_516898, baseEnd_516898] using wordTrace_append hprefix tailTrace_516898
  have hstable : (prefixWord ++ tailWord_516898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516898).length < 2 ^ (prefixWord ++ tailWord_516898).sum := by decide
  have hdescent : baseEnd_516898 < baseStart_516898 := by decide
  rcases family_descends (prefixWord ++ tailWord_516898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516915 : List Nat := [1, 1, 1, 2, 6, 1, 3, 3, 3]
def baseStart_516915 : Nat := 118140960795 + 516915 * 2 ^ 59
def prefixEnd_516915 : Nat := 4983230072969 + 3 ^ 40 * 516915 * 2
def baseEnd_516915 : Nat := 117967045563977911726781

theorem tailTrace_516915 : CollatzResearch.WordTrace tailWord_516915 prefixEnd_516915 117967045563977911726781 := by
  unfold tailWord_516915
  simp only [CollatzResearch.WordTrace]
  refine ⟨18853438922312711898616199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12568959281541807932410799 18853438922312711898616199)
  ·
    refine ⟨28280158383469067847924299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18853438922312711898616199 28280158383469067847924299)
    ·
      refine ⟨42420237575203601771886449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28280158383469067847924299 42420237575203601771886449)
      ·
        refine ⟨31815178181402701328914837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42420237575203601771886449 31815178181402701328914837)
        ·
          refine ⟨1491336477253251624792883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31815178181402701328914837 1491336477253251624792883)
          ·
            refine ⟨2237004715879877437189325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491336477253251624792883 2237004715879877437189325)
            ·
              refine ⟨838876768454954038945997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2237004715879877437189325 838876768454954038945997)
              ·
                refine ⟨314578788170607764604749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 838876768454954038945997 314578788170607764604749)
                ·
                  refine ⟨117967045563977911726781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314578788170607764604749 117967045563977911726781)
                  ·
                    rfl

theorem cell21_516915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 3].length) (baseStart_516915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516915 prefixEnd_516915 := by exact prefixLift 516915
  have htrace : WordTrace (prefixWord ++ tailWord_516915) baseStart_516915 baseEnd_516915 := by
    simpa [prefixWord, tailWord_516915, baseEnd_516915] using wordTrace_append hprefix tailTrace_516915
  have hstable : (prefixWord ++ tailWord_516915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516915).length < 2 ^ (prefixWord ++ tailWord_516915).sum := by decide
  have hdescent : baseEnd_516915 < baseStart_516915 := by decide
  rcases family_descends (prefixWord ++ tailWord_516915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516971 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 8]
def baseStart_516971 : Nat := 118140960795 + 516971 * 2 ^ 59
def prefixEnd_516971 : Nat := 4983230072969 + 3 ^ 40 * 516971 * 2
def baseEnd_516971 : Nat := 117979825526934258793333

theorem tailTrace_516971 : CollatzResearch.WordTrace tailWord_516971 prefixEnd_516971 117979825526934258793333 := by
  unfold tailWord_516971
  simp only [CollatzResearch.WordTrace]
  refine ⟨18855481410109833462654767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12570320940073222308436511 18855481410109833462654767)
  ·
    refine ⟨28283222115164750193982151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18855481410109833462654767 28283222115164750193982151)
    ·
      refine ⟨42424833172747125290973227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28283222115164750193982151 42424833172747125290973227)
      ·
        refine ⟨63637249759120687936459841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42424833172747125290973227 63637249759120687936459841)
        ·
          refine ⟨47727937319340515952344881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63637249759120687936459841 47727937319340515952344881)
          ·
            refine ⟨35795952989505386964258661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47727937319340515952344881 35795952989505386964258661)
            ·
              refine ⟨6711741185532260055798499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35795952989505386964258661 6711741185532260055798499)
              ·
                refine ⟨10067611778298390083697749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6711741185532260055798499 10067611778298390083697749)
                ·
                  refine ⟨117979825526934258793333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10067611778298390083697749 117979825526934258793333)
                  ·
                    rfl

theorem cell21_516971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 8].length) (baseStart_516971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516971 prefixEnd_516971 := by exact prefixLift 516971
  have htrace : WordTrace (prefixWord ++ tailWord_516971) baseStart_516971 baseEnd_516971 := by
    simpa [prefixWord, tailWord_516971, baseEnd_516971] using wordTrace_append hprefix tailTrace_516971
  have hstable : (prefixWord ++ tailWord_516971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516971).length < 2 ^ (prefixWord ++ tailWord_516971).sum := by decide
  have hdescent : baseEnd_516971 < baseStart_516971 := by decide
  rcases family_descends (prefixWord ++ tailWord_516971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516991 : List Nat := [1, 1, 2, 2, 1, 1, 8, 2, 3]
def baseStart_516991 : Nat := 118140960795 + 516991 * 2 ^ 59
def prefixEnd_516991 : Nat := 4983230072969 + 3 ^ 40 * 516991 * 2
def baseEnd_516991 : Nat := 117984389799418668459959

theorem tailTrace_516991 : CollatzResearch.WordTrace tailWord_516991 prefixEnd_516991 117984389799418668459959 := by
  unfold tailWord_516991
  simp only [CollatzResearch.WordTrace]
  refine ⟨18856210870037376878382827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12570807246691584585588551 18856210870037376878382827)
  ·
    refine ⟨28284316305056065317574241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18856210870037376878382827 28284316305056065317574241)
    ·
      refine ⟨21213237228792048988180681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28284316305056065317574241 21213237228792048988180681)
      ·
        refine ⟨15909927921594036741135511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21213237228792048988180681 15909927921594036741135511)
        ·
          refine ⟨23864891882391055111703267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15909927921594036741135511 23864891882391055111703267)
          ·
            refine ⟨35797337823586582667554901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23864891882391055111703267 35797337823586582667554901)
            ·
              refine ⟨419500052620155265635409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 35797337823586582667554901 419500052620155265635409)
              ·
                refine ⟨314625039465116449226557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419500052620155265635409 314625039465116449226557)
                ·
                  refine ⟨117984389799418668459959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314625039465116449226557 117984389799418668459959)
                  ·
                    rfl

theorem cell21_516991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 3].length) (baseStart_516991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516991 prefixEnd_516991 := by exact prefixLift 516991
  have htrace : WordTrace (prefixWord ++ tailWord_516991) baseStart_516991 baseEnd_516991 := by
    simpa [prefixWord, tailWord_516991, baseEnd_516991] using wordTrace_append hprefix tailTrace_516991
  have hstable : (prefixWord ++ tailWord_516991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516991).length < 2 ^ (prefixWord ++ tailWord_516991).sum := by decide
  have hdescent : baseEnd_516991 < baseStart_516991 := by decide
  rcases family_descends (prefixWord ++ tailWord_516991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516994 : List Nat := [3, 4, 2, 2, 1, 2, 1, 6]
def baseStart_516994 : Nat := 118140960795 + 516994 * 2 ^ 59
def prefixEnd_516994 : Nat := 4983230072969 + 3 ^ 40 * 516994 * 2
def baseEnd_516994 : Nat := 39328358146763776636651

theorem tailTrace_516994 : CollatzResearch.WordTrace tailWord_516994 prefixEnd_516994 39328358146763776636651 := by
  unfold tailWord_516994
  simp only [CollatzResearch.WordTrace]
  refine ⟨4714080072256627097685509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12570880192684338927161357 4714080072256627097685509)
  ·
    refine ⟨883890013548117580816033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4714080072256627097685509 883890013548117580816033)
    ·
      refine ⟨662917510161088185612025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 883890013548117580816033 662917510161088185612025)
      ·
        refine ⟨497188132620816139209019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662917510161088185612025 497188132620816139209019)
        ·
          refine ⟨745782198931224208813529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497188132620816139209019 745782198931224208813529)
          ·
            refine ⟨559336649198418156610147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745782198931224208813529 559336649198418156610147)
            ·
              refine ⟨839004973797627234915221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559336649198418156610147 839004973797627234915221)
              ·
                refine ⟨39328358146763776636651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 839004973797627234915221 39328358146763776636651)
                ·
                  rfl

theorem cell21_516994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_516994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_516994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_516994 prefixEnd_516994 := by exact prefixLift 516994
  have htrace : WordTrace (prefixWord ++ tailWord_516994) baseStart_516994 baseEnd_516994 := by
    simpa [prefixWord, tailWord_516994, baseEnd_516994] using wordTrace_append hprefix tailTrace_516994
  have hstable : (prefixWord ++ tailWord_516994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516994).length < 2 ^ (prefixWord ++ tailWord_516994).sum := by decide
  have hdescent : baseEnd_516994 < baseStart_516994 := by decide
  rcases family_descends (prefixWord ++ tailWord_516994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517050 : List Nat := [3, 1, 1, 1, 2, 1, 3, 6, 3]
def baseStart_517050 : Nat := 118140960795 + 517050 * 2 ^ 59
def prefixEnd_517050 : Nat := 4983230072969 + 3 ^ 40 * 517050 * 2
def baseEnd_517050 : Nat := 117997854403247676976505

theorem tailTrace_517050 : CollatzResearch.WordTrace tailWord_517050 prefixEnd_517050 117997854403247676976505 := by
  unfold tailWord_517050
  simp only [CollatzResearch.WordTrace]
  refine ⟨4714590694205907488695151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12572241851215753303187069 4714590694205907488695151)
  ·
    refine ⟨7071886041308861233042727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4714590694205907488695151 7071886041308861233042727)
    ·
      refine ⟨10607829061963291849564091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7071886041308861233042727 10607829061963291849564091)
      ·
        refine ⟨15911743592944937774346137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10607829061963291849564091 15911743592944937774346137)
        ·
          refine ⟨11933807694708703330759603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15911743592944937774346137 11933807694708703330759603)
          ·
            refine ⟨17900711542063054996139405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11933807694708703330759603 17900711542063054996139405)
            ·
              refine ⟨6712766828273645623552277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17900711542063054996139405 6712766828273645623552277)
              ·
                refine ⟨314660945075327138604013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6712766828273645623552277 314660945075327138604013)
                ·
                  refine ⟨117997854403247676976505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314660945075327138604013 117997854403247676976505)
                  ·
                    rfl

theorem cell21_517050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_517050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517050 prefixEnd_517050 := by exact prefixLift 517050
  have htrace : WordTrace (prefixWord ++ tailWord_517050) baseStart_517050 baseEnd_517050 := by
    simpa [prefixWord, tailWord_517050, baseEnd_517050] using wordTrace_append hprefix tailTrace_517050
  have hstable : (prefixWord ++ tailWord_517050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517050).length < 2 ^ (prefixWord ++ tailWord_517050).sum := by decide
  have hdescent : baseEnd_517050 < baseStart_517050 := by decide
  rcases family_descends (prefixWord ++ tailWord_517050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517095 : List Nat := [1, 1, 5, 2, 2, 3, 7]
def baseStart_517095 : Nat := 118140960795 + 517095 * 2 ^ 59
def prefixEnd_517095 : Nat := 4983230072969 + 3 ^ 40 * 517095 * 2
def baseEnd_517095 : Nat := 13112013779593066525157

theorem tailTrace_517095 : CollatzResearch.WordTrace tailWord_517095 prefixEnd_517095 13112013779593066525157 := by
  unfold tailWord_517095
  simp only [CollatzResearch.WordTrace]
  refine ⟨18860004061660602640168739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12573336041107068426779159 18860004061660602640168739)
  ·
    refine ⟨28290006092490903960253109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18860004061660602640168739 28290006092490903960253109)
    ·
      refine ⟨2652188071171022246273729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28290006092490903960253109 2652188071171022246273729)
      ·
        refine ⟨1989141053378266684705297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2652188071171022246273729 1989141053378266684705297)
        ·
          refine ⟨1491855790033700013528973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1989141053378266684705297 1491855790033700013528973)
          ·
            refine ⟨559445921262637505073365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1491855790033700013528973 559445921262637505073365)
            ·
              refine ⟨13112013779593066525157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 559445921262637505073365 13112013779593066525157)
              ·
                rfl

theorem cell21_517095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 7].length) (baseStart_517095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517095 prefixEnd_517095 := by exact prefixLift 517095
  have htrace : WordTrace (prefixWord ++ tailWord_517095) baseStart_517095 baseEnd_517095 := by
    simpa [prefixWord, tailWord_517095, baseEnd_517095] using wordTrace_append hprefix tailTrace_517095
  have hstable : (prefixWord ++ tailWord_517095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517095).length < 2 ^ (prefixWord ++ tailWord_517095).sum := by decide
  have hdescent : baseEnd_517095 < baseStart_517095 := by decide
  rcases family_descends (prefixWord ++ tailWord_517095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517154 : List Nat := [3, 3, 1, 1, 1, 12]
def baseStart_517154 : Nat := 118140960795 + 517154 * 2 ^ 59
def prefixEnd_517154 : Nat := 4983230072969 + 3 ^ 40 * 517154 * 2
def baseEnd_517154 : Nat := 4371169948895059527517

theorem tailTrace_517154 : CollatzResearch.WordTrace tailWord_517154 prefixEnd_517154 4371169948895059527517 := by
  unfold tailWord_517154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4715538992111713929141629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12574770645631237144377677 4715538992111713929141629)
  ·
    refine ⟨1768327122041892723428111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4715538992111713929141629 1768327122041892723428111)
    ·
      refine ⟨2652490683062839085142167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1768327122041892723428111 2652490683062839085142167)
      ·
        refine ⟨3978736024594258627713251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2652490683062839085142167 3978736024594258627713251)
        ·
          refine ⟨5968104036891387941569877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3978736024594258627713251 5968104036891387941569877)
          ·
            refine ⟨4371169948895059527517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5968104036891387941569877 4371169948895059527517)
            ·
              rfl

theorem cell21_517154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 12].length) (baseStart_517154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517154 prefixEnd_517154 := by exact prefixLift 517154
  have htrace : WordTrace (prefixWord ++ tailWord_517154) baseStart_517154 baseEnd_517154 := by
    simpa [prefixWord, tailWord_517154, baseEnd_517154] using wordTrace_append hprefix tailTrace_517154
  have hstable : (prefixWord ++ tailWord_517154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517154).length < 2 ^ (prefixWord ++ tailWord_517154).sum := by decide
  have hdescent : baseEnd_517154 < baseStart_517154 := by decide
  rcases family_descends (prefixWord ++ tailWord_517154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517413 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 5]
def baseStart_517413 : Nat := 118140960795 + 517413 * 2 ^ 59
def prefixEnd_517413 : Nat := 4983230072969 + 3 ^ 40 * 517413 * 2
def baseEnd_517413 : Nat := 118080695948839712425763

theorem tailTrace_517413 : CollatzResearch.WordTrace tailWord_517413 prefixEnd_517413 118080695948839712425763 := by
  unfold tailWord_517413
  simp only [CollatzResearch.WordTrace]
  refine ⟨18871602474508542950244893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12581068316339028633496595 18871602474508542950244893)
  ·
    refine ⟨7076850927940703606341835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18871602474508542950244893 7076850927940703606341835)
    ·
      refine ⟨10615276391911055409512753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7076850927940703606341835 10615276391911055409512753)
      ·
        refine ⟨7961457293933291557134565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10615276391911055409512753 7961457293933291557134565)
        ·
          refine ⟨1492773242612492166962731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7961457293933291557134565 1492773242612492166962731)
          ·
            refine ⟨2239159863918738250444097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492773242612492166962731 2239159863918738250444097)
            ·
              refine ⟨1679369897939053687833073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2239159863918738250444097 1679369897939053687833073)
              ·
                refine ⟨1259527423454290265874805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1679369897939053687833073 1259527423454290265874805)
                ·
                  refine ⟨118080695948839712425763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1259527423454290265874805 118080695948839712425763)
                  ·
                    rfl

theorem cell21_517413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_517413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517413 prefixEnd_517413 := by exact prefixLift 517413
  have htrace : WordTrace (prefixWord ++ tailWord_517413) baseStart_517413 baseEnd_517413 := by
    simpa [prefixWord, tailWord_517413, baseEnd_517413] using wordTrace_append hprefix tailTrace_517413
  have hstable : (prefixWord ++ tailWord_517413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517413).length < 2 ^ (prefixWord ++ tailWord_517413).sum := by decide
  have hdescent : baseEnd_517413 < baseStart_517413 := by decide
  rcases family_descends (prefixWord ++ tailWord_517413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517416 : List Nat := [2, 1, 5, 1, 2, 3, 2, 5]
def baseStart_517416 : Nat := 118140960795 + 517416 * 2 ^ 59
def prefixEnd_517416 : Nat := 4983230072969 + 3 ^ 40 * 517416 * 2
def baseEnd_517416 : Nat := 39360460196570791291919

theorem tailTrace_517416 : CollatzResearch.WordTrace tailWord_517416 prefixEnd_517416 39360460196570791291919 := by
  unfold tailWord_517416
  simp only [CollatzResearch.WordTrace]
  refine ⟨9435855946748837231302051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12581141262331782975069401 9435855946748837231302051)
  ·
    refine ⟨14153783920123255846953077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9435855946748837231302051 14153783920123255846953077)
    ·
      refine ⟨1326917242511555235651851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14153783920123255846953077 1326917242511555235651851)
      ·
        refine ⟨1990375863767332853477777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1326917242511555235651851 1990375863767332853477777)
        ·
          refine ⟨1492781897825499640108333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1990375863767332853477777 1492781897825499640108333)
          ·
            refine ⟨559793211684562365040625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1492781897825499640108333 559793211684562365040625)
            ·
              refine ⟨419844908763421773780469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 559793211684562365040625 419844908763421773780469)
              ·
                refine ⟨39360460196570791291919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 419844908763421773780469 39360460196570791291919)
                ·
                  rfl

theorem cell21_517416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 5].length) (baseStart_517416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517416 prefixEnd_517416 := by exact prefixLift 517416
  have htrace : WordTrace (prefixWord ++ tailWord_517416) baseStart_517416 baseEnd_517416 := by
    simpa [prefixWord, tailWord_517416, baseEnd_517416] using wordTrace_append hprefix tailTrace_517416
  have hstable : (prefixWord ++ tailWord_517416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517416).length < 2 ^ (prefixWord ++ tailWord_517416).sum := by decide
  have hdescent : baseEnd_517416 < baseStart_517416 := by decide
  rcases family_descends (prefixWord ++ tailWord_517416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517427 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 6]
def baseStart_517427 : Nat := 118140960795 + 517427 * 2 ^ 59
def prefixEnd_517427 : Nat := 4983230072969 + 3 ^ 40 * 517427 * 2
def baseEnd_517427 : Nat := 118083890939578799192401

theorem tailTrace_517427 : CollatzResearch.WordTrace tailWord_517427 prefixEnd_517427 118083890939578799192401 := by
  unfold tailWord_517427
  simp only [CollatzResearch.WordTrace]
  refine ⟨18872113096457823341254535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12581408730971882227503023 18872113096457823341254535)
  ·
    refine ⟨28308169644686735011881803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18872113096457823341254535 28308169644686735011881803)
    ·
      refine ⟨42462254467030102517822705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28308169644686735011881803 42462254467030102517822705)
      ·
        refine ⟨31846690850272576888367029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42462254467030102517822705 31846690850272576888367029)
        ·
          refine ⟨2985627267213054083284409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31846690850272576888367029 2985627267213054083284409)
          ·
            refine ⟨2239220450409790562463307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2985627267213054083284409 2239220450409790562463307)
            ·
              refine ⟨3358830675614685843694961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239220450409790562463307 3358830675614685843694961)
              ·
                refine ⟨2519123006711014382771221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3358830675614685843694961 2519123006711014382771221)
                ·
                  refine ⟨118083890939578799192401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2519123006711014382771221 118083890939578799192401)
                  ·
                    rfl

theorem cell21_517427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 6].length) (baseStart_517427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517427 prefixEnd_517427 := by exact prefixLift 517427
  have htrace : WordTrace (prefixWord ++ tailWord_517427) baseStart_517427 baseEnd_517427 := by
    simpa [prefixWord, tailWord_517427, baseEnd_517427] using wordTrace_append hprefix tailTrace_517427
  have hstable : (prefixWord ++ tailWord_517427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517427).length < 2 ^ (prefixWord ++ tailWord_517427).sum := by decide
  have hdescent : baseEnd_517427 < baseStart_517427 := by decide
  rcases family_descends (prefixWord ++ tailWord_517427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517447 : List Nat := [1, 1, 4, 1, 2, 4, 3, 2, 3]
def baseStart_517447 : Nat := 118140960795 + 517447 * 2 ^ 59
def prefixEnd_517447 : Nat := 4983230072969 + 3 ^ 40 * 517447 * 2
def baseEnd_517447 : Nat := 118088455212063208859027

theorem tailTrace_517447 : CollatzResearch.WordTrace tailWord_517447 prefixEnd_517447 118088455212063208859027 := by
  unfold tailWord_517447
  simp only [CollatzResearch.WordTrace]
  refine ⟨18872842556385366756982595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12581895037590244504655063 18872842556385366756982595)
  ·
    refine ⟨28309263834578050135473893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18872842556385366756982595 28309263834578050135473893)
    ·
      refine ⟨5307986968983384400401355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28309263834578050135473893 5307986968983384400401355)
      ·
        refine ⟨7961980453475076600602033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5307986968983384400401355 7961980453475076600602033)
        ·
          refine ⟨5971485340106307450451525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7961980453475076600602033 5971485340106307450451525)
          ·
            refine ⟨1119653501269932646959661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5971485340106307450451525 1119653501269932646959661)
            ·
              refine ⟨419870062976224742609873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1119653501269932646959661 419870062976224742609873)
              ·
                refine ⟨314902547232168556957405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419870062976224742609873 314902547232168556957405)
                ·
                  refine ⟨118088455212063208859027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314902547232168556957405 118088455212063208859027)
                  ·
                    rfl

theorem cell21_517447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 3].length) (baseStart_517447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517447 prefixEnd_517447 := by exact prefixLift 517447
  have htrace : WordTrace (prefixWord ++ tailWord_517447) baseStart_517447 baseEnd_517447 := by
    simpa [prefixWord, tailWord_517447, baseEnd_517447] using wordTrace_append hprefix tailTrace_517447
  have hstable : (prefixWord ++ tailWord_517447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517447).length < 2 ^ (prefixWord ++ tailWord_517447).sum := by decide
  have hdescent : baseEnd_517447 < baseStart_517447 := by decide
  rcases family_descends (prefixWord ++ tailWord_517447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517461 : List Nat := [1, 3, 2, 2, 3, 1, 4, 1, 4]
def baseStart_517461 : Nat := 118140960795 + 517461 * 2 ^ 59
def prefixEnd_517461 : Nat := 4983230072969 + 3 ^ 40 * 517461 * 2
def baseEnd_517461 : Nat := 118091650202802295625665

theorem tailTrace_517461 : CollatzResearch.WordTrace tailWord_517461 prefixEnd_517461 118091650202802295625665 := by
  unfold tailWord_517461
  simp only [CollatzResearch.WordTrace]
  refine ⟨18873353178334647147992237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12582235452223098098661491 18873353178334647147992237)
  ·
    refine ⟨7077507441875492680497089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18873353178334647147992237 7077507441875492680497089)
    ·
      refine ⟨5308130581406619510372817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7077507441875492680497089 5308130581406619510372817)
      ·
        refine ⟨3981097936054964632779613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5308130581406619510372817 3981097936054964632779613)
        ·
          refine ⟨1492911726020611737292355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3981097936054964632779613 1492911726020611737292355)
          ·
            refine ⟨2239367589030917605938533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492911726020611737292355 2239367589030917605938533)
            ·
              refine ⟨419881422943297051113475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2239367589030917605938533 419881422943297051113475)
              ·
                refine ⟨629822134414945576670213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419881422943297051113475 629822134414945576670213)
                ·
                  refine ⟨118091650202802295625665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 629822134414945576670213 118091650202802295625665)
                  ·
                    rfl

theorem cell21_517461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_517461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517461 prefixEnd_517461 := by exact prefixLift 517461
  have htrace : WordTrace (prefixWord ++ tailWord_517461) baseStart_517461 baseEnd_517461 := by
    simpa [prefixWord, tailWord_517461, baseEnd_517461] using wordTrace_append hprefix tailTrace_517461
  have hstable : (prefixWord ++ tailWord_517461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517461).length < 2 ^ (prefixWord ++ tailWord_517461).sum := by decide
  have hdescent : baseEnd_517461 < baseStart_517461 := by decide
  rcases family_descends (prefixWord ++ tailWord_517461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517565 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 5]
def baseStart_517565 : Nat := 118140960795 + 517565 * 2 ^ 59
def prefixEnd_517565 : Nat := 4983230072969 + 3 ^ 40 * 517565 * 2
def baseEnd_517565 : Nat := 118115384419721225892119

theorem tailTrace_517565 : CollatzResearch.WordTrace tailWord_517565 prefixEnd_517565 118115384419721225892119 := by
  unfold tailWord_517565
  simp only [CollatzResearch.WordTrace]
  refine ⟨18877146369957872909778149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12584764246638581939852099 18877146369957872909778149)
  ·
    refine ⟨3539464944367101170583403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18877146369957872909778149 3539464944367101170583403)
    ·
      refine ⟨5309197416550651755875105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3539464944367101170583403 5309197416550651755875105)
      ·
        refine ⟨3981898062412988816906329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5309197416550651755875105 3981898062412988816906329)
        ·
          refine ⟨2986423546809741612679747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3981898062412988816906329 2986423546809741612679747)
          ·
            refine ⟨4479635320214612419019621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2986423546809741612679747 4479635320214612419019621)
            ·
              refine ⟨839931622540239828566179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4479635320214612419019621 839931622540239828566179)
              ·
                refine ⟨1259897433810359742849269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839931622540239828566179 1259897433810359742849269)
                ·
                  refine ⟨118115384419721225892119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1259897433810359742849269 118115384419721225892119)
                  ·
                    rfl

theorem cell21_517565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_517565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517565 prefixEnd_517565 := by exact prefixLift 517565
  have htrace : WordTrace (prefixWord ++ tailWord_517565) baseStart_517565 baseEnd_517565 := by
    simpa [prefixWord, tailWord_517565, baseEnd_517565] using wordTrace_append hprefix tailTrace_517565
  have hstable : (prefixWord ++ tailWord_517565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517565).length < 2 ^ (prefixWord ++ tailWord_517565).sum := by decide
  have hdescent : baseEnd_517565 < baseStart_517565 := by decide
  rcases family_descends (prefixWord ++ tailWord_517565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517579 : List Nat := [1, 1, 1, 1, 3, 3, 2, 5, 4]
def baseStart_517579 : Nat := 118140960795 + 517579 * 2 ^ 59
def prefixEnd_517579 : Nat := 4983230072969 + 3 ^ 40 * 517579 * 2
def baseEnd_517579 : Nat := 118118579410460312658757

theorem tailTrace_517579 : CollatzResearch.WordTrace tailWord_517579 prefixEnd_517579 118118579410460312658757 := by
  unfold tailWord_517579
  simp only [CollatzResearch.WordTrace]
  refine ⟨18877656991907153300787791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12585104661271435533858527 18877656991907153300787791)
  ·
    refine ⟨28316485487860729951181687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18877656991907153300787791 28316485487860729951181687)
    ·
      refine ⟨42474728231791094926772531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28316485487860729951181687 42474728231791094926772531)
      ·
        refine ⟨63712092347686642390158797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42474728231791094926772531 63712092347686642390158797)
        ·
          refine ⟨23892034630382490896309549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63712092347686642390158797 23892034630382490896309549)
          ·
            refine ⟨8959512986393434086116081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23892034630382490896309549 8959512986393434086116081)
            ·
              refine ⟨6719634739795075564587061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8959512986393434086116081 6719634739795075564587061)
              ·
                refine ⟨629965756855788334180037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6719634739795075564587061 629965756855788334180037)
                ·
                  refine ⟨118118579410460312658757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 629965756855788334180037 118118579410460312658757)
                  ·
                    rfl

theorem cell21_517579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 4].length) (baseStart_517579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517579 prefixEnd_517579 := by exact prefixLift 517579
  have htrace : WordTrace (prefixWord ++ tailWord_517579) baseStart_517579 baseEnd_517579 := by
    simpa [prefixWord, tailWord_517579, baseEnd_517579] using wordTrace_append hprefix tailTrace_517579
  have hstable : (prefixWord ++ tailWord_517579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517579).length < 2 ^ (prefixWord ++ tailWord_517579).sum := by decide
  have hdescent : baseEnd_517579 < baseStart_517579 := by decide
  rcases family_descends (prefixWord ++ tailWord_517579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517630 : List Nat := [4, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_517630 : Nat := 118140960795 + 517630 * 2 ^ 59
def prefixEnd_517630 : Nat := 4983230072969 + 3 ^ 40 * 517630 * 2
def baseEnd_517630 : Nat := 118130218305295557308653

theorem tailTrace_517630 : CollatzResearch.WordTrace tailWord_517630 prefixEnd_517630 118130218305295557308653 := by
  unfold tailWord_517630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2359939639340298626361793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12586344743148259340596229 2359939639340298626361793)
  ·
    refine ⟨1769954729505223969771345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2359939639340298626361793 1769954729505223969771345)
    ·
      refine ⟨1327466047128917977328509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1769954729505223969771345 1327466047128917977328509)
      ·
        refine ⟨497799767673344241498191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1327466047128917977328509 497799767673344241498191)
        ·
          refine ⟨746699651510016362247287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497799767673344241498191 746699651510016362247287)
          ·
            refine ⟨1120049477265024543370931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746699651510016362247287 1120049477265024543370931)
            ·
              refine ⟨1680074215897536815056397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120049477265024543370931 1680074215897536815056397)
              ·
                refine ⟨630027830961576305646149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1680074215897536815056397 630027830961576305646149)
                ·
                  refine ⟨118130218305295557308653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 630027830961576305646149 118130218305295557308653)
                  ·
                    rfl

theorem cell21_517630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_517630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517630 prefixEnd_517630 := by exact prefixLift 517630
  have htrace : WordTrace (prefixWord ++ tailWord_517630) baseStart_517630 baseEnd_517630 := by
    simpa [prefixWord, tailWord_517630, baseEnd_517630] using wordTrace_append hprefix tailTrace_517630
  have hstable : (prefixWord ++ tailWord_517630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517630).length < 2 ^ (prefixWord ++ tailWord_517630).sum := by decide
  have hdescent : baseEnd_517630 < baseStart_517630 := by decide
  rcases family_descends (prefixWord ++ tailWord_517630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517703 : List Nat := [1, 1, 4, 1, 5, 1, 3, 5]
def baseStart_517703 : Nat := 118140960795 + 517703 * 2 ^ 59
def prefixEnd_517703 : Nat := 4983230072969 + 3 ^ 40 * 517703 * 2
def baseEnd_517703 : Nat := 39382292633287884197279

theorem tailTrace_517703 : CollatzResearch.WordTrace tailWord_517703 prefixEnd_517703 39382292633287884197279 := by
  unfold tailWord_517703
  simp only [CollatzResearch.WordTrace]
  refine ⟨18882179643457922478301763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12588119762305281652201175 18882179643457922478301763)
  ·
    refine ⟨28323269465186883717452645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18882179643457922478301763 28323269465186883717452645)
    ·
      refine ⟨5310613024722540697022371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28323269465186883717452645 5310613024722540697022371)
      ·
        refine ⟨7965919537083811045533557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5310613024722540697022371 7965919537083811045533557)
        ·
          refine ⟨746804956601607285518771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7965919537083811045533557 746804956601607285518771)
          ·
            refine ⟨1120207434902410928278157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746804956601607285518771 1120207434902410928278157)
            ·
              refine ⟨420077788088404098104309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1120207434902410928278157 420077788088404098104309)
              ·
                refine ⟨39382292633287884197279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 420077788088404098104309 39382292633287884197279)
                ·
                  rfl

theorem cell21_517703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 5].length) (baseStart_517703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517703 prefixEnd_517703 := by exact prefixLift 517703
  have htrace : WordTrace (prefixWord ++ tailWord_517703) baseStart_517703 baseEnd_517703 := by
    simpa [prefixWord, tailWord_517703, baseEnd_517703] using wordTrace_append hprefix tailTrace_517703
  have hstable : (prefixWord ++ tailWord_517703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517703).length < 2 ^ (prefixWord ++ tailWord_517703).sum := by decide
  have hdescent : baseEnd_517703 < baseStart_517703 := by decide
  rcases family_descends (prefixWord ++ tailWord_517703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517731 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 6]
def baseStart_517731 : Nat := 118140960795 + 517731 * 2 ^ 59
def prefixEnd_517731 : Nat := 4983230072969 + 3 ^ 40 * 517731 * 2
def baseEnd_517731 : Nat := 118153267881341826125113

theorem tailTrace_517731 : CollatzResearch.WordTrace tailWord_517731 prefixEnd_517731 118153267881341826125113 := by
  unfold tailWord_517731
  simp only [CollatzResearch.WordTrace]
  refine ⟨18883200887356483260321047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12588800591570988840214031 18883200887356483260321047)
  ·
    refine ⟨28324801331034724890481571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18883200887356483260321047 28324801331034724890481571)
    ·
      refine ⟨42487201996552087335722357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28324801331034724890481571 42487201996552087335722357)
      ·
        refine ⟨3983175187176758187723971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42487201996552087335722357 3983175187176758187723971)
        ·
          refine ⟨5974762780765137281585957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3983175187176758187723971 5974762780765137281585957)
          ·
            refine ⟨1120268021393463240297367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5974762780765137281585957 1120268021393463240297367)
            ·
              refine ⟨1680402032090194860446051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120268021393463240297367 1680402032090194860446051)
              ·
                refine ⟨2520603048135292290669077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680402032090194860446051 2520603048135292290669077)
                ·
                  refine ⟨118153267881341826125113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2520603048135292290669077 118153267881341826125113)
                  ·
                    rfl

theorem cell21_517731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 6].length) (baseStart_517731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517731 prefixEnd_517731 := by exact prefixLift 517731
  have htrace : WordTrace (prefixWord ++ tailWord_517731) baseStart_517731 baseEnd_517731 := by
    simpa [prefixWord, tailWord_517731, baseEnd_517731] using wordTrace_append hprefix tailTrace_517731
  have hstable : (prefixWord ++ tailWord_517731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517731).length < 2 ^ (prefixWord ++ tailWord_517731).sum := by decide
  have hdescent : baseEnd_517731 < baseStart_517731 := by decide
  rcases family_descends (prefixWord ++ tailWord_517731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517768 : List Nat := [2, 1, 3, 5, 1, 2, 1, 3, 3]
def baseStart_517768 : Nat := 118140960795 + 517768 * 2 ^ 59
def prefixEnd_517768 : Nat := 4983230072969 + 3 ^ 40 * 517768 * 2
def baseEnd_517768 : Nat := 118161711785437984008371

theorem tailTrace_517768 : CollatzResearch.WordTrace tailWord_517768 prefixEnd_517768 118161711785437984008371 := by
  unfold tailWord_517768
  simp only [CollatzResearch.WordTrace]
  refine ⟨9442275194111219289708979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12589700258814959052945305 9442275194111219289708979)
  ·
    refine ⟨14163412791166828934563469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9442275194111219289708979 14163412791166828934563469)
    ·
      refine ⟨5311279796687560850461301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14163412791166828934563469 5311279796687560850461301)
      ·
        refine ⟨497932480939458829730747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5311279796687560850461301 497932480939458829730747)
        ·
          refine ⟨746898721409188244596121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497932480939458829730747 746898721409188244596121)
          ·
            refine ⟨560174041056891183447091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 746898721409188244596121 560174041056891183447091)
            ·
              refine ⟨840261061585336775170637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560174041056891183447091 840261061585336775170637)
              ·
                refine ⟨315097898094501290688989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 840261061585336775170637 315097898094501290688989)
                ·
                  refine ⟨118161711785437984008371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315097898094501290688989 118161711785437984008371)
                  ·
                    rfl

theorem cell21_517768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 3].length) (baseStart_517768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517768 prefixEnd_517768 := by exact prefixLift 517768
  have htrace : WordTrace (prefixWord ++ tailWord_517768) baseStart_517768 baseEnd_517768 := by
    simpa [prefixWord, tailWord_517768, baseEnd_517768] using wordTrace_append hprefix tailTrace_517768
  have hstable : (prefixWord ++ tailWord_517768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517768).length < 2 ^ (prefixWord ++ tailWord_517768).sum := by decide
  have hdescent : baseEnd_517768 < baseStart_517768 := by decide
  rcases family_descends (prefixWord ++ tailWord_517768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517793 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 5]
def baseStart_517793 : Nat := 118140960795 + 517793 * 2 ^ 59
def prefixEnd_517793 : Nat := 4983230072969 + 3 ^ 40 * 517793 * 2
def baseEnd_517793 : Nat := 118167417126043496091653

theorem tailTrace_517793 : CollatzResearch.WordTrace tailWord_517793 prefixEnd_517793 118167417126043496091653 := by
  unfold tailWord_517793
  simp only [CollatzResearch.WordTrace]
  refine ⟨18885462213131867849078033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12590308142087911899385355 18885462213131867849078033)
  ·
    refine ⟨14164096659848900886808525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18885462213131867849078033 14164096659848900886808525)
    ·
      refine ⟨5311536247443337832553197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14164096659848900886808525 5311536247443337832553197)
      ·
        refine ⟨1991826092791251687207449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5311536247443337832553197 1991826092791251687207449)
        ·
          refine ⟨1493869569593438765405587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1991826092791251687207449 1493869569593438765405587)
          ·
            refine ⟨2240804354390158148108381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1493869569593438765405587 2240804354390158148108381)
            ·
              refine ⟨840301632896309305540643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2240804354390158148108381 840301632896309305540643)
              ·
                refine ⟨1260452449344463958310965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840301632896309305540643 1260452449344463958310965)
                ·
                  refine ⟨118167417126043496091653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1260452449344463958310965 118167417126043496091653)
                  ·
                    rfl

theorem cell21_517793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_517793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517793 prefixEnd_517793 := by exact prefixLift 517793
  have htrace : WordTrace (prefixWord ++ tailWord_517793) baseStart_517793 baseEnd_517793 := by
    simpa [prefixWord, tailWord_517793, baseEnd_517793] using wordTrace_append hprefix tailTrace_517793
  have hstable : (prefixWord ++ tailWord_517793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517793).length < 2 ^ (prefixWord ++ tailWord_517793).sum := by decide
  have hdescent : baseEnd_517793 < baseStart_517793 := by decide
  rcases family_descends (prefixWord ++ tailWord_517793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517807 : List Nat := [1, 1, 2, 1, 2, 4, 3, 3, 4]
def baseStart_517807 : Nat := 118140960795 + 517807 * 2 ^ 59
def prefixEnd_517807 : Nat := 4983230072969 + 3 ^ 40 * 517807 * 2
def baseEnd_517807 : Nat := 118170612116782582858291

theorem tailTrace_517807 : CollatzResearch.WordTrace tailWord_517807 prefixEnd_517807 118170612116782582858291 := by
  unfold tailWord_517807
  simp only [CollatzResearch.WordTrace]
  refine ⟨18885972835081148240087675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12590648556720765493391783 18885972835081148240087675)
  ·
    refine ⟨28328959252621722360131513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18885972835081148240087675 28328959252621722360131513)
    ·
      refine ⟨21246719439466291770098635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28328959252621722360131513 21246719439466291770098635)
      ·
        refine ⟨31870079159199437655147953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21246719439466291770098635 31870079159199437655147953)
        ·
          refine ⟨23902559369399578241360965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31870079159199437655147953 23902559369399578241360965)
          ·
            refine ⟨4481729881762420920255181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23902559369399578241360965 4481729881762420920255181)
            ·
              refine ⟨1680648705660907845095693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4481729881762420920255181 1680648705660907845095693)
              ·
                refine ⟨630243264622840441910885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1680648705660907845095693 630243264622840441910885)
                ·
                  refine ⟨118170612116782582858291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 630243264622840441910885 118170612116782582858291)
                  ·
                    rfl

theorem cell21_517807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 4].length) (baseStart_517807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517807 prefixEnd_517807 := by exact prefixLift 517807
  have htrace : WordTrace (prefixWord ++ tailWord_517807) baseStart_517807 baseEnd_517807 := by
    simpa [prefixWord, tailWord_517807, baseEnd_517807] using wordTrace_append hprefix tailTrace_517807
  have hstable : (prefixWord ++ tailWord_517807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517807).length < 2 ^ (prefixWord ++ tailWord_517807).sum := by decide
  have hdescent : baseEnd_517807 < baseStart_517807 := by decide
  rcases family_descends (prefixWord ++ tailWord_517807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517821 : List Nat := [1, 4, 1, 2, 1, 2, 1, 9]
def baseStart_517821 : Nat := 118140960795 + 517821 * 2 ^ 59
def prefixEnd_517821 : Nat := 4983230072969 + 3 ^ 40 * 517821 * 2
def baseEnd_517821 : Nat := 39391269035840556541643

theorem tailTrace_517821 : CollatzResearch.WordTrace tailWord_517821 prefixEnd_517821 39391269035840556541643 := by
  unfold tailWord_517821
  simp only [CollatzResearch.WordTrace]
  refine ⟨18886483457030428631097317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12590988971353619087398211 18886483457030428631097317)
  ·
    refine ⟨3541215648193205368330747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18886483457030428631097317 3541215648193205368330747)
    ·
      refine ⟨5311823472289808052496121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3541215648193205368330747 5311823472289808052496121)
      ·
        refine ⟨3983867604217356039372091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5311823472289808052496121 3983867604217356039372091)
        ·
          refine ⟨5975801406326034059058137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3983867604217356039372091 5975801406326034059058137)
          ·
            refine ⟨4481851054744525544293603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5975801406326034059058137 4481851054744525544293603)
            ·
              refine ⟨6722776582116788316440405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4481851054744525544293603 6722776582116788316440405)
              ·
                refine ⟨39391269035840556541643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6722776582116788316440405 39391269035840556541643)
                ·
                  rfl

theorem cell21_517821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 9].length) (baseStart_517821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517821 prefixEnd_517821 := by exact prefixLift 517821
  have htrace : WordTrace (prefixWord ++ tailWord_517821) baseStart_517821 baseEnd_517821 := by
    simpa [prefixWord, tailWord_517821, baseEnd_517821] using wordTrace_append hprefix tailTrace_517821
  have hstable : (prefixWord ++ tailWord_517821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517821).length < 2 ^ (prefixWord ++ tailWord_517821).sum := by decide
  have hdescent : baseEnd_517821 < baseStart_517821 := by decide
  rcases family_descends (prefixWord ++ tailWord_517821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517844 : List Nat := [2, 4, 1, 3, 1, 3, 2, 2, 3]
def baseStart_517844 : Nat := 118140960795 + 517844 * 2 ^ 59
def prefixEnd_517844 : Nat := 4983230072969 + 3 ^ 40 * 517844 * 2
def baseEnd_517844 : Nat := 118179056020878740741549

theorem tailTrace_517844 : CollatzResearch.WordTrace tailWord_517844 prefixEnd_517844 118179056020878740741549 := by
  unfold tailWord_517844
  simp only [CollatzResearch.WordTrace]
  refine ⟨9443661167973551779592293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12591548223964735706123057 9443661167973551779592293)
  ·
    refine ⟨1770686468995040958673555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9443661167973551779592293 1770686468995040958673555)
    ·
      refine ⟨2656029703492561438010333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1770686468995040958673555 2656029703492561438010333)
      ·
        refine ⟨996011138809710539253875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2656029703492561438010333 996011138809710539253875)
        ·
          refine ⟨1494016708214565808880813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996011138809710539253875 1494016708214565808880813)
          ·
            refine ⟨560256265580462178330305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1494016708214565808880813 560256265580462178330305)
            ·
              refine ⟨420192199185346633747729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560256265580462178330305 420192199185346633747729)
              ·
                refine ⟨315144149389009975310797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420192199185346633747729 315144149389009975310797)
                ·
                  refine ⟨118179056020878740741549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315144149389009975310797 118179056020878740741549)
                  ·
                    rfl

theorem cell21_517844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_517844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517844 prefixEnd_517844 := by exact prefixLift 517844
  have htrace : WordTrace (prefixWord ++ tailWord_517844) baseStart_517844 baseEnd_517844 := by
    simpa [prefixWord, tailWord_517844, baseEnd_517844] using wordTrace_append hprefix tailTrace_517844
  have hstable : (prefixWord ++ tailWord_517844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517844).length < 2 ^ (prefixWord ++ tailWord_517844).sum := by decide
  have hdescent : baseEnd_517844 < baseStart_517844 := by decide
  rcases family_descends (prefixWord ++ tailWord_517844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517869 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 5]
def baseStart_517869 : Nat := 118140960795 + 517869 * 2 ^ 59
def prefixEnd_517869 : Nat := 4983230072969 + 3 ^ 40 * 517869 * 2
def baseEnd_517869 : Nat := 118184761361484252824831

theorem tailTrace_517869 : CollatzResearch.WordTrace tailWord_517869 prefixEnd_517869 118184761361484252824831 := by
  unfold tailWord_517869
  simp only [CollatzResearch.WordTrace]
  refine ⟨18888234160856532828844661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12592156107237688552563107 18888234160856532828844661)
  ·
    refine ⟨1770771952580299952704187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18888234160856532828844661 1770771952580299952704187)
    ·
      refine ⟨2656157928870449929056281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1770771952580299952704187 2656157928870449929056281)
      ·
        refine ⟨1992118446652837446792211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2656157928870449929056281 1992118446652837446792211)
        ·
          refine ⟨2988177669979256170188317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1992118446652837446792211 2988177669979256170188317)
          ·
            refine ⟨1120566626242221063820619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2988177669979256170188317 1120566626242221063820619)
            ·
              refine ⟨1680849939363331595730929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120566626242221063820619 1680849939363331595730929)
              ·
                refine ⟨1260637454522498696798197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1680849939363331595730929 1260637454522498696798197)
                ·
                  refine ⟨118184761361484252824831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1260637454522498696798197 118184761361484252824831)
                  ·
                    rfl

theorem cell21_517869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_517869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517869 prefixEnd_517869 := by exact prefixLift 517869
  have htrace : WordTrace (prefixWord ++ tailWord_517869) baseStart_517869 baseEnd_517869 := by
    simpa [prefixWord, tailWord_517869, baseEnd_517869] using wordTrace_append hprefix tailTrace_517869
  have hstable : (prefixWord ++ tailWord_517869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517869).length < 2 ^ (prefixWord ++ tailWord_517869).sum := by decide
  have hdescent : baseEnd_517869 < baseStart_517869 := by decide
  rcases family_descends (prefixWord ++ tailWord_517869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517962 : List Nat := [3, 1, 2, 1, 1, 1, 7, 2, 3]
def baseStart_517962 : Nat := 118140960795 + 517962 * 2 ^ 59
def prefixEnd_517962 : Nat := 4983230072969 + 3 ^ 40 * 517962 * 2
def baseEnd_517962 : Nat := 118205985228536757774641

theorem tailTrace_517962 : CollatzResearch.WordTrace tailWord_517962 prefixEnd_517962 118205985228536757774641 := by
  unfold tailWord_517962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4722906537379902427995035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12594417433013073141320093 4722906537379902427995035)
  ·
    refine ⟨7084359806069853641992553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4722906537379902427995035 7084359806069853641992553)
    ·
      refine ⟨5313269854552390231494415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7084359806069853641992553 5313269854552390231494415)
      ·
        refine ⟨7969904781828585347241623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5313269854552390231494415 7969904781828585347241623)
        ·
          refine ⟨11954857172742878020862435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7969904781828585347241623 11954857172742878020862435)
          ·
            refine ⟨17932285759114317031293653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11954857172742878020862435 17932285759114317031293653)
            ·
              refine ⟨420287947479241805420945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17932285759114317031293653 420287947479241805420945)
              ·
                refine ⟨315215960609431354065709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420287947479241805420945 315215960609431354065709)
                ·
                  refine ⟨118205985228536757774641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315215960609431354065709 118205985228536757774641)
                  ·
                    rfl

theorem cell21_517962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_517962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517962 prefixEnd_517962 := by exact prefixLift 517962
  have htrace : WordTrace (prefixWord ++ tailWord_517962) baseStart_517962 baseEnd_517962 := by
    simpa [prefixWord, tailWord_517962, baseEnd_517962] using wordTrace_append hprefix tailTrace_517962
  have hstable : (prefixWord ++ tailWord_517962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517962).length < 2 ^ (prefixWord ++ tailWord_517962).sum := by decide
  have hdescent : baseEnd_517962 < baseStart_517962 := by decide
  rcases family_descends (prefixWord ++ tailWord_517962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517973 : List Nat := [1, 3, 2, 2, 2, 2, 1, 8]
def baseStart_517973 : Nat := 118140960795 + 517973 * 2 ^ 59
def prefixEnd_517973 : Nat := 4983230072969 + 3 ^ 40 * 517973 * 2
def baseEnd_517973 : Nat := 39402831859467727697095

theorem tailTrace_517973 : CollatzResearch.WordTrace tailWord_517973 prefixEnd_517973 39402831859467727697095 := by
  unfold tailWord_517973
  simp only [CollatzResearch.WordTrace]
  refine ⟨18892027352479758590630573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12594684901653172393753715 18892027352479758590630573)
  ·
    refine ⟨7084510257179909471486465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18892027352479758590630573 7084510257179909471486465)
    ·
      refine ⟨5313382692884932103614849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7084510257179909471486465 5313382692884932103614849)
      ·
        refine ⟨3985037019663699077711137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5313382692884932103614849 3985037019663699077711137)
        ·
          refine ⟨2988777764747774308283353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3985037019663699077711137 2988777764747774308283353)
          ·
            refine ⟨2241583323560830731212515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2988777764747774308283353 2241583323560830731212515)
            ·
              refine ⟨3362374985341246096818773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2241583323560830731212515 3362374985341246096818773)
              ·
                refine ⟨39402831859467727697095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3362374985341246096818773 39402831859467727697095)
                ·
                  rfl

theorem cell21_517973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 8].length) (baseStart_517973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_517973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_517973 prefixEnd_517973 := by exact prefixLift 517973
  have htrace : WordTrace (prefixWord ++ tailWord_517973) baseStart_517973 baseEnd_517973 := by
    simpa [prefixWord, tailWord_517973, baseEnd_517973] using wordTrace_append hprefix tailTrace_517973
  have hstable : (prefixWord ++ tailWord_517973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517973).length < 2 ^ (prefixWord ++ tailWord_517973).sum := by decide
  have hdescent : baseEnd_517973 < baseStart_517973 := by decide
  rcases family_descends (prefixWord ++ tailWord_517973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518021 : List Nat := [1, 3, 1, 1, 3, 2, 3, 4, 3]
def baseStart_518021 : Nat := 118140960795 + 518021 * 2 ^ 59
def prefixEnd_518021 : Nat := 4983230072969 + 3 ^ 40 * 518021 * 2
def baseEnd_518021 : Nat := 118219449832365766291187

theorem tailTrace_518021 : CollatzResearch.WordTrace tailWord_518021 prefixEnd_518021 118219449832365766291187 := by
  unfold tailWord_518021
  simp only [CollatzResearch.WordTrace]
  refine ⟨18893778056305862788377917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12595852037537241858918611 18893778056305862788377917)
  ·
    refine ⟨7085166771114698545641719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18893778056305862788377917 7085166771114698545641719)
    ·
      refine ⟨10627750156672047818462579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7085166771114698545641719 10627750156672047818462579)
      ·
        refine ⟨15941625235008071727693869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10627750156672047818462579 15941625235008071727693869)
        ·
          refine ⟨5978109463128026897885201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15941625235008071727693869 5978109463128026897885201)
          ·
            refine ⟨4483582097346020173413901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5978109463128026897885201 4483582097346020173413901)
            ·
              refine ⟨1681343286504757565030213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4483582097346020173413901 1681343286504757565030213)
              ·
                refine ⟨315251866219642043443165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1681343286504757565030213 315251866219642043443165)
                ·
                  refine ⟨118219449832365766291187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315251866219642043443165 118219449832365766291187)
                  ·
                    rfl

theorem cell21_518021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_518021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518021 prefixEnd_518021 := by exact prefixLift 518021
  have htrace : WordTrace (prefixWord ++ tailWord_518021) baseStart_518021 baseEnd_518021 := by
    simpa [prefixWord, tailWord_518021, baseEnd_518021] using wordTrace_append hprefix tailTrace_518021
  have hstable : (prefixWord ++ tailWord_518021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518021).length < 2 ^ (prefixWord ++ tailWord_518021).sum := by decide
  have hdescent : baseEnd_518021 < baseStart_518021 := by decide
  rcases family_descends (prefixWord ++ tailWord_518021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518063 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 7]
def baseStart_518063 : Nat := 118140960795 + 518063 * 2 ^ 59
def prefixEnd_518063 : Nat := 4983230072969 + 3 ^ 40 * 518063 * 2
def baseEnd_518063 : Nat := 118229034804583026591101

theorem tailTrace_518063 : CollatzResearch.WordTrace tailWord_518063 prefixEnd_518063 118229034804583026591101 := by
  unfold tailWord_518063
  simp only [CollatzResearch.WordTrace]
  refine ⟨18895309922153703961406843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12596873281435802640937895 18895309922153703961406843)
  ·
    refine ⟨28342964883230555942110265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18895309922153703961406843 28342964883230555942110265)
    ·
      refine ⟨21257223662422916956582699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28342964883230555942110265 21257223662422916956582699)
      ·
        refine ⟨31885835493634375434874049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21257223662422916956582699 31885835493634375434874049)
        ·
          refine ⟨23914376620225781576155537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31885835493634375434874049 23914376620225781576155537)
          ·
            refine ⟨17935782465169336182116653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23914376620225781576155537 17935782465169336182116653)
            ·
              refine ⟨6725918424438501068293745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17935782465169336182116653 6725918424438501068293745)
              ·
                refine ⟨5044438818328875801220309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6725918424438501068293745 5044438818328875801220309)
                ·
                  refine ⟨118229034804583026591101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5044438818328875801220309 118229034804583026591101)
                  ·
                    rfl

theorem cell21_518063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 7].length) (baseStart_518063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518063 prefixEnd_518063 := by exact prefixLift 518063
  have htrace : WordTrace (prefixWord ++ tailWord_518063) baseStart_518063 baseEnd_518063 := by
    simpa [prefixWord, tailWord_518063, baseEnd_518063] using wordTrace_append hprefix tailTrace_518063
  have hstable : (prefixWord ++ tailWord_518063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518063).length < 2 ^ (prefixWord ++ tailWord_518063).sum := by decide
  have hdescent : baseEnd_518063 < baseStart_518063 := by decide
  rcases family_descends (prefixWord ++ tailWord_518063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518080 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 5]
def baseStart_518080 : Nat := 118140960795 + 518080 * 2 ^ 59
def prefixEnd_518080 : Nat := 4983230072969 + 3 ^ 40 * 518080 * 2
def baseEnd_518080 : Nat := 118232914436194774807733

theorem tailTrace_518080 : CollatzResearch.WordTrace tailWord_518080 prefixEnd_518080 118232914436194774807733 := by
  unfold tailWord_518080
  simp only [CollatzResearch.WordTrace]
  refine ⟨9447964981546057932387847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12597286642061410576517129 9447964981546057932387847)
  ·
    refine ⟨14171947472319086898581771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9447964981546057932387847 14171947472319086898581771)
    ·
      refine ⟨21257921208478630347872657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14171947472319086898581771 21257921208478630347872657)
      ·
        refine ⟨15943440906358972760904493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21257921208478630347872657 15943440906358972760904493)
        ·
          refine ⟨5978790339884614785339185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15943440906358972760904493 5978790339884614785339185)
          ·
            refine ⟨4484092754913461089004389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5978790339884614785339185 4484092754913461089004389)
            ·
              refine ⟨840767391546273954188323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4484092754913461089004389 840767391546273954188323)
              ·
                refine ⟨1261151087319410931282485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840767391546273954188323 1261151087319410931282485)
                ·
                  refine ⟨118232914436194774807733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1261151087319410931282485 118232914436194774807733)
                  ·
                    rfl

theorem cell21_518080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_518080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518080 prefixEnd_518080 := by exact prefixLift 518080
  have htrace : WordTrace (prefixWord ++ tailWord_518080) baseStart_518080 baseEnd_518080 := by
    simpa [prefixWord, tailWord_518080, baseEnd_518080] using wordTrace_append hprefix tailTrace_518080
  have hstable : (prefixWord ++ tailWord_518080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518080).length < 2 ^ (prefixWord ++ tailWord_518080).sum := by decide
  have hdescent : baseEnd_518080 < baseStart_518080 := by decide
  rcases family_descends (prefixWord ++ tailWord_518080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518142 : List Nat := [4, 2, 2, 2, 1, 1, 1, 8]
def baseStart_518142 : Nat := 118140960795 + 518142 * 2 ^ 59
def prefixEnd_518142 : Nat := 4983230072969 + 3 ^ 40 * 518142 * 2
def baseEnd_518142 : Nat := 39415687893632148258091

theorem tailTrace_518142 : CollatzResearch.WordTrace tailWord_518142 prefixEnd_518142 39415687893632148258091 := by
  unfold tailWord_518142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2362273911108437556691585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12598794192578333635688453 2362273911108437556691585)
  ·
    refine ⟨1771705433331328167518689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2362273911108437556691585 1771705433331328167518689)
    ·
      refine ⟨1328779074998496125639017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1771705433331328167518689 1328779074998496125639017)
      ·
        refine ⟨996584306248872094229263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1328779074998496125639017 996584306248872094229263)
        ·
          refine ⟨1494876459373308141343895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996584306248872094229263 1494876459373308141343895)
          ·
            refine ⟨2242314689059962212015843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494876459373308141343895 2242314689059962212015843)
            ·
              refine ⟨3363472033589943318023765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2242314689059962212015843 3363472033589943318023765)
              ·
                refine ⟨39415687893632148258091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3363472033589943318023765 39415687893632148258091)
                ·
                  rfl

theorem cell21_518142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_518142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518142 prefixEnd_518142 := by exact prefixLift 518142
  have htrace : WordTrace (prefixWord ++ tailWord_518142) baseStart_518142 baseEnd_518142 := by
    simpa [prefixWord, tailWord_518142, baseEnd_518142] using wordTrace_append hprefix tailTrace_518142
  have hstable : (prefixWord ++ tailWord_518142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518142).length < 2 ^ (prefixWord ++ tailWord_518142).sum := by decide
  have hdescent : baseEnd_518142 < baseStart_518142 := by decide
  rcases family_descends (prefixWord ++ tailWord_518142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518190 : List Nat := [4, 1, 3, 1, 1, 3, 1, 4, 3]
def baseStart_518190 : Nat := 118140960795 + 518190 * 2 ^ 59
def prefixEnd_518190 : Nat := 4983230072969 + 3 ^ 40 * 518190 * 2
def baseEnd_518190 : Nat := 118258017934859027974175

theorem tailTrace_518190 : CollatzResearch.WordTrace tailWord_518190 prefixEnd_518190 118258017934859027974175 := by
  unfold tailWord_518190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2362492749086700581410003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12599961328462403100853349 2362492749086700581410003)
  ·
    refine ⟨3543739123630050872115005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2362492749086700581410003 3543739123630050872115005)
    ·
      refine ⟨1328902171361269077043127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3543739123630050872115005 1328902171361269077043127)
      ·
        refine ⟨1993353257041903615564691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1328902171361269077043127 1993353257041903615564691)
        ·
          refine ⟨2990029885562855423347037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1993353257041903615564691 2990029885562855423347037)
          ·
            refine ⟨1121261207086070783755139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2990029885562855423347037 1121261207086070783755139)
            ·
              refine ⟨1681891810629106175632709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121261207086070783755139 1681891810629106175632709)
              ·
                refine ⟨315354714492957407931133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1681891810629106175632709 315354714492957407931133)
                ·
                  refine ⟨118258017934859027974175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315354714492957407931133 118258017934859027974175)
                  ·
                    rfl

theorem cell21_518190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_518190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518190 prefixEnd_518190 := by exact prefixLift 518190
  have htrace : WordTrace (prefixWord ++ tailWord_518190) baseStart_518190 baseEnd_518190 := by
    simpa [prefixWord, tailWord_518190, baseEnd_518190] using wordTrace_append hprefix tailTrace_518190
  have hstable : (prefixWord ++ tailWord_518190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518190).length < 2 ^ (prefixWord ++ tailWord_518190).sum := by decide
  have hdescent : baseEnd_518190 < baseStart_518190 := by decide
  rcases family_descends (prefixWord ++ tailWord_518190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518277 : List Nat := [1, 3, 1, 1, 5, 2, 1, 7]
def baseStart_518277 : Nat := 118140960795 + 518277 * 2 ^ 59
def prefixEnd_518277 : Nat := 4983230072969 + 3 ^ 40 * 518277 * 2
def baseEnd_518277 : Nat := 39425957506722070007999

theorem tailTrace_518277 : CollatzResearch.WordTrace tailWord_518277 prefixEnd_518277 39425957506722070007999 := by
  unfold tailWord_518277
  simp only [CollatzResearch.WordTrace]
  refine ⟨18903115143378418509697085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12602076762252279006464723 18903115143378418509697085)
  ·
    refine ⟨7088668178766906941136407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18903115143378418509697085 7088668178766906941136407)
    ·
      refine ⟨10633002268150360411704611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7088668178766906941136407 10633002268150360411704611)
      ·
        refine ⟨15949503402225540617556917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10633002268150360411704611 15949503402225540617556917)
        ·
          refine ⟨1495265943958644432895961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15949503402225540617556917 1495265943958644432895961)
          ·
            refine ⟨1121449457968983324671971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1495265943958644432895961 1121449457968983324671971)
            ·
              refine ⟨1682174186953474987007957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121449457968983324671971 1682174186953474987007957)
              ·
                refine ⟨39425957506722070007999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1682174186953474987007957 39425957506722070007999)
                ·
                  rfl

theorem cell21_518277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 7].length) (baseStart_518277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518277 prefixEnd_518277 := by exact prefixLift 518277
  have htrace : WordTrace (prefixWord ++ tailWord_518277) baseStart_518277 baseEnd_518277 := by
    simpa [prefixWord, tailWord_518277, baseEnd_518277] using wordTrace_append hprefix tailTrace_518277
  have hstable : (prefixWord ++ tailWord_518277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518277).length < 2 ^ (prefixWord ++ tailWord_518277).sum := by decide
  have hdescent : baseEnd_518277 < baseStart_518277 := by decide
  rcases family_descends (prefixWord ++ tailWord_518277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518314 : List Nat := [3, 1, 5, 1, 2, 2, 2, 1, 4]
def baseStart_518314 : Nat := 118140960795 + 518314 * 2 ^ 59
def prefixEnd_518314 : Nat := 4983230072969 + 3 ^ 40 * 518314 * 2
def baseEnd_518314 : Nat := 118286316424262367907255

theorem tailTrace_518314 : CollatzResearch.WordTrace tailWord_518314 prefixEnd_518314 118286316424262367907255 := by
  unfold tailWord_518314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4726116161061093457198499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12602976429496249219195997 4726116161061093457198499)
  ·
    refine ⟨7089174241591640185797749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4726116161061093457198499 7089174241591640185797749)
    ·
      refine ⟨664610085149216267418539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7089174241591640185797749 664610085149216267418539)
      ·
        refine ⟨996915127723824401127809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664610085149216267418539 996915127723824401127809)
        ·
          refine ⟨747686345792868300845857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996915127723824401127809 747686345792868300845857)
          ·
            refine ⟨560764759344651225634393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747686345792868300845857 560764759344651225634393)
            ·
              refine ⟨420573569508488419225795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560764759344651225634393 420573569508488419225795)
              ·
                refine ⟨630860354262732628838693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420573569508488419225795 630860354262732628838693)
                ·
                  refine ⟨118286316424262367907255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 630860354262732628838693 118286316424262367907255)
                  ·
                    rfl

theorem cell21_518314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_518314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518314 prefixEnd_518314 := by exact prefixLift 518314
  have htrace : WordTrace (prefixWord ++ tailWord_518314) baseStart_518314 baseEnd_518314 := by
    simpa [prefixWord, tailWord_518314, baseEnd_518314] using wordTrace_append hprefix tailTrace_518314
  have hstable : (prefixWord ++ tailWord_518314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518314).length < 2 ^ (prefixWord ++ tailWord_518314).sum := by decide
  have hdescent : baseEnd_518314 < baseStart_518314 := by decide
  rcases family_descends (prefixWord ++ tailWord_518314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518367 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 5]
def baseStart_518367 : Nat := 118140960795 + 518367 * 2 ^ 59
def prefixEnd_518367 : Nat := 4983230072969 + 3 ^ 40 * 518367 * 2
def baseEnd_518367 : Nat := 118298411746346053523813

theorem tailTrace_518367 : CollatzResearch.WordTrace tailWord_518367 prefixEnd_518367 118298411746346053523813 := by
  unfold tailWord_518367
  simp only [CollatzResearch.WordTrace]
  refine ⟨18906397713052363880473355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12604265142034909253648903 18906397713052363880473355)
  ·
    refine ⟨28359596569578545820710033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18906397713052363880473355 28359596569578545820710033)
    ·
      refine ⟨21269697427183909365532525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28359596569578545820710033 21269697427183909365532525)
      ·
        refine ⟨7976136535193966012074697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21269697427183909365532525 7976136535193966012074697)
        ·
          refine ⟨5982102401395474509056023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7976136535193966012074697 5982102401395474509056023)
          ·
            refine ⟨8973153602093211763584035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982102401395474509056023 8973153602093211763584035)
            ·
              refine ⟨13459730403139817645376053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8973153602093211763584035 13459730403139817645376053)
              ·
                refine ⟨1261849725294357904254005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13459730403139817645376053 1261849725294357904254005)
                ·
                  refine ⟨118298411746346053523813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1261849725294357904254005 118298411746346053523813)
                  ·
                    rfl

theorem cell21_518367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 5].length) (baseStart_518367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518367 prefixEnd_518367 := by exact prefixLift 518367
  have htrace : WordTrace (prefixWord ++ tailWord_518367) baseStart_518367 baseEnd_518367 := by
    simpa [prefixWord, tailWord_518367, baseEnd_518367] using wordTrace_append hprefix tailTrace_518367
  have hstable : (prefixWord ++ tailWord_518367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518367).length < 2 ^ (prefixWord ++ tailWord_518367).sum := by decide
  have hdescent : baseEnd_518367 < baseStart_518367 := by decide
  rcases family_descends (prefixWord ++ tailWord_518367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518401 : List Nat := [1, 2, 4, 1, 1, 2, 4, 3, 3]
def baseStart_518401 : Nat := 118140960795 + 518401 * 2 ^ 59
def prefixEnd_518401 : Nat := 4983230072969 + 3 ^ 40 * 518401 * 2
def baseEnd_518401 : Nat := 118306171009569549957077

theorem tailTrace_518401 : CollatzResearch.WordTrace tailWord_518401 prefixEnd_518401 118306171009569549957077 := by
  unfold tailWord_518401
  simp only [CollatzResearch.WordTrace]
  refine ⟨18907637794929187687211057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12605091863286125124807371 18907637794929187687211057)
  ·
    refine ⟨14180728346196890765408293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18907637794929187687211057 14180728346196890765408293)
    ·
      refine ⟨2658886564911917018514055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14180728346196890765408293 2658886564911917018514055)
      ·
        refine ⟨3988329847367875527771083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2658886564911917018514055 3988329847367875527771083)
        ·
          refine ⟨5982494771051813291656625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3988329847367875527771083 5982494771051813291656625)
          ·
            refine ⟨4486871078288859968742469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5982494771051813291656625 4486871078288859968742469)
            ·
              refine ⟨841288327179161244139213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4486871078288859968742469 841288327179161244139213)
              ·
                refine ⟨315483122692185466552205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 841288327179161244139213 315483122692185466552205)
                ·
                  refine ⟨118306171009569549957077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315483122692185466552205 118306171009569549957077)
                  ·
                    rfl

theorem cell21_518401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 3].length) (baseStart_518401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518401 prefixEnd_518401 := by exact prefixLift 518401
  have htrace : WordTrace (prefixWord ++ tailWord_518401) baseStart_518401 baseEnd_518401 := by
    simpa [prefixWord, tailWord_518401, baseEnd_518401] using wordTrace_append hprefix tailTrace_518401
  have hstable : (prefixWord ++ tailWord_518401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518401).length < 2 ^ (prefixWord ++ tailWord_518401).sum := by decide
  have hdescent : baseEnd_518401 < baseStart_518401 := by decide
  rcases family_descends (prefixWord ++ tailWord_518401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518412 : List Nat := [2, 2, 1, 2, 2, 2, 10]
def baseStart_518412 : Nat := 118140960795 + 518412 * 2 ^ 59
def prefixEnd_518412 : Nat := 4983230072969 + 3 ^ 40 * 518412 * 2
def baseEnd_518412 : Nat := 13145409039937330585969

theorem tailTrace_518412 : CollatzResearch.WordTrace tailWord_518412 prefixEnd_518412 13145409039937330585969 := by
  unfold tailWord_518412
  simp only [CollatzResearch.WordTrace]
  refine ⟨9454019498944668282930745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12605359331926224377240993 9454019498944668282930745)
  ·
    refine ⟨7090514624208501212198059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9454019498944668282930745 7090514624208501212198059)
    ·
      refine ⟨10635771936312751818297089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7090514624208501212198059 10635771936312751818297089)
      ·
        refine ⟨7976828952234563863722817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10635771936312751818297089 7976828952234563863722817)
        ·
          refine ⟨5982621714175922897792113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7976828952234563863722817 5982621714175922897792113)
          ·
            refine ⟨4486966285631942173344085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5982621714175922897792113 4486966285631942173344085)
            ·
              refine ⟨13145409039937330585969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4486966285631942173344085 13145409039937330585969)
              ·
                rfl

theorem cell21_518412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 10].length) (baseStart_518412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518412 prefixEnd_518412 := by exact prefixLift 518412
  have htrace : WordTrace (prefixWord ++ tailWord_518412) baseStart_518412 baseEnd_518412 := by
    simpa [prefixWord, tailWord_518412, baseEnd_518412] using wordTrace_append hprefix tailTrace_518412
  have hstable : (prefixWord ++ tailWord_518412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518412).length < 2 ^ (prefixWord ++ tailWord_518412).sum := by decide
  have hdescent : baseEnd_518412 < baseStart_518412 := by decide
  rcases family_descends (prefixWord ++ tailWord_518412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518432 : List Nat := [2, 1, 1, 5, 2, 2, 3, 1, 4]
def baseStart_518432 : Nat := 118140960795 + 518432 * 2 ^ 59
def prefixEnd_518432 : Nat := 4983230072969 + 3 ^ 40 * 518432 * 2
def baseEnd_518432 : Nat := 118313245631920384940347

theorem tailTrace_518432 : CollatzResearch.WordTrace tailWord_518432 prefixEnd_518432 118313245631920384940347 := by
  unfold tailWord_518432
  simp only [CollatzResearch.WordTrace]
  refine ⟨9454384228908439990794775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12605845638544586654393033 9454384228908439990794775)
  ·
    refine ⟨14181576343362659986192163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9454384228908439990794775 14181576343362659986192163)
    ·
      refine ⟨21272364515043989979288245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14181576343362659986192163 21272364515043989979288245)
      ·
        refine ⟨1994284173285374060558273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21272364515043989979288245 1994284173285374060558273)
        ·
          refine ⟨1495713129964030545418705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1994284173285374060558273 1495713129964030545418705)
          ·
            refine ⟨1121784847473022909064029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1495713129964030545418705 1121784847473022909064029)
            ·
              refine ⟨420669317802383590899011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1121784847473022909064029 420669317802383590899011)
              ·
                refine ⟨631003976703575386348517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420669317802383590899011 631003976703575386348517)
                ·
                  refine ⟨118313245631920384940347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 631003976703575386348517 118313245631920384940347)
                  ·
                    rfl

theorem cell21_518432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 4].length) (baseStart_518432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518432 prefixEnd_518432 := by exact prefixLift 518432
  have htrace : WordTrace (prefixWord ++ tailWord_518432) baseStart_518432 baseEnd_518432 := by
    simpa [prefixWord, tailWord_518432, baseEnd_518432] using wordTrace_append hprefix tailTrace_518432
  have hstable : (prefixWord ++ tailWord_518432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518432).length < 2 ^ (prefixWord ++ tailWord_518432).sum := by decide
  have hdescent : baseEnd_518432 < baseStart_518432 := by decide
  rcases family_descends (prefixWord ++ tailWord_518432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518564 : List Nat := [2, 3, 1, 2, 1, 1, 2, 9]
def baseStart_518564 : Nat := 118140960795 + 518564 * 2 ^ 59
def prefixEnd_518564 : Nat := 4983230072969 + 3 ^ 40 * 518564 * 2
def baseEnd_518564 : Nat := 39447789943439162913359

theorem tailTrace_518564 : CollatzResearch.WordTrace tailWord_518564 prefixEnd_518564 39447789943439162913359 := by
  unfold tailWord_518564
  simp only [CollatzResearch.WordTrace]
  refine ⟨9456791446669333262697373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12609055262225777683596497 9456791446669333262697373)
  ·
    refine ⟨3546296792500999973511515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9456791446669333262697373 3546296792500999973511515)
    ·
      refine ⟨5319445188751499960267273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3546296792500999973511515 5319445188751499960267273)
      ·
        refine ⟨3989583891563624970200455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5319445188751499960267273 3989583891563624970200455)
        ·
          refine ⟨5984375837345437455300683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3989583891563624970200455 5984375837345437455300683)
          ·
            refine ⟨8976563756018156182951025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5984375837345437455300683 8976563756018156182951025)
            ·
              refine ⟨6732422817013617137213269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8976563756018156182951025 6732422817013617137213269)
              ·
                refine ⟨39447789943439162913359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6732422817013617137213269 39447789943439162913359)
                ·
                  rfl

theorem cell21_518564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 9].length) (baseStart_518564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518564 prefixEnd_518564 := by exact prefixLift 518564
  have htrace : WordTrace (prefixWord ++ tailWord_518564) baseStart_518564 baseEnd_518564 := by
    simpa [prefixWord, tailWord_518564, baseEnd_518564] using wordTrace_append hprefix tailTrace_518564
  have hstable : (prefixWord ++ tailWord_518564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518564).length < 2 ^ (prefixWord ++ tailWord_518564).sum := by decide
  have hdescent : baseEnd_518564 < baseStart_518564 := by decide
  rcases family_descends (prefixWord ++ tailWord_518564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518581 : List Nat := [1, 3, 3, 2, 3, 1, 8]
def baseStart_518581 : Nat := 118140960795 + 518581 * 2 ^ 59
def prefixEnd_518581 : Nat := 4983230072969 + 3 ^ 40 * 518581 * 2
def baseEnd_518581 : Nat := 13149694384658804106301

theorem tailTrace_518581 : CollatzResearch.WordTrace tailWord_518581 prefixEnd_518581 13149694384658804106301 := by
  unfold tailWord_518581
  simp only [CollatzResearch.WordTrace]
  refine ⟨18914202934277078428763597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12609468622851385619175731 18914202934277078428763597)
  ·
    refine ⟨7092826100353904410786349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18914202934277078428763597 7092826100353904410786349)
    ·
      refine ⟨2659809787632714154044881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7092826100353904410786349 2659809787632714154044881)
      ·
        refine ⟨1994857340724535615533661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2659809787632714154044881 1994857340724535615533661)
        ·
          refine ⟨748071502771700855825123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1994857340724535615533661 748071502771700855825123)
          ·
            refine ⟨1122107254157551283737685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748071502771700855825123 1122107254157551283737685)
            ·
              refine ⟨13149694384658804106301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1122107254157551283737685 13149694384658804106301)
              ·
                rfl

theorem cell21_518581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 8].length) (baseStart_518581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518581 prefixEnd_518581 := by exact prefixLift 518581
  have htrace : WordTrace (prefixWord ++ tailWord_518581) baseStart_518581 baseEnd_518581 := by
    simpa [prefixWord, tailWord_518581, baseEnd_518581] using wordTrace_append hprefix tailTrace_518581
  have hstable : (prefixWord ++ tailWord_518581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518581).length < 2 ^ (prefixWord ++ tailWord_518581).sum := by decide
  have hdescent : baseEnd_518581 < baseStart_518581 := by decide
  rcases family_descends (prefixWord ++ tailWord_518581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518612 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 5]
def baseStart_518612 : Nat := 118140960795 + 518612 * 2 ^ 59
def prefixEnd_518612 : Nat := 4983230072969 + 3 ^ 40 * 518612 * 2
def baseEnd_518612 : Nat := 118354324084280071939979

theorem tailTrace_518612 : CollatzResearch.WordTrace tailWord_518612 prefixEnd_518612 118354324084280071939979 := by
  unfold tailWord_518612
  simp only [CollatzResearch.WordTrace]
  refine ⟨9457666798582385361571045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12610222398109847148761393 9457666798582385361571045)
  ·
    refine ⟨1773312524734197255294571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9457666798582385361571045 1773312524734197255294571)
    ·
      refine ⟨2659968787101295882941857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1773312524734197255294571 2659968787101295882941857)
      ·
        refine ⟨1994976590325971912206393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2659968787101295882941857 1994976590325971912206393)
        ·
          refine ⟨1496232442744478934154795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1994976590325971912206393 1496232442744478934154795)
          ·
            refine ⟨2244348664116718401232193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496232442744478934154795 2244348664116718401232193)
            ·
              refine ⟨1683261498087538800924145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2244348664116718401232193 1683261498087538800924145)
              ·
                refine ⟨1262446123565654100693109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1683261498087538800924145 1262446123565654100693109)
                ·
                  refine ⟨118354324084280071939979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1262446123565654100693109 118354324084280071939979)
                  ·
                    rfl

theorem cell21_518612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_518612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518612 prefixEnd_518612 := by exact prefixLift 518612
  have htrace : WordTrace (prefixWord ++ tailWord_518612) baseStart_518612 baseEnd_518612 := by
    simpa [prefixWord, tailWord_518612, baseEnd_518612] using wordTrace_append hprefix tailTrace_518612
  have hstable : (prefixWord ++ tailWord_518612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518612).length < 2 ^ (prefixWord ++ tailWord_518612).sum := by decide
  have hdescent : baseEnd_518612 < baseStart_518612 := by decide
  rcases family_descends (prefixWord ++ tailWord_518612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518646 : List Nat := [5, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_518646 : Nat := 118140960795 + 518646 * 2 ^ 59
def prefixEnd_518646 : Nat := 4983230072969 + 3 ^ 40 * 518646 * 2
def baseEnd_518646 : Nat := 118362083347503568373243

theorem tailTrace_518646 : CollatzResearch.WordTrace tailWord_518646 prefixEnd_518646 118362083347503568373243 := by
  unfold tailWord_518646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1182285854940099658117487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12611049119361063019919861 1182285854940099658117487)
  ·
    refine ⟨1773428782410149487176231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1182285854940099658117487 1773428782410149487176231)
    ·
      refine ⟨2660143173615224230764347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1773428782410149487176231 2660143173615224230764347)
      ·
        refine ⟨3990214760422836346146521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2660143173615224230764347 3990214760422836346146521)
        ·
          refine ⟨2992661070317127259609891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3990214760422836346146521 2992661070317127259609891)
          ·
            refine ⟨4488991605475690889414837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2992661070317127259609891 4488991605475690889414837)
            ·
              refine ⟨420842963013346020882641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4488991605475690889414837 420842963013346020882641)
              ·
                refine ⟨315632222260009515661981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420842963013346020882641 315632222260009515661981)
                ·
                  refine ⟨118362083347503568373243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315632222260009515661981 118362083347503568373243)
                  ·
                    rfl

theorem cell21_518646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_518646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518646 prefixEnd_518646 := by exact prefixLift 518646
  have htrace : WordTrace (prefixWord ++ tailWord_518646) baseStart_518646 baseEnd_518646 := by
    simpa [prefixWord, tailWord_518646, baseEnd_518646] using wordTrace_append hprefix tailTrace_518646
  have hstable : (prefixWord ++ tailWord_518646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518646).length < 2 ^ (prefixWord ++ tailWord_518646).sum := by decide
  have hdescent : baseEnd_518646 < baseStart_518646 := by decide
  rcases family_descends (prefixWord ++ tailWord_518646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518657 : List Nat := [1, 2, 4, 1, 3, 2, 2, 6]
def baseStart_518657 : Nat := 118140960795 + 518657 * 2 ^ 59
def prefixEnd_518657 : Nat := 4983230072969 + 3 ^ 40 * 518657 * 2
def baseEnd_518657 : Nat := 39454864565789997896629

theorem tailTrace_518657 : CollatzResearch.WordTrace tailWord_518657 prefixEnd_518657 39454864565789997896629 := by
  unfold tailWord_518657
  simp only [CollatzResearch.WordTrace]
  refine ⟨18916974882001743408530225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12611316588001162272353483 18916974882001743408530225)
  ·
    refine ⟨14187731161501307556397669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18916974882001743408530225 14187731161501307556397669)
    ·
      refine ⟨2660199592781495166824563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14187731161501307556397669 2660199592781495166824563)
      ·
        refine ⟨3990299389172242750236845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2660199592781495166824563 3990299389172242750236845)
        ·
          refine ⟨1496362270939591031338817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3990299389172242750236845 1496362270939591031338817)
          ·
            refine ⟨1122271703204693273504113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1496362270939591031338817 1122271703204693273504113)
            ·
              refine ⟨841703777403519955128085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1122271703204693273504113 841703777403519955128085)
              ·
                refine ⟨39454864565789997896629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 841703777403519955128085 39454864565789997896629)
                ·
                  rfl

theorem cell21_518657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 6].length) (baseStart_518657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518657 prefixEnd_518657 := by exact prefixLift 518657
  have htrace : WordTrace (prefixWord ++ tailWord_518657) baseStart_518657 baseEnd_518657 := by
    simpa [prefixWord, tailWord_518657, baseEnd_518657] using wordTrace_append hprefix tailTrace_518657
  have hstable : (prefixWord ++ tailWord_518657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518657).length < 2 ^ (prefixWord ++ tailWord_518657).sum := by decide
  have hdescent : baseEnd_518657 < baseStart_518657 := by decide
  rcases family_descends (prefixWord ++ tailWord_518657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518660 : List Nat := [2, 3, 2, 3, 1, 1, 4, 1, 4]
def baseStart_518660 : Nat := 118140960795 + 518660 * 2 ^ 59
def prefixEnd_518660 : Nat := 4983230072969 + 3 ^ 40 * 518660 * 2
def baseEnd_518660 : Nat := 118365278338242655139881

theorem tailTrace_518660 : CollatzResearch.WordTrace tailWord_518660 prefixEnd_518660 118365278338242655139881 := by
  unfold tailWord_518660
  simp only [CollatzResearch.WordTrace]
  refine ⟨9458542150495437460444717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12611389533993916613926289 9458542150495437460444717)
  ·
    refine ⟨3546953306435789047666769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9458542150495437460444717 3546953306435789047666769)
    ·
      refine ⟨2660214979826841785750077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3546953306435789047666769 2660214979826841785750077)
      ·
        refine ⟨997580617435065669656279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2660214979826841785750077 997580617435065669656279)
        ·
          refine ⟨1496370926152598504484419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997580617435065669656279 1496370926152598504484419)
          ·
            refine ⟨2244556389228897756726629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496370926152598504484419 2244556389228897756726629)
            ·
              refine ⟨420854322980418329386243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2244556389228897756726629 420854322980418329386243)
              ·
                refine ⟨631281484470627494079365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420854322980418329386243 631281484470627494079365)
                ·
                  refine ⟨118365278338242655139881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 631281484470627494079365 118365278338242655139881)
                  ·
                    rfl

theorem cell21_518660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_518660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518660 prefixEnd_518660 := by exact prefixLift 518660
  have htrace : WordTrace (prefixWord ++ tailWord_518660) baseStart_518660 baseEnd_518660 := by
    simpa [prefixWord, tailWord_518660, baseEnd_518660] using wordTrace_append hprefix tailTrace_518660
  have hstable : (prefixWord ++ tailWord_518660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518660).length < 2 ^ (prefixWord ++ tailWord_518660).sum := by decide
  have hdescent : baseEnd_518660 < baseStart_518660 := by decide
  rcases family_descends (prefixWord ++ tailWord_518660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518705 : List Nat := [1, 2, 2, 3, 1, 1, 6, 2, 3]
def baseStart_518705 : Nat := 118140960795 + 518705 * 2 ^ 59
def prefixEnd_518705 : Nat := 4983230072969 + 3 ^ 40 * 518705 * 2
def baseEnd_518705 : Nat := 118375547951332576889789

theorem tailTrace_518705 : CollatzResearch.WordTrace tailWord_518705 prefixEnd_518705 118375547951332576889789 := by
  unfold tailWord_518705
  simp only [CollatzResearch.WordTrace]
  refine ⟨18918725585827847606277569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12612483723885231737518379 18918725585827847606277569)
  ·
    refine ⟨14189044189370885704708177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18918725585827847606277569 14189044189370885704708177)
    ·
      refine ⟨10641783142028164278531133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14189044189370885704708177 10641783142028164278531133)
      ·
        refine ⟨3990668678260561604449175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10641783142028164278531133 3990668678260561604449175)
        ·
          refine ⟨5986003017390842406673763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3990668678260561604449175 5986003017390842406673763)
          ·
            refine ⟨8979004526086263610010645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5986003017390842406673763 8979004526086263610010645)
            ·
              refine ⟨420890837160293606719249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8979004526086263610010645 420890837160293606719249)
              ·
                refine ⟨315668127870220205039437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420890837160293606719249 315668127870220205039437)
                ·
                  refine ⟨118375547951332576889789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315668127870220205039437 118375547951332576889789)
                  ·
                    rfl

theorem cell21_518705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 3].length) (baseStart_518705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518705 prefixEnd_518705 := by exact prefixLift 518705
  have htrace : WordTrace (prefixWord ++ tailWord_518705) baseStart_518705 baseEnd_518705 := by
    simpa [prefixWord, tailWord_518705, baseEnd_518705] using wordTrace_append hprefix tailTrace_518705
  have hstable : (prefixWord ++ tailWord_518705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518705).length < 2 ^ (prefixWord ++ tailWord_518705).sum := by decide
  have hdescent : baseEnd_518705 < baseStart_518705 := by decide
  rcases family_descends (prefixWord ++ tailWord_518705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518708 : List Nat := [2, 5, 1, 3, 2, 1, 1, 6]
def baseStart_518708 : Nat := 118140960795 + 518708 * 2 ^ 59
def prefixEnd_518708 : Nat := 4983230072969 + 3 ^ 40 * 518708 * 2
def baseEnd_518708 : Nat := 39458744197401746113261

theorem tailTrace_518708 : CollatzResearch.WordTrace tailWord_518708 prefixEnd_518708 39458744197401746113261 := by
  unfold tailWord_518708
  simp only [CollatzResearch.WordTrace]
  refine ⟨9459417502408489559318389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12612556669877986079091185 9459417502408489559318389)
  ·
    refine ⟨886820390850795896186099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9459417502408489559318389 886820390850795896186099)
    ·
      refine ⟨1330230586276193844279149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 886820390850795896186099 1330230586276193844279149)
      ·
        refine ⟨498836469853572691604681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1330230586276193844279149 498836469853572691604681)
        ·
          refine ⟨374127352390179518703511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498836469853572691604681 374127352390179518703511)
          ·
            refine ⟨561191028585269278055267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374127352390179518703511 561191028585269278055267)
            ·
              refine ⟨841786542877903917082901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561191028585269278055267 841786542877903917082901)
              ·
                refine ⟨39458744197401746113261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 841786542877903917082901 39458744197401746113261)
                ·
                  rfl

theorem cell21_518708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 6].length) (baseStart_518708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518708 prefixEnd_518708 := by exact prefixLift 518708
  have htrace : WordTrace (prefixWord ++ tailWord_518708) baseStart_518708 baseEnd_518708 := by
    simpa [prefixWord, tailWord_518708, baseEnd_518708] using wordTrace_append hprefix tailTrace_518708
  have hstable : (prefixWord ++ tailWord_518708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518708).length < 2 ^ (prefixWord ++ tailWord_518708).sum := by decide
  have hdescent : baseEnd_518708 < baseStart_518708 := by decide
  rcases family_descends (prefixWord ++ tailWord_518708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518764 : List Nat := [2, 2, 1, 1, 3, 1, 4, 4, 3]
def baseStart_518764 : Nat := 118140960795 + 518764 * 2 ^ 59
def prefixEnd_518764 : Nat := 4983230072969 + 3 ^ 40 * 518764 * 2
def baseEnd_518764 : Nat := 118389012555161585406335

theorem tailTrace_518764 : CollatzResearch.WordTrace tailWord_518764 prefixEnd_518764 118389012555161585406335 := by
  unfold tailWord_518764
  simp only [CollatzResearch.WordTrace]
  refine ⟨9460438746307050341337673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12613918328409400455116897 9460438746307050341337673)
  ·
    refine ⟨7095329059730287756003255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9460438746307050341337673 7095329059730287756003255)
    ·
      refine ⟨10642993589595431634004883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7095329059730287756003255 10642993589595431634004883)
      ·
        refine ⟨15964490384393147451007325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10642993589595431634004883 15964490384393147451007325)
        ·
          refine ⟨5986683894147430294127747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15964490384393147451007325 5986683894147430294127747)
          ·
            refine ⟨8980025841221145441191621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5986683894147430294127747 8980025841221145441191621)
            ·
              refine ⟨1683754845228964770223429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8980025841221145441191621 1683754845228964770223429)
              ·
                refine ⟨315704033480430894416893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1683754845228964770223429 315704033480430894416893)
                ·
                  refine ⟨118389012555161585406335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315704033480430894416893 118389012555161585406335)
                  ·
                    rfl

theorem cell21_518764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_518764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518764 prefixEnd_518764 := by exact prefixLift 518764
  have htrace : WordTrace (prefixWord ++ tailWord_518764) baseStart_518764 baseEnd_518764 := by
    simpa [prefixWord, tailWord_518764, baseEnd_518764] using wordTrace_append hprefix tailTrace_518764
  have hstable : (prefixWord ++ tailWord_518764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518764).length < 2 ^ (prefixWord ++ tailWord_518764).sum := by decide
  have hdescent : baseEnd_518764 < baseStart_518764 := by decide
  rcases family_descends (prefixWord ++ tailWord_518764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518868 : List Nat := [2, 4, 1, 3, 11]
def baseStart_518868 : Nat := 118140960795 + 518868 * 2 ^ 59
def prefixEnd_518868 : Nat := 4983230072969 + 3 ^ 40 * 518868 * 2
def baseEnd_518868 : Nat := 1461885762618277971269

theorem tailTrace_518868 : CollatzResearch.WordTrace tailWord_518868 prefixEnd_518868 1461885762618277971269 := by
  unfold tailWord_518868
  simp only [CollatzResearch.WordTrace]
  refine ⟨9462335342118663222230629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12616447122824884296307505 9462335342118663222230629)
  ·
    refine ⟨1774187876647249354168243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9462335342118663222230629 1774187876647249354168243)
    ·
      refine ⟨2661281814970874031252365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1774187876647249354168243 2661281814970874031252365)
      ·
        refine ⟨997980680614077761719637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2661281814970874031252365 997980680614077761719637)
        ·
          refine ⟨1461885762618277971269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 997980680614077761719637 1461885762618277971269)
          ·
            rfl

theorem cell21_518868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 11].length) (baseStart_518868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518868 prefixEnd_518868 := by exact prefixLift 518868
  have htrace : WordTrace (prefixWord ++ tailWord_518868) baseStart_518868 baseEnd_518868 := by
    simpa [prefixWord, tailWord_518868, baseEnd_518868] using wordTrace_append hprefix tailTrace_518868
  have hstable : (prefixWord ++ tailWord_518868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518868).length < 2 ^ (prefixWord ++ tailWord_518868).sum := by decide
  have hdescent : baseEnd_518868 < baseStart_518868 := by decide
  rcases family_descends (prefixWord ++ tailWord_518868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518885 : List Nat := [1, 3, 1, 4, 1, 4, 1, 6]
def baseStart_518885 : Nat := 118140960795 + 518885 * 2 ^ 59
def prefixEnd_518885 : Nat := 4983230072969 + 3 ^ 40 * 518885 * 2
def baseEnd_518885 : Nat := 39472208801230754629807

theorem tailTrace_518885 : CollatzResearch.WordTrace tailWord_518885 prefixEnd_518885 39472208801230754629807 := by
  unfold tailWord_518885
  simp only [CollatzResearch.WordTrace]
  refine ⟨18925290725175738347830109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12616860483450492231886739 18925290725175738347830109)
  ·
    refine ⟨7096984021940901880436291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18925290725175738347830109 7096984021940901880436291)
    ·
      refine ⟨10645476032911352820654437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7096984021940901880436291 10645476032911352820654437)
      ·
        refine ⟨1996026756170878653872707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10645476032911352820654437 1996026756170878653872707)
        ·
          refine ⟨2994040134256317980809061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1996026756170878653872707 2994040134256317980809061)
          ·
            refine ⟨561382525173059621401699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2994040134256317980809061 561382525173059621401699)
            ·
              refine ⟨842073787759589432102549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561382525173059621401699 842073787759589432102549)
              ·
                refine ⟨39472208801230754629807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 842073787759589432102549 39472208801230754629807)
                ·
                  rfl

theorem cell21_518885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 6].length) (baseStart_518885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518885 prefixEnd_518885 := by exact prefixLift 518885
  have htrace : WordTrace (prefixWord ++ tailWord_518885) baseStart_518885 baseEnd_518885 := by
    simpa [prefixWord, tailWord_518885, baseEnd_518885] using wordTrace_append hprefix tailTrace_518885
  have hstable : (prefixWord ++ tailWord_518885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518885).length < 2 ^ (prefixWord ++ tailWord_518885).sum := by decide
  have hdescent : baseEnd_518885 < baseStart_518885 := by decide
  rcases family_descends (prefixWord ++ tailWord_518885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518913 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 6]
def baseStart_518913 : Nat := 118140960795 + 518913 * 2 ^ 59
def prefixEnd_518913 : Nat := 4983230072969 + 3 ^ 40 * 518913 * 2
def baseEnd_518913 : Nat := 118423016385170437422697

theorem tailTrace_518913 : CollatzResearch.WordTrace tailWord_518913 prefixEnd_518913 118423016385170437422697 := by
  unfold tailWord_518913
  simp only [CollatzResearch.WordTrace]
  refine ⟨18926311969074299129849393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12617541312716199419899595 18926311969074299129849393)
  ·
    refine ⟨14194733976805724347387045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18926311969074299129849393 14194733976805724347387045)
    ·
      refine ⟨2661512620651073315135071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14194733976805724347387045 2661512620651073315135071)
      ·
        refine ⟨3992268930976609972702607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2661512620651073315135071 3992268930976609972702607)
        ·
          refine ⟨5988403396464914959053911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3992268930976609972702607 5988403396464914959053911)
          ·
            refine ⟨8982605094697372438580867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5988403396464914959053911 8982605094697372438580867)
            ·
              refine ⟨13473907642046058657871301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8982605094697372438580867 13473907642046058657871301)
              ·
                refine ⟨2526357682883635998350869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13473907642046058657871301 2526357682883635998350869)
                ·
                  refine ⟨118423016385170437422697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2526357682883635998350869 118423016385170437422697)
                  ·
                    rfl

theorem cell21_518913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_518913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518913 prefixEnd_518913 := by exact prefixLift 518913
  have htrace : WordTrace (prefixWord ++ tailWord_518913) baseStart_518913 baseEnd_518913 := by
    simpa [prefixWord, tailWord_518913, baseEnd_518913] using wordTrace_append hprefix tailTrace_518913
  have hstable : (prefixWord ++ tailWord_518913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518913).length < 2 ^ (prefixWord ++ tailWord_518913).sum := by decide
  have hdescent : baseEnd_518913 < baseStart_518913 := by decide
  rcases family_descends (prefixWord ++ tailWord_518913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518927 : List Nat := [1, 1, 2, 1, 1, 1, 14]
def baseStart_518927 : Nat := 118140960795 + 518927 * 2 ^ 59
def prefixEnd_518927 : Nat := 4983230072969 + 3 ^ 40 * 518927 * 2
def baseEnd_518927 : Nat := 13158467930656613798815

theorem tailTrace_518927 : CollatzResearch.WordTrace tailWord_518927 prefixEnd_518927 13158467930656613798815 := by
  unfold tailWord_518927
  simp only [CollatzResearch.WordTrace]
  refine ⟨18926822591023579520859035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12617881727349053013906023 18926822591023579520859035)
  ·
    refine ⟨28390233886535369281288553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18926822591023579520859035 28390233886535369281288553)
    ·
      refine ⟨21292675414901526960966415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28390233886535369281288553 21292675414901526960966415)
      ·
        refine ⟨31939013122352290441449623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21292675414901526960966415 31939013122352290441449623)
        ·
          refine ⟨47908519683528435662174435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31939013122352290441449623 47908519683528435662174435)
          ·
            refine ⟨71862779525292653493261653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47908519683528435662174435 71862779525292653493261653)
            ·
              refine ⟨13158467930656613798815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 71862779525292653493261653 13158467930656613798815)
              ·
                rfl

theorem cell21_518927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 14].length) (baseStart_518927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_518927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_518927 prefixEnd_518927 := by exact prefixLift 518927
  have htrace : WordTrace (prefixWord ++ tailWord_518927) baseStart_518927 baseEnd_518927 := by
    simpa [prefixWord, tailWord_518927, baseEnd_518927] using wordTrace_append hprefix tailTrace_518927
  have hstable : (prefixWord ++ tailWord_518927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518927).length < 2 ^ (prefixWord ++ tailWord_518927).sum := by decide
  have hdescent : baseEnd_518927 < baseStart_518927 := by decide
  rcases family_descends (prefixWord ++ tailWord_518927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519068 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 5]
def baseStart_519068 : Nat := 118140960795 + 519068 * 2 ^ 59
def prefixEnd_519068 : Nat := 4983230072969 + 3 ^ 40 * 519068 * 2
def baseEnd_519068 : Nat := 118458389496924612339047

theorem tailTrace_519068 : CollatzResearch.WordTrace tailWord_519068 prefixEnd_519068 118458389496924612339047 := by
  unfold tailWord_519068
  simp only [CollatzResearch.WordTrace]
  refine ⟨9465982641756380300870929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12621310189008507067827905 9465982641756380300870929)
  ·
    refine ⟨7099486981317285225653197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9465982641756380300870929 7099486981317285225653197)
    ·
      refine ⟨2662307617993981959619949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7099486981317285225653197 2662307617993981959619949)
      ·
        refine ⟨998365356747743234857481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2662307617993981959619949 998365356747743234857481)
        ·
          refine ⟨748774017560807426143111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 998365356747743234857481 748774017560807426143111)
          ·
            refine ⟨1123161026341211139214667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748774017560807426143111 1123161026341211139214667)
            ·
              refine ⟨1684741539511816708822001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123161026341211139214667 1684741539511816708822001)
              ·
                refine ⟨1263556154633862531616501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1684741539511816708822001 1263556154633862531616501)
                ·
                  refine ⟨118458389496924612339047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1263556154633862531616501 118458389496924612339047)
                  ·
                    rfl

theorem cell21_519068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_519068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519068 prefixEnd_519068 := by exact prefixLift 519068
  have htrace : WordTrace (prefixWord ++ tailWord_519068) baseStart_519068 baseEnd_519068 := by
    simpa [prefixWord, tailWord_519068, baseEnd_519068] using wordTrace_append hprefix tailTrace_519068
  have hstable : (prefixWord ++ tailWord_519068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519068).length < 2 ^ (prefixWord ++ tailWord_519068).sum := by decide
  have hdescent : baseEnd_519068 < baseStart_519068 := by decide
  rcases family_descends (prefixWord ++ tailWord_519068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519144 : List Nat := [2, 1, 4, 1, 1, 1, 5, 3, 3]
def baseStart_519144 : Nat := 118140960795 + 519144 * 2 ^ 59
def prefixEnd_519144 : Nat := 4983230072969 + 3 ^ 40 * 519144 * 2
def baseEnd_519144 : Nat := 118475733732365369072225

theorem tailTrace_519144 : CollatzResearch.WordTrace tailWord_519144 prefixEnd_519144 118475733732365369072225 := by
  unfold tailWord_519144
  simp only [CollatzResearch.WordTrace]
  refine ⟨9467368615618712790754243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12623158154158283721005657 9467368615618712790754243)
  ·
    refine ⟨14201052923428069186131365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9467368615618712790754243 14201052923428069186131365)
    ·
      refine ⟨2662697423142762972399631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14201052923428069186131365 2662697423142762972399631)
      ·
        refine ⟨3994046134714144458599447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662697423142762972399631 3994046134714144458599447)
        ·
          refine ⟨5991069202071216687899171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3994046134714144458599447 5991069202071216687899171)
          ·
            refine ⟨8986603803106825031848757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5991069202071216687899171 8986603803106825031848757)
            ·
              refine ⟨842494106541264846735821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8986603803106825031848757 842494106541264846735821)
              ·
                refine ⟨315935289952974317525933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 842494106541264846735821 315935289952974317525933)
                ·
                  refine ⟨118475733732365369072225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315935289952974317525933 118475733732365369072225)
                  ·
                    rfl

theorem cell21_519144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 3].length) (baseStart_519144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519144 prefixEnd_519144 := by exact prefixLift 519144
  have htrace : WordTrace (prefixWord ++ tailWord_519144) baseStart_519144 baseEnd_519144 := by
    simpa [prefixWord, tailWord_519144, baseEnd_519144] using wordTrace_append hprefix tailTrace_519144
  have hstable : (prefixWord ++ tailWord_519144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519144).length < 2 ^ (prefixWord ++ tailWord_519144).sum := by decide
  have hdescent : baseEnd_519144 < baseStart_519144 := by decide
  rcases family_descends (prefixWord ++ tailWord_519144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519158 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_519158 : Nat := 118140960795 + 519158 * 2 ^ 59
def prefixEnd_519158 : Nat := 4983230072969 + 3 ^ 40 * 519158 * 2
def baseEnd_519158 : Nat := 118478928723104455838863

theorem tailTrace_519158 : CollatzResearch.WordTrace tailWord_519158 prefixEnd_519158 118478928723104455838863 := by
  unfold tailWord_519158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1183452990824169123282383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12623498568791137315012085 1183452990824169123282383)
  ·
    refine ⟨1775179486236253684923575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1183452990824169123282383 1775179486236253684923575)
    ·
      refine ⟨2662769229354380527385363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1775179486236253684923575 2662769229354380527385363)
      ·
        refine ⟨3994153844031570791078045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662769229354380527385363 3994153844031570791078045)
        ·
          refine ⟨1497807691511839046654267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3994153844031570791078045 1497807691511839046654267)
          ·
            refine ⟨2246711537267758569981401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497807691511839046654267 2246711537267758569981401)
            ·
              refine ⟨1685033652950818927486051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2246711537267758569981401 1685033652950818927486051)
              ·
                refine ⟨2527550479426228391229077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1685033652950818927486051 2527550479426228391229077)
                ·
                  refine ⟨118478928723104455838863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2527550479426228391229077 118478928723104455838863)
                  ·
                    rfl

theorem cell21_519158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_519158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519158 prefixEnd_519158 := by exact prefixLift 519158
  have htrace : WordTrace (prefixWord ++ tailWord_519158) baseStart_519158 baseEnd_519158 := by
    simpa [prefixWord, tailWord_519158, baseEnd_519158] using wordTrace_append hprefix tailTrace_519158
  have hstable : (prefixWord ++ tailWord_519158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519158).length < 2 ^ (prefixWord ++ tailWord_519158).sum := by decide
  have hdescent : baseEnd_519158 < baseStart_519158 := by decide
  rcases family_descends (prefixWord ++ tailWord_519158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519279 : List Nat := [1, 1, 2, 1, 3, 3, 1, 6, 3]
def baseStart_519279 : Nat := 118140960795 + 519279 * 2 ^ 59
def prefixEnd_519279 : Nat := 4983230072969 + 3 ^ 40 * 519279 * 2
def baseEnd_519279 : Nat := 118506542571635134321949

theorem tailTrace_519279 : CollatzResearch.WordTrace tailWord_519279 prefixEnd_519279 118506542571635134321949 := by
  unfold tailWord_519279
  simp only [CollatzResearch.WordTrace]
  refine ⟨18939661085748343637672891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12626440723832229091781927 18939661085748343637672891)
  ·
    refine ⟨28409491628622515456509337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18939661085748343637672891 28409491628622515456509337)
    ·
      refine ⟨21307118721466886592382003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28409491628622515456509337 21307118721466886592382003)
      ·
        refine ⟨31960678082200329888573005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21307118721466886592382003 31960678082200329888573005)
        ·
          refine ⟨11985254280825123708214877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31960678082200329888573005 11985254280825123708214877)
          ·
            refine ⟨4494470355309421390580579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11985254280825123708214877 4494470355309421390580579)
            ·
              refine ⟨6741705532964132085870869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4494470355309421390580579 6741705532964132085870869)
              ·
                refine ⟨316017446857693691525197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6741705532964132085870869 316017446857693691525197)
                ·
                  refine ⟨118506542571635134321949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316017446857693691525197 118506542571635134321949)
                  ·
                    rfl

theorem cell21_519279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 3].length) (baseStart_519279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519279 prefixEnd_519279 := by exact prefixLift 519279
  have htrace : WordTrace (prefixWord ++ tailWord_519279) baseStart_519279 baseEnd_519279 := by
    simpa [prefixWord, tailWord_519279, baseEnd_519279] using wordTrace_append hprefix tailTrace_519279
  have hstable : (prefixWord ++ tailWord_519279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519279).length < 2 ^ (prefixWord ++ tailWord_519279).sum := by decide
  have hdescent : baseEnd_519279 < baseStart_519279 := by decide
  rcases family_descends (prefixWord ++ tailWord_519279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519324 : List Nat := [2, 2, 3, 2, 1, 4, 7]
def baseStart_519324 : Nat := 118140960795 + 519324 * 2 ^ 59
def prefixEnd_519324 : Nat := 4983230072969 + 3 ^ 40 * 519324 * 2
def baseEnd_519324 : Nat := 13168534687191672896873

theorem tailTrace_519324 : CollatzResearch.WordTrace tailWord_519324 prefixEnd_519324 13168534687191672896873 := by
  unfold tailWord_519324
  simp only [CollatzResearch.WordTrace]
  refine ⟨9470651185292658161530513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12627534913723544215374017 9470651185292658161530513)
  ·
    refine ⟨7102988388969493621147885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9470651185292658161530513 7102988388969493621147885)
    ·
      refine ⟨2663620645863560107930457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7102988388969493621147885 2663620645863560107930457)
      ·
        refine ⟨1997715484397670080947843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2663620645863560107930457 1997715484397670080947843)
        ·
          refine ⟨2996573226596505121421765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1997715484397670080947843 2996573226596505121421765)
          ·
            refine ⟨561857479986844710266581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2996573226596505121421765 561857479986844710266581)
            ·
              refine ⟨13168534687191672896873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 561857479986844710266581 13168534687191672896873)
              ·
                rfl

theorem cell21_519324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 7].length) (baseStart_519324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519324 prefixEnd_519324 := by exact prefixLift 519324
  have htrace : WordTrace (prefixWord ++ tailWord_519324) baseStart_519324 baseEnd_519324 := by
    simpa [prefixWord, tailWord_519324, baseEnd_519324] using wordTrace_append hprefix tailTrace_519324
  have hstable : (prefixWord ++ tailWord_519324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519324).length < 2 ^ (prefixWord ++ tailWord_519324).sum := by decide
  have hdescent : baseEnd_519324 < baseStart_519324 := by decide
  rcases family_descends (prefixWord ++ tailWord_519324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519330 : List Nat := [3, 3, 1, 3, 2, 1, 3, 2, 3]
def baseStart_519330 : Nat := 118140960795 + 519330 * 2 ^ 59
def prefixEnd_519330 : Nat := 4983230072969 + 3 ^ 40 * 519330 * 2
def baseEnd_519330 : Nat := 118518181466470378971845

theorem tailTrace_519330 : CollatzResearch.WordTrace tailWord_519330 prefixEnd_519330 118518181466470378971845 := by
  unfold tailWord_519330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4735380302140894836944861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12627680805709052898519629 4735380302140894836944861)
  ·
    refine ⟨1775767613302835563854323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4735380302140894836944861 1775767613302835563854323)
    ·
      refine ⟨2663651419954253345781485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1775767613302835563854323 2663651419954253345781485)
      ·
        refine ⟨998869282482845004668057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2663651419954253345781485 998869282482845004668057)
        ·
          refine ⟨749151961862133753501043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 998869282482845004668057 749151961862133753501043)
          ·
            refine ⟨1123727942793200630251565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749151961862133753501043 1123727942793200630251565)
            ·
              refine ⟨421397978547450236344337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1123727942793200630251565 421397978547450236344337)
              ·
                refine ⟨316048483910587677258253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421397978547450236344337 316048483910587677258253)
                ·
                  refine ⟨118518181466470378971845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316048483910587677258253 118518181466470378971845)
                  ·
                    rfl

theorem cell21_519330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_519330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519330 prefixEnd_519330 := by exact prefixLift 519330
  have htrace : WordTrace (prefixWord ++ tailWord_519330) baseStart_519330 baseEnd_519330 := by
    simpa [prefixWord, tailWord_519330, baseEnd_519330] using wordTrace_append hprefix tailTrace_519330
  have hstable : (prefixWord ++ tailWord_519330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519330).length < 2 ^ (prefixWord ++ tailWord_519330).sum := by decide
  have hdescent : baseEnd_519330 < baseStart_519330 := by decide
  rcases family_descends (prefixWord ++ tailWord_519330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519341 : List Nat := [1, 5, 2, 1, 3, 1, 2, 6]
def baseStart_519341 : Nat := 118140960795 + 519341 * 2 ^ 59
def prefixEnd_519341 : Nat := 4983230072969 + 3 ^ 40 * 519341 * 2
def baseEnd_519341 : Nat := 39506897272112268096163

theorem tailTrace_519341 : CollatzResearch.WordTrace tailWord_519341 prefixEnd_519341 39506897272112268096163 := by
  unfold tailWord_519341
  simp only [CollatzResearch.WordTrace]
  refine ⟨18941922411523728226429877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12627948274349152150953251 18941922411523728226429877)
  ·
    refine ⟨1775805226080349521227801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18941922411523728226429877 1775805226080349521227801)
    ·
      refine ⟨1331853919560262140920851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1775805226080349521227801 1331853919560262140920851)
      ·
        refine ⟨1997780879340393211381277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1331853919560262140920851 1997780879340393211381277)
        ·
          refine ⟨749167829752647454267979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1997780879340393211381277 749167829752647454267979)
          ·
            refine ⟨1123751744628971181401969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749167829752647454267979 1123751744628971181401969)
            ·
              refine ⟨842813808471728386051477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123751744628971181401969 842813808471728386051477)
              ·
                refine ⟨39506897272112268096163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 842813808471728386051477 39506897272112268096163)
                ·
                  rfl

theorem cell21_519341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 6].length) (baseStart_519341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519341 prefixEnd_519341 := by exact prefixLift 519341
  have htrace : WordTrace (prefixWord ++ tailWord_519341) baseStart_519341 baseEnd_519341 := by
    simpa [prefixWord, tailWord_519341, baseEnd_519341] using wordTrace_append hprefix tailTrace_519341
  have hstable : (prefixWord ++ tailWord_519341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519341).length < 2 ^ (prefixWord ++ tailWord_519341).sum := by decide
  have hdescent : baseEnd_519341 < baseStart_519341 := by decide
  rcases family_descends (prefixWord ++ tailWord_519341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519352 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 8]
def baseStart_519352 : Nat := 118140960795 + 519352 * 2 ^ 59
def prefixEnd_519352 : Nat := 4983230072969 + 3 ^ 40 * 519352 * 2
def baseEnd_519352 : Nat := 118523202166203229605133

theorem tailTrace_519352 : CollatzResearch.WordTrace tailWord_519352 prefixEnd_519352 118523202166203229605133 := by
  unfold tailWord_519352
  simp only [CollatzResearch.WordTrace]
  refine ⟨9471161807241938552540155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12628215742989251403386873 9471161807241938552540155)
  ·
    refine ⟨14206742710862907828810233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9471161807241938552540155 14206742710862907828810233)
    ·
      refine ⟨10655057033147180871607675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14206742710862907828810233 10655057033147180871607675)
      ·
        refine ⟨15982585549720771307411513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10655057033147180871607675 15982585549720771307411513)
        ·
          refine ⟨11986939162290578480558635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15982585549720771307411513 11986939162290578480558635)
          ·
            refine ⟨17980408743435867720837953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11986939162290578480558635 17980408743435867720837953)
            ·
              refine ⟨13485306557576900790628465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17980408743435867720837953 13485306557576900790628465)
              ·
                refine ⟨10113979918182675592971349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13485306557576900790628465 10113979918182675592971349)
                ·
                  refine ⟨118523202166203229605133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10113979918182675592971349 118523202166203229605133)
                  ·
                    rfl

theorem cell21_519352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_519352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519352 prefixEnd_519352 := by exact prefixLift 519352
  have htrace : WordTrace (prefixWord ++ tailWord_519352) baseStart_519352 baseEnd_519352 := by
    simpa [prefixWord, tailWord_519352, baseEnd_519352] using wordTrace_append hprefix tailTrace_519352
  have hstable : (prefixWord ++ tailWord_519352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519352).length < 2 ^ (prefixWord ++ tailWord_519352).sum := by decide
  have hdescent : baseEnd_519352 < baseStart_519352 := by decide
  rcases family_descends (prefixWord ++ tailWord_519352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519389 : List Nat := [1, 4, 3, 2, 2, 1, 1, 4, 3]
def baseStart_519389 : Nat := 118140960795 + 519389 * 2 ^ 59
def prefixEnd_519389 : Nat := 4983230072969 + 3 ^ 40 * 519389 * 2
def baseEnd_519389 : Nat := 118531646070299387488391

theorem tailTrace_519389 : CollatzResearch.WordTrace tailWord_519389 prefixEnd_519389 118531646070299387488391 := by
  unfold tailWord_519389
  simp only [CollatzResearch.WordTrace]
  refine ⟨18943673115349832424177221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12629115410233221616118147 18943673115349832424177221)
  ·
    refine ⟨3551938709128093579533229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18943673115349832424177221 3551938709128093579533229)
    ·
      refine ⟨1331977015923035092324961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3551938709128093579533229 1331977015923035092324961)
      ·
        refine ⟨998982761942276319243721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1331977015923035092324961 998982761942276319243721)
        ·
          refine ⟨749237071456707239432791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 998982761942276319243721 749237071456707239432791)
          ·
            refine ⟨1123855607185060859149187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749237071456707239432791 1123855607185060859149187)
            ·
              refine ⟨1685783410777591288723781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123855607185060859149187 1685783410777591288723781)
              ·
                refine ⟨316084389520798366635709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1685783410777591288723781 316084389520798366635709)
                ·
                  refine ⟨118531646070299387488391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316084389520798366635709 118531646070299387488391)
                  ·
                    rfl

theorem cell21_519389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_519389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519389 prefixEnd_519389 := by exact prefixLift 519389
  have htrace : WordTrace (prefixWord ++ tailWord_519389) baseStart_519389 baseEnd_519389 := by
    simpa [prefixWord, tailWord_519389, baseEnd_519389] using wordTrace_append hprefix tailTrace_519389
  have hstable : (prefixWord ++ tailWord_519389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519389).length < 2 ^ (prefixWord ++ tailWord_519389).sum := by decide
  have hdescent : baseEnd_519389 < baseStart_519389 := by decide
  rcases family_descends (prefixWord ++ tailWord_519389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519476 : List Nat := [2, 5, 1, 1, 1, 1, 3, 7]
def baseStart_519476 : Nat := 118140960795 + 519476 * 2 ^ 59
def prefixEnd_519476 : Nat := 4983230072969 + 3 ^ 40 * 519476 * 2
def baseEnd_519476 : Nat := 39517166885202189846071

theorem tailTrace_519476 : CollatzResearch.WordTrace tailWord_519476 prefixEnd_519476 39517166885202189846071 := by
  unfold tailWord_519476
  simp only [CollatzResearch.WordTrace]
  refine ⟨9473423133017323141297141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12631230844023097521729521 9473423133017323141297141)
  ·
    refine ⟨888133418720374044496607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9473423133017323141297141 888133418720374044496607)
    ·
      refine ⟨1332200128080561066744911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 888133418720374044496607 1332200128080561066744911)
      ·
        refine ⟨1998300192120841600117367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1332200128080561066744911 1998300192120841600117367)
        ·
          refine ⟨2997450288181262400176051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1998300192120841600117367 2997450288181262400176051)
          ·
            refine ⟨4496175432271893600264077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2997450288181262400176051 4496175432271893600264077)
            ·
              refine ⟨1686065787101960100099029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4496175432271893600264077 1686065787101960100099029)
              ·
                refine ⟨39517166885202189846071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1686065787101960100099029 39517166885202189846071)
                ·
                  rfl

theorem cell21_519476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 7].length) (baseStart_519476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519476 prefixEnd_519476 := by exact prefixLift 519476
  have htrace : WordTrace (prefixWord ++ tailWord_519476) baseStart_519476 baseEnd_519476 := by
    simpa [prefixWord, tailWord_519476, baseEnd_519476] using wordTrace_append hprefix tailTrace_519476
  have hstable : (prefixWord ++ tailWord_519476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519476).length < 2 ^ (prefixWord ++ tailWord_519476).sum := by decide
  have hdescent : baseEnd_519476 < baseStart_519476 := by decide
  rcases family_descends (prefixWord ++ tailWord_519476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519504 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 6]
def baseStart_519504 : Nat := 118140960795 + 519504 * 2 ^ 59
def prefixEnd_519504 : Nat := 4983230072969 + 3 ^ 40 * 519504 * 2
def baseEnd_519504 : Nat := 118557890637084743071489

theorem tailTrace_519504 : CollatzResearch.WordTrace tailWord_519504 prefixEnd_519504 118557890637084743071489 := by
  unfold tailWord_519504
  simp only [CollatzResearch.WordTrace]
  refine ⟨9473933754966603532306783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12631911673288804709742377 9473933754966603532306783)
  ·
    refine ⟨14210900632449905298460175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9473933754966603532306783 14210900632449905298460175)
    ·
      refine ⟨21316350948674857947690263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14210900632449905298460175 21316350948674857947690263)
      ·
        refine ⟨31974526423012286921535395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21316350948674857947690263 31974526423012286921535395)
        ·
          refine ⟨47961789634518430382303093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31974526423012286921535395 47961789634518430382303093)
          ·
            refine ⟨4496417778236102848340915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47961789634518430382303093 4496417778236102848340915)
            ·
              refine ⟨6744626667354154272511373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496417778236102848340915 6744626667354154272511373)
              ·
                refine ⟨2529235000257807852191765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6744626667354154272511373 2529235000257807852191765)
                ·
                  refine ⟨118557890637084743071489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2529235000257807852191765 118557890637084743071489)
                  ·
                    rfl

theorem cell21_519504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_519504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519504 prefixEnd_519504 := by exact prefixLift 519504
  have htrace : WordTrace (prefixWord ++ tailWord_519504) baseStart_519504 baseEnd_519504 := by
    simpa [prefixWord, tailWord_519504, baseEnd_519504] using wordTrace_append hprefix tailTrace_519504
  have hstable : (prefixWord ++ tailWord_519504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519504).length < 2 ^ (prefixWord ++ tailWord_519504).sum := by decide
  have hdescent : baseEnd_519504 < baseStart_519504 := by decide
  rcases family_descends (prefixWord ++ tailWord_519504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519642 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 5]
def baseStart_519642 : Nat := 118140960795 + 519642 * 2 ^ 59
def prefixEnd_519642 : Nat := 4983230072969 + 3 ^ 40 * 519642 * 2
def baseEnd_519642 : Nat := 118589384117227169771207

theorem tailTrace_519642 : CollatzResearch.WordTrace tailWord_519642 prefixEnd_519642 118589384117227169771207 := by
  unfold tailWord_519642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4738225195858314158284295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12635267188955504422091453 4738225195858314158284295)
  ·
    refine ⟨7107337793787471237426443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4738225195858314158284295 7107337793787471237426443)
    ·
      refine ⟨10661006690681206856139665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7107337793787471237426443 10661006690681206856139665)
      ·
        refine ⟨7995755018010905142104749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10661006690681206856139665 7995755018010905142104749)
        ·
          refine ⟨2998408131754089428289281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7995755018010905142104749 2998408131754089428289281)
          ·
            refine ⟨2248806098815567071216961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2998408131754089428289281 2248806098815567071216961)
            ·
              refine ⟨1686604574111675303412721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2248806098815567071216961 1686604574111675303412721)
              ·
                refine ⟨1264953430583756477559541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1686604574111675303412721 1264953430583756477559541)
                ·
                  refine ⟨118589384117227169771207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1264953430583756477559541 118589384117227169771207)
                  ·
                    rfl

theorem cell21_519642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_519642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519642 prefixEnd_519642 := by exact prefixLift 519642
  have htrace : WordTrace (prefixWord ++ tailWord_519642) baseStart_519642 baseEnd_519642 := by
    simpa [prefixWord, tailWord_519642, baseEnd_519642] using wordTrace_append hprefix tailTrace_519642
  have hstable : (prefixWord ++ tailWord_519642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519642).length < 2 ^ (prefixWord ++ tailWord_519642).sum := by decide
  have hdescent : baseEnd_519642 < baseStart_519642 := by decide
  rcases family_descends (prefixWord ++ tailWord_519642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519645 : List Nat := [1, 4, 3, 1, 1, 4, 2, 5]
def baseStart_519645 : Nat := 118140960795 + 519645 * 2 ^ 59
def prefixEnd_519645 : Nat := 4983230072969 + 3 ^ 40 * 519645 * 2
def baseEnd_519645 : Nat := 39530022919366610407067

theorem tailTrace_519645 : CollatzResearch.WordTrace tailWord_519645 prefixEnd_519645 39530022919366610407067 := by
  unfold tailWord_519645
  simp only [CollatzResearch.WordTrace]
  refine ⟨18953010202422388145496389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12635340134948258763664259 18953010202422388145496389)
  ·
    refine ⟨3553689412954197777280573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18953010202422388145496389 3553689412954197777280573)
    ·
      refine ⟨1332633529857824166480215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3553689412954197777280573 1332633529857824166480215)
      ·
        refine ⟨1998950294786736249720323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1332633529857824166480215 1998950294786736249720323)
        ·
          refine ⟨2998425442180104374580485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1998950294786736249720323 2998425442180104374580485)
          ·
            refine ⟨562204770408769570233841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2998425442180104374580485 562204770408769570233841)
            ·
              refine ⟨421653577806577177675381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562204770408769570233841 421653577806577177675381)
              ·
                refine ⟨39530022919366610407067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 421653577806577177675381 39530022919366610407067)
                ·
                  rfl

theorem cell21_519645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 5].length) (baseStart_519645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519645 prefixEnd_519645 := by exact prefixLift 519645
  have htrace : WordTrace (prefixWord ++ tailWord_519645) baseStart_519645 baseEnd_519645 := by
    simpa [prefixWord, tailWord_519645, baseEnd_519645] using wordTrace_append hprefix tailTrace_519645
  have hstable : (prefixWord ++ tailWord_519645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519645).length < 2 ^ (prefixWord ++ tailWord_519645).sum := by decide
  have hdescent : baseEnd_519645 < baseStart_519645 := by decide
  rcases family_descends (prefixWord ++ tailWord_519645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519656 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 8]
def baseStart_519656 : Nat := 118140960795 + 519656 * 2 ^ 59
def prefixEnd_519656 : Nat := 4983230072969 + 3 ^ 40 * 519656 * 2
def baseEnd_519656 : Nat := 118592579107966256537845

theorem tailTrace_519656 : CollatzResearch.WordTrace tailWord_519656 prefixEnd_519656 118592579107966256537845 := by
  unfold tailWord_519656
  simp only [CollatzResearch.WordTrace]
  refine ⟨9476705702691268512073411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12635607603588358016097881 9476705702691268512073411)
  ·
    refine ⟨14215058554036902768110117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9476705702691268512073411 14215058554036902768110117)
    ·
      refine ⟨2665323478881919269020647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14215058554036902768110117 2665323478881919269020647)
      ·
        refine ⟨3997985218322878903530971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2665323478881919269020647 3997985218322878903530971)
        ·
          refine ⟨5996977827484318355296457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3997985218322878903530971 5996977827484318355296457)
          ·
            refine ⟨4497733370613238766472343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5996977827484318355296457 4497733370613238766472343)
            ·
              refine ⟨6746600055919858149708515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4497733370613238766472343 6746600055919858149708515)
              ·
                refine ⟨10119900083879787224562773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6746600055919858149708515 10119900083879787224562773)
                ·
                  refine ⟨118592579107966256537845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10119900083879787224562773 118592579107966256537845)
                  ·
                    rfl

theorem cell21_519656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_519656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519656 prefixEnd_519656 := by exact prefixLift 519656
  have htrace : WordTrace (prefixWord ++ tailWord_519656) baseStart_519656 baseEnd_519656 := by
    simpa [prefixWord, tailWord_519656, baseEnd_519656] using wordTrace_append hprefix tailTrace_519656
  have hstable : (prefixWord ++ tailWord_519656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519656).length < 2 ^ (prefixWord ++ tailWord_519656).sum := by decide
  have hdescent : baseEnd_519656 < baseStart_519656 := by decide
  rcases family_descends (prefixWord ++ tailWord_519656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519687 : List Nat := [1, 1, 4, 3, 2, 1, 1, 8]
def baseStart_519687 : Nat := 118140960795 + 519687 * 2 ^ 59
def prefixEnd_519687 : Nat := 4983230072969 + 3 ^ 40 * 519687 * 2
def baseEnd_519687 : Nat := 39533217910105697173705

theorem tailTrace_519687 : CollatzResearch.WordTrace tailWord_519687 prefixEnd_519687 39533217910105697173705 := by
  unfold tailWord_519687
  simp only [CollatzResearch.WordTrace]
  refine ⟨18954542068270229318525315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12636361378846819545683543 18954542068270229318525315)
  ·
    refine ⟨28431813102405343977787973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18954542068270229318525315 28431813102405343977787973)
    ·
      refine ⟨5330964956701001995835245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28431813102405343977787973 5330964956701001995835245)
      ·
        refine ⟨1999111858762875748438217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5330964956701001995835245 1999111858762875748438217)
        ·
          refine ⟨1499333894072156811328663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1999111858762875748438217 1499333894072156811328663)
          ·
            refine ⟨2249000841108235216992995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499333894072156811328663 2249000841108235216992995)
            ·
              refine ⟨3373501261662352825489493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2249000841108235216992995 3373501261662352825489493)
              ·
                refine ⟨39533217910105697173705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3373501261662352825489493 39533217910105697173705)
                ·
                  rfl

theorem cell21_519687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 8].length) (baseStart_519687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519687 prefixEnd_519687 := by exact prefixLift 519687
  have htrace : WordTrace (prefixWord ++ tailWord_519687) baseStart_519687 baseEnd_519687 := by
    simpa [prefixWord, tailWord_519687, baseEnd_519687] using wordTrace_append hprefix tailTrace_519687
  have hstable : (prefixWord ++ tailWord_519687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519687).length < 2 ^ (prefixWord ++ tailWord_519687).sum := by decide
  have hdescent : baseEnd_519687 < baseStart_519687 := by decide
  rcases family_descends (prefixWord ++ tailWord_519687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519690 : List Nat := [3, 1, 2, 2, 2, 2, 4, 1, 4]
def baseStart_519690 : Nat := 118140960795 + 519690 * 2 ^ 59
def prefixEnd_519690 : Nat := 4983230072969 + 3 ^ 40 * 519690 * 2
def baseEnd_519690 : Nat := 118600338371189752971109

theorem tailTrace_519690 : CollatzResearch.WordTrace tailWord_519690 prefixEnd_519690 118600338371189752971109 := by
  unfold tailWord_519690
  simp only [CollatzResearch.WordTrace]
  refine ⟨4738662871814840207721131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12636434324839573887256349 4738662871814840207721131)
  ·
    refine ⟨7107994307722260311581697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4738662871814840207721131 7107994307722260311581697)
    ·
      refine ⟨5330995730791695233686273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7107994307722260311581697 5330995730791695233686273)
      ·
        refine ⟨3998246798093771425264705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5330995730791695233686273 3998246798093771425264705)
        ·
          refine ⟨2998685098570328568948529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3998246798093771425264705 2998685098570328568948529)
          ·
            refine ⟨2249013823927746426711397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2998685098570328568948529 2249013823927746426711397)
            ·
              refine ⟨421690091986452455008387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2249013823927746426711397 421690091986452455008387)
              ·
                refine ⟨632535137979678682512581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421690091986452455008387 632535137979678682512581)
                ·
                  refine ⟨118600338371189752971109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 632535137979678682512581 118600338371189752971109)
                  ·
                    rfl

theorem cell21_519690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_519690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519690 prefixEnd_519690 := by exact prefixLift 519690
  have htrace : WordTrace (prefixWord ++ tailWord_519690) baseStart_519690 baseEnd_519690 := by
    simpa [prefixWord, tailWord_519690, baseEnd_519690] using wordTrace_append hprefix tailTrace_519690
  have hstable : (prefixWord ++ tailWord_519690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519690).length < 2 ^ (prefixWord ++ tailWord_519690).sum := by decide
  have hdescent : baseEnd_519690 < baseStart_519690 := by decide
  rcases family_descends (prefixWord ++ tailWord_519690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519735 : List Nat := [1, 1, 3, 1, 2, 5, 1, 4, 3]
def baseStart_519735 : Nat := 118140960795 + 519735 * 2 ^ 59
def prefixEnd_519735 : Nat := 4983230072969 + 3 ^ 40 * 519735 * 2
def baseEnd_519735 : Nat := 118610607984279674721017

theorem tailTrace_519735 : CollatzResearch.WordTrace tailWord_519735 prefixEnd_519735 118610607984279674721017 := by
  unfold tailWord_519735
  simp only [CollatzResearch.WordTrace]
  refine ⟨18956292772096333516272659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12637528514730889010848439 18956292772096333516272659)
  ·
    refine ⟨28434439158144500274408989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18956292772096333516272659 28434439158144500274408989)
    ·
      refine ⟨10662914684304187602903371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28434439158144500274408989 10662914684304187602903371)
      ·
        refine ⟨15994372026456281404355057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10662914684304187602903371 15994372026456281404355057)
        ·
          refine ⟨11995779019842211053266293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15994372026456281404355057 11995779019842211053266293)
          ·
            refine ⟨1124604283110207286243715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11995779019842211053266293 1124604283110207286243715)
            ·
              refine ⟨1686906424665310929365573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124604283110207286243715 1686906424665310929365573)
              ·
                refine ⟨316294954624745799256045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1686906424665310929365573 316294954624745799256045)
                ·
                  refine ⟨118610607984279674721017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316294954624745799256045 118610607984279674721017)
                  ·
                    rfl

theorem cell21_519735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 3].length) (baseStart_519735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519735 prefixEnd_519735 := by exact prefixLift 519735
  have htrace : WordTrace (prefixWord ++ tailWord_519735) baseStart_519735 baseEnd_519735 := by
    simpa [prefixWord, tailWord_519735, baseEnd_519735] using wordTrace_append hprefix tailTrace_519735
  have hstable : (prefixWord ++ tailWord_519735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519735).length < 2 ^ (prefixWord ++ tailWord_519735).sum := by decide
  have hdescent : baseEnd_519735 < baseStart_519735 := by decide
  rcases family_descends (prefixWord ++ tailWord_519735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519777 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 7]
def baseStart_519777 : Nat := 118140960795 + 519777 * 2 ^ 59
def prefixEnd_519777 : Nat := 4983230072969 + 3 ^ 40 * 519777 * 2
def baseEnd_519777 : Nat := 118620192956496935020931

theorem tailTrace_519777 : CollatzResearch.WordTrace tailWord_519777 prefixEnd_519777 118620192956496935020931 := by
  unfold tailWord_519777
  simp only [CollatzResearch.WordTrace]
  refine ⟨18957824637944174689301585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12638549758629449792867723 18957824637944174689301585)
  ·
    refine ⟨14218368478458131016976189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18957824637944174689301585 14218368478458131016976189)
    ·
      refine ⟨5331888179421799131366071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14218368478458131016976189 5331888179421799131366071)
      ·
        refine ⟨7997832269132698697049107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5331888179421799131366071 7997832269132698697049107)
        ·
          refine ⟨11996748403699048045573661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7997832269132698697049107 11996748403699048045573661)
          ·
            refine ⟨4498780651387143017090123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11996748403699048045573661 4498780651387143017090123)
            ·
              refine ⟨6748170977080714525635185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4498780651387143017090123 6748170977080714525635185)
              ·
                refine ⟨5061128232810535894226389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6748170977080714525635185 5061128232810535894226389)
                ·
                  refine ⟨118620192956496935020931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5061128232810535894226389 118620192956496935020931)
                  ·
                    rfl

theorem cell21_519777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_519777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519777 prefixEnd_519777 := by exact prefixLift 519777
  have htrace : WordTrace (prefixWord ++ tailWord_519777) baseStart_519777 baseEnd_519777 := by
    simpa [prefixWord, tailWord_519777, baseEnd_519777] using wordTrace_append hprefix tailTrace_519777
  have hstable : (prefixWord ++ tailWord_519777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519777).length < 2 ^ (prefixWord ++ tailWord_519777).sum := by decide
  have hdescent : baseEnd_519777 < baseStart_519777 := by decide
  rcases family_descends (prefixWord ++ tailWord_519777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519794 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 5]
def baseStart_519794 : Nat := 118140960795 + 519794 * 2 ^ 59
def prefixEnd_519794 : Nat := 4983230072969 + 3 ^ 40 * 519794 * 2
def baseEnd_519794 : Nat := 118624072588108683237563

theorem tailTrace_519794 : CollatzResearch.WordTrace tailWord_519794 prefixEnd_519794 118624072588108683237563 := by
  unfold tailWord_519794
  simp only [CollatzResearch.WordTrace]
  refine ⟨4739611169720646648167609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12638963119255057728446957 4739611169720646648167609)
  ·
    refine ⟨3554708377290484986125707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4739611169720646648167609 3554708377290484986125707)
    ·
      refine ⟨5332062565935727479188561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3554708377290484986125707 5332062565935727479188561)
      ·
        refine ⟨3999046924451795609391421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5332062565935727479188561 3999046924451795609391421)
        ·
          refine ⟨1499642596669423353521783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3999046924451795609391421 1499642596669423353521783)
          ·
            refine ⟨2249463895004135030282675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499642596669423353521783 2249463895004135030282675)
            ·
              refine ⟨3374195842506202545424013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2249463895004135030282675 3374195842506202545424013)
              ·
                refine ⟨1265323440939825954534005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3374195842506202545424013 1265323440939825954534005)
                ·
                  refine ⟨118624072588108683237563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1265323440939825954534005 118624072588108683237563)
                  ·
                    rfl

theorem cell21_519794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_519794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519794 prefixEnd_519794 := by exact prefixLift 519794
  have htrace : WordTrace (prefixWord ++ tailWord_519794) baseStart_519794 baseEnd_519794 := by
    simpa [prefixWord, tailWord_519794, baseEnd_519794] using wordTrace_append hprefix tailTrace_519794
  have hstable : (prefixWord ++ tailWord_519794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519794).length < 2 ^ (prefixWord ++ tailWord_519794).sum := by decide
  have hdescent : baseEnd_519794 < baseStart_519794 := by decide
  rcases family_descends (prefixWord ++ tailWord_519794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519898 : List Nat := [3, 1, 1, 2, 2, 12]
def baseStart_519898 : Nat := 118140960795 + 519898 * 2 ^ 59
def prefixEnd_519898 : Nat := 4983230072969 + 3 ^ 40 * 519898 * 2
def baseEnd_519898 : Nat := 4394363215001022722371

theorem tailTrace_519898 : CollatzResearch.WordTrace tailWord_519898 prefixEnd_519898 4394363215001022722371 := by
  unfold tailWord_519898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4740559467626453088614087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12641491913670541569637565 4740559467626453088614087)
  ·
    refine ⟨7110839201439679632921131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4740559467626453088614087 7110839201439679632921131)
    ·
      refine ⟨10666258802159519449381697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7110839201439679632921131 10666258802159519449381697)
      ·
        refine ⟨7999694101619639587036273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10666258802159519449381697 7999694101619639587036273)
        ·
          refine ⟨5999770576214729690277205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7999694101619639587036273 5999770576214729690277205)
          ·
            refine ⟨4394363215001022722371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5999770576214729690277205 4394363215001022722371)
            ·
              rfl

theorem cell21_519898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 12].length) (baseStart_519898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_519898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_519898 prefixEnd_519898 := by exact prefixLift 519898
  have htrace : WordTrace (prefixWord ++ tailWord_519898) baseStart_519898 baseEnd_519898 := by
    simpa [prefixWord, tailWord_519898, baseEnd_519898] using wordTrace_append hprefix tailTrace_519898
  have hstable : (prefixWord ++ tailWord_519898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519898).length < 2 ^ (prefixWord ++ tailWord_519898).sum := by decide
  have hdescent : baseEnd_519898 < baseStart_519898 := by decide
  rcases family_descends (prefixWord ++ tailWord_519898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520028 : List Nat := [2, 2, 4, 2, 3, 1, 2, 1, 4]
def baseStart_520028 : Nat := 118140960795 + 520028 * 2 ^ 59
def prefixEnd_520028 : Nat := 4983230072969 + 3 ^ 40 * 520028 * 2
def baseEnd_520028 : Nat := 118677474576176276337085

theorem tailTrace_520028 : CollatzResearch.WordTrace tailWord_520028 prefixEnd_520028 118677474576176276337085 := by
  unfold tailWord_520028
  simp only [CollatzResearch.WordTrace]
  refine ⟨9483489680017422278344369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12644652906689896371125825 9483489680017422278344369)
  ·
    refine ⟨7112617260013066708758277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9483489680017422278344369 7112617260013066708758277)
    ·
      refine ⟨1333615736252450007892177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7112617260013066708758277 1333615736252450007892177)
      ·
        refine ⟨1000211802189337505919133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1333615736252450007892177 1000211802189337505919133)
        ·
          refine ⟨375079425821001564719675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1000211802189337505919133 375079425821001564719675)
          ·
            refine ⟨562619138731502347079513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375079425821001564719675 562619138731502347079513)
            ·
              refine ⟨421964354048626760309635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562619138731502347079513 421964354048626760309635)
              ·
                refine ⟨632946531072940140464453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421964354048626760309635 632946531072940140464453)
                ·
                  refine ⟨118677474576176276337085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 632946531072940140464453 118677474576176276337085)
                  ·
                    rfl

theorem cell21_520028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_520028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_520028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_520028 prefixEnd_520028 := by exact prefixLift 520028
  have htrace : WordTrace (prefixWord ++ tailWord_520028) baseStart_520028 baseEnd_520028 := by
    simpa [prefixWord, tailWord_520028, baseEnd_520028] using wordTrace_append hprefix tailTrace_520028
  have hstable : (prefixWord ++ tailWord_520028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520028).length < 2 ^ (prefixWord ++ tailWord_520028).sum := by decide
  have hdescent : baseEnd_520028 < baseStart_520028 := by decide
  rcases family_descends (prefixWord ++ tailWord_520028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520084 : List Nat := [2, 4, 2, 1, 1, 4, 1, 6]
def baseStart_520084 : Nat := 118140960795 + 520084 * 2 ^ 59
def prefixEnd_520084 : Nat := 4983230072969 + 3 ^ 40 * 520084 * 2
def baseEnd_520084 : Nat := 39563418179710874467879

theorem tailTrace_520084 : CollatzResearch.WordTrace tailWord_520084 prefixEnd_520084 39563418179710874467879 := by
  unfold tailWord_520084
  simp only [CollatzResearch.WordTrace]
  refine ⟨9484510923915983060363653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12646014565221310747151537 9484510923915983060363653)
  ·
    refine ⟨1778345798234246823818185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9484510923915983060363653 1778345798234246823818185)
    ·
      refine ⟨1333759348675685117863639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1778345798234246823818185 1333759348675685117863639)
      ·
        refine ⟨2000639023013527676795459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1333759348675685117863639 2000639023013527676795459)
        ·
          refine ⟨3000958534520291515193189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2000639023013527676795459 3000958534520291515193189)
          ·
            refine ⟨562679725222554659098723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3000958534520291515193189 562679725222554659098723)
            ·
              refine ⟨844019587833831988648085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562679725222554659098723 844019587833831988648085)
              ·
                refine ⟨39563418179710874467879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 844019587833831988648085 39563418179710874467879)
                ·
                  rfl

theorem cell21_520084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 6].length) (baseStart_520084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_520084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_520084 prefixEnd_520084 := by exact prefixLift 520084
  have htrace : WordTrace (prefixWord ++ tailWord_520084) baseStart_520084 baseEnd_520084 := by
    simpa [prefixWord, tailWord_520084, baseEnd_520084] using wordTrace_append hprefix tailTrace_520084
  have hstable : (prefixWord ++ tailWord_520084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520084).length < 2 ^ (prefixWord ++ tailWord_520084).sum := by decide
  have hdescent : baseEnd_520084 < baseStart_520084 := by decide
  rcases family_descends (prefixWord ++ tailWord_520084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520188 : List Nat := [2, 2, 2, 1, 2, 2, 2, 4, 4]
def baseStart_520188 : Nat := 118140960795 + 520188 * 2 ^ 59
def prefixEnd_520188 : Nat := 4983230072969 + 3 ^ 40 * 520188 * 2
def baseEnd_520188 : Nat := 118713988756051553670091

theorem tailTrace_520188 : CollatzResearch.WordTrace tailWord_520188 prefixEnd_520188 118713988756051553670091 := by
  unfold tailWord_520188
  simp only [CollatzResearch.WordTrace]
  refine ⟨9486407519727595941256609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12648543359636794588342145 9486407519727595941256609)
  ·
    refine ⟨7114805639795696955942457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9486407519727595941256609 7114805639795696955942457)
    ·
      refine ⟨5336104229846772716956843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7114805639795696955942457 5336104229846772716956843)
      ·
        refine ⟨8004156344770159075435265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5336104229846772716956843 8004156344770159075435265)
        ·
          refine ⟨6003117258577619306576449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8004156344770159075435265 6003117258577619306576449)
          ·
            refine ⟨4502337943933214479932337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6003117258577619306576449 4502337943933214479932337)
            ·
              refine ⟨3376753457949910859949253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4502337943933214479932337 3376753457949910859949253)
              ·
                refine ⟨633141273365608286240485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3376753457949910859949253 633141273365608286240485)
                ·
                  refine ⟨118713988756051553670091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 633141273365608286240485 118713988756051553670091)
                  ·
                    rfl

theorem cell21_520188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_520188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_520188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_520188 prefixEnd_520188 := by exact prefixLift 520188
  have htrace : WordTrace (prefixWord ++ tailWord_520188) baseStart_520188 baseEnd_520188 := by
    simpa [prefixWord, tailWord_520188, baseEnd_520188] using wordTrace_append hprefix tailTrace_520188
  have hstable : (prefixWord ++ tailWord_520188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520188).length < 2 ^ (prefixWord ++ tailWord_520188).sum := by decide
  have hdescent : baseEnd_520188 < baseStart_520188 := by decide
  rcases family_descends (prefixWord ++ tailWord_520188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520247 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 6]
def baseStart_520247 : Nat := 118140960795 + 520247 * 2 ^ 59
def prefixEnd_520247 : Nat := 4983230072969 + 3 ^ 40 * 520247 * 2
def baseEnd_520247 : Nat := 118727453359880562186637

theorem tailTrace_520247 : CollatzResearch.WordTrace tailWord_520247 prefixEnd_520247 118727453359880562186637 := by
  unfold tailWord_520247
  simp only [CollatzResearch.WordTrace]
  refine ⟨18974966946241444958910995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12649977964160963305940663 18974966946241444958910995)
  ·
    refine ⟨28462450419362167438366493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18974966946241444958910995 28462450419362167438366493)
    ·
      refine ⟨10673418907260812789387435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28462450419362167438366493 10673418907260812789387435)
      ·
        refine ⟨16010128360891219184081153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10673418907260812789387435 16010128360891219184081153)
        ·
          refine ⟨12007596270668414388060865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16010128360891219184081153 12007596270668414388060865)
          ·
            refine ⟨9005697203001310791045649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12007596270668414388060865 9005697203001310791045649)
            ·
              refine ⟨6754272902250983093284237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9005697203001310791045649 6754272902250983093284237)
              ·
                refine ⟨2532852338344118659981589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6754272902250983093284237 2532852338344118659981589)
                ·
                  refine ⟨118727453359880562186637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2532852338344118659981589 118727453359880562186637)
                  ·
                    rfl

theorem cell21_520247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 6].length) (baseStart_520247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_520247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_520247 prefixEnd_520247 := by exact prefixLift 520247
  have htrace : WordTrace (prefixWord ++ tailWord_520247) baseStart_520247 baseEnd_520247 := by
    simpa [prefixWord, tailWord_520247, baseEnd_520247] using wordTrace_append hprefix tailTrace_520247
  have hstable : (prefixWord ++ tailWord_520247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520247).length < 2 ^ (prefixWord ++ tailWord_520247).sum := by decide
  have hdescent : baseEnd_520247 < baseStart_520247 := by decide
  rcases family_descends (prefixWord ++ tailWord_520247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520298 : List Nat := [3, 1, 3, 2, 3, 2, 1, 2, 4]
def baseStart_520298 : Nat := 118140960795 + 520298 * 2 ^ 59
def prefixEnd_520298 : Nat := 4983230072969 + 3 ^ 40 * 520298 * 2
def baseEnd_520298 : Nat := 118739092254715806836533

theorem tailTrace_520298 : CollatzResearch.WordTrace tailWord_520298 prefixEnd_520298 118739092254715806836533 := by
  unfold tailWord_520298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4744206767264170167254387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12651218046037787112678365 4744206767264170167254387)
  ·
    refine ⟨7116310150896255250881581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4744206767264170167254387 7116310150896255250881581)
    ·
      refine ⟨2668616306586095719080593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7116310150896255250881581 2668616306586095719080593)
      ·
        refine ⟨2001462229939571789310445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2668616306586095719080593 2001462229939571789310445)
        ·
          refine ⟨750548336227339420991417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2001462229939571789310445 750548336227339420991417)
          ·
            refine ⟨562911252170504565743563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 750548336227339420991417 562911252170504565743563)
            ·
              refine ⟨844366878255756848615345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562911252170504565743563 844366878255756848615345)
              ·
                refine ⟨633275158691817636461509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844366878255756848615345 633275158691817636461509)
                ·
                  refine ⟨118739092254715806836533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 633275158691817636461509 118739092254715806836533)
                  ·
                    rfl

theorem cell21_520298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_520298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_520298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_520298 prefixEnd_520298 := by exact prefixLift 520298
  have htrace : WordTrace (prefixWord ++ tailWord_520298) baseStart_520298 baseEnd_520298 := by
    simpa [prefixWord, tailWord_520298, baseEnd_520298] using wordTrace_append hprefix tailTrace_520298
  have hstable : (prefixWord ++ tailWord_520298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520298).length < 2 ^ (prefixWord ++ tailWord_520298).sum := by decide
  have hdescent : baseEnd_520298 < baseStart_520298 := by decide
  rcases family_descends (prefixWord ++ tailWord_520298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520416 : List Nat := [2, 1, 1, 3, 1, 3, 4, 2, 4]
def baseStart_520416 : Nat := 118140960795 + 520416 * 2 ^ 59
def prefixEnd_520416 : Nat := 4983230072969 + 3 ^ 40 * 520416 * 2
def baseEnd_520416 : Nat := 118766021462373823869625

theorem tailTrace_520416 : CollatzResearch.WordTrace tailWord_520416 prefixEnd_520416 118766021462373823869625 := by
  unfold tailWord_520416
  simp only [CollatzResearch.WordTrace]
  refine ⟨9490565441314593410906551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12654087255086124547875401 9490565441314593410906551)
  ·
    refine ⟨14235848161971890116359827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9490565441314593410906551 14235848161971890116359827)
    ·
      refine ⟨21353772242957835174539741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14235848161971890116359827 21353772242957835174539741)
      ·
        refine ⟨8007664591109188190452403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21353772242957835174539741 8007664591109188190452403)
        ·
          refine ⟨12011496886663782285678605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8007664591109188190452403 12011496886663782285678605)
          ·
            refine ⟨4504311332498918357129477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12011496886663782285678605 4504311332498918357129477)
            ·
              refine ⟨844558374843547191961777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4504311332498918357129477 844558374843547191961777)
              ·
                refine ⟨633418781132660393971333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844558374843547191961777 633418781132660393971333)
                ·
                  refine ⟨118766021462373823869625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 633418781132660393971333 118766021462373823869625)
                  ·
                    rfl

theorem cell21_520416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_520416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_520416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_520416 prefixEnd_520416 := by exact prefixLift 520416
  have htrace : WordTrace (prefixWord ++ tailWord_520416) baseStart_520416 baseEnd_520416 := by
    simpa [prefixWord, tailWord_520416, baseEnd_520416] using wordTrace_append hprefix tailTrace_520416
  have hstable : (prefixWord ++ tailWord_520416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520416).length < 2 ^ (prefixWord ++ tailWord_520416).sum := by decide
  have hdescent : baseEnd_520416 < baseStart_520416 := by decide
  rcases family_descends (prefixWord ++ tailWord_520416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520506 : List Nat := [3, 1, 1, 1, 4, 3, 1, 7]
def baseStart_520506 : Nat := 118140960795 + 520506 * 2 ^ 59
def prefixEnd_520506 : Nat := 4983230072969 + 3 ^ 40 * 520506 * 2
def baseEnd_520506 : Nat := 39595520229517889123147

theorem tailTrace_520506 : CollatzResearch.WordTrace tailWord_520506 prefixEnd_520506 39595520229517889123147 := by
  unfold tailWord_520506
  simp only [CollatzResearch.WordTrace]
  refine ⟨4746103363075783048147343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12656275634868754795059581 4746103363075783048147343)
  ·
    refine ⟨7119155044613674572221015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4746103363075783048147343 7119155044613674572221015)
    ·
      refine ⟨10678732566920511858331523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7119155044613674572221015 10678732566920511858331523)
      ·
        refine ⟨16018098850380767787497285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10678732566920511858331523 16018098850380767787497285)
        ·
          refine ⟨3003393534446393960155741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16018098850380767787497285 3003393534446393960155741)
          ·
            refine ⟨1126272575417397735058403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3003393534446393960155741 1126272575417397735058403)
            ·
              refine ⟨1689408863126096602587605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126272575417397735058403 1689408863126096602587605)
              ·
                refine ⟨39595520229517889123147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1689408863126096602587605 39595520229517889123147)
                ·
                  rfl

theorem cell21_520506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_520506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_520506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_520506 prefixEnd_520506 := by exact prefixLift 520506
  have htrace : WordTrace (prefixWord ++ tailWord_520506) baseStart_520506 baseEnd_520506 := by
    simpa [prefixWord, tailWord_520506, baseEnd_520506] using wordTrace_append hprefix tailTrace_520506
  have hstable : (prefixWord ++ tailWord_520506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520506).length < 2 ^ (prefixWord ++ tailWord_520506).sum := by decide
  have hdescent : baseEnd_520506 < baseStart_520506 := by decide
  rcases family_descends (prefixWord ++ tailWord_520506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520520 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 7]
def baseStart_520520 : Nat := 118140960795 + 520520 * 2 ^ 59
def prefixEnd_520520 : Nat := 4983230072969 + 3 ^ 40 * 520520 * 2
def baseEnd_520520 : Nat := 118789755679292754136079

theorem tailTrace_520520 : CollatzResearch.WordTrace tailWord_520520 prefixEnd_520520 118789755679292754136079 := by
  unfold tailWord_520520
  simp only [CollatzResearch.WordTrace]
  refine ⟨9492462037126206291799507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12656616049501608389066009 9492462037126206291799507)
  ·
    refine ⟨14238693055689309437699261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9492462037126206291799507 14238693055689309437699261)
    ·
      refine ⟨5339509895883491039137223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14238693055689309437699261 5339509895883491039137223)
      ·
        refine ⟨8009264843825236558705835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5339509895883491039137223 8009264843825236558705835)
        ·
          refine ⟨12013897265737854838058753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8009264843825236558705835 12013897265737854838058753)
          ·
            refine ⟨9010422949303391128544065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12013897265737854838058753 9010422949303391128544065)
            ·
              refine ⟨6757817211977543346408049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9010422949303391128544065 6757817211977543346408049)
              ·
                refine ⟨5068362908983157509806037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6757817211977543346408049 5068362908983157509806037)
                ·
                  refine ⟨118789755679292754136079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5068362908983157509806037 118789755679292754136079)
                  ·
                    rfl

theorem cell21_520520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_520520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_520520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_520520 prefixEnd_520520 := by exact prefixLift 520520
  have htrace : WordTrace (prefixWord ++ tailWord_520520) baseStart_520520 baseEnd_520520 := by
    simpa [prefixWord, tailWord_520520, baseEnd_520520] using wordTrace_append hprefix tailTrace_520520
  have hstable : (prefixWord ++ tailWord_520520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520520).length < 2 ^ (prefixWord ++ tailWord_520520).sum := by decide
  have hdescent : baseEnd_520520 < baseStart_520520 := by decide
  rcases family_descends (prefixWord ++ tailWord_520520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
