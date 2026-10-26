import V185TrunkScan22Chunk404

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3612783 : List Nat := [1, 1, 2, 1, 3, 6, 2, 1, 5]
def baseStart_3612783 : Nat := 118140960795 + 3612783 * 2 ^ 59
def prefixEnd_3612783 : Nat := 4983230072969 + 3 ^ 40 * 3612783 * 2
def baseEnd_3612783 : Nat := 412243150976098600799471

theorem tailTrace_3612783 : CollatzResearch.WordTrace tailWord_3612783 prefixEnd_3612783 412243150976098600799471 := by
  unfold tailWord_3612783
  simp only [CollatzResearch.WordTrace]
  refine ⟨131769021270511680058499003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87846014180341120038999335 131769021270511680058499003)
  ·
    refine ⟨197653531905767520087748505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131769021270511680058499003 197653531905767520087748505)
    ·
      refine ⟨148240148929325640065811379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197653531905767520087748505 148240148929325640065811379)
      ·
        refine ⟨222360223393988460098717069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148240148929325640065811379 222360223393988460098717069)
        ·
          refine ⟨83385083772745672537018901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222360223393988460098717069 83385083772745672537018901)
          ·
            refine ⟨3908675801847453400172761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83385083772745672537018901 3908675801847453400172761)
            ·
              refine ⟨2931506851385590050129571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3908675801847453400172761 2931506851385590050129571)
              ·
                refine ⟨4397260277078385075194357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2931506851385590050129571 4397260277078385075194357)
                ·
                  refine ⟨412243150976098600799471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4397260277078385075194357 412243150976098600799471)
                  ·
                    rfl

theorem cell22_3612783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 5].length) (baseStart_3612783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612783 prefixEnd_3612783 := by exact prefixLift 3612783
  have htrace : WordTrace (prefixWord ++ tailWord_3612783) baseStart_3612783 baseEnd_3612783 := by
    simpa [prefixWord, tailWord_3612783, baseEnd_3612783] using wordTrace_append hprefix tailTrace_3612783
  have hstable : (prefixWord ++ tailWord_3612783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612783).length < 2 ^ (prefixWord ++ tailWord_3612783).sum := by decide
  have hdescent : baseEnd_3612783 < baseStart_3612783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612796 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 3, 4]
def baseStart_3612796 : Nat := 118140960795 + 3612796 * 2 ^ 59
def prefixEnd_3612796 : Nat := 4983230072969 + 3 ^ 40 * 3612796 * 2
def baseEnd_3612796 : Nat := 1236733903093968101823373

theorem tailTrace_3612796 : CollatzResearch.WordTrace tailWord_3612796 prefixEnd_3612796 1236733903093968101823373 := by
  unfold tailWord_3612796
  simp only [CollatzResearch.WordTrace]
  refine ⟨65884747709732291639361121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87846330279643055519148161 65884747709732291639361121)
  ·
    refine ⟨49413560782299218729520841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65884747709732291639361121 49413560782299218729520841)
    ·
      refine ⟨37060170586724414047140631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49413560782299218729520841 37060170586724414047140631)
      ·
        refine ⟨55590255880086621070710947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37060170586724414047140631 55590255880086621070710947)
        ·
          refine ⟨83385383820129931606066421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55590255880086621070710947 83385383820129931606066421)
          ·
            refine ⟨7817379733137181088068727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83385383820129931606066421 7817379733137181088068727)
            ·
              refine ⟨11726069599705771632103091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7817379733137181088068727 11726069599705771632103091)
              ·
                refine ⟨17589104399558657448154637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11726069599705771632103091 17589104399558657448154637)
                ·
                  refine ⟨6595914149834496543057989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17589104399558657448154637 6595914149834496543057989)
                  ·
                    refine ⟨1236733903093968101823373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6595914149834496543057989 1236733903093968101823373)
                    ·
                      rfl

theorem cell22_3612796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_3612796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612796 prefixEnd_3612796 := by exact prefixLift 3612796
  have htrace : WordTrace (prefixWord ++ tailWord_3612796) baseStart_3612796 baseEnd_3612796 := by
    simpa [prefixWord, tailWord_3612796, baseEnd_3612796] using wordTrace_append hprefix tailTrace_3612796
  have hstable : (prefixWord ++ tailWord_3612796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612796).length < 2 ^ (prefixWord ++ tailWord_3612796).sum := by decide
  have hdescent : baseEnd_3612796 < baseStart_3612796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612828 : List Nat := [2, 2, 3, 2, 1, 1, 3, 4, 4]
def baseStart_3612828 : Nat := 118140960795 + 3612828 * 2 ^ 59
def prefixEnd_3612828 : Nat := 4983230072969 + 3 ^ 40 * 3612828 * 2
def baseEnd_3612828 : Nat := 412248285782643561674425

theorem tailTrace_3612828 : CollatzResearch.WordTrace tailWord_3612828 prefixEnd_3612828 412248285782643561674425 := by
  unfold tailWord_3612828
  simp only [CollatzResearch.WordTrace]
  refine ⟨65885331277674326371943569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87847108370232435162591425 65885331277674326371943569)
  ·
    refine ⟨49413998458255744778957677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65885331277674326371943569 49413998458255744778957677)
    ·
      refine ⟨18530249421845904292109129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49413998458255744778957677 18530249421845904292109129)
      ·
        refine ⟨13897687066384428219081847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18530249421845904292109129 13897687066384428219081847)
        ·
          refine ⟨20846530599576642328622771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13897687066384428219081847 20846530599576642328622771)
          ·
            refine ⟨31269795899364963492934157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20846530599576642328622771 31269795899364963492934157)
            ·
              refine ⟨11726173462261861309850309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31269795899364963492934157 11726173462261861309850309)
              ·
                refine ⟨2198657524174098995596933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11726173462261861309850309 2198657524174098995596933)
                ·
                  refine ⟨412248285782643561674425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2198657524174098995596933 412248285782643561674425)
                  ·
                    rfl

theorem cell22_3612828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_3612828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612828 prefixEnd_3612828 := by exact prefixLift 3612828
  have htrace : WordTrace (prefixWord ++ tailWord_3612828) baseStart_3612828 baseEnd_3612828 := by
    simpa [prefixWord, tailWord_3612828, baseEnd_3612828] using wordTrace_append hprefix tailTrace_3612828
  have hstable : (prefixWord ++ tailWord_3612828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612828).length < 2 ^ (prefixWord ++ tailWord_3612828).sum := by decide
  have hdescent : baseEnd_3612828 < baseStart_3612828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612856 : List Nat := [2, 1, 2, 1, 2, 1, 7, 6]
def baseStart_3612856 : Nat := 118140960795 + 3612856 * 2 ^ 59
def prefixEnd_3612856 : Nat := 4983230072969 + 3 ^ 40 * 3612856 * 2
def baseEnd_3612856 : Nat := 137417160257794216147021

theorem tailTrace_3612856 : CollatzResearch.WordTrace tailWord_3612856 prefixEnd_3612856 137417160257794216147021 := by
  unfold tailWord_3612856
  simp only [CollatzResearch.WordTrace]
  refine ⟨65885841899623606762953211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87847789199498142350604281 65885841899623606762953211)
  ·
    refine ⟨98828762849435410144429817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65885841899623606762953211 98828762849435410144429817)
    ·
      refine ⟨74121572137076557608322363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98828762849435410144429817 74121572137076557608322363)
      ·
        refine ⟨111182358205614836412483545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74121572137076557608322363 111182358205614836412483545)
        ·
          refine ⟨83386768654211127309362659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111182358205614836412483545 83386768654211127309362659)
          ·
            refine ⟨125080152981316690964043989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83386768654211127309362659 125080152981316690964043989)
            ·
              refine ⟨2931566085499609944469781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 125080152981316690964043989 2931566085499609944469781)
              ·
                refine ⟨137417160257794216147021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2931566085499609944469781 137417160257794216147021)
                ·
                  rfl

theorem cell22_3612856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 6].length) (baseStart_3612856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612856 prefixEnd_3612856 := by exact prefixLift 3612856
  have htrace : WordTrace (prefixWord ++ tailWord_3612856) baseStart_3612856 baseEnd_3612856 := by
    simpa [prefixWord, tailWord_3612856, baseEnd_3612856] using wordTrace_append hprefix tailTrace_3612856
  have hstable : (prefixWord ++ tailWord_3612856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612856).length < 2 ^ (prefixWord ++ tailWord_3612856).sum := by decide
  have hdescent : baseEnd_3612856 < baseStart_3612856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612888 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 3, 3]
def baseStart_3612888 : Nat := 118140960795 + 3612888 * 2 ^ 59
def prefixEnd_3612888 : Nat := 4983230072969 + 3 ^ 40 * 3612888 * 2
def baseEnd_3612888 : Nat := 1236765396574110528523091

theorem tailTrace_3612888 : CollatzResearch.WordTrace tailWord_3612888 prefixEnd_3612888 1236765396574110528523091 := by
  unfold tailWord_3612888
  simp only [CollatzResearch.WordTrace]
  refine ⟨65886425467565641495535659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87848567290087521994047545 65886425467565641495535659)
  ·
    refine ⟨98829638201348462243303489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65886425467565641495535659 98829638201348462243303489)
    ·
      refine ⟨74122228651011346682477617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98829638201348462243303489 74122228651011346682477617)
      ·
        refine ⟨55591671488258510011858213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74122228651011346682477617 55591671488258510011858213)
        ·
          refine ⟨10423438404048470627223415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55591671488258510011858213 10423438404048470627223415)
          ·
            refine ⟨15635157606072705940835123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10423438404048470627223415 15635157606072705940835123)
            ·
              refine ⟨23452736409109058911252685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15635157606072705940835123 23452736409109058911252685)
              ·
                refine ⟨8794776153415897091719757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23452736409109058911252685 8794776153415897091719757)
                ·
                  refine ⟨3298041057530961409394909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8794776153415897091719757 3298041057530961409394909)
                  ·
                    refine ⟨1236765396574110528523091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3298041057530961409394909 1236765396574110528523091)
                    ·
                      rfl

theorem cell22_3612888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_3612888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612888 prefixEnd_3612888 := by exact prefixLift 3612888
  have htrace : WordTrace (prefixWord ++ tailWord_3612888) baseStart_3612888 baseEnd_3612888 := by
    simpa [prefixWord, tailWord_3612888, baseEnd_3612888] using wordTrace_append hprefix tailTrace_3612888
  have hstable : (prefixWord ++ tailWord_3612888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612888).length < 2 ^ (prefixWord ++ tailWord_3612888).sum := by decide
  have hdescent : baseEnd_3612888 < baseStart_3612888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612922 : List Nat := [3, 1, 1, 1, 1, 7, 1, 3, 1, 3]
def baseStart_3612922 : Nat := 118140960795 + 3612922 * 2 ^ 59
def prefixEnd_3612922 : Nat := 4983230072969 + 3 ^ 40 * 3612922 * 2
def baseEnd_3612922 : Nat := 1236777035468945773172987

theorem tailTrace_3612922 : CollatzResearch.WordTrace tailWord_3612922 prefixEnd_3612922 1236777035468945773172987 := by
  unfold tailWord_3612922
  simp only [CollatzResearch.WordTrace]
  refine ⟨32943522754252026699452255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87849394011338737865206013 32943522754252026699452255)
  ·
    refine ⟨49415284131378040049178383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32943522754252026699452255 49415284131378040049178383)
    ·
      refine ⟨74122926197067060073767575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49415284131378040049178383 74122926197067060073767575)
      ·
        refine ⟨111184389295600590110651363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74122926197067060073767575 111184389295600590110651363)
        ·
          refine ⟨166776583943400885165977045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111184389295600590110651363 166776583943400885165977045)
          ·
            refine ⟨3908826186173458246077587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 166776583943400885165977045 3908826186173458246077587)
            ·
              refine ⟨5863239279260187369116381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3908826186173458246077587 5863239279260187369116381)
              ·
                refine ⟨2198714729722570263418643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5863239279260187369116381 2198714729722570263418643)
                ·
                  refine ⟨3298072094583855395127965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2198714729722570263418643 3298072094583855395127965)
                  ·
                    refine ⟨1236777035468945773172987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3298072094583855395127965 1236777035468945773172987)
                    ·
                      rfl

theorem cell22_3612922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 1, 3].length) (baseStart_3612922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612922 prefixEnd_3612922 := by exact prefixLift 3612922
  have htrace : WordTrace (prefixWord ++ tailWord_3612922) baseStart_3612922 baseEnd_3612922 := by
    simpa [prefixWord, tailWord_3612922, baseEnd_3612922] using wordTrace_append hprefix tailTrace_3612922
  have hstable : (prefixWord ++ tailWord_3612922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612922).length < 2 ^ (prefixWord ++ tailWord_3612922).sum := by decide
  have hdescent : baseEnd_3612922 < baseStart_3612922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613008 : List Nat := [2, 1, 1, 1, 1, 8, 1, 7]
def baseStart_3613008 : Nat := 118140960795 + 3613008 * 2 ^ 59
def prefixEnd_3613008 : Nat := 4983230072969 + 3 ^ 40 * 3613008 * 2
def baseEnd_3613008 : Nat := 137422941669607801724747

theorem tailTrace_3613008 : CollatzResearch.WordTrace tailWord_3613008 prefixEnd_3613008 137422941669607801724747 := by
  unfold tailWord_3613008
  simp only [CollatzResearch.WordTrace]
  refine ⟨65888613847348271742719839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87851485129797695656959785 65888613847348271742719839)
  ·
    refine ⟨98832920771022407614079759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65888613847348271742719839 98832920771022407614079759)
    ·
      refine ⟨148249381156533611421119639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98832920771022407614079759 148249381156533611421119639)
      ·
        refine ⟨222374071734800417131679459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148249381156533611421119639 222374071734800417131679459)
        ·
          refine ⟨333561107602200625697519189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222374071734800417131679459 333561107602200625697519189)
          ·
            refine ⟨3908919229713288582392803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 333561107602200625697519189 3908919229713288582392803)
            ·
              refine ⟨5863378844569932873589205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3908919229713288582392803 5863378844569932873589205)
              ·
                refine ⟨137422941669607801724747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5863378844569932873589205 137422941669607801724747)
                ·
                  rfl

theorem cell22_3613008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 7].length) (baseStart_3613008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613008 prefixEnd_3613008 := by exact prefixLift 3613008
  have htrace : WordTrace (prefixWord ++ tailWord_3613008) baseStart_3613008 baseEnd_3613008 := by
    simpa [prefixWord, tailWord_3613008, baseEnd_3613008] using wordTrace_append hprefix tailTrace_3613008
  have hstable : (prefixWord ++ tailWord_3613008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613008).length < 2 ^ (prefixWord ++ tailWord_3613008).sum := by decide
  have hdescent : baseEnd_3613008 < baseStart_3613008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613023 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 5, 3]
def baseStart_3613023 : Nat := 118140960795 + 3613023 * 2 ^ 59
def prefixEnd_3613023 : Nat := 4983230072969 + 3 ^ 40 * 3613023 * 2
def baseEnd_3613023 : Nat := 1236811609833015176397677

theorem tailTrace_3613023 : CollatzResearch.WordTrace tailWord_3613023 prefixEnd_3613023 1236811609833015176397677 := by
  unfold tailWord_3613023
  simp only [CollatzResearch.WordTrace]
  refine ⟨131777774789642201047235723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87851849859761467364823815 131777774789642201047235723)
  ·
    refine ⟨197666662184463301570853585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131777774789642201047235723 197666662184463301570853585)
    ·
      refine ⟨148249996638347476178140189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197666662184463301570853585 148249996638347476178140189)
      ·
        refine ⟨55593748739380303566802571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148249996638347476178140189 55593748739380303566802571)
        ·
          refine ⟨83390623109070455350203857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55593748739380303566802571 83390623109070455350203857)
          ·
            refine ⟨62542967331802841512652893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83390623109070455350203857 62542967331802841512652893)
            ·
              refine ⟨23453612749426065567244835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62542967331802841512652893 23453612749426065567244835)
              ·
                refine ⟨35180419124139098350867253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23453612749426065567244835 35180419124139098350867253)
                ·
                  refine ⟨3298164292888040470393805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35180419124139098350867253 3298164292888040470393805)
                  ·
                    refine ⟨1236811609833015176397677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3298164292888040470393805 1236811609833015176397677)
                    ·
                      rfl

theorem cell22_3613023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 3].length) (baseStart_3613023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613023 prefixEnd_3613023 := by exact prefixLift 3613023
  have htrace : WordTrace (prefixWord ++ tailWord_3613023) baseStart_3613023 baseEnd_3613023 := by
    simpa [prefixWord, tailWord_3613023, baseEnd_3613023] using wordTrace_append hprefix tailTrace_3613023
  have hstable : (prefixWord ++ tailWord_3613023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613023).length < 2 ^ (prefixWord ++ tailWord_3613023).sum := by decide
  have hdescent : baseEnd_3613023 < baseStart_3613023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613046 : List Nat := [5, 1, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_3613046 : Nat := 118140960795 + 3613046 * 2 ^ 59
def prefixEnd_3613046 : Nat := 4983230072969 + 3 ^ 40 * 3613046 * 2
def baseEnd_3613046 : Nat := 1236819483203050783072607

theorem tailTrace_3613046 : CollatzResearch.WordTrace tailWord_3613046 prefixEnd_3613046 1236819483203050783072607 := by
  unfold tailWord_3613046
  simp only [CollatzResearch.WordTrace]
  refine ⟨8236163354284929748457687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87852409112372583983548661 8236163354284929748457687)
  ·
    refine ⟨12354245031427394622686531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8236163354284929748457687 12354245031427394622686531)
    ·
      refine ⟨18531367547141091934029797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12354245031427394622686531 18531367547141091934029797)
      ·
        refine ⟨3474631415088954737630587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18531367547141091934029797 3474631415088954737630587)
        ·
          refine ⟨5211947122633432106445881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3474631415088954737630587 5211947122633432106445881)
          ·
            refine ⟨3908960341975074079834411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5211947122633432106445881 3908960341975074079834411)
            ·
              refine ⟨5863440512962611119751617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3908960341975074079834411 5863440512962611119751617)
              ·
                refine ⟨4397580384721958339813713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5863440512962611119751617 4397580384721958339813713)
                ·
                  refine ⟨3298185288541468754860285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4397580384721958339813713 3298185288541468754860285)
                  ·
                    refine ⟨1236819483203050783072607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3298185288541468754860285 1236819483203050783072607)
                    ·
                      rfl

theorem cell22_3613046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_3613046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613046 prefixEnd_3613046 := by exact prefixLift 3613046
  have htrace : WordTrace (prefixWord ++ tailWord_3613046) baseStart_3613046 baseEnd_3613046 := by
    simpa [prefixWord, tailWord_3613046, baseEnd_3613046] using wordTrace_append hprefix tailTrace_3613046
  have hstable : (prefixWord ++ tailWord_3613046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613046).length < 2 ^ (prefixWord ++ tailWord_3613046).sum := by decide
  have hdescent : baseEnd_3613046 < baseStart_3613046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613053 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 7]
def baseStart_3613053 : Nat := 118140960795 + 3613053 * 2 ^ 59
def prefixEnd_3613053 : Nat := 4983230072969 + 3 ^ 40 * 3613053 * 2
def baseEnd_3613053 : Nat := 412273959815368366049195

theorem tailTrace_3613053 : CollatzResearch.WordTrace tailWord_3613053 prefixEnd_3613053 412273959815368366049195 := by
  unfold tailWord_3613053
  simp only [CollatzResearch.WordTrace]
  refine ⟨131778868979533516170827813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87852579319689010780551875 131778868979533516170827813)
  ·
    refine ⟨24708537933662534282030215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131778868979533516170827813 24708537933662534282030215)
    ·
      refine ⟨37062806900493801423045323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24708537933662534282030215 37062806900493801423045323)
      ·
        refine ⟨55594210350740702134567985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37062806900493801423045323 55594210350740702134567985)
        ·
          refine ⟨41695657763055526600925989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55594210350740702134567985 41695657763055526600925989)
          ·
            refine ⟨7817935830572911237673623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41695657763055526600925989 7817935830572911237673623)
            ·
              refine ⟨11726903745859366856510435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7817935830572911237673623 11726903745859366856510435)
              ·
                refine ⟨17590355618789050284765653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11726903745859366856510435 17590355618789050284765653)
                ·
                  refine ⟨412273959815368366049195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17590355618789050284765653 412273959815368366049195)
                  ·
                    rfl

theorem cell22_3613053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_3613053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613053 prefixEnd_3613053 := by exact prefixLift 3613053
  have htrace : WordTrace (prefixWord ++ tailWord_3613053) baseStart_3613053 baseEnd_3613053 := by
    simpa [prefixWord, tailWord_3613053, baseEnd_3613053] using wordTrace_append hprefix tailTrace_3613053
  have hstable : (prefixWord ++ tailWord_3613053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613053).length < 2 ^ (prefixWord ++ tailWord_3613053).sum := by decide
  have hdescent : baseEnd_3613053 < baseStart_3613053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613057 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 3, 3]
def baseStart_3613057 : Nat := 118140960795 + 3613057 * 2 ^ 59
def prefixEnd_3613057 : Nat := 4983230072969 + 3 ^ 40 * 3613057 * 2
def baseEnd_3613057 : Nat := 1236823248727850421047573

theorem tailTrace_3613057 : CollatzResearch.WordTrace tailWord_3613057 prefixEnd_3613057 1236823248727850421047573 := by
  unfold tailWord_3613057
  simp only [CollatzResearch.WordTrace]
  refine ⟨131779014871519024853973425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87852676581012683235982283 131779014871519024853973425)
  ·
    refine ⟨98834261153639268640480069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131779014871519024853973425 98834261153639268640480069)
    ·
      refine ⟨18531423966307362870090013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98834261153639268640480069 18531423966307362870090013)
      ·
        refine ⟨6949283987365261076283755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18531423966307362870090013 6949283987365261076283755)
        ·
          refine ⟨10423925981047891614425633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6949283987365261076283755 10423925981047891614425633)
          ·
            refine ⟨7817944485785918710819225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10423925981047891614425633 7817944485785918710819225)
            ·
              refine ⟨5863458364339439033114419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7817944485785918710819225 5863458364339439033114419)
              ·
                refine ⟨8795187546509158549671629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5863458364339439033114419 8795187546509158549671629)
                ·
                  refine ⟨3298195329940934456126861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8795187546509158549671629 3298195329940934456126861)
                  ·
                    refine ⟨1236823248727850421047573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3298195329940934456126861 1236823248727850421047573)
                    ·
                      rfl

theorem cell22_3613057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_3613057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613057 prefixEnd_3613057 := by exact prefixLift 3613057
  have htrace : WordTrace (prefixWord ++ tailWord_3613057) baseStart_3613057 baseEnd_3613057 := by
    simpa [prefixWord, tailWord_3613057, baseEnd_3613057] using wordTrace_append hprefix tailTrace_3613057
  have hstable : (prefixWord ++ tailWord_3613057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613057).length < 2 ^ (prefixWord ++ tailWord_3613057).sum := by decide
  have hdescent : baseEnd_3613057 < baseStart_3613057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613068 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 2, 5]
def baseStart_3613068 : Nat := 118140960795 + 3613068 * 2 ^ 59
def prefixEnd_3613068 : Nat := 4983230072969 + 3 ^ 40 * 3613068 * 2
def baseEnd_3613068 : Nat := 1236827014252650059022539

theorem tailTrace_3613068 : CollatzResearch.WordTrace tailWord_3613068 prefixEnd_3613068 1236827014252650059022539 := by
  unfold tailWord_3613068
  simp only [CollatzResearch.WordTrace]
  refine ⟨65889708037239586866311929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87852944049652782488415905 65889708037239586866311929)
  ·
    refine ⟨49417281027929690149733947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65889708037239586866311929 49417281027929690149733947)
    ·
      refine ⟨74125921541894535224600921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49417281027929690149733947 74125921541894535224600921)
      ·
        refine ⟨55594441156420901418450691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74125921541894535224600921 55594441156420901418450691)
        ·
          refine ⟨83391661734631352127676037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55594441156420901418450691 83391661734631352127676037)
          ·
            refine ⟨15635936575243378523939257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83391661734631352127676037 15635936575243378523939257)
            ·
              refine ⟨11726952431432533892954443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15635936575243378523939257 11726952431432533892954443)
              ·
                refine ⟨17590428647148800839431665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11726952431432533892954443 17590428647148800839431665)
                ·
                  refine ⟨13192821485361600629573749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17590428647148800839431665 13192821485361600629573749)
                  ·
                    refine ⟨1236827014252650059022539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13192821485361600629573749 1236827014252650059022539)
                    ·
                      rfl

theorem cell22_3613068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_3613068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613068 prefixEnd_3613068 := by exact prefixLift 3613068
  have htrace : WordTrace (prefixWord ++ tailWord_3613068) baseStart_3613068 baseEnd_3613068 := by
    simpa [prefixWord, tailWord_3613068, baseEnd_3613068] using wordTrace_append hprefix tailTrace_3613068
  have hstable : (prefixWord ++ tailWord_3613068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613068).length < 2 ^ (prefixWord ++ tailWord_3613068).sum := by decide
  have hdescent : baseEnd_3613068 < baseStart_3613068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613108 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_3613108 : Nat := 118140960795 + 3613108 * 2 ^ 59
def prefixEnd_3613108 : Nat := 4983230072969 + 3 ^ 40 * 3613108 * 2
def baseEnd_3613108 : Nat := 1236840707070103288022417

theorem tailTrace_3613108 : CollatzResearch.WordTrace tailWord_3613108 prefixEnd_3613108 1236840707070103288022417 := by
  unfold tailWord_3613108
  simp only [CollatzResearch.WordTrace]
  refine ⟨65890437497167130282039989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87853916662889507042719985 65890437497167130282039989)
  ·
    refine ⟨6177228515359418463941249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65890437497167130282039989 6177228515359418463941249)
    ·
      refine ⟨4632921386519563847955937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6177228515359418463941249 4632921386519563847955937)
      ·
        refine ⟨3474691039889672885966953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4632921386519563847955937 3474691039889672885966953)
        ·
          refine ⟨2606018279917254664475215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3474691039889672885966953 2606018279917254664475215)
          ·
            refine ⟨3909027419875881996712823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606018279917254664475215 3909027419875881996712823)
            ·
              refine ⟨5863541129813822995069235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3909027419875881996712823 5863541129813822995069235)
              ·
                refine ⟨8795311694720734492603853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5863541129813822995069235 8795311694720734492603853)
                ·
                  refine ⟨3298241885520275434726445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8795311694720734492603853 3298241885520275434726445)
                  ·
                    refine ⟨1236840707070103288022417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3298241885520275434726445 1236840707070103288022417)
                    ·
                      rfl

theorem cell22_3613108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_3613108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613108 prefixEnd_3613108 := by exact prefixLift 3613108
  have htrace : WordTrace (prefixWord ++ tailWord_3613108) baseStart_3613108 baseEnd_3613108 := by
    simpa [prefixWord, tailWord_3613108, baseEnd_3613108] using wordTrace_append hprefix tailTrace_3613108
  have hstable : (prefixWord ++ tailWord_3613108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613108).length < 2 ^ (prefixWord ++ tailWord_3613108).sum := by decide
  have hdescent : baseEnd_3613108 < baseStart_3613108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613145 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 2, 4]
def baseStart_3613145 : Nat := 118140960795 + 3613145 * 2 ^ 59
def prefixEnd_3613145 : Nat := 4983230072969 + 3 ^ 40 * 3613145 * 2
def baseEnd_3613145 : Nat := 1236853372926247524847303

theorem tailTrace_3613145 : CollatzResearch.WordTrace tailWord_3613145 prefixEnd_3613145 1236853372926247524847303 := by
  unfold tailWord_3613145
  simp only [CollatzResearch.WordTrace]
  refine ⟨131782224495200215883176889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87854816330133477255451259 131782224495200215883176889)
  ·
    refine ⟨98836668371400161912382667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131782224495200215883176889 98836668371400161912382667)
    ·
      refine ⟨148255002557100242868574001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98836668371400161912382667 148255002557100242868574001)
      ·
        refine ⟨111191251917825182151430501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148255002557100242868574001 111191251917825182151430501)
        ·
          refine ⟨20848359734592221653393219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111191251917825182151430501 20848359734592221653393219)
          ·
            refine ⟨31272539601888332480089829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20848359734592221653393219 31272539601888332480089829)
            ·
              refine ⟨5863601175354062340016843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31272539601888332480089829 5863601175354062340016843)
              ·
                refine ⟨8795401763031093510025265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5863601175354062340016843 8795401763031093510025265)
                ·
                  refine ⟨6596551322273320132518949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8795401763031093510025265 6596551322273320132518949)
                  ·
                    refine ⟨1236853372926247524847303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6596551322273320132518949 1236853372926247524847303)
                    ·
                      rfl

theorem cell22_3613145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 4].length) (baseStart_3613145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613145 prefixEnd_3613145 := by exact prefixLift 3613145
  have htrace : WordTrace (prefixWord ++ tailWord_3613145) baseStart_3613145 baseEnd_3613145 := by
    simpa [prefixWord, tailWord_3613145, baseEnd_3613145] using wordTrace_append hprefix tailTrace_3613145
  have hstable : (prefixWord ++ tailWord_3613145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613145).length < 2 ^ (prefixWord ++ tailWord_3613145).sum := by decide
  have hdescent : baseEnd_3613145 < baseStart_3613145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613203 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 1, 7]
def baseStart_3613203 : Nat := 118140960795 + 3613203 * 2 ^ 59
def prefixEnd_3613203 : Nat := 4983230072969 + 3 ^ 40 * 3613203 * 2
def baseEnd_3613203 : Nat := 1236873227511554706897125

theorem tailTrace_3613203 : CollatzResearch.WordTrace tailWord_3613203 prefixEnd_3613203 1236873227511554706897125 := by
  unfold tailWord_3613203
  simp only [CollatzResearch.WordTrace]
  refine ⟨131784339928990091788788263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87856226619326727859192175 131784339928990091788788263)
  ·
    refine ⟨197676509893485137683182395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131784339928990091788788263 197676509893485137683182395)
    ·
      refine ⟨296514764840227706524773593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197676509893485137683182395 296514764840227706524773593)
      ·
        refine ⟨222386073630170779893580195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296514764840227706524773593 222386073630170779893580195)
        ·
          refine ⟨333579110445256169840370293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222386073630170779893580195 333579110445256169840370293)
          ·
            refine ⟨31273041604242765922534715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 333579110445256169840370293 31273041604242765922534715)
            ·
              refine ⟨46909562406364148883802073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31273041604242765922534715 46909562406364148883802073)
              ·
                refine ⟨35182171804773111662851555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46909562406364148883802073 35182171804773111662851555)
                ·
                  refine ⟨52773257707159667494277333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35182171804773111662851555 52773257707159667494277333)
                  ·
                    refine ⟨1236873227511554706897125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52773257707159667494277333 1236873227511554706897125)
                    ·
                      rfl

theorem cell22_3613203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 7].length) (baseStart_3613203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613203 prefixEnd_3613203 := by exact prefixLift 3613203
  have htrace : WordTrace (prefixWord ++ tailWord_3613203) baseStart_3613203 baseEnd_3613203 := by
    simpa [prefixWord, tailWord_3613203, baseEnd_3613203] using wordTrace_append hprefix tailTrace_3613203
  have hstable : (prefixWord ++ tailWord_3613203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613203).length < 2 ^ (prefixWord ++ tailWord_3613203).sum := by decide
  have hdescent : baseEnd_3613203 < baseStart_3613203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613280 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 4, 4]
def baseStart_3613280 : Nat := 118140960795 + 3613280 * 2 ^ 59
def prefixEnd_3613280 : Nat := 4983230072969 + 3 ^ 40 * 3613280 * 2
def baseEnd_3613280 : Nat := 1236899586185152172721889

theorem tailTrace_3613280 : CollatzResearch.WordTrace tailWord_3613280 prefixEnd_3613280 1236899586185152172721889 := by
  unfold tailWord_3613280
  simp only [CollatzResearch.WordTrace]
  refine ⟨65893574174855566969670647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87858098899807422626227529 65893574174855566969670647)
  ·
    refine ⟨98840361262283350454505971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65893574174855566969670647 98840361262283350454505971)
    ·
      refine ⟨148260541893425025681758957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98840361262283350454505971 148260541893425025681758957)
      ·
        refine ⟨55597703210034384630659609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148260541893425025681758957 55597703210034384630659609)
        ·
          refine ⟨41698277407525788472994707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55597703210034384630659609 41698277407525788472994707)
          ·
            refine ⟨62547416111288682709492061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41698277407525788472994707 62547416111288682709492061)
            ·
              refine ⟨23455281041733256016059523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62547416111288682709492061 23455281041733256016059523)
              ·
                refine ⟨35182921562599884024089285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23455281041733256016059523 35182921562599884024089285)
                ·
                  refine ⟨6596797792987478254516741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35182921562599884024089285 6596797792987478254516741)
                  ·
                    refine ⟨1236899586185152172721889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6596797792987478254516741 1236899586185152172721889)
                    ·
                      rfl

theorem cell22_3613280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_3613280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613280 prefixEnd_3613280 := by exact prefixLift 3613280
  have htrace : WordTrace (prefixWord ++ tailWord_3613280) baseStart_3613280 baseEnd_3613280 := by
    simpa [prefixWord, tailWord_3613280, baseEnd_3613280] using wordTrace_append hprefix tailTrace_3613280
  have hstable : (prefixWord ++ tailWord_3613280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613280).length < 2 ^ (prefixWord ++ tailWord_3613280).sum := by decide
  have hdescent : baseEnd_3613280 < baseStart_3613280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613284 : List Nat := [2, 3, 1, 1, 2, 2, 5, 2, 4]
def baseStart_3613284 : Nat := 118140960795 + 3613284 * 2 ^ 59
def prefixEnd_3613284 : Nat := 4983230072969 + 3 ^ 40 * 3613284 * 2
def baseEnd_3613284 : Nat := 412300318488965831873959

theorem tailTrace_3613284 : CollatzResearch.WordTrace tailWord_3613284 prefixEnd_3613284 412300318488965831873959 := by
  unfold tailWord_3613284
  simp only [CollatzResearch.WordTrace]
  refine ⟨65893647120848321311243453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87858196161131095081657937 65893647120848321311243453)
  ·
    refine ⟨24710117670318120491716295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65893647120848321311243453 24710117670318120491716295)
    ·
      refine ⟨37065176505477180737574443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24710117670318120491716295 37065176505477180737574443)
      ·
        refine ⟨55597764758215771106361665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37065176505477180737574443 55597764758215771106361665)
        ·
          refine ⟨41698323568661828329771249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55597764758215771106361665 41698323568661828329771249)
          ·
            refine ⟨31273742676496371247328437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41698323568661828329771249 31273742676496371247328437)
            ·
              refine ⟨2931913375921534804437041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31273742676496371247328437 2931913375921534804437041)
              ·
                refine ⟨2198935031941151103327781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2931913375921534804437041 2198935031941151103327781)
                ·
                  refine ⟨412300318488965831873959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2198935031941151103327781 412300318488965831873959)
                  ·
                    rfl

theorem cell22_3613284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_3613284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613284 prefixEnd_3613284 := by exact prefixLift 3613284
  have htrace : WordTrace (prefixWord ++ tailWord_3613284) baseStart_3613284 baseEnd_3613284 := by
    simpa [prefixWord, tailWord_3613284, baseEnd_3613284] using wordTrace_append hprefix tailTrace_3613284
  have hstable : (prefixWord ++ tailWord_3613284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613284).length < 2 ^ (prefixWord ++ tailWord_3613284).sum := by decide
  have hdescent : baseEnd_3613284 < baseStart_3613284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613342 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_3613342 : Nat := 118140960795 + 3613342 * 2 ^ 59
def prefixEnd_3613342 : Nat := 4983230072969 + 3 ^ 40 * 3613342 * 2
def baseEnd_3613342 : Nat := 1236920810052204677671699

theorem tailTrace_3613342 : CollatzResearch.WordTrace tailWord_3613342 prefixEnd_3613342 1236920810052204677671699 := by
  unfold tailWord_3613342
  simp only [CollatzResearch.WordTrace]
  refine ⟨16473676209435814816012285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87859606450324345685398853 16473676209435814816012285)
  ·
    refine ⟨6177628578538430556004607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16473676209435814816012285 6177628578538430556004607)
    ·
      refine ⟨9266442867807645834006911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6177628578538430556004607 9266442867807645834006911)
      ·
        refine ⟨13899664301711468751010367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9266442867807645834006911 13899664301711468751010367)
        ·
          refine ⟨20849496452567203126515551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13899664301711468751010367 20849496452567203126515551)
          ·
            refine ⟨31274244678850804689773327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20849496452567203126515551 31274244678850804689773327)
            ·
              refine ⟨46911367018276207034659991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31274244678850804689773327 46911367018276207034659991)
              ·
                refine ⟨70367050527414310551989987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46911367018276207034659991 70367050527414310551989987)
                ·
                  refine ⟨105550575791121465827984981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70367050527414310551989987 105550575791121465827984981)
                  ·
                    refine ⟨1236920810052204677671699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105550575791121465827984981 1236920810052204677671699)
                    ·
                      rfl

theorem cell22_3613342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_3613342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613342 prefixEnd_3613342 := by exact prefixLift 3613342
  have htrace : WordTrace (prefixWord ++ tailWord_3613342) baseStart_3613342 baseEnd_3613342 := by
    simpa [prefixWord, tailWord_3613342, baseEnd_3613342] using wordTrace_append hprefix tailTrace_3613342
  have hstable : (prefixWord ++ tailWord_3613342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613342).length < 2 ^ (prefixWord ++ tailWord_3613342).sum := by decide
  have hdescent : baseEnd_3613342 < baseStart_3613342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613361 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 3, 3]
def baseStart_3613361 : Nat := 118140960795 + 3613361 * 2 ^ 59
def prefixEnd_3613361 : Nat := 4983230072969 + 3 ^ 40 * 3613361 * 2
def baseEnd_3613361 : Nat := 1236927314140494961446641

theorem tailTrace_3613361 : CollatzResearch.WordTrace tailWord_3613361 prefixEnd_3613361 1236927314140494961446641 := by
  unfold tailWord_3613361
  simp only [CollatzResearch.WordTrace]
  refine ⟨131790102662417684773039937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87860068441611789848693291 131790102662417684773039937)
  ·
    refine ⟨98842576996813263579779953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131790102662417684773039937 98842576996813263579779953)
    ·
      refine ⟨74131932747609947684834965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98842576996813263579779953 74131932747609947684834965)
      ·
        refine ⟨3474934347544216297726639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74131932747609947684834965 3474934347544216297726639)
        ·
          refine ⟨5212401521316324446589959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3474934347544216297726639 5212401521316324446589959)
          ·
            refine ⟨7818602281974486669884939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5212401521316324446589959 7818602281974486669884939)
            ·
              refine ⟨11727903422961730004827409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7818602281974486669884939 11727903422961730004827409)
              ·
                refine ⟨8795927567221297503620557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11727903422961730004827409 8795927567221297503620557)
                ·
                  refine ⟨3298472837707986563857709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8795927567221297503620557 3298472837707986563857709)
                  ·
                    refine ⟨1236927314140494961446641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3298472837707986563857709 1236927314140494961446641)
                    ·
                      rfl

theorem cell22_3613361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_3613361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613361 prefixEnd_3613361 := by exact prefixLift 3613361
  have htrace : WordTrace (prefixWord ++ tailWord_3613361) baseStart_3613361 baseEnd_3613361 := by
    simpa [prefixWord, tailWord_3613361, baseEnd_3613361] using wordTrace_append hprefix tailTrace_3613361
  have hstable : (prefixWord ++ tailWord_3613361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613361).length < 2 ^ (prefixWord ++ tailWord_3613361).sum := by decide
  have hdescent : baseEnd_3613361 < baseStart_3613361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613402 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 6]
def baseStart_3613402 : Nat := 118140960795 + 3613402 * 2 ^ 59
def prefixEnd_3613402 : Nat := 4983230072969 + 3 ^ 40 * 3613402 * 2
def baseEnd_3613402 : Nat := 412313783092794840390505

theorem tailTrace_3613402 : CollatzResearch.WordTrace tailWord_3613402 prefixEnd_3613402 412313783092794840390505 := by
  unfold tailWord_3613402
  simp only [CollatzResearch.WordTrace]
  refine ⟨32947899513817287193820615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87861065370179432516854973 32947899513817287193820615)
  ·
    refine ⟨49421849270725930790730923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32947899513817287193820615 49421849270725930790730923)
    ·
      refine ⟨74132773906088896186096385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49421849270725930790730923 74132773906088896186096385)
      ·
        refine ⟨55599580429566672139572289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74132773906088896186096385 55599580429566672139572289)
        ·
          refine ⟨41699685322175004104679217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55599580429566672139572289 41699685322175004104679217)
          ·
            refine ⟨31274763991631253078509413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41699685322175004104679217 31274763991631253078509413)
            ·
              refine ⟨5864018248430859952220515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31274763991631253078509413 5864018248430859952220515)
              ·
                refine ⟨8796027372646289928330773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5864018248430859952220515 8796027372646289928330773)
                ·
                  refine ⟨412313783092794840390505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8796027372646289928330773 412313783092794840390505)
                  ·
                    rfl

theorem cell22_3613402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_3613402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613402 prefixEnd_3613402 := by exact prefixLift 3613402
  have htrace : WordTrace (prefixWord ++ tailWord_3613402) baseStart_3613402 baseEnd_3613402 := by
    simpa [prefixWord, tailWord_3613402, baseEnd_3613402] using wordTrace_append hprefix tailTrace_3613402
  have hstable : (prefixWord ++ tailWord_3613402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613402).length < 2 ^ (prefixWord ++ tailWord_3613402).sum := by decide
  have hdescent : baseEnd_3613402 < baseStart_3613402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613417 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 1, 5]
def baseStart_3613417 : Nat := 118140960795 + 3613417 * 2 ^ 59
def prefixEnd_3613417 : Nat := 4983230072969 + 3 ^ 40 * 3613417 * 2
def baseEnd_3613417 : Nat := 1236946484084929482046469

theorem tailTrace_3613417 : CollatzResearch.WordTrace tailWord_3613417 prefixEnd_3613417 1236946484084929482046469 := by
  unfold tailWord_3613417
  simp only [CollatzResearch.WordTrace]
  refine ⟨131792145150214806337078505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87861430100143204224719003 131792145150214806337078505)
  ·
    refine ⟨98844108862661104752808879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131792145150214806337078505 98844108862661104752808879)
    ·
      refine ⟨148266163293991657129213319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98844108862661104752808879 148266163293991657129213319)
      ·
        refine ⟨222399244940987485693819979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148266163293991657129213319 222399244940987485693819979)
        ·
          refine ⟨333598867411481228540729969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222399244940987485693819979 333598867411481228540729969)
          ·
            refine ⟨250199150558610921405547477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333598867411481228540729969 250199150558610921405547477)
            ·
              refine ⟨5864042591217443470442519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 250199150558610921405547477 5864042591217443470442519)
              ·
                refine ⟨8796063886826165205663779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5864042591217443470442519 8796063886826165205663779)
                ·
                  refine ⟨13194095830239247808495669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8796063886826165205663779 13194095830239247808495669)
                  ·
                    refine ⟨1236946484084929482046469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13194095830239247808495669 1236946484084929482046469)
                    ·
                      rfl

theorem cell22_3613417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 5].length) (baseStart_3613417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613417 prefixEnd_3613417 := by exact prefixLift 3613417
  have htrace : WordTrace (prefixWord ++ tailWord_3613417) baseStart_3613417 baseEnd_3613417 := by
    simpa [prefixWord, tailWord_3613417, baseEnd_3613417] using wordTrace_append hprefix tailTrace_3613417
  have hstable : (prefixWord ++ tailWord_3613417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613417).length < 2 ^ (prefixWord ++ tailWord_3613417).sum := by decide
  have hdescent : baseEnd_3613417 < baseStart_3613417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613429 : List Nat := [1, 3, 6, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3613429 : Nat := 118140960795 + 3613429 * 2 ^ 59
def prefixEnd_3613429 : Nat := 4983230072969 + 3 ^ 40 * 3613429 * 2
def baseEnd_3613429 : Nat := 1236950591930165450746433

theorem tailTrace_3613429 : CollatzResearch.WordTrace tailWord_3613429 prefixEnd_3613429 1236950591930165450746433 := by
  unfold tailWord_3613429
  simp only [CollatzResearch.WordTrace]
  refine ⟨131792582826171332386515341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87861721884114221591010227 131792582826171332386515341)
  ·
    refine ⟨49422218559814249644943253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131792582826171332386515341 49422218559814249644943253)
    ·
      refine ⟨2316666494991292952106715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49422218559814249644943253 2316666494991292952106715)
      ·
        refine ⟨3474999742486939428160073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2316666494991292952106715 3474999742486939428160073)
        ·
          refine ⟨2606249806865204571120055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3474999742486939428160073 2606249806865204571120055)
          ·
            refine ⟨3909374710297806856680083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606249806865204571120055 3909374710297806856680083)
            ·
              refine ⟨5864062065446710285020125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3909374710297806856680083 5864062065446710285020125)
              ·
                refine ⟨2199023274542516356882547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5864062065446710285020125 2199023274542516356882547)
                ·
                  refine ⟨3298534911813774535323821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2199023274542516356882547 3298534911813774535323821)
                  ·
                    refine ⟨1236950591930165450746433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3298534911813774535323821 1236950591930165450746433)
                    ·
                      rfl

theorem cell22_3613429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3613429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613429 prefixEnd_3613429 := by exact prefixLift 3613429
  have htrace : WordTrace (prefixWord ++ tailWord_3613429) baseStart_3613429 baseEnd_3613429 := by
    simpa [prefixWord, tailWord_3613429, baseEnd_3613429] using wordTrace_append hprefix tailTrace_3613429
  have hstable : (prefixWord ++ tailWord_3613429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613429).length < 2 ^ (prefixWord ++ tailWord_3613429).sum := by decide
  have hdescent : baseEnd_3613429 < baseStart_3613429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613432 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 2, 4]
def baseStart_3613432 : Nat := 118140960795 + 3613432 * 2 ^ 59
def prefixEnd_3613432 : Nat := 4983230072969 + 3 ^ 40 * 3613432 * 2
def baseEnd_3613432 : Nat := 1236951618891474442921423

theorem tailTrace_3613432 : CollatzResearch.WordTrace tailWord_3613432 prefixEnd_3613432 1236951618891474442921423 := by
  unfold tailWord_3613432
  simp only [CollatzResearch.WordTrace]
  refine ⟨65896346122580231949437275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87861794830106975932583033 65896346122580231949437275)
  ·
    refine ⟨98844519183870347924155913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65896346122580231949437275 98844519183870347924155913)
    ·
      refine ⟨74133389387902760943116935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98844519183870347924155913 74133389387902760943116935)
      ·
        refine ⟨111200084081854141414675403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74133389387902760943116935 111200084081854141414675403)
        ·
          refine ⟨166800126122781212122013105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111200084081854141414675403 166800126122781212122013105)
          ·
            refine ⟨125100094592085909091509829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166800126122781212122013105 125100094592085909091509829)
            ·
              refine ⟨23456267736016107954658093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125100094592085909091509829 23456267736016107954658093)
              ·
                refine ⟨8796100401006040482996785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23456267736016107954658093 8796100401006040482996785)
                ·
                  refine ⟨6597075300754530362247589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8796100401006040482996785 6597075300754530362247589)
                  ·
                    refine ⟨1236951618891474442921423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6597075300754530362247589 1236951618891474442921423)
                    ·
                      rfl

theorem cell22_3613432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_3613432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613432 prefixEnd_3613432 := by exact prefixLift 3613432
  have htrace : WordTrace (prefixWord ++ tailWord_3613432) baseStart_3613432 baseEnd_3613432 := by
    simpa [prefixWord, tailWord_3613432, baseEnd_3613432] using wordTrace_append hprefix tailTrace_3613432
  have hstable : (prefixWord ++ tailWord_3613432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613432).length < 2 ^ (prefixWord ++ tailWord_3613432).sum := by decide
  have hdescent : baseEnd_3613432 < baseStart_3613432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613436 : List Nat := [2, 2, 2, 1, 3, 4, 1, 3, 4]
def baseStart_3613436 : Nat := 118140960795 + 3613436 * 2 ^ 59
def prefixEnd_3613436 : Nat := 4983230072969 + 3 ^ 40 * 3613436 * 2
def baseEnd_3613436 : Nat := 412317662724406588607137

theorem tailTrace_3613436 : CollatzResearch.WordTrace tailWord_3613436 prefixEnd_3613436 412317662724406588607137 := by
  unfold tailWord_3613436
  simp only [CollatzResearch.WordTrace]
  refine ⟨65896419068572986291010081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87861892091430648388013441 65896419068572986291010081)
  ·
    refine ⟨49422314301429739718257561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65896419068572986291010081 49422314301429739718257561)
    ·
      refine ⟨37066735726072304788693171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49422314301429739718257561 37066735726072304788693171)
      ·
        refine ⟨55600103589108457183039757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37066735726072304788693171 55600103589108457183039757)
        ·
          refine ⟨20850038845915671443639909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55600103589108457183039757 20850038845915671443639909)
          ·
            refine ⟨3909382283609188395682483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20850038845915671443639909 3909382283609188395682483)
            ·
              refine ⟨5864073425413782593523725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3909382283609188395682483 5864073425413782593523725)
              ·
                refine ⟨2199027534530168472571397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5864073425413782593523725 2199027534530168472571397)
                ·
                  refine ⟨412317662724406588607137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2199027534530168472571397 412317662724406588607137)
                  ·
                    rfl

theorem cell22_3613436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_3613436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613436 prefixEnd_3613436 := by exact prefixLift 3613436
  have htrace : WordTrace (prefixWord ++ tailWord_3613436) baseStart_3613436 baseEnd_3613436 := by
    simpa [prefixWord, tailWord_3613436, baseEnd_3613436] using wordTrace_append hprefix tailTrace_3613436
  have hstable : (prefixWord ++ tailWord_3613436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613436).length < 2 ^ (prefixWord ++ tailWord_3613436).sum := by decide
  have hdescent : baseEnd_3613436 < baseStart_3613436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613447 : List Nat := [1, 1, 4, 4, 1, 1, 10]
def baseStart_3613447 : Nat := 118140960795 + 3613447 * 2 ^ 59
def prefixEnd_3613447 : Nat := 4983230072969 + 3 ^ 40 * 3613447 * 2
def baseEnd_3613447 : Nat := 45813213099926644585051

theorem tailTrace_3613447 : CollatzResearch.WordTrace tailWord_3613447 prefixEnd_3613447 45813213099926644585051 := by
  unfold tailWord_3613447
  simp only [CollatzResearch.WordTrace]
  refine ⟨131793239340106121460670595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87862159560070747640447063 131793239340106121460670595)
  ·
    refine ⟨197689859010159182191005893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131793239340106121460670595 197689859010159182191005893)
    ·
      refine ⟨37066848564404846660813605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197689859010159182191005893 37066848564404846660813605)
      ·
        refine ⟨6950034105825908748902551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37066848564404846660813605 6950034105825908748902551)
        ·
          refine ⟨10425051158738863123353827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6950034105825908748902551 10425051158738863123353827)
          ·
            refine ⟨15637576738108294685030741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10425051158738863123353827 15637576738108294685030741)
            ·
              refine ⟨45813213099926644585051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15637576738108294685030741 45813213099926644585051)
              ·
                rfl

theorem cell22_3613447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 10].length) (baseStart_3613447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613447 prefixEnd_3613447 := by exact prefixLift 3613447
  have htrace : WordTrace (prefixWord ++ tailWord_3613447) baseStart_3613447 baseEnd_3613447 := by
    simpa [prefixWord, tailWord_3613447, baseEnd_3613447] using wordTrace_append hprefix tailTrace_3613447
  have hstable : (prefixWord ++ tailWord_3613447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613447).length < 2 ^ (prefixWord ++ tailWord_3613447).sum := by decide
  have hdescent : baseEnd_3613447 < baseStart_3613447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613468 : List Nat := [2, 2, 3, 1, 1, 5, 2, 1, 2, 3]
def baseStart_3613468 : Nat := 118140960795 + 3613468 * 2 ^ 59
def prefixEnd_3613468 : Nat := 4983230072969 + 3 ^ 40 * 3613468 * 2
def baseEnd_3613468 : Nat := 1236963942427182349021313

theorem tailTrace_3613468 : CollatzResearch.WordTrace tailWord_3613468 prefixEnd_3613468 1236963942427182349021313 := by
  unfold tailWord_3613468
  simp only [CollatzResearch.WordTrace]
  refine ⟨65897002636515021023592529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87862670182020028031456705 65897002636515021023592529)
  ·
    refine ⟨49422751977386265767694397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65897002636515021023592529 49422751977386265767694397)
    ·
      refine ⟨18533531991519849662885399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49422751977386265767694397 18533531991519849662885399)
      ·
        refine ⟨27800297987279774494328099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18533531991519849662885399 27800297987279774494328099)
        ·
          refine ⟨41700446980919661741492149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27800297987279774494328099 41700446980919661741492149)
          ·
            refine ⟨3909416904461218288264889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41700446980919661741492149 3909416904461218288264889)
            ·
              refine ⟨2932062678345913716198667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3909416904461218288264889 2932062678345913716198667)
              ·
                refine ⟨4398094017518870574298001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2932062678345913716198667 4398094017518870574298001)
                ·
                  refine ⟨3298570513139152930723501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4398094017518870574298001 3298570513139152930723501)
                  ·
                    refine ⟨1236963942427182349021313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3298570513139152930723501 1236963942427182349021313)
                    ·
                      rfl

theorem cell22_3613468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_3613468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613468 prefixEnd_3613468 := by exact prefixLift 3613468
  have htrace : WordTrace (prefixWord ++ tailWord_3613468) baseStart_3613468 baseEnd_3613468 := by
    simpa [prefixWord, tailWord_3613468, baseEnd_3613468] using wordTrace_append hprefix tailTrace_3613468
  have hstable : (prefixWord ++ tailWord_3613468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613468).length < 2 ^ (prefixWord ++ tailWord_3613468).sum := by decide
  have hdescent : baseEnd_3613468 < baseStart_3613468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613496 : List Nat := [2, 1, 2, 1, 3, 2, 2, 5, 1, 3]
def baseStart_3613496 : Nat := 118140960795 + 3613496 * 2 ^ 59
def prefixEnd_3613496 : Nat := 4983230072969 + 3 ^ 40 * 3613496 * 2
def baseEnd_3613496 : Nat := 1236973527399399609321227

theorem tailTrace_3613496 : CollatzResearch.WordTrace tailWord_3613496 prefixEnd_3613496 1236973527399399609321227 := by
  unfold tailWord_3613496
  simp only [CollatzResearch.WordTrace]
  refine ⟨65897513258464301414602171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87863351011285735219469561 65897513258464301414602171)
  ·
    refine ⟨98846269887696452121903257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65897513258464301414602171 98846269887696452121903257)
    ·
      refine ⟨74134702415772339091427443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98846269887696452121903257 74134702415772339091427443)
      ·
        refine ⟨111202053623658508637141165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74134702415772339091427443 111202053623658508637141165)
        ·
          refine ⟨41700770108871940738927937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111202053623658508637141165 41700770108871940738927937)
          ·
            refine ⟨31275577581653955554195953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41700770108871940738927937 31275577581653955554195953)
            ·
              refine ⟨23456683186240466665646965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31275577581653955554195953 23456683186240466665646965)
              ·
                refine ⟨2199064048710043749904403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23456683186240466665646965 2199064048710043749904403)
                ·
                  refine ⟨3298596073065065624856605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2199064048710043749904403 3298596073065065624856605)
                  ·
                    refine ⟨1236973527399399609321227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3298596073065065624856605 1236973527399399609321227)
                    ·
                      rfl

theorem cell22_3613496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 1, 3].length) (baseStart_3613496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613496 prefixEnd_3613496 := by exact prefixLift 3613496
  have htrace : WordTrace (prefixWord ++ tailWord_3613496) baseStart_3613496 baseEnd_3613496 := by
    simpa [prefixWord, tailWord_3613496, baseEnd_3613496] using wordTrace_append hprefix tailTrace_3613496
  have hstable : (prefixWord ++ tailWord_3613496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613496).length < 2 ^ (prefixWord ++ tailWord_3613496).sum := by decide
  have hdescent : baseEnd_3613496 < baseStart_3613496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613507 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 2, 5]
def baseStart_3613507 : Nat := 118140960795 + 3613507 * 2 ^ 59
def prefixEnd_3613507 : Nat := 4983230072969 + 3 ^ 40 * 3613507 * 2
def baseEnd_3613507 : Nat := 1236977292924199247296193

theorem tailTrace_3613507 : CollatzResearch.WordTrace tailWord_3613507 prefixEnd_3613507 1236977292924199247296193 := by
  unfold tailWord_3613507
  simp only [CollatzResearch.WordTrace]
  refine ⟨131795427719888751707854775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87863618479925834471903183 131795427719888751707854775)
  ·
    refine ⟨197693141579833127561782163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131795427719888751707854775 197693141579833127561782163)
    ·
      refine ⟨296539712369749691342673245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197693141579833127561782163 296539712369749691342673245)
      ·
        refine ⟨111202392138656134253502467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296539712369749691342673245 111202392138656134253502467)
        ·
          refine ⟨166803588207984201380253701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111202392138656134253502467 166803588207984201380253701)
          ·
            refine ⟨31275672788997037758797569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166803588207984201380253701 31275672788997037758797569)
            ·
              refine ⟨23456754591747778319098177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31275672788997037758797569 23456754591747778319098177)
              ·
                refine ⟨17592565943810833739323633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23456754591747778319098177 17592565943810833739323633)
                ·
                  refine ⟨13194424457858125304492725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17592565943810833739323633 13194424457858125304492725)
                  ·
                    refine ⟨1236977292924199247296193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13194424457858125304492725 1236977292924199247296193)
                    ·
                      rfl

theorem cell22_3613507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 5].length) (baseStart_3613507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613507 prefixEnd_3613507 := by exact prefixLift 3613507
  have htrace : WordTrace (prefixWord ++ tailWord_3613507) baseStart_3613507 baseEnd_3613507 := by
    simpa [prefixWord, tailWord_3613507, baseEnd_3613507] using wordTrace_append hprefix tailTrace_3613507
  have hstable : (prefixWord ++ tailWord_3613507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613507).length < 2 ^ (prefixWord ++ tailWord_3613507).sum := by decide
  have hdescent : baseEnd_3613507 < baseStart_3613507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613513 : List Nat := [1, 2, 1, 1, 2, 5, 4, 2, 1, 3]
def baseStart_3613513 : Nat := 118140960795 + 3613513 * 2 ^ 59
def prefixEnd_3613513 : Nat := 4983230072969 + 3 ^ 40 * 3613513 * 2
def baseEnd_3613513 : Nat := 1236979346846817231646175

theorem tailTrace_3613513 : CollatzResearch.WordTrace tailWord_3613513 prefixEnd_3613513 1236979346846817231646175 := by
  unfold tailWord_3613513
  simp only [CollatzResearch.WordTrace]
  refine ⟨131795646557867014732573193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87863764371911343155048795 131795646557867014732573193)
  ·
    refine ⟨98846734918400261049429895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131795646557867014732573193 98846734918400261049429895)
    ·
      refine ⟨148270102377600391574144843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98846734918400261049429895 148270102377600391574144843)
      ·
        refine ⟨222405153566400587361217265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148270102377600391574144843 222405153566400587361217265)
        ·
          refine ⟨166803865174800440520912949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222405153566400587361217265 166803865174800440520912949)
          ·
            refine ⟨15637862360137541298835589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166803865174800440520912949 15637862360137541298835589)
            ·
              refine ⟨2932099192525788993531673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15637862360137541298835589 2932099192525788993531673)
              ·
                refine ⟨2199074394394341745148755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2932099192525788993531673 2199074394394341745148755)
                ·
                  refine ⟨3298611591591512617723133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2199074394394341745148755 3298611591591512617723133)
                  ·
                    refine ⟨1236979346846817231646175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3298611591591512617723133 1236979346846817231646175)
                    ·
                      rfl

theorem cell22_3613513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 1, 3].length) (baseStart_3613513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613513 prefixEnd_3613513 := by exact prefixLift 3613513
  have htrace : WordTrace (prefixWord ++ tailWord_3613513) baseStart_3613513 baseEnd_3613513 := by
    simpa [prefixWord, tailWord_3613513, baseEnd_3613513] using wordTrace_append hprefix tailTrace_3613513
  have hstable : (prefixWord ++ tailWord_3613513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613513).length < 2 ^ (prefixWord ++ tailWord_3613513).sum := by decide
  have hdescent : baseEnd_3613513 < baseStart_3613513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613539 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 3, 4]
def baseStart_3613539 : Nat := 118140960795 + 3613539 * 2 ^ 59
def prefixEnd_3613539 : Nat := 4983230072969 + 3 ^ 40 * 3613539 * 2
def baseEnd_3613539 : Nat := 1236988247178161830496095

theorem tailTrace_3613539 : CollatzResearch.WordTrace tailWord_3613539 prefixEnd_3613539 1236988247178161830496095 := by
  unfold tailWord_3613539
  simp only [CollatzResearch.WordTrace]
  refine ⟨131796594855772821173019671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87864396570515214115346447 131796594855772821173019671)
  ·
    refine ⟨197694892283659231759529507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131796594855772821173019671 197694892283659231759529507)
    ·
      refine ⟨296542338425488847639294261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197694892283659231759529507 296542338425488847639294261)
      ·
        refine ⟨27800844227389579466183837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 296542338425488847639294261 27800844227389579466183837)
        ·
          refine ⟨10425316585271092299818939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27800844227389579466183837 10425316585271092299818939)
          ·
            refine ⟨15637974877906638449728409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10425316585271092299818939 15637974877906638449728409)
            ·
              refine ⟨11728481158429978837296307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15637974877906638449728409 11728481158429978837296307)
              ·
                refine ⟨17592721737644968255944461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11728481158429978837296307 17592721737644968255944461)
                ·
                  refine ⟨6597270651616863095979173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17592721737644968255944461 6597270651616863095979173)
                  ·
                    refine ⟨1236988247178161830496095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6597270651616863095979173 1236988247178161830496095)
                    ·
                      rfl

theorem cell22_3613539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 4].length) (baseStart_3613539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613539 prefixEnd_3613539 := by exact prefixLift 3613539
  have htrace : WordTrace (prefixWord ++ tailWord_3613539) baseStart_3613539 baseEnd_3613539 := by
    simpa [prefixWord, tailWord_3613539, baseEnd_3613539] using wordTrace_append hprefix tailTrace_3613539
  have hstable : (prefixWord ++ tailWord_3613539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613539).length < 2 ^ (prefixWord ++ tailWord_3613539).sum := by decide
  have hdescent : baseEnd_3613539 < baseStart_3613539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613590 : List Nat := [5, 3, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_3613590 : Nat := 118140960795 + 3613590 * 2 ^ 59
def prefixEnd_3613590 : Nat := 4983230072969 + 3 ^ 40 * 3613590 * 2
def baseEnd_3613590 : Nat := 1237005705520414697470939

theorem tailTrace_3613590 : CollatzResearch.WordTrace tailWord_3613590 prefixEnd_3613590 1237005705520414697470939 := by
  unfold tailWord_3613590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8237403436161753555195389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87865636652392037922084149 8237403436161753555195389)
  ·
    refine ⟨3089026288560657583198271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8237403436161753555195389 3089026288560657583198271)
    ·
      refine ⟨4633539432840986374797407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3089026288560657583198271 4633539432840986374797407)
      ·
        refine ⟨6950309149261479562196111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4633539432840986374797407 6950309149261479562196111)
        ·
          refine ⟨10425463723892219343294167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6950309149261479562196111 10425463723892219343294167)
          ·
            refine ⟨15638195585838329014941251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10425463723892219343294167 15638195585838329014941251)
            ·
              refine ⟨23457293378757493522411877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15638195585838329014941251 23457293378757493522411877)
              ·
                refine ⟨4398242508517030035452227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23457293378757493522411877 4398242508517030035452227)
                ·
                  refine ⟨6597363762775545053178341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4398242508517030035452227 6597363762775545053178341)
                  ·
                    refine ⟨1237005705520414697470939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6597363762775545053178341 1237005705520414697470939)
                    ·
                      rfl

theorem cell22_3613590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_3613590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613590 prefixEnd_3613590 := by exact prefixLift 3613590
  have htrace : WordTrace (prefixWord ++ tailWord_3613590) baseStart_3613590 baseEnd_3613590 := by
    simpa [prefixWord, tailWord_3613590, baseEnd_3613590] using wordTrace_append hprefix tailTrace_3613590
  have hstable : (prefixWord ++ tailWord_3613590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613590).length < 2 ^ (prefixWord ++ tailWord_3613590).sum := by decide
  have hdescent : baseEnd_3613590 < baseStart_3613590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613599 : List Nat := [1, 1, 2, 5, 2, 2, 1, 8]
def baseStart_3613599 : Nat := 118140960795 + 3613599 * 2 ^ 59
def prefixEnd_3613599 : Nat := 4983230072969 + 3 ^ 40 * 3613599 * 2
def baseEnd_3613599 : Nat := 137445420711593519332879

theorem tailTrace_3613599 : CollatzResearch.WordTrace tailWord_3613599 prefixEnd_3613599 137445420711593519332879 := by
  unfold tailWord_3613599
  simp only [CollatzResearch.WordTrace]
  refine ⟨131798783235555451420203851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87865855490370300946802567 131798783235555451420203851)
  ·
    refine ⟨197698174853333177130305777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131798783235555451420203851 197698174853333177130305777)
    ·
      refine ⟨148273631139999882847729333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197698174853333177130305777 148273631139999882847729333)
      ·
        refine ⟨13900652919374989016974625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148273631139999882847729333 13900652919374989016974625)
        ·
          refine ⟨10425489689531241762730969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13900652919374989016974625 10425489689531241762730969)
          ·
            refine ⟨7819117267148431322048227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10425489689531241762730969 7819117267148431322048227)
            ·
              refine ⟨11728675900722646983072341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7819117267148431322048227 11728675900722646983072341)
              ·
                refine ⟨137445420711593519332879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11728675900722646983072341 137445420711593519332879)
                ·
                  rfl

theorem cell22_3613599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 8].length) (baseStart_3613599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613599 prefixEnd_3613599 := by exact prefixLift 3613599
  have htrace : WordTrace (prefixWord ++ tailWord_3613599) baseStart_3613599 baseEnd_3613599 := by
    simpa [prefixWord, tailWord_3613599, baseEnd_3613599] using wordTrace_append hprefix tailTrace_3613599
  have hstable : (prefixWord ++ tailWord_3613599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613599).length < 2 ^ (prefixWord ++ tailWord_3613599).sum := by decide
  have hdescent : baseEnd_3613599 < baseStart_3613599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613622 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_3613622 : Nat := 118140960795 + 3613622 * 2 ^ 59
def prefixEnd_3613622 : Nat := 4983230072969 + 3 ^ 40 * 3613622 * 2
def baseEnd_3613622 : Nat := 412338886591459093556947

theorem tailTrace_3613622 : CollatzResearch.WordTrace tailWord_3613622 prefixEnd_3613622 412338886591459093556947 := by
  unfold tailWord_3613622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8237476382154507896768195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87866414742981417565527413 8237476382154507896768195)
  ·
    refine ⟨12356214573231761845152293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8237476382154507896768195 12356214573231761845152293)
    ·
      refine ⟨2316790232480955345966055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12356214573231761845152293 2316790232480955345966055)
      ·
        refine ⟨3475185348721433018949083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2316790232480955345966055 3475185348721433018949083)
        ·
          refine ⟨5212778023082149528423625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3475185348721433018949083 5212778023082149528423625)
          ·
            refine ⟨3909583517311612146317719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5212778023082149528423625 3909583517311612146317719)
            ·
              refine ⟨5864375275967418219476579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3909583517311612146317719 5864375275967418219476579)
              ·
                refine ⟨8796562913951127329214869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5864375275967418219476579 8796562913951127329214869)
                ·
                  refine ⟨412338886591459093556947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8796562913951127329214869 412338886591459093556947)
                  ·
                    rfl

theorem cell22_3613622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_3613622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613622 prefixEnd_3613622 := by exact prefixLift 3613622
  have htrace : WordTrace (prefixWord ++ tailWord_3613622) baseStart_3613622 baseEnd_3613622 := by
    simpa [prefixWord, tailWord_3613622, baseEnd_3613622] using wordTrace_append hprefix tailTrace_3613622
  have hstable : (prefixWord ++ tailWord_3613622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613622).length < 2 ^ (prefixWord ++ tailWord_3613622).sum := by decide
  have hdescent : baseEnd_3613622 < baseStart_3613622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613627 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 11]
def baseStart_3613627 : Nat := 118140960795 + 3613627 * 2 ^ 59
def prefixEnd_3613627 : Nat := 4983230072969 + 3 ^ 40 * 3613627 * 2
def baseEnd_3613627 : Nat := 412339457125519644765275

theorem tailTrace_3613627 : CollatzResearch.WordTrace tailWord_3613627 prefixEnd_3613627 412339457125519644765275 := by
  unfold tailWord_3613627
  simp only [CollatzResearch.WordTrace]
  refine ⟨131799804479454012202223135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87866536319636008134815423 131799804479454012202223135)
  ·
    refine ⟨197699706719181018303334703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131799804479454012202223135 197699706719181018303334703)
    ·
      refine ⟨296549560078771527455002055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197699706719181018303334703 296549560078771527455002055)
      ·
        refine ⟨444824340118157291182503083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296549560078771527455002055 444824340118157291182503083)
        ·
          refine ⟨667236510177235936773754625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444824340118157291182503083 667236510177235936773754625)
          ·
            refine ⟨500427382632926952580315969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667236510177235936773754625 500427382632926952580315969)
            ·
              refine ⟨375320536974695214435236977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500427382632926952580315969 375320536974695214435236977)
              ·
                refine ⟨281490402731021410826427733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375320536974695214435236977 281490402731021410826427733)
                ·
                  refine ⟨412339457125519644765275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 281490402731021410826427733 412339457125519644765275)
                  ·
                    rfl

theorem cell22_3613627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 11].length) (baseStart_3613627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613627 prefixEnd_3613627 := by exact prefixLift 3613627
  have htrace : WordTrace (prefixWord ++ tailWord_3613627) baseStart_3613627 baseEnd_3613627 := by
    simpa [prefixWord, tailWord_3613627, baseEnd_3613627] using wordTrace_append hprefix tailTrace_3613627
  have hstable : (prefixWord ++ tailWord_3613627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613627).length < 2 ^ (prefixWord ++ tailWord_3613627).sum := by decide
  have hdescent : baseEnd_3613627 < baseStart_3613627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613678 : List Nat := [4, 1, 2, 1, 4, 1, 2, 2, 5]
def baseStart_3613678 : Nat := 118140960795 + 3613678 * 2 ^ 59
def prefixEnd_3613678 : Nat := 4983230072969 + 3 ^ 40 * 3613678 * 2
def baseEnd_3613678 : Nat := 412345276572937267090223

theorem tailTrace_3613678 : CollatzResearch.WordTrace tailWord_3613678 prefixEnd_3613678 412345276572937267090223 := by
  unfold tailWord_3613678
  simp only [CollatzResearch.WordTrace]
  refine ⟨16475208075283655989041211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87867776401512831941553125 16475208075283655989041211)
  ·
    refine ⟨24712812112925483983561817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16475208075283655989041211 24712812112925483983561817)
    ·
      refine ⟨18534609084694112987671363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24712812112925483983561817 18534609084694112987671363)
      ·
        refine ⟨27801913627041169481507045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18534609084694112987671363 27801913627041169481507045)
        ·
          refine ⟨5212858805070219277782571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27801913627041169481507045 5212858805070219277782571)
          ·
            refine ⟨7819288207605328916673857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5212858805070219277782571 7819288207605328916673857)
            ·
              refine ⟨5864466155703996687505393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7819288207605328916673857 5864466155703996687505393)
              ·
                refine ⟨4398349616777997515629045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5864466155703996687505393 4398349616777997515629045)
                ·
                  refine ⟨412345276572937267090223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4398349616777997515629045 412345276572937267090223)
                  ·
                    rfl

theorem cell22_3613678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_3613678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613678 prefixEnd_3613678 := by exact prefixLift 3613678
  have htrace : WordTrace (prefixWord ++ tailWord_3613678) baseStart_3613678 baseEnd_3613678 := by
    simpa [prefixWord, tailWord_3613678, baseEnd_3613678] using wordTrace_append hprefix tailTrace_3613678
  have hstable : (prefixWord ++ tailWord_3613678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613678).length < 2 ^ (prefixWord ++ tailWord_3613678).sum := by decide
  have hdescent : baseEnd_3613678 < baseStart_3613678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613682 : List Nat := [3, 2, 1, 5, 1, 1, 1, 4, 1, 3]
def baseStart_3613682 : Nat := 118140960795 + 3613682 * 2 ^ 59
def prefixEnd_3613682 : Nat := 4983230072969 + 3 ^ 40 * 3613682 * 2
def baseEnd_3613682 : Nat := 1237037199000557124170657

theorem tailTrace_3613682 : CollatzResearch.WordTrace tailWord_3613682 prefixEnd_3613682 1237037199000557124170657 := by
  unfold tailWord_3613682
  simp only [CollatzResearch.WordTrace]
  refine ⟨32950452623563689148868825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87867873662836504396983533 32950452623563689148868825)
  ·
    refine ⟨24712839467672766861651619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32950452623563689148868825 24712839467672766861651619)
    ·
      refine ⟨37069259201509150292477429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24712839467672766861651619 37069259201509150292477429)
      ·
        refine ⟨3475243050141482839919759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37069259201509150292477429 3475243050141482839919759)
        ·
          refine ⟨5212864575212224259879639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3475243050141482839919759 5212864575212224259879639)
          ·
            refine ⟨7819296862818336389819459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5212864575212224259879639 7819296862818336389819459)
            ·
              refine ⟨11728945294227504584729189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7819296862818336389819459 11728945294227504584729189)
              ·
                refine ⟨2199177242667657109636723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11728945294227504584729189 2199177242667657109636723)
                ·
                  refine ⟨3298765864001485664455085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2199177242667657109636723 3298765864001485664455085)
                  ·
                    refine ⟨1237037199000557124170657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3298765864001485664455085 1237037199000557124170657)
                    ·
                      rfl

theorem cell22_3613682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_3613682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613682 prefixEnd_3613682 := by exact prefixLift 3613682
  have htrace : WordTrace (prefixWord ++ tailWord_3613682) baseStart_3613682 baseEnd_3613682 := by
    simpa [prefixWord, tailWord_3613682, baseEnd_3613682] using wordTrace_append hprefix tailTrace_3613682
  have hstable : (prefixWord ++ tailWord_3613682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613682).length < 2 ^ (prefixWord ++ tailWord_3613682).sum := by decide
  have hdescent : baseEnd_3613682 < baseStart_3613682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613684 : List Nat := [2, 6, 2, 1, 2, 1, 1, 7]
def baseStart_3613684 : Nat := 118140960795 + 3613684 * 2 ^ 59
def prefixEnd_3613684 : Nat := 4983230072969 + 3 ^ 40 * 3613684 * 2
def baseEnd_3613684 : Nat := 137448653737936642846739

theorem tailTrace_3613684 : CollatzResearch.WordTrace tailWord_3613684 prefixEnd_3613684 137448653737936642846739 := by
  unfold tailWord_3613684
  simp only [CollatzResearch.WordTrace]
  refine ⟨65900941720123755468524053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87867922293498340624698737 65900941720123755468524053)
  ·
    refine ⟨3089106643130801037587065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65900941720123755468524053 3089106643130801037587065)
    ·
      refine ⟨2316829982348100778190299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3089106643130801037587065 2316829982348100778190299)
      ·
        refine ⟨3475244973522151167285449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2316829982348100778190299 3475244973522151167285449)
        ·
          refine ⟨2606433730141613375464087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3475244973522151167285449 2606433730141613375464087)
          ·
            refine ⟨3909650595212420063196131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606433730141613375464087 3909650595212420063196131)
            ·
              refine ⟨5864475892818630094794197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3909650595212420063196131 5864475892818630094794197)
              ·
                refine ⟨137448653737936642846739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5864475892818630094794197 137448653737936642846739)
                ·
                  rfl

theorem cell22_3613684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 7].length) (baseStart_3613684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613684 prefixEnd_3613684 := by exact prefixLift 3613684
  have htrace : WordTrace (prefixWord ++ tailWord_3613684) baseStart_3613684 baseEnd_3613684 := by
    simpa [prefixWord, tailWord_3613684, baseEnd_3613684] using wordTrace_append hprefix tailTrace_3613684
  have hstable : (prefixWord ++ tailWord_3613684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613684).length < 2 ^ (prefixWord ++ tailWord_3613684).sum := by decide
  have hdescent : baseEnd_3613684 < baseStart_3613684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613689 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 6]
def baseStart_3613689 : Nat := 118140960795 + 3613689 * 2 ^ 59
def prefixEnd_3613689 : Nat := 4983230072969 + 3 ^ 40 * 3613689 * 2
def baseEnd_3613689 : Nat := 412346531747870479748545

theorem tailTrace_3613689 : CollatzResearch.WordTrace tailWord_3613689 prefixEnd_3613689 412346531747870479748545 := by
  unfold tailWord_3613689
  simp only [CollatzResearch.WordTrace]
  refine ⟨131802065805229396790980121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87868043870152931193986747 131802065805229396790980121)
  ·
    refine ⟨98851549353922047593235091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131802065805229396790980121 98851549353922047593235091)
    ·
      refine ⟨148277324030883071389852637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98851549353922047593235091 148277324030883071389852637)
      ·
        refine ⟨55603996511581151771194739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148277324030883071389852637 55603996511581151771194739)
        ·
          refine ⟨83405994767371727656792109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55603996511581151771194739 83405994767371727656792109)
          ·
            refine ⟨31277248037764397871297041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83405994767371727656792109 31277248037764397871297041)
            ·
              refine ⟨23457936028323298403472781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31277248037764397871297041 23457936028323298403472781)
              ·
                refine ⟨8796726010621236901302293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23457936028323298403472781 8796726010621236901302293)
                ·
                  refine ⟨412346531747870479748545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8796726010621236901302293 412346531747870479748545)
                  ·
                    rfl

theorem cell22_3613689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 6].length) (baseStart_3613689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613689 prefixEnd_3613689 := by exact prefixLift 3613689
  have htrace : WordTrace (prefixWord ++ tailWord_3613689) baseStart_3613689 baseEnd_3613689 := by
    simpa [prefixWord, tailWord_3613689, baseEnd_3613689] using wordTrace_append hprefix tailTrace_3613689
  have hstable : (prefixWord ++ tailWord_3613689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613689).length < 2 ^ (prefixWord ++ tailWord_3613689).sum := by decide
  have hdescent : baseEnd_3613689 < baseStart_3613689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613706 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 6]
def baseStart_3613706 : Nat := 118140960795 + 3613706 * 2 ^ 59
def prefixEnd_3613706 : Nat := 4983230072969 + 3 ^ 40 * 3613706 * 2
def baseEnd_3613706 : Nat := 412348471563676353856861

theorem tailTrace_3613706 : CollatzResearch.WordTrace tailWord_3613706 prefixEnd_3613706 412348471563676353856861 := by
  unfold tailWord_3613706
  simp only [CollatzResearch.WordTrace]
  refine ⟨32950671461541952173587243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87868457230778539129565981 32950671461541952173587243)
  ·
    refine ⟨49426007192312928260380865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32950671461541952173587243 49426007192312928260380865)
    ·
      refine ⟨37069505394234696195285649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49426007192312928260380865 37069505394234696195285649)
      ·
        refine ⟨27802129045676022146464237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37069505394234696195285649 27802129045676022146464237)
        ·
          refine ⟨10425798392128508304924089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27802129045676022146464237 10425798392128508304924089)
          ·
            refine ⟨7819348794096381228693067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10425798392128508304924089 7819348794096381228693067)
            ·
              refine ⟨11729023191144571843039601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7819348794096381228693067 11729023191144571843039601)
              ·
                refine ⟨8796767393358428882279701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11729023191144571843039601 8796767393358428882279701)
                ·
                  refine ⟨412348471563676353856861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8796767393358428882279701 412348471563676353856861)
                  ·
                    rfl

theorem cell22_3613706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_3613706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613706 prefixEnd_3613706 := by exact prefixLift 3613706
  have htrace : WordTrace (prefixWord ++ tailWord_3613706) baseStart_3613706 baseEnd_3613706 := by
    simpa [prefixWord, tailWord_3613706, baseEnd_3613706] using wordTrace_append hprefix tailTrace_3613706
  have hstable : (prefixWord ++ tailWord_3613706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613706).length < 2 ^ (prefixWord ++ tailWord_3613706).sum := by decide
  have hdescent : baseEnd_3613706 < baseStart_3613706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613779 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 7]
def baseStart_3613779 : Nat := 118140960795 + 3613779 * 2 ^ 59
def prefixEnd_3613779 : Nat := 4983230072969 + 3 ^ 40 * 3613779 * 2
def baseEnd_3613779 : Nat := 412356801360960401498453

theorem tailTrace_3613779 : CollatzResearch.WordTrace tailWord_3613779 prefixEnd_3613779 412356801360960401498453 := by
  unfold tailWord_3613779
  simp only [CollatzResearch.WordTrace]
  refine ⟨131805348374903342161756391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87870232249935561441170927 131805348374903342161756391)
  ·
    refine ⟨197708022562355013242634587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131805348374903342161756391 197708022562355013242634587)
    ·
      refine ⟨296562033843532519863951881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197708022562355013242634587 296562033843532519863951881)
      ·
        refine ⟨222421525382649389897963911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296562033843532519863951881 222421525382649389897963911)
        ·
          refine ⟨333632288073974084846945867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222421525382649389897963911 333632288073974084846945867)
          ·
            refine ⟨500448432110961127270418801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333632288073974084846945867 500448432110961127270418801)
            ·
              refine ⟨375336324083220845452814101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500448432110961127270418801 375336324083220845452814101)
              ·
                refine ⟨17593890191400977130600661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 375336324083220845452814101 17593890191400977130600661)
                ·
                  refine ⟨412356801360960401498453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17593890191400977130600661 412356801360960401498453)
                  ·
                    rfl

theorem cell22_3613779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 7].length) (baseStart_3613779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613779 prefixEnd_3613779 := by exact prefixLift 3613779
  have htrace : WordTrace (prefixWord ++ tailWord_3613779) baseStart_3613779 baseEnd_3613779 := by
    simpa [prefixWord, tailWord_3613779, baseEnd_3613779] using wordTrace_append hprefix tailTrace_3613779
  have hstable : (prefixWord ++ tailWord_3613779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613779).length < 2 ^ (prefixWord ++ tailWord_3613779).sum := by decide
  have hdescent : baseEnd_3613779 < baseStart_3613779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613796 : List Nat := [2, 3, 1, 1, 2, 1, 1, 6, 5]
def baseStart_3613796 : Nat := 118140960795 + 3613796 * 2 ^ 59
def prefixEnd_3613796 : Nat := 4983230072969 + 3 ^ 40 * 3613796 * 2
def baseEnd_3613796 : Nat := 412358741176766275606769

theorem tailTrace_3613796 : CollatzResearch.WordTrace tailWord_3613796 prefixEnd_3613796 412358741176766275606769 := by
  unfold tailWord_3613796
  simp only [CollatzResearch.WordTrace]
  refine ⟨65902984207920877032562621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87870645610561169376750161 65902984207920877032562621)
  ·
    refine ⟨24713619077970328887210983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65902984207920877032562621 24713619077970328887210983)
    ·
      refine ⟨37070428616955493330816475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24713619077970328887210983 37070428616955493330816475)
      ·
        refine ⟨55605642925433239996224713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37070428616955493330816475 55605642925433239996224713)
        ·
          refine ⟨41704232194074929997168535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55605642925433239996224713 41704232194074929997168535)
          ·
            refine ⟨62556348291112394995752803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41704232194074929997168535 62556348291112394995752803)
            ·
              refine ⟨93834522436668592493629205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62556348291112394995752803 93834522436668592493629205)
              ·
                refine ⟨4398493239218840273138869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93834522436668592493629205 4398493239218840273138869)
                ·
                  refine ⟨412358741176766275606769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4398493239218840273138869 412358741176766275606769)
                  ·
                    rfl

theorem cell22_3613796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_3613796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613796 prefixEnd_3613796 := by exact prefixLift 3613796
  have htrace : WordTrace (prefixWord ++ tailWord_3613796) baseStart_3613796 baseEnd_3613796 := by
    simpa [prefixWord, tailWord_3613796, baseEnd_3613796] using wordTrace_append hprefix tailTrace_3613796
  have hstable : (prefixWord ++ tailWord_3613796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613796).length < 2 ^ (prefixWord ++ tailWord_3613796).sum := by decide
  have hdescent : baseEnd_3613796 < baseStart_3613796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613856 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 3, 5]
def baseStart_3613856 : Nat := 118140960795 + 3613856 * 2 ^ 59
def prefixEnd_3613856 : Nat := 4983230072969 + 3 ^ 40 * 3613856 * 2
def baseEnd_3613856 : Nat := 1237096762756478670320123

theorem tailTrace_3613856 : CollatzResearch.WordTrace tailWord_3613856 prefixEnd_3613856 1237096762756478670320123 := by
  unfold tailWord_3613856
  simp only [CollatzResearch.WordTrace]
  refine ⟨65904078397812192156154711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87872104530416256208206281 65904078397812192156154711)
  ·
    refine ⟨98856117596718288234232067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65904078397812192156154711 98856117596718288234232067)
    ·
      refine ⟨148284176395077432351348101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98856117596718288234232067 148284176395077432351348101)
      ·
        refine ⟨27803283074077018565877769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148284176395077432351348101 27803283074077018565877769)
        ·
          refine ⟨20852462305557763924408327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27803283074077018565877769 20852462305557763924408327)
          ·
            refine ⟨31278693458336645886612491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20852462305557763924408327 31278693458336645886612491)
            ·
              refine ⟨46918040187504968829918737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31278693458336645886612491 46918040187504968829918737)
              ·
                refine ⟨35188530140628726622439053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46918040187504968829918737 35188530140628726622439053)
                ·
                  refine ⟨13195698802735772483414645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35188530140628726622439053 13195698802735772483414645)
                  ·
                    refine ⟨1237096762756478670320123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13195698802735772483414645 1237096762756478670320123)
                    ·
                      rfl

theorem cell22_3613856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_3613856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613856 prefixEnd_3613856 := by exact prefixLift 3613856
  have htrace : WordTrace (prefixWord ++ tailWord_3613856) baseStart_3613856 baseEnd_3613856 := by
    simpa [prefixWord, tailWord_3613856, baseEnd_3613856] using wordTrace_append hprefix tailTrace_3613856
  have hstable : (prefixWord ++ tailWord_3613856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613856).length < 2 ^ (prefixWord ++ tailWord_3613856).sum := by decide
  have hdescent : baseEnd_3613856 < baseStart_3613856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613871 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 4, 4]
def baseStart_3613871 : Nat := 118140960795 + 3613871 * 2 ^ 59
def prefixEnd_3613871 : Nat := 4983230072969 + 3 ^ 40 * 3613871 * 2
def baseEnd_3613871 : Nat := 1237101897563023631195077

theorem tailTrace_3613871 : CollatzResearch.WordTrace tailWord_3613871 prefixEnd_3613871 1237101897563023631195077 := by
  unfold tailWord_3613871
  simp only [CollatzResearch.WordTrace]
  refine ⟨131808703890570041874105467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87872469260380027916070311 131808703890570041874105467)
  ·
    refine ⟨197713055835855062811158201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131808703890570041874105467 197713055835855062811158201)
    ·
      refine ⟨148284791876891297108368651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197713055835855062811158201 148284791876891297108368651)
      ·
        refine ⟨222427187815336945662552977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148284791876891297108368651 222427187815336945662552977)
        ·
          refine ⟨166820390861502709246914733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222427187815336945662552977 166820390861502709246914733)
          ·
            refine ⟨62557646573063515967593025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166820390861502709246914733 62557646573063515967593025)
            ·
              refine ⟨46918234929797636975694769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62557646573063515967593025 46918234929797636975694769)
              ·
                refine ⟨35188676197348227731771077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46918234929797636975694769 35188676197348227731771077)
                ·
                  refine ⟨6597876787002792699707077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35188676197348227731771077 6597876787002792699707077)
                  ·
                    refine ⟨1237101897563023631195077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6597876787002792699707077 1237101897563023631195077)
                    ·
                      rfl

theorem cell22_3613871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_3613871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613871 prefixEnd_3613871 := by exact prefixLift 3613871
  have htrace : WordTrace (prefixWord ++ tailWord_3613871) baseStart_3613871 baseEnd_3613871 := by
    simpa [prefixWord, tailWord_3613871, baseEnd_3613871] using wordTrace_append hprefix tailTrace_3613871
  have hstable : (prefixWord ++ tailWord_3613871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613871).length < 2 ^ (prefixWord ++ tailWord_3613871).sum := by decide
  have hdescent : baseEnd_3613871 < baseStart_3613871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613873 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 1, 5]
def baseStart_3613873 : Nat := 118140960795 + 3613873 * 2 ^ 59
def prefixEnd_3613873 : Nat := 4983230072969 + 3 ^ 40 * 3613873 * 2
def baseEnd_3613873 : Nat := 1237102582203896292645071

theorem tailTrace_3613873 : CollatzResearch.WordTrace tailWord_3613873 prefixEnd_3613873 1237102582203896292645071 := by
  unfold tailWord_3613873
  simp only [CollatzResearch.WordTrace]
  refine ⟨131808776836562796215678273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87872517891041864143785515 131808776836562796215678273)
  ·
    refine ⟨98856582627422097161758705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131808776836562796215678273 98856582627422097161758705)
    ·
      refine ⟨74142436970566572871319029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98856582627422097161758705 74142436970566572871319029)
      ·
        refine ⟨6950853465990616206686159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74142436970566572871319029 6950853465990616206686159)
        ·
          refine ⟨10426280198985924310029239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6950853465990616206686159 10426280198985924310029239)
          ·
            refine ⟨15639420298478886465043859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10426280198985924310029239 15639420298478886465043859)
            ·
              refine ⟨23459130447718329697565789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15639420298478886465043859 23459130447718329697565789)
              ·
                refine ⟨8797173917894373636587171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23459130447718329697565789 8797173917894373636587171)
                ·
                  refine ⟨13195760876841560454880757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8797173917894373636587171 13195760876841560454880757)
                  ·
                    refine ⟨1237102582203896292645071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13195760876841560454880757 1237102582203896292645071)
                    ·
                      rfl

theorem cell22_3613873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_3613873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613873 prefixEnd_3613873 := by exact prefixLift 3613873
  have htrace : WordTrace (prefixWord ++ tailWord_3613873) baseStart_3613873 baseEnd_3613873 := by
    simpa [prefixWord, tailWord_3613873, baseEnd_3613873] using wordTrace_append hprefix tailTrace_3613873
  have hstable : (prefixWord ++ tailWord_3613873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613873).length < 2 ^ (prefixWord ++ tailWord_3613873).sum := by decide
  have hdescent : baseEnd_3613873 < baseStart_3613873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613888 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 1, 6]
def baseStart_3613888 : Nat := 118140960795 + 3613888 * 2 ^ 59
def prefixEnd_3613888 : Nat := 4983230072969 + 3 ^ 40 * 3613888 * 2
def baseEnd_3613888 : Nat := 1237107717010441253520025

theorem tailTrace_3613888 : CollatzResearch.WordTrace tailWord_3613888 prefixEnd_3613888 1237107717010441253520025 := by
  unfold tailWord_3613888
  simp only [CollatzResearch.WordTrace]
  refine ⟨65904661965754226888737159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87872882621005635851649545 65904661965754226888737159)
  ·
    refine ⟨98856992948631340333105739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65904661965754226888737159 98856992948631340333105739)
    ·
      refine ⟨148285489422947010499658609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98856992948631340333105739 148285489422947010499658609)
      ·
        refine ⟨111214117067210257874743957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148285489422947010499658609 111214117067210257874743957)
        ·
          refine ⟨5213161737525480837878623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111214117067210257874743957 5213161737525480837878623)
          ·
            refine ⟨7819742606288221256817935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5213161737525480837878623 7819742606288221256817935)
            ·
              refine ⟨11729613909432331885226903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7819742606288221256817935 11729613909432331885226903)
              ·
                refine ⟨17594420864148497827840355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11729613909432331885226903 17594420864148497827840355)
                ·
                  refine ⟨26391631296222746741760533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17594420864148497827840355 26391631296222746741760533)
                  ·
                    refine ⟨1237107717010441253520025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26391631296222746741760533 1237107717010441253520025)
                    ·
                      rfl

theorem cell22_3613888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 1, 6].length) (baseStart_3613888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613888 prefixEnd_3613888 := by exact prefixLift 3613888
  have htrace : WordTrace (prefixWord ++ tailWord_3613888) baseStart_3613888 baseEnd_3613888 := by
    simpa [prefixWord, tailWord_3613888, baseEnd_3613888] using wordTrace_append hprefix tailTrace_3613888
  have hstable : (prefixWord ++ tailWord_3613888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613888).length < 2 ^ (prefixWord ++ tailWord_3613888).sum := by decide
  have hdescent : baseEnd_3613888 < baseStart_3613888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613892 : List Nat := [2, 3, 3, 1, 3, 1, 2, 3, 4]
def baseStart_3613892 : Nat := 118140960795 + 3613892 * 2 ^ 59
def prefixEnd_3613892 : Nat := 4983230072969 + 3 ^ 40 * 3613892 * 2
def baseEnd_3613892 : Nat := 412369695430728858806671

theorem tailTrace_3613892 : CollatzResearch.WordTrace tailWord_3613892 prefixEnd_3613892 412369695430728858806671 := by
  unfold tailWord_3613892
  simp only [CollatzResearch.WordTrace]
  refine ⟨65904734911746981230309965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87872979882329308307079953 65904734911746981230309965)
  ·
    refine ⟨24714275591905117961366237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65904734911746981230309965 24714275591905117961366237)
    ·
      refine ⟨9267853346964419235512339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24714275591905117961366237 9267853346964419235512339)
      ·
        refine ⟨13901780020446628853268509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9267853346964419235512339 13901780020446628853268509)
        ·
          refine ⟨5213167507667485819975691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13901780020446628853268509 5213167507667485819975691)
          ·
            refine ⟨7819751261501228729963537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5213167507667485819975691 7819751261501228729963537)
            ·
              refine ⟨5864813446125921547472653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7819751261501228729963537 5864813446125921547472653)
              ·
                refine ⟨2199305042297220580302245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5864813446125921547472653 2199305042297220580302245)
                ·
                  refine ⟨412369695430728858806671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2199305042297220580302245 412369695430728858806671)
                  ·
                    rfl

theorem cell22_3613892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_3613892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3613892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3613892 prefixEnd_3613892 := by exact prefixLift 3613892
  have htrace : WordTrace (prefixWord ++ tailWord_3613892) baseStart_3613892 baseEnd_3613892 := by
    simpa [prefixWord, tailWord_3613892, baseEnd_3613892] using wordTrace_append hprefix tailTrace_3613892
  have hstable : (prefixWord ++ tailWord_3613892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613892).length < 2 ^ (prefixWord ++ tailWord_3613892).sum := by decide
  have hdescent : baseEnd_3613892 < baseStart_3613892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614010 : List Nat := [3, 1, 1, 1, 4, 1, 2, 5, 4]
def baseStart_3614010 : Nat := 118140960795 + 3614010 * 2 ^ 59
def prefixEnd_3614010 : Nat := 4983230072969 + 3 ^ 40 * 3614010 * 2
def baseEnd_3614010 : Nat := 412383160034557867323217

theorem tailTrace_3614010 : CollatzResearch.WordTrace tailWord_3614010 prefixEnd_3614010 412383160034557867323217 := by
  unfold tailWord_3614010
  simp only [CollatzResearch.WordTrace]
  refine ⟨32953443409266617153353871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87875849091377645742276989 32953443409266617153353871)
  ·
    refine ⟨49430165113899925730030807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32953443409266617153353871 49430165113899925730030807)
    ·
      refine ⟨74145247670849888595046211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49430165113899925730030807 74145247670849888595046211)
      ·
        refine ⟨111217871506274832892569317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74145247670849888595046211 111217871506274832892569317)
        ·
          refine ⟨20853350907426531167356747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111217871506274832892569317 20853350907426531167356747)
          ·
            refine ⟨31280026361139796751035121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20853350907426531167356747 31280026361139796751035121)
            ·
              refine ⟨23460019770854847563276341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31280026361139796751035121 23460019770854847563276341)
              ·
                refine ⟨2199376853517641959057157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23460019770854847563276341 2199376853517641959057157)
                ·
                  refine ⟨412383160034557867323217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2199376853517641959057157 412383160034557867323217)
                  ·
                    rfl

theorem cell22_3614010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_3614010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614010 prefixEnd_3614010 := by exact prefixLift 3614010
  have htrace : WordTrace (prefixWord ++ tailWord_3614010) baseStart_3614010 baseEnd_3614010 := by
    simpa [prefixWord, tailWord_3614010, baseEnd_3614010] using wordTrace_append hprefix tailTrace_3614010
  have hstable : (prefixWord ++ tailWord_3614010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614010).length < 2 ^ (prefixWord ++ tailWord_3614010).sum := by decide
  have hdescent : baseEnd_3614010 < baseStart_3614010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614012 : List Nat := [2, 2, 2, 2, 1, 4, 3, 1, 1, 4]
def baseStart_3614012 : Nat := 118140960795 + 3614012 * 2 ^ 59
def prefixEnd_3614012 : Nat := 4983230072969 + 3 ^ 40 * 3614012 * 2
def baseEnd_3614012 : Nat := 1237150164744546263419645

theorem tailTrace_3614012 : CollatzResearch.WordTrace tailWord_3614012 prefixEnd_3614012 1237150164744546263419645 := by
  unfold tailWord_3614012
  simp only [CollatzResearch.WordTrace]
  refine ⟨65906923291529611477494145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87875897722039481969992193 65906923291529611477494145)
  ·
    refine ⟨49430192468647208608120609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65906923291529611477494145 49430192468647208608120609)
    ·
      refine ⟨37072644351485406456090457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49430192468647208608120609 37072644351485406456090457)
      ·
        refine ⟨27804483263614054842067843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37072644351485406456090457 27804483263614054842067843)
        ·
          refine ⟨41706724895421082263101765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27804483263614054842067843 41706724895421082263101765)
          ·
            refine ⟨7820010917891452924331581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41706724895421082263101765 7820010917891452924331581)
            ·
              refine ⟨2932504094209294846624343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7820010917891452924331581 2932504094209294846624343)
              ·
                refine ⟨4398756141313942269936515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2932504094209294846624343 4398756141313942269936515)
                ·
                  refine ⟨6598134211970913404904773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4398756141313942269936515 6598134211970913404904773)
                  ·
                    refine ⟨1237150164744546263419645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6598134211970913404904773 1237150164744546263419645)
                    ·
                      rfl

theorem cell22_3614012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_3614012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614012 prefixEnd_3614012 := by exact prefixLift 3614012
  have htrace : WordTrace (prefixWord ++ tailWord_3614012) baseStart_3614012 baseEnd_3614012 := by
    simpa [prefixWord, tailWord_3614012, baseEnd_3614012] using wordTrace_append hprefix tailTrace_3614012
  have hstable : (prefixWord ++ tailWord_3614012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614012).length < 2 ^ (prefixWord ++ tailWord_3614012).sum := by decide
  have hdescent : baseEnd_3614012 < baseStart_3614012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614025 : List Nat := [1, 2, 1, 1, 2, 3, 3, 4, 2, 3]
def baseStart_3614025 : Nat := 118140960795 + 3614025 * 2 ^ 59
def prefixEnd_3614025 : Nat := 4983230072969 + 3 ^ 40 * 3614025 * 2
def baseEnd_3614025 : Nat := 1237154614910218562844605

theorem tailTrace_3614025 : CollatzResearch.WordTrace tailWord_3614025 prefixEnd_3614025 1237154614910218562844605 := by
  unfold tailWord_3614025
  simp only [CollatzResearch.WordTrace]
  refine ⟨131814320732012126175211529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87876213821341417450141019 131814320732012126175211529)
  ·
    refine ⟨98860740549009094631408647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131814320732012126175211529 98860740549009094631408647)
    ·
      refine ⟨148291110823513641947112971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98860740549009094631408647 148291110823513641947112971)
      ·
        refine ⟨222436666235270462920669457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148291110823513641947112971 222436666235270462920669457)
        ·
          refine ⟨166827499676452847190502093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222436666235270462920669457 166827499676452847190502093)
          ·
            refine ⟨62560312378669817696438285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166827499676452847190502093 62560312378669817696438285)
            ·
              refine ⟨23460117142001181636164357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62560312378669817696438285 23460117142001181636164357)
              ·
                refine ⟨4398771964125221556780817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23460117142001181636164357 4398771964125221556780817)
                ·
                  refine ⟨3299078973093916167585613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4398771964125221556780817 3299078973093916167585613)
                  ·
                    refine ⟨1237154614910218562844605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3299078973093916167585613 1237154614910218562844605)
                    ·
                      rfl

theorem cell22_3614025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 3].length) (baseStart_3614025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614025 prefixEnd_3614025 := by exact prefixLift 3614025
  have htrace : WordTrace (prefixWord ++ tailWord_3614025) baseStart_3614025 baseEnd_3614025 := by
    simpa [prefixWord, tailWord_3614025, baseEnd_3614025] using wordTrace_append hprefix tailTrace_3614025
  have hstable : (prefixWord ++ tailWord_3614025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614025).length < 2 ^ (prefixWord ++ tailWord_3614025).sum := by decide
  have hdescent : baseEnd_3614025 < baseStart_3614025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614087 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 3, 3]
def baseStart_3614087 : Nat := 118140960795 + 3614087 * 2 ^ 59
def prefixEnd_3614087 : Nat := 4983230072969 + 3 ^ 40 * 3614087 * 2
def baseEnd_3614087 : Nat := 1237175838777271067794415

theorem tailTrace_3614087 : CollatzResearch.WordTrace tailWord_3614087 prefixEnd_3614087 1237175838777271067794415 := by
  unfold tailWord_3614087
  simp only [CollatzResearch.WordTrace]
  refine ⟨131816582057787510763968515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87877721371858340509312343 131816582057787510763968515)
  ·
    refine ⟨197724873086681266145952773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131816582057787510763968515 197724873086681266145952773)
    ·
      refine ⟨37073413703752737402366145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197724873086681266145952773 37073413703752737402366145)
      ·
        refine ⟨27805060277814553051774609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37073413703752737402366145 27805060277814553051774609)
        ·
          refine ⟨20853795208360914788830957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27805060277814553051774609 20853795208360914788830957)
          ·
            refine ⟨7820173203135343045811609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20853795208360914788830957 7820173203135343045811609)
            ·
              refine ⟨5865129902351507284358707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7820173203135343045811609 5865129902351507284358707)
              ·
                refine ⟨8797694853527260926538061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5865129902351507284358707 8797694853527260926538061)
                ·
                  refine ⟨3299135570072722847451773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8797694853527260926538061 3299135570072722847451773)
                  ·
                    refine ⟨1237175838777271067794415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3299135570072722847451773 1237175838777271067794415)
                    ·
                      rfl

theorem cell22_3614087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_3614087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614087 prefixEnd_3614087 := by exact prefixLift 3614087
  have htrace : WordTrace (prefixWord ++ tailWord_3614087) baseStart_3614087 baseEnd_3614087 := by
    simpa [prefixWord, tailWord_3614087, baseEnd_3614087] using wordTrace_append hprefix tailTrace_3614087
  have hstable : (prefixWord ++ tailWord_3614087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614087).length < 2 ^ (prefixWord ++ tailWord_3614087).sum := by decide
  have hdescent : baseEnd_3614087 < baseStart_3614087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614194 : List Nat := [3, 2, 1, 4, 1, 1, 1, 4, 2, 3]
def baseStart_3614194 : Nat := 118140960795 + 3614194 * 2 ^ 59
def prefixEnd_3614194 : Nat := 4983230072969 + 3 ^ 40 * 3614194 * 2
def baseEnd_3614194 : Nat := 1237212467063958455369087

theorem tailTrace_3614194 : CollatzResearch.WordTrace tailWord_3614194 prefixEnd_3614194 1237212467063958455369087 := by
  unfold tailWord_3614194
  simp only [CollatzResearch.WordTrace]
  refine ⟨32955121167099967009528409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87880323112266578692075757 32955121167099967009528409)
  ·
    refine ⟨24716340875324975257146307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32955121167099967009528409 24716340875324975257146307)
    ·
      refine ⟨37074511312987462885719461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24716340875324975257146307 37074511312987462885719461)
      ·
        refine ⟨6951470871185149291072399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37074511312987462885719461 6951470871185149291072399)
        ·
          refine ⟨10427206306777723936608599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6951470871185149291072399 10427206306777723936608599)
          ·
            refine ⟨15640809460166585904912899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10427206306777723936608599 15640809460166585904912899)
            ·
              refine ⟨23461214190249878857369349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15640809460166585904912899 23461214190249878857369349)
              ·
                refine ⟨4398977660671852285756753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23461214190249878857369349 4398977660671852285756753)
                ·
                  refine ⟨3299233245503889214317565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4398977660671852285756753 3299233245503889214317565)
                  ·
                    refine ⟨1237212467063958455369087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3299233245503889214317565 1237212467063958455369087)
                    ·
                      rfl

theorem cell22_3614194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_3614194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614194 prefixEnd_3614194 := by exact prefixLift 3614194
  have htrace : WordTrace (prefixWord ++ tailWord_3614194) baseStart_3614194 baseEnd_3614194 := by
    simpa [prefixWord, tailWord_3614194, baseEnd_3614194] using wordTrace_append hprefix tailTrace_3614194
  have hstable : (prefixWord ++ tailWord_3614194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614194).length < 2 ^ (prefixWord ++ tailWord_3614194).sum := by decide
  have hdescent : baseEnd_3614194 < baseStart_3614194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614239 : List Nat := [1, 1, 2, 4, 1, 1, 3, 5, 1, 3]
def baseStart_3614239 : Nat := 118140960795 + 3614239 * 2 ^ 59
def prefixEnd_3614239 : Nat := 4983230072969 + 3 ^ 40 * 3614239 * 2
def baseEnd_3614239 : Nat := 1237227871483593337993949

theorem tailTrace_3614239 : CollatzResearch.WordTrace tailWord_3614239 prefixEnd_3614239 1237227871483593337993949 := by
  unfold tailWord_3614239
  simp only [CollatzResearch.WordTrace]
  refine ⟨131822125953236840723501771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87881417302157893815667847 131822125953236840723501771)
  ·
    refine ⟨197733188929855261085252657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131822125953236840723501771 197733188929855261085252657)
    ·
      refine ⟨148299891697391445813939493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197733188929855261085252657 148299891697391445813939493)
      ·
        refine ⟨27806229693260896090113655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148299891697391445813939493 27806229693260896090113655)
        ·
          refine ⟨41709344539891344135170483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27806229693260896090113655 41709344539891344135170483)
          ·
            refine ⟨62564016809837016202755725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41709344539891344135170483 62564016809837016202755725)
            ·
              refine ⟨23461506303688881076033397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62564016809837016202755725 23461506303688881076033397)
              ·
                refine ⟨2199516215970832600878131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23461506303688881076033397 2199516215970832600878131)
                ·
                  refine ⟨3299274323956248901317197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2199516215970832600878131 3299274323956248901317197)
                  ·
                    refine ⟨1237227871483593337993949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3299274323956248901317197 1237227871483593337993949)
                    ·
                      rfl

theorem cell22_3614239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 1, 3].length) (baseStart_3614239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614239 prefixEnd_3614239 := by exact prefixLift 3614239
  have htrace : WordTrace (prefixWord ++ tailWord_3614239) baseStart_3614239 baseEnd_3614239 := by
    simpa [prefixWord, tailWord_3614239, baseEnd_3614239] using wordTrace_append hprefix tailTrace_3614239
  have hstable : (prefixWord ++ tailWord_3614239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614239).length < 2 ^ (prefixWord ++ tailWord_3614239).sum := by decide
  have hdescent : baseEnd_3614239 < baseStart_3614239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614314 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 6]
def baseStart_3614314 : Nat := 118140960795 + 3614314 * 2 ^ 59
def prefixEnd_3614314 : Nat := 4983230072969 + 3 ^ 40 * 3614314 * 2
def baseEnd_3614314 : Nat := 412417848505439380789573

theorem tailTrace_3614314 : CollatzResearch.WordTrace tailWord_3614314 prefixEnd_3614314 412417848505439380789573 := by
  unfold tailWord_3614314
  simp only [CollatzResearch.WordTrace]
  refine ⟨32956215356991282133120499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87883240951976752354987997 32956215356991282133120499)
  ·
    refine ⟨49434323035486923199680749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32956215356991282133120499 49434323035486923199680749)
    ·
      refine ⟨18537871138307596199880281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49434323035486923199680749 18537871138307596199880281)
      ·
        refine ⟨13903403353730697149910211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18537871138307596199880281 13903403353730697149910211)
        ·
          refine ⟨20855105030596045724865317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13903403353730697149910211 20855105030596045724865317)
          ·
            refine ⟨3910332193236758573412247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20855105030596045724865317 3910332193236758573412247)
            ·
              refine ⟨5865498289855137860118371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3910332193236758573412247 5865498289855137860118371)
              ·
                refine ⟨8798247434782706790177557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5865498289855137860118371 8798247434782706790177557)
                ·
                  refine ⟨412417848505439380789573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8798247434782706790177557 412417848505439380789573)
                  ·
                    rfl

theorem cell22_3614314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_3614314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614314 prefixEnd_3614314 := by exact prefixLift 3614314
  have htrace : WordTrace (prefixWord ++ tailWord_3614314) baseStart_3614314 baseEnd_3614314 := by
    simpa [prefixWord, tailWord_3614314, baseEnd_3614314] using wordTrace_append hprefix tailTrace_3614314
  have hstable : (prefixWord ++ tailWord_3614314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614314).length < 2 ^ (prefixWord ++ tailWord_3614314).sum := by decide
  have hdescent : baseEnd_3614314 < baseStart_3614314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614329 : List Nat := [1, 2, 1, 3, 3, 1, 3, 3, 2, 3]
def baseStart_3614329 : Nat := 118140960795 + 3614329 * 2 ^ 59
def prefixEnd_3614329 : Nat := 4983230072969 + 3 ^ 40 * 3614329 * 2
def baseEnd_3614329 : Nat := 1237258680322863103243673

theorem tailTrace_3614329 : CollatzResearch.WordTrace tailWord_3614329 prefixEnd_3614329 1237258680322863103243673 := by
  unfold tailWord_3614329
  simp only [CollatzResearch.WordTrace]
  refine ⟨131825408522910786094278041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87883605681940524062852027 131825408522910786094278041)
  ·
    refine ⟨98869056392183089570708531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131825408522910786094278041 98869056392183089570708531)
    ·
      refine ⟨148303584588274634356062797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98869056392183089570708531 148303584588274634356062797)
      ·
        refine ⟨55613844220602987883523549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148303584588274634356062797 55613844220602987883523549)
        ·
          refine ⟨20855191582726120456321331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55613844220602987883523549 20855191582726120456321331)
          ·
            refine ⟨31282787374089180684481997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20855191582726120456321331 31282787374089180684481997)
            ·
              refine ⟨11731045265283442756680749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31282787374089180684481997 11731045265283442756680749)
              ·
                refine ⟨4399141974481291033755281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11731045265283442756680749 4399141974481291033755281)
                ·
                  refine ⟨3299356480860968275316461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4399141974481291033755281 3299356480860968275316461)
                  ·
                    refine ⟨1237258680322863103243673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3299356480860968275316461 1237258680322863103243673)
                    ·
                      rfl

theorem cell22_3614329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 3].length) (baseStart_3614329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614329 prefixEnd_3614329 := by exact prefixLift 3614329
  have htrace : WordTrace (prefixWord ++ tailWord_3614329) baseStart_3614329 baseEnd_3614329 := by
    simpa [prefixWord, tailWord_3614329, baseEnd_3614329] using wordTrace_append hprefix tailTrace_3614329
  have hstable : (prefixWord ++ tailWord_3614329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614329).length < 2 ^ (prefixWord ++ tailWord_3614329).sum := by decide
  have hdescent : baseEnd_3614329 < baseStart_3614329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614355 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 3, 8]
def baseStart_3614355 : Nat := 118140960795 + 3614355 * 2 ^ 59
def prefixEnd_3614355 : Nat := 4983230072969 + 3 ^ 40 * 3614355 * 2
def baseEnd_3614355 : Nat := 1237267580654207702093593

theorem tailTrace_3614355 : CollatzResearch.WordTrace tailWord_3614355 prefixEnd_3614355 1237267580654207702093593 := by
  unfold tailWord_3614355
  simp only [CollatzResearch.WordTrace]
  refine ⟨131826356820816592534724519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87884237880544395023149679 131826356820816592534724519)
  ·
    refine ⟨197739535231224888802086779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131826356820816592534724519 197739535231224888802086779)
    ·
      refine ⟨296609302846837333203130169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197739535231224888802086779 296609302846837333203130169)
      ·
        refine ⟨222456977135127999902347627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296609302846837333203130169 222456977135127999902347627)
        ·
          refine ⟨333685465702691999853521441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222456977135127999902347627 333685465702691999853521441)
          ·
            refine ⟨250264099277018999890141081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333685465702691999853521441 250264099277018999890141081)
            ·
              refine ⟨187698074457764249917605811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250264099277018999890141081 187698074457764249917605811)
              ·
                refine ⟨281547111686646374876408717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187698074457764249917605811 281547111686646374876408717)
                ·
                  refine ⟨105580166882492390578653269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281547111686646374876408717 105580166882492390578653269)
                  ·
                    refine ⟨1237267580654207702093593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105580166882492390578653269 1237267580654207702093593)
                    ·
                      rfl

theorem cell22_3614355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 8].length) (baseStart_3614355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614355 prefixEnd_3614355 := by exact prefixLift 3614355
  have htrace : WordTrace (prefixWord ++ tailWord_3614355) baseStart_3614355 baseEnd_3614355 := by
    simpa [prefixWord, tailWord_3614355, baseEnd_3614355] using wordTrace_append hprefix tailTrace_3614355
  have hstable : (prefixWord ++ tailWord_3614355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614355).length < 2 ^ (prefixWord ++ tailWord_3614355).sum := by decide
  have hdescent : baseEnd_3614355 < baseStart_3614355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614372 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_3614372 : Nat := 118140960795 + 3614372 * 2 ^ 59
def prefixEnd_3614372 : Nat := 4983230072969 + 3 ^ 40 * 3614372 * 2
def baseEnd_3614372 : Nat := 1237273400101625324418541

theorem tailTrace_3614372 : CollatzResearch.WordTrace tailWord_3614372 prefixEnd_3614372 1237273400101625324418541 := by
  unfold tailWord_3614372
  simp only [CollatzResearch.WordTrace]
  refine ⟨65913488430877502219046685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87884651241170002958728913 65913488430877502219046685)
  ·
    refine ⟨24717558161579063332142507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65913488430877502219046685 24717558161579063332142507)
    ·
      refine ⟨37076337242368594998213761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24717558161579063332142507 37076337242368594998213761)
      ·
        refine ⟨27807252931776446248660321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37076337242368594998213761 27807252931776446248660321)
        ·
          refine ⟨20855439698832334686495241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27807252931776446248660321 20855439698832334686495241)
          ·
            refine ⟨15641579774124251014871431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20855439698832334686495241 15641579774124251014871431)
            ·
              refine ⟨23462369661186376522307147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15641579774124251014871431 23462369661186376522307147)
              ·
                refine ⟨35193554491779564783460721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23462369661186376522307147 35193554491779564783460721)
                ·
                  refine ⟨26395165868834673587595541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35193554491779564783460721 26395165868834673587595541)
                  ·
                    refine ⟨1237273400101625324418541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26395165868834673587595541 1237273400101625324418541)
                    ·
                      rfl

theorem cell22_3614372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_3614372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614372 prefixEnd_3614372 := by exact prefixLift 3614372
  have htrace : WordTrace (prefixWord ++ tailWord_3614372) baseStart_3614372 baseEnd_3614372 := by
    simpa [prefixWord, tailWord_3614372, baseEnd_3614372] using wordTrace_append hprefix tailTrace_3614372
  have hstable : (prefixWord ++ tailWord_3614372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614372).length < 2 ^ (prefixWord ++ tailWord_3614372).sum := by decide
  have hdescent : baseEnd_3614372 < baseStart_3614372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614387 : List Nat := [1, 1, 1, 2, 3, 3, 1, 5, 5]
def baseStart_3614387 : Nat := 118140960795 + 3614387 * 2 ^ 59
def prefixEnd_3614387 : Nat := 4983230072969 + 3 ^ 40 * 3614387 * 2
def baseEnd_3614387 : Nat := 412426178302723428431165

theorem tailTrace_3614387 : CollatzResearch.WordTrace tailWord_3614387 prefixEnd_3614387 412426178302723428431165 := by
  unfold tailWord_3614387
  simp only [CollatzResearch.WordTrace]
  refine ⟨131827523956700661999889415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87885015971133774666592943 131827523956700661999889415)
  ·
    refine ⟨197741285935050992999834123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131827523956700661999889415 197741285935050992999834123)
    ·
      refine ⟨296611928902576489499751185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197741285935050992999834123 296611928902576489499751185)
      ·
        refine ⟨222458946676932367124813389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296611928902576489499751185 222458946676932367124813389)
        ·
          refine ⟨83422105003849637671805021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222458946676932367124813389 83422105003849637671805021)
          ·
            refine ⟨31283289376443614126926883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83422105003849637671805021 31283289376443614126926883)
            ·
              refine ⟨46924934064665421190390325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31283289376443614126926883 46924934064665421190390325)
              ·
                refine ⟨4399212568562383236599093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46924934064665421190390325 4399212568562383236599093)
                ·
                  refine ⟨412426178302723428431165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4399212568562383236599093 412426178302723428431165)
                  ·
                    rfl

theorem cell22_3614387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 5].length) (baseStart_3614387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614387 prefixEnd_3614387 := by exact prefixLift 3614387
  have htrace : WordTrace (prefixWord ++ tailWord_3614387) baseStart_3614387 baseEnd_3614387 := by
    simpa [prefixWord, tailWord_3614387, baseEnd_3614387] using wordTrace_append hprefix tailTrace_3614387
  have hstable : (prefixWord ++ tailWord_3614387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614387).length < 2 ^ (prefixWord ++ tailWord_3614387).sum := by decide
  have hdescent : baseEnd_3614387 < baseStart_3614387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614432 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 6]
def baseStart_3614432 : Nat := 118140960795 + 3614432 * 2 ^ 59
def prefixEnd_3614432 : Nat := 4983230072969 + 3 ^ 40 * 3614432 * 2
def baseEnd_3614432 : Nat := 412431313109268389306119

theorem tailTrace_3614432 : CollatzResearch.WordTrace tailWord_3614432 prefixEnd_3614432 412431313109268389306119 := by
  unfold tailWord_3614432
  simp only [CollatzResearch.WordTrace]
  refine ⟨65914582620768817342638775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87886110161025089790185033 65914582620768817342638775)
  ·
    refine ⟨98871873931153226013958163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65914582620768817342638775 98871873931153226013958163)
    ·
      refine ⟨148307810896729839020937245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98871873931153226013958163 148307810896729839020937245)
      ·
        refine ⟨55615429086273689632851467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148307810896729839020937245 55615429086273689632851467)
        ·
          refine ⟨83423143629410534449277201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55615429086273689632851467 83423143629410534449277201)
          ·
            refine ⟨62567357722057900836957901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83423143629410534449277201 62567357722057900836957901)
            ·
              refine ⟨23462759145771712813859213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62567357722057900836957901 23462759145771712813859213)
              ·
                refine ⟨8798534679664392305197205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23462759145771712813859213 8798534679664392305197205)
                ·
                  refine ⟨412431313109268389306119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8798534679664392305197205 412431313109268389306119)
                  ·
                    rfl

theorem cell22_3614432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 6].length) (baseStart_3614432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614432 prefixEnd_3614432 := by exact prefixLift 3614432
  have htrace : WordTrace (prefixWord ++ tailWord_3614432) baseStart_3614432 baseEnd_3614432 := by
    simpa [prefixWord, tailWord_3614432, baseEnd_3614432] using wordTrace_append hprefix tailTrace_3614432
  have hstable : (prefixWord ++ tailWord_3614432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614432).length < 2 ^ (prefixWord ++ tailWord_3614432).sum := by decide
  have hdescent : baseEnd_3614432 < baseStart_3614432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614541 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_3614541 : Nat := 118140960795 + 3614541 * 2 ^ 59
def prefixEnd_3614541 : Nat := 4983230072969 + 3 ^ 40 * 3614541 * 2
def baseEnd_3614541 : Nat := 1237331252255365216943023

theorem tailTrace_3614541 : CollatzResearch.WordTrace tailWord_3614541 prefixEnd_3614541 1237331252255365216943023 := by
  unfold tailWord_3614541
  simp only [CollatzResearch.WordTrace]
  refine ⟨131833140798142746300995477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87888760532095164200663651 131833140798142746300995477)
  ·
    refine ⟨6179678474912941232859163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131833140798142746300995477 6179678474912941232859163)
    ·
      refine ⟨9269517712369411849288745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6179678474912941232859163 9269517712369411849288745)
      ·
        refine ⟨6952138284277058886966559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9269517712369411849288745 6952138284277058886966559)
        ·
          refine ⟨10428207426415588330449839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6952138284277058886966559 10428207426415588330449839)
          ·
            refine ⟨15642311139623382495674759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10428207426415588330449839 15642311139623382495674759)
            ·
              refine ⟨23463466709435073743512139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15642311139623382495674759 23463466709435073743512139)
              ·
                refine ⟨35195200064152610615268209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23463466709435073743512139 35195200064152610615268209)
                ·
                  refine ⟨26396400048114457961451157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35195200064152610615268209 26396400048114457961451157)
                  ·
                    refine ⟨1237331252255365216943023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26396400048114457961451157 1237331252255365216943023)
                    ·
                      rfl

theorem cell22_3614541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_3614541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614541 prefixEnd_3614541 := by exact prefixLift 3614541
  have htrace : WordTrace (prefixWord ++ tailWord_3614541) baseStart_3614541 baseEnd_3614541 := by
    simpa [prefixWord, tailWord_3614541, baseEnd_3614541] using wordTrace_append hprefix tailTrace_3614541
  have hstable : (prefixWord ++ tailWord_3614541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614541).length < 2 ^ (prefixWord ++ tailWord_3614541).sum := by decide
  have hdescent : baseEnd_3614541 < baseStart_3614541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614554 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 2, 5]
def baseStart_3614554 : Nat := 118140960795 + 3614554 * 2 ^ 59
def prefixEnd_3614554 : Nat := 4983230072969 + 3 ^ 40 * 3614554 * 2
def baseEnd_3614554 : Nat := 1237335702421037516367983

theorem tailTrace_3614554 : CollatzResearch.WordTrace tailWord_3614554 prefixEnd_3614554 1237335702421037516367983 := by
  unfold tailWord_3614554
  simp only [CollatzResearch.WordTrace]
  refine ⟨32958403736773912380304679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87889076631397099680812477 32958403736773912380304679)
  ·
    refine ⟨49437605605160868570457019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32958403736773912380304679 49437605605160868570457019)
    ·
      refine ⟨74156408407741302855685529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49437605605160868570457019 74156408407741302855685529)
      ·
        refine ⟨55617306305805977141764147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74156408407741302855685529 55617306305805977141764147)
        ·
          refine ⟨83425959458708965712646221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55617306305805977141764147 83425959458708965712646221)
          ·
            refine ⟨31284734797015862142242333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83425959458708965712646221 31284734797015862142242333)
            ·
              refine ⟨11731775548880948303340875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31284734797015862142242333 11731775548880948303340875)
              ·
                refine ⟨17597663323321422455011313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11731775548880948303340875 17597663323321422455011313)
                ·
                  refine ⟨13198247492491066841258485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17597663323321422455011313 13198247492491066841258485)
                  ·
                    refine ⟨1237335702421037516367983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13198247492491066841258485 1237335702421037516367983)
                    ·
                      rfl

theorem cell22_3614554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_3614554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614554 prefixEnd_3614554 := by exact prefixLift 3614554
  have htrace : WordTrace (prefixWord ++ tailWord_3614554) baseStart_3614554 baseEnd_3614554 := by
    simpa [prefixWord, tailWord_3614554, baseEnd_3614554] using wordTrace_append hprefix tailTrace_3614554
  have hstable : (prefixWord ++ tailWord_3614554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614554).length < 2 ^ (prefixWord ++ tailWord_3614554).sum := by decide
  have hdescent : baseEnd_3614554 < baseStart_3614554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614590 : List Nat := [4, 2, 3, 1, 1, 3, 1, 2, 5]
def baseStart_3614590 : Nat := 118140960795 + 3614590 * 2 ^ 59
def prefixEnd_3614590 : Nat := 4983230072969 + 3 ^ 40 * 3614590 * 2
def baseEnd_3614590 : Nat := 412449341985581807489291

theorem tailTrace_3614590 : CollatzResearch.WordTrace tailWord_3614590 prefixEnd_3614590 412449341985581807489291 := by
  unfold tailWord_3614590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16479365996870653458691153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87889951983310151779686149 16479365996870653458691153)
  ·
    refine ⟨12359524497652990094018365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16479365996870653458691153 12359524497652990094018365)
    ·
      refine ⟨4634821686619871285256887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12359524497652990094018365 4634821686619871285256887)
      ·
        refine ⟨6952232529929806927885331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4634821686619871285256887 6952232529929806927885331)
        ·
          refine ⟨10428348794894710391827997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6952232529929806927885331 10428348794894710391827997)
          ·
            refine ⟨3910630798085516396935499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10428348794894710391827997 3910630798085516396935499)
            ·
              refine ⟨5865946197128274595403249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3910630798085516396935499 5865946197128274595403249)
              ·
                refine ⟨4399459647846205946552437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5865946197128274595403249 4399459647846205946552437)
                ·
                  refine ⟨412449341985581807489291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4399459647846205946552437 412449341985581807489291)
                  ·
                    rfl

theorem cell22_3614590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_3614590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614590 prefixEnd_3614590 := by exact prefixLift 3614590
  have htrace : WordTrace (prefixWord ++ tailWord_3614590) baseStart_3614590 baseEnd_3614590 := by
    simpa [prefixWord, tailWord_3614590, baseEnd_3614590] using wordTrace_append hprefix tailTrace_3614590
  have hstable : (prefixWord ++ tailWord_3614590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614590).length < 2 ^ (prefixWord ++ tailWord_3614590).sum := by decide
  have hdescent : baseEnd_3614590 < baseStart_3614590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614601 : List Nat := [1, 2, 1, 1, 5, 1, 1, 6, 4]
def baseStart_3614601 : Nat := 118140960795 + 3614601 * 2 ^ 59
def prefixEnd_3614601 : Nat := 4983230072969 + 3 ^ 40 * 3614601 * 2
def baseEnd_3614601 : Nat := 412450597160515020147613

theorem tailTrace_3614601 : CollatzResearch.WordTrace tailWord_3614601 prefixEnd_3614601 412450597160515020147613 := by
  unfold tailWord_3614601
  simp only [CollatzResearch.WordTrace]
  refine ⟨131835329177925376548179657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87890219451950251032119771 131835329177925376548179657)
  ·
    refine ⟨98876496883444032411134743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131835329177925376548179657 98876496883444032411134743)
    ·
      refine ⟨148314745325166048616702115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98876496883444032411134743 148314745325166048616702115)
      ·
        refine ⟨222472117987749072925053173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148314745325166048616702115 222472117987749072925053173)
        ·
          refine ⟨20856761061351475586723735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222472117987749072925053173 20856761061351475586723735)
          ·
            refine ⟨31285141592027213380085603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20856761061351475586723735 31285141592027213380085603)
            ·
              refine ⟨46927712388040820070128405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31285141592027213380085603 46927712388040820070128405)
              ·
                refine ⟨2199736518189413440787269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46927712388040820070128405 2199736518189413440787269)
                ·
                  refine ⟨412450597160515020147613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2199736518189413440787269 412450597160515020147613)
                  ·
                    rfl

theorem cell22_3614601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 4].length) (baseStart_3614601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614601 prefixEnd_3614601 := by exact prefixLift 3614601
  have htrace : WordTrace (prefixWord ++ tailWord_3614601) baseStart_3614601 baseEnd_3614601 := by
    simpa [prefixWord, tailWord_3614601, baseEnd_3614601] using wordTrace_append hprefix tailTrace_3614601
  have hstable : (prefixWord ++ tailWord_3614601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614601).length < 2 ^ (prefixWord ++ tailWord_3614601).sum := by decide
  have hdescent : baseEnd_3614601 < baseStart_3614601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614631 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3614631 : Nat := 118140960795 + 3614631 * 2 ^ 59
def prefixEnd_3614631 : Nat := 4983230072969 + 3 ^ 40 * 3614631 * 2
def baseEnd_3614631 : Nat := 1237362061094634982192747

theorem tailTrace_3614631 : CollatzResearch.WordTrace tailWord_3614631 prefixEnd_3614631 1237362061094634982192747 := by
  unfold tailWord_3614631
  simp only [CollatzResearch.WordTrace]
  refine ⟨131836423367816691671771747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87890948911877794447847831 131836423367816691671771747)
  ·
    refine ⟨197754635051725037507657621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131836423367816691671771747 197754635051725037507657621)
    ·
      refine ⟨9269748518049611133171451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 197754635051725037507657621 9269748518049611133171451)
      ·
        refine ⟨13904622777074416699757177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9269748518049611133171451 13904622777074416699757177)
        ·
          refine ⟨10428467082805812524817883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13904622777074416699757177 10428467082805812524817883)
          ·
            refine ⟨15642700624208718787226825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10428467082805812524817883 15642700624208718787226825)
            ·
              refine ⟨11732025468156539090420119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15642700624208718787226825 11732025468156539090420119)
              ·
                refine ⟨17598038202234808635630179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11732025468156539090420119 17598038202234808635630179)
                ·
                  refine ⟨26397057303352212953445269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17598038202234808635630179 26397057303352212953445269)
                  ·
                    refine ⟨1237362061094634982192747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26397057303352212953445269 1237362061094634982192747)
                    ·
                      rfl

theorem cell22_3614631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3614631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614631 prefixEnd_3614631 := by exact prefixLift 3614631
  have htrace : WordTrace (prefixWord ++ tailWord_3614631) baseStart_3614631 baseEnd_3614631 := by
    simpa [prefixWord, tailWord_3614631, baseEnd_3614631] using wordTrace_append hprefix tailTrace_3614631
  have hstable : (prefixWord ++ tailWord_3614631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614631).length < 2 ^ (prefixWord ++ tailWord_3614631).sum := by decide
  have hdescent : baseEnd_3614631 < baseStart_3614631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614652 : List Nat := [2, 2, 2, 5, 1, 1, 3, 2, 4]
def baseStart_3614652 : Nat := 118140960795 + 3614652 * 2 ^ 59
def prefixEnd_3614652 : Nat := 4983230072969 + 3 ^ 40 * 3614652 * 2
def baseEnd_3614652 : Nat := 412456416607932642472561

theorem tailTrace_3614652 : CollatzResearch.WordTrace tailWord_3614652 prefixEnd_3614652 412456416607932642472561 := by
  unfold tailWord_3614652
  simp only [CollatzResearch.WordTrace]
  refine ⟨65918594650370306129143105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87891459533827074838857473 65918594650370306129143105)
  ·
    refine ⟨49438945987777729596857329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65918594650370306129143105 49438945987777729596857329)
    ·
      refine ⟨37079209490833297197642997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49438945987777729596857329 37079209490833297197642997)
      ·
        refine ⟨3476175889765621612279031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37079209490833297197642997 3476175889765621612279031)
        ·
          refine ⟨5214263834648432418418547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3476175889765621612279031 5214263834648432418418547)
          ·
            refine ⟨7821395751972648627627821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5214263834648432418418547 7821395751972648627627821)
            ·
              refine ⟨2933023406989743235360433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7821395751972648627627821 2933023406989743235360433)
              ·
                refine ⟨2199767555242307426520325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2933023406989743235360433 2199767555242307426520325)
                ·
                  refine ⟨412456416607932642472561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2199767555242307426520325 412456416607932642472561)
                  ·
                    rfl

theorem cell22_3614652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_3614652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614652 prefixEnd_3614652 := by exact prefixLift 3614652
  have htrace : WordTrace (prefixWord ++ tailWord_3614652) baseStart_3614652 baseEnd_3614652 := by
    simpa [prefixWord, tailWord_3614652, baseEnd_3614652] using wordTrace_append hprefix tailTrace_3614652
  have hstable : (prefixWord ++ tailWord_3614652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614652).length < 2 ^ (prefixWord ++ tailWord_3614652).sum := by decide
  have hdescent : baseEnd_3614652 < baseStart_3614652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614661 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 3, 3]
def baseStart_3614661 : Nat := 118140960795 + 3614661 * 2 ^ 59
def prefixEnd_3614661 : Nat := 4983230072969 + 3 ^ 40 * 3614661 * 2
def baseEnd_3614661 : Nat := 1237372330707724903942655

theorem tailTrace_3614661 : CollatzResearch.WordTrace tailWord_3614661 prefixEnd_3614661 1237372330707724903942655 := by
  unfold tailWord_3614661
  simp only [CollatzResearch.WordTrace]
  refine ⟨131837517557708006795363837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87891678371805337863575891 131837517557708006795363837)
  ·
    refine ⟨49439069084140502548261439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131837517557708006795363837 49439069084140502548261439)
    ·
      refine ⟨74158603626210753822392159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49439069084140502548261439 74158603626210753822392159)
      ·
        refine ⟨111237905439316130733588239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74158603626210753822392159 111237905439316130733588239)
        ·
          refine ⟨166856858158974196100382359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111237905439316130733588239 166856858158974196100382359)
          ·
            refine ⟨250285287238461294150573539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166856858158974196100382359 250285287238461294150573539)
            ·
              refine ⟨375427930857691941225860309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250285287238461294150573539 375427930857691941225860309)
              ·
                refine ⟨8799092129477154872481101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 375427930857691941225860309 8799092129477154872481101)
                ·
                  refine ⟨3299659548553933077180413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8799092129477154872481101 3299659548553933077180413)
                  ·
                    refine ⟨1237372330707724903942655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3299659548553933077180413 1237372330707724903942655)
                    ·
                      rfl

theorem cell22_3614661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_3614661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614661 prefixEnd_3614661 := by exact prefixLift 3614661
  have htrace : WordTrace (prefixWord ++ tailWord_3614661) baseStart_3614661 baseEnd_3614661 := by
    simpa [prefixWord, tailWord_3614661, baseEnd_3614661] using wordTrace_append hprefix tailTrace_3614661
  have hstable : (prefixWord ++ tailWord_3614661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614661).length < 2 ^ (prefixWord ++ tailWord_3614661).sum := by decide
  have hdescent : baseEnd_3614661 < baseStart_3614661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614719 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 10]
def baseStart_3614719 : Nat := 118140960795 + 3614719 * 2 ^ 59
def prefixEnd_3614719 : Nat := 4983230072969 + 3 ^ 40 * 3614719 * 2
def baseEnd_3614719 : Nat := 412464061764344028664159

theorem tailTrace_3614719 : CollatzResearch.WordTrace tailWord_3614719 prefixEnd_3614719 412464061764344028664159 := by
  unfold tailWord_3614719
  simp only [CollatzResearch.WordTrace]
  refine ⟨131839632991497882700975211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87893088660998588467316807 131839632991497882700975211)
  ·
    refine ⟨197759449487246824051462817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131839632991497882700975211 197759449487246824051462817)
    ·
      refine ⟨148319587115435118038597113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197759449487246824051462817 148319587115435118038597113)
      ·
        refine ⟨111239690336576338528947835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148319587115435118038597113 111239690336576338528947835)
        ·
          refine ⟨166859535504864507793421753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111239690336576338528947835 166859535504864507793421753)
          ·
            refine ⟨125144651628648380845066315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166859535504864507793421753 125144651628648380845066315)
            ·
              refine ⟨187716977442972571267599473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125144651628648380845066315 187716977442972571267599473)
              ·
                refine ⟨140787733082229428450699605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187716977442972571267599473 140787733082229428450699605)
                ·
                  refine ⟨412464061764344028664159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 140787733082229428450699605 412464061764344028664159)
                  ·
                    rfl

theorem cell22_3614719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 10].length) (baseStart_3614719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614719 prefixEnd_3614719 := by exact prefixLift 3614719
  have htrace : WordTrace (prefixWord ++ tailWord_3614719) baseStart_3614719 baseEnd_3614719 := by
    simpa [prefixWord, tailWord_3614719, baseEnd_3614719] using wordTrace_append hprefix tailTrace_3614719
  have hstable : (prefixWord ++ tailWord_3614719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614719).length < 2 ^ (prefixWord ++ tailWord_3614719).sum := by decide
  have hdescent : baseEnd_3614719 < baseStart_3614719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614721 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 5, 4]
def baseStart_3614721 : Nat := 118140960795 + 3614721 * 2 ^ 59
def prefixEnd_3614721 : Nat := 4983230072969 + 3 ^ 40 * 3614721 * 2
def baseEnd_3614721 : Nat := 1237392869933904747442471

theorem tailTrace_3614721 : CollatzResearch.WordTrace tailWord_3614721 prefixEnd_3614721 1237392869933904747442471 := by
  unfold tailWord_3614721
  simp only [CollatzResearch.WordTrace]
  refine ⟨131839705937490637042548017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87893137291660424695032011 131839705937490637042548017)
  ·
    refine ⟨98879779453117977781911013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131839705937490637042548017 98879779453117977781911013)
    ·
      refine ⟨18539958647459620834108315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98879779453117977781911013 18539958647459620834108315)
      ·
        refine ⟨27809937971189431251162473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18539958647459620834108315 27809937971189431251162473)
        ·
          refine ⟨20857453478392073438371855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27809937971189431251162473 20857453478392073438371855)
          ·
            refine ⟨31286180217588110157557783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20857453478392073438371855 31286180217588110157557783)
            ·
              refine ⟨46929270326382165236336675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31286180217588110157557783 46929270326382165236336675)
              ·
                refine ⟨70393905489573247854505013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46929270326382165236336675 70393905489573247854505013)
                ·
                  refine ⟨6599428639647491986359845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70393905489573247854505013 6599428639647491986359845)
                  ·
                    refine ⟨1237392869933904747442471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6599428639647491986359845 1237392869933904747442471)
                    ·
                      rfl

theorem cell22_3614721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_3614721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614721 prefixEnd_3614721 := by exact prefixLift 3614721
  have htrace : WordTrace (prefixWord ++ tailWord_3614721) baseStart_3614721 baseEnd_3614721 := by
    simpa [prefixWord, tailWord_3614721, baseEnd_3614721] using wordTrace_append hprefix tailTrace_3614721
  have hstable : (prefixWord ++ tailWord_3614721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614721).length < 2 ^ (prefixWord ++ tailWord_3614721).sum := by decide
  have hdescent : baseEnd_3614721 < baseStart_3614721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614751 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 1, 5]
def baseStart_3614751 : Nat := 118140960795 + 3614751 * 2 ^ 59
def prefixEnd_3614751 : Nat := 4983230072969 + 3 ^ 40 * 3614751 * 2
def baseEnd_3614751 : Nat := 1237403139546994669192379

theorem tailTrace_3614751 : CollatzResearch.WordTrace tailWord_3614751 prefixEnd_3614751 1237403139546994669192379 := by
  unfold tailWord_3614751
  simp only [CollatzResearch.WordTrace]
  refine ⟨131840800127381952166140107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87893866751587968110760071 131840800127381952166140107)
  ·
    refine ⟨197761200191072928249210161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131840800127381952166140107 197761200191072928249210161)
    ·
      refine ⟨148320900143304696186907621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197761200191072928249210161 148320900143304696186907621)
      ·
        refine ⟨27810168776869630535045179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148320900143304696186907621 27810168776869630535045179)
        ·
          refine ⟨41715253165304445802567769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27810168776869630535045179 41715253165304445802567769)
          ·
            refine ⟨31286439873978334351925827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41715253165304445802567769 31286439873978334351925827)
            ·
              refine ⟨46929659810967501527888741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31286439873978334351925827 46929659810967501527888741)
              ·
                refine ⟨8799311214556406536479139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46929659810967501527888741 8799311214556406536479139)
                ·
                  refine ⟨13198966821834609804718709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8799311214556406536479139 13198966821834609804718709)
                  ·
                    refine ⟨1237403139546994669192379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13198966821834609804718709 1237403139546994669192379)
                    ·
                      rfl

theorem cell22_3614751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_3614751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614751 prefixEnd_3614751 := by exact prefixLift 3614751
  have htrace : WordTrace (prefixWord ++ tailWord_3614751) baseStart_3614751 baseEnd_3614751 := by
    simpa [prefixWord, tailWord_3614751, baseEnd_3614751] using wordTrace_append hprefix tailTrace_3614751
  have hstable : (prefixWord ++ tailWord_3614751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614751).length < 2 ^ (prefixWord ++ tailWord_3614751).sum := by decide
  have hdescent : baseEnd_3614751 < baseStart_3614751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614768 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 4, 3]
def baseStart_3614768 : Nat := 118140960795 + 3614768 * 2 ^ 59
def prefixEnd_3614768 : Nat := 4983230072969 + 3 ^ 40 * 3614768 * 2
def baseEnd_3614768 : Nat := 1237408958994412291517327

theorem tailTrace_3614768 : CollatzResearch.WordTrace tailWord_3614768 prefixEnd_3614768 1237408958994412291517327 := by
  unfold tailWord_3614768
  simp only [CollatzResearch.WordTrace]
  refine ⟨65920710084160182034754479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87894280112213576046339305 65920710084160182034754479)
  ·
    refine ⟨98881065126240273052131719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65920710084160182034754479 98881065126240273052131719)
    ·
      refine ⟨148321597689360409578197579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98881065126240273052131719 148321597689360409578197579)
      ·
        refine ⟨222482396534040614367296369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148321597689360409578197579 222482396534040614367296369)
        ·
          refine ⟨166861797400530460775472277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222482396534040614367296369 166861797400530460775472277)
          ·
            refine ⟨7821646753149865348850263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166861797400530460775472277 7821646753149865348850263)
            ·
              refine ⟨11732470129724798023275395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7821646753149865348850263 11732470129724798023275395)
              ·
                refine ⟨17598705194587197034913093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11732470129724798023275395 17598705194587197034913093)
                ·
                  refine ⟨3299757223985099444046205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17598705194587197034913093 3299757223985099444046205)
                  ·
                    refine ⟨1237408958994412291517327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3299757223985099444046205 1237408958994412291517327)
                    ·
                      rfl

theorem cell22_3614768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 4, 3].length) (baseStart_3614768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614768 prefixEnd_3614768 := by exact prefixLift 3614768
  have htrace : WordTrace (prefixWord ++ tailWord_3614768) baseStart_3614768 baseEnd_3614768 := by
    simpa [prefixWord, tailWord_3614768, baseEnd_3614768] using wordTrace_append hprefix tailTrace_3614768
  have hstable : (prefixWord ++ tailWord_3614768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614768).length < 2 ^ (prefixWord ++ tailWord_3614768).sum := by decide
  have hdescent : baseEnd_3614768 < baseStart_3614768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614781 : List Nat := [1, 4, 1, 3, 1, 1, 2, 9]
def baseStart_3614781 : Nat := 118140960795 + 3614781 * 2 ^ 59
def prefixEnd_3614781 : Nat := 4983230072969 + 3 ^ 40 * 3614781 * 2
def baseEnd_3614781 : Nat := 137490378795564954549143

theorem tailTrace_3614781 : CollatzResearch.WordTrace tailWord_3614781 prefixEnd_3614781 137490378795564954549143 := by
  unfold tailWord_3614781
  simp only [CollatzResearch.WordTrace]
  refine ⟨131841894317273267289732197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87894596211515511526488131 131841894317273267289732197)
  ·
    refine ⟨24720355184488737616824787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131841894317273267289732197 24720355184488737616824787)
    ·
      refine ⟨37080532776733106425237181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24720355184488737616824787 37080532776733106425237181)
      ·
        refine ⟨13905199791274914909463943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37080532776733106425237181 13905199791274914909463943)
        ·
          refine ⟨20857799686912372364195915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13905199791274914909463943 20857799686912372364195915)
          ·
            refine ⟨31286699530368558546293873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20857799686912372364195915 31286699530368558546293873)
            ·
              refine ⟨23465024647776418909720405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31286699530368558546293873 23465024647776418909720405)
              ·
                refine ⟨137490378795564954549143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23465024647776418909720405 137490378795564954549143)
                ·
                  rfl

theorem cell22_3614781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 9].length) (baseStart_3614781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614781 prefixEnd_3614781 := by exact prefixLift 3614781
  have htrace : WordTrace (prefixWord ++ tailWord_3614781) baseStart_3614781 baseEnd_3614781 := by
    simpa [prefixWord, tailWord_3614781, baseEnd_3614781] using wordTrace_append hprefix tailTrace_3614781
  have hstable : (prefixWord ++ tailWord_3614781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614781).length < 2 ^ (prefixWord ++ tailWord_3614781).sum := by decide
  have hdescent : baseEnd_3614781 < baseStart_3614781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614785 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 1, 5]
def baseStart_3614785 : Nat := 118140960795 + 3614785 * 2 ^ 59
def prefixEnd_3614785 : Nat := 4983230072969 + 3 ^ 40 * 3614785 * 2
def baseEnd_3614785 : Nat := 1237414778441829913842275

theorem tailTrace_3614785 : CollatzResearch.WordTrace tailWord_3614785 prefixEnd_3614785 1237414778441829913842275 := by
  unfold tailWord_3614785
  simp only [CollatzResearch.WordTrace]
  refine ⟨131842040209258775972877809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87894693472839183981918539 131842040209258775972877809)
  ·
    refine ⟨98881530156944081979658357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131842040209258775972877809 98881530156944081979658357)
    ·
      refine ⟨9270143452213507685592971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98881530156944081979658357 9270143452213507685592971)
      ·
        refine ⟨13905215178320261528389457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9270143452213507685592971 13905215178320261528389457)
        ·
          refine ⟨10428911383740196146292093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13905215178320261528389457 10428911383740196146292093)
          ·
            refine ⟨3910841768902573554859535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10428911383740196146292093 3910841768902573554859535)
            ·
              refine ⟨5866262653353860332289303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3910841768902573554859535 5866262653353860332289303)
              ·
                refine ⟨8799393980030790498433955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5866262653353860332289303 8799393980030790498433955)
                ·
                  refine ⟨13199090970046185747650933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8799393980030790498433955 13199090970046185747650933)
                  ·
                    refine ⟨1237414778441829913842275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13199090970046185747650933 1237414778441829913842275)
                    ·
                      rfl

theorem cell22_3614785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_3614785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614785 prefixEnd_3614785 := by exact prefixLift 3614785
  have htrace : WordTrace (prefixWord ++ tailWord_3614785) baseStart_3614785 baseEnd_3614785 := by
    simpa [prefixWord, tailWord_3614785, baseEnd_3614785] using wordTrace_append hprefix tailTrace_3614785
  have hstable : (prefixWord ++ tailWord_3614785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614785).length < 2 ^ (prefixWord ++ tailWord_3614785).sum := by decide
  have hdescent : baseEnd_3614785 < baseStart_3614785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614798 : List Nat := [4, 1, 1, 1, 1, 4, 4, 6]
def baseStart_3614798 : Nat := 118140960795 + 3614798 * 2 ^ 59
def prefixEnd_3614798 : Nat := 4983230072969 + 3 ^ 40 * 3614798 * 2
def baseEnd_3614798 : Nat := 137491025400833579251915

theorem tailTrace_3614798 : CollatzResearch.WordTrace tailWord_3614798 prefixEnd_3614798 137491025400833579251915 := by
  unfold tailWord_3614798
  simp only [CollatzResearch.WordTrace]
  refine ⟨16480314294776459899137631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87895009572141119462067365 16480314294776459899137631)
  ·
    refine ⟨24720471442164689848706447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16480314294776459899137631 24720471442164689848706447)
    ·
      refine ⟨37080707163247034773059671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24720471442164689848706447 37080707163247034773059671)
      ·
        refine ⟨55621060744870552159589507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37080707163247034773059671 55621060744870552159589507)
        ·
          refine ⟨83431591117305828239384261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55621060744870552159589507 83431591117305828239384261)
          ·
            refine ⟨15643423334494842794884549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83431591117305828239384261 15643423334494842794884549)
            ·
              refine ⟨2933141875217783024040853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15643423334494842794884549 2933141875217783024040853)
              ·
                refine ⟨137491025400833579251915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2933141875217783024040853 137491025400833579251915)
                ·
                  rfl

theorem cell22_3614798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_3614798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614798 prefixEnd_3614798 := by exact prefixLift 3614798
  have htrace : WordTrace (prefixWord ++ tailWord_3614798) baseStart_3614798 baseEnd_3614798 := by
    simpa [prefixWord, tailWord_3614798, baseEnd_3614798] using wordTrace_append hprefix tailTrace_3614798
  have hstable : (prefixWord ++ tailWord_3614798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614798).length < 2 ^ (prefixWord ++ tailWord_3614798).sum := by decide
  have hdescent : baseEnd_3614798 < baseStart_3614798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614873 : List Nat := [1, 2, 1, 2, 1, 2, 1, 7, 1, 4]
def baseStart_3614873 : Nat := 118140960795 + 3614873 * 2 ^ 59
def prefixEnd_3614873 : Nat := 4983230072969 + 3 ^ 40 * 3614873 * 2
def baseEnd_3614873 : Nat := 1237444902640227017642005

theorem tailTrace_3614873 : CollatzResearch.WordTrace tailWord_3614873 prefixEnd_3614873 1237444902640227017642005 := by
  unfold tailWord_3614873
  simp only [CollatzResearch.WordTrace]
  refine ⟨131845249832939967002081273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87896833221959978001387515 131845249832939967002081273)
  ·
    refine ⟨98883937374704975251560955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131845249832939967002081273 98883937374704975251560955)
    ·
      refine ⟨148325906062057462877341433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98883937374704975251560955 148325906062057462877341433)
      ·
        refine ⟨111244429546543097158006075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148325906062057462877341433 111244429546543097158006075)
        ·
          refine ⟨166866644319814645737009113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111244429546543097158006075 166866644319814645737009113)
          ·
            refine ⟨125149983239860984302756835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166866644319814645737009113 125149983239860984302756835)
            ·
              refine ⟨187724974859791476454135253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125149983239860984302756835 187724974859791476454135253)
              ·
                refine ⟨4399804098276362729393795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 187724974859791476454135253 4399804098276362729393795)
                ·
                  refine ⟨6599706147414544094090693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4399804098276362729393795 6599706147414544094090693)
                  ·
                    refine ⟨1237444902640227017642005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6599706147414544094090693 1237444902640227017642005)
                    ·
                      rfl

theorem cell22_3614873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 4].length) (baseStart_3614873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614873 prefixEnd_3614873 := by exact prefixLift 3614873
  have htrace : WordTrace (prefixWord ++ tailWord_3614873) baseStart_3614873 baseEnd_3614873 := by
    simpa [prefixWord, tailWord_3614873, baseEnd_3614873] using wordTrace_append hprefix tailTrace_3614873
  have hstable : (prefixWord ++ tailWord_3614873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614873).length < 2 ^ (prefixWord ++ tailWord_3614873).sum := by decide
  have hdescent : baseEnd_3614873 < baseStart_3614873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614903 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 1, 5]
def baseStart_3614903 : Nat := 118140960795 + 3614903 * 2 ^ 59
def prefixEnd_3614903 : Nat := 4983230072969 + 3 ^ 40 * 3614903 * 2
def baseEnd_3614903 : Nat := 1237455172253316939391913

theorem tailTrace_3614903 : CollatzResearch.WordTrace tailWord_3614903 prefixEnd_3614903 1237455172253316939391913 := by
  unfold tailWord_3614903
  simp only [CollatzResearch.WordTrace]
  refine ⟨131846344022831282125673363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87897562681887521417115575 131846344022831282125673363)
  ·
    refine ⟨197769516034246923188510045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131846344022831282125673363 197769516034246923188510045)
    ·
      refine ⟨74163568512842596195691267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197769516034246923188510045 74163568512842596195691267)
      ·
        refine ⟨111245352769263894293536901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74163568512842596195691267 111245352769263894293536901)
        ·
          refine ⟨20858503644236980180038169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111245352769263894293536901 20858503644236980180038169)
          ·
            refine ⟨15643877733177735135028627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20858503644236980180038169 15643877733177735135028627)
            ·
              refine ⟨23465816599766602702542941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15643877733177735135028627 23465816599766602702542941)
              ·
                refine ⟨8799681224912476013453603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23465816599766602702542941 8799681224912476013453603)
                ·
                  refine ⟨13199521837368714020180405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8799681224912476013453603 13199521837368714020180405)
                  ·
                    refine ⟨1237455172253316939391913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13199521837368714020180405 1237455172253316939391913)
                    ·
                      rfl

theorem cell22_3614903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_3614903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3614903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3614903 prefixEnd_3614903 := by exact prefixLift 3614903
  have htrace : WordTrace (prefixWord ++ tailWord_3614903) baseStart_3614903 baseEnd_3614903 := by
    simpa [prefixWord, tailWord_3614903, baseEnd_3614903] using wordTrace_append hprefix tailTrace_3614903
  have hstable : (prefixWord ++ tailWord_3614903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614903).length < 2 ^ (prefixWord ++ tailWord_3614903).sum := by decide
  have hdescent : baseEnd_3614903 < baseStart_3614903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615012 : List Nat := [2, 3, 1, 3, 1, 2, 4, 1, 5]
def baseStart_3615012 : Nat := 118140960795 + 3615012 * 2 ^ 59
def prefixEnd_3615012 : Nat := 4983230072969 + 3 ^ 40 * 3615012 * 2
def baseEnd_3615012 : Nat := 412497495060292329472193

theorem tailTrace_3615012 : CollatzResearch.WordTrace tailWord_3615012 prefixEnd_3615012 412497495060292329472193 := by
  unfold tailWord_3615012
  simp only [CollatzResearch.WordTrace]
  refine ⟨65925159789718196870695645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87900213052957595827594193 65925159789718196870695645)
  ·
    refine ⟨24721934921144323826510867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65925159789718196870695645 24721934921144323826510867)
    ·
      refine ⟨37082902381716485739766301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24721934921144323826510867 37082902381716485739766301)
      ·
        refine ⟨13906088393143682152412363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37082902381716485739766301 13906088393143682152412363)
        ·
          refine ⟨20859132589715523228618545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13906088393143682152412363 20859132589715523228618545)
          ·
            refine ⟨15644349442286642421463909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20859132589715523228618545 15644349442286642421463909)
            ·
              refine ⟨2933315520428745454024483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15644349442286642421463909 2933315520428745454024483)
              ·
                refine ⟨4399973280643118181036725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2933315520428745454024483 4399973280643118181036725)
                ·
                  refine ⟨412497495060292329472193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4399973280643118181036725 412497495060292329472193)
                  ·
                    rfl

theorem cell22_3615012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_3615012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615012 prefixEnd_3615012 := by exact prefixLift 3615012
  have htrace : WordTrace (prefixWord ++ tailWord_3615012) baseStart_3615012 baseEnd_3615012 := by
    simpa [prefixWord, tailWord_3615012, baseEnd_3615012] using wordTrace_append hprefix tailTrace_3615012
  have hstable : (prefixWord ++ tailWord_3615012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615012).length < 2 ^ (prefixWord ++ tailWord_3615012).sum := by decide
  have hdescent : baseEnd_3615012 < baseStart_3615012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615023 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 6]
def baseStart_3615023 : Nat := 118140960795 + 3615023 * 2 ^ 59
def prefixEnd_3615023 : Nat := 4983230072969 + 3 ^ 40 * 3615023 * 2
def baseEnd_3615023 : Nat := 412498750235225542130515

theorem tailTrace_3615023 : CollatzResearch.WordTrace tailWord_3615023 prefixEnd_3615023 412498750235225542130515 := by
  unfold tailWord_3615023
  simp only [CollatzResearch.WordTrace]
  refine ⟨131850720782396542620041723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87900480521597695080027815 131850720782396542620041723)
  ·
    refine ⟨197776081173594813930062585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131850720782396542620041723 197776081173594813930062585)
    ·
      refine ⟨148332060880196110447546939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197776081173594813930062585 148332060880196110447546939)
      ·
        refine ⟨222498091320294165671320409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148332060880196110447546939 222498091320294165671320409)
        ·
          refine ⟨166873568490220624253490307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222498091320294165671320409 166873568490220624253490307)
          ·
            refine ⟨250310352735330936380235461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166873568490220624253490307 250310352735330936380235461)
            ·
              refine ⟨46933191137874550571294149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250310352735330936380235461 46933191137874550571294149)
              ·
                refine ⟨8799973338351478232117653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46933191137874550571294149 8799973338351478232117653)
                ·
                  refine ⟨412498750235225542130515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8799973338351478232117653 412498750235225542130515)
                  ·
                    rfl

theorem cell22_3615023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 6].length) (baseStart_3615023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615023 prefixEnd_3615023 := by exact prefixLift 3615023
  have htrace : WordTrace (prefixWord ++ tailWord_3615023) baseStart_3615023 baseEnd_3615023 := by
    simpa [prefixWord, tailWord_3615023, baseEnd_3615023] using wordTrace_append hprefix tailTrace_3615023
  have hstable : (prefixWord ++ tailWord_3615023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615023).length < 2 ^ (prefixWord ++ tailWord_3615023).sum := by decide
  have hdescent : baseEnd_3615023 < baseStart_3615023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615057 : List Nat := [1, 2, 2, 1, 4, 3, 1, 4, 4]
def baseStart_3615057 : Nat := 118140960795 + 3615057 * 2 ^ 59
def prefixEnd_3615057 : Nat := 4983230072969 + 3 ^ 40 * 3615057 * 2
def baseEnd_3615057 : Nat := 412502629866837290347147

theorem tailTrace_3615057 : CollatzResearch.WordTrace tailWord_3615057 prefixEnd_3615057 412502629866837290347147 := by
  unfold tailWord_3615057
  simp only [CollatzResearch.WordTrace]
  refine ⟨131851960864273366426779425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87901307242848910951186283 131851960864273366426779425)
  ·
    refine ⟨98888970648205024820084569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131851960864273366426779425 98888970648205024820084569)
    ·
      refine ⟨74166727986153768615063427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98888970648205024820084569 74166727986153768615063427)
      ·
        refine ⟨111250091979230652922595141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74166727986153768615063427 111250091979230652922595141)
        ·
          refine ⟨20859392246105747422986589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111250091979230652922595141 20859392246105747422986589)
          ·
            refine ⟨7822272092289655283619971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20859392246105747422986589 7822272092289655283619971)
            ·
              refine ⟨11733408138434482925429957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7822272092289655283619971 11733408138434482925429957)
              ·
                refine ⟨2200014025956465548518117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11733408138434482925429957 2200014025956465548518117)
                ·
                  refine ⟨412502629866837290347147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2200014025956465548518117 412502629866837290347147)
                  ·
                    rfl

theorem cell22_3615057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 4].length) (baseStart_3615057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615057 prefixEnd_3615057 := by exact prefixLift 3615057
  have htrace : WordTrace (prefixWord ++ tailWord_3615057) baseStart_3615057 baseEnd_3615057 := by
    simpa [prefixWord, tailWord_3615057, baseEnd_3615057] using wordTrace_append hprefix tailTrace_3615057
  have hstable : (prefixWord ++ tailWord_3615057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615057).length < 2 ^ (prefixWord ++ tailWord_3615057).sum := by decide
  have hdescent : baseEnd_3615057 < baseStart_3615057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615072 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 1, 5]
def baseStart_3615072 : Nat := 118140960795 + 3615072 * 2 ^ 59
def prefixEnd_3615072 : Nat := 4983230072969 + 3 ^ 40 * 3615072 * 2
def baseEnd_3615072 : Nat := 1237513024407056831916395

theorem tailTrace_3615072 : CollatzResearch.WordTrace tailWord_3615072 prefixEnd_3615072 1237513024407056831916395 := by
  unfold tailWord_3615072
  simp only [CollatzResearch.WordTrace]
  refine ⟨65926253979609511994287735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87901671972812682659050313 65926253979609511994287735)
  ·
    refine ⟨98889380969414267991431603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65926253979609511994287735 98889380969414267991431603)
    ·
      refine ⟨148334071454121401987147405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98889380969414267991431603 148334071454121401987147405)
      ·
        refine ⟨55625276795295525745180277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148334071454121401987147405 55625276795295525745180277)
        ·
          refine ⟨5214869699558955538610651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55625276795295525745180277 5214869699558955538610651)
          ·
            refine ⟨7822304549338433307915977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5214869699558955538610651 7822304549338433307915977)
            ·
              refine ⟨5866728412003824980936983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7822304549338433307915977 5866728412003824980936983)
              ·
                refine ⟨8800092618005737471405475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5866728412003824980936983 8800092618005737471405475)
                ·
                  refine ⟨13200138927008606207108213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8800092618005737471405475 13200138927008606207108213)
                  ·
                    refine ⟨1237513024407056831916395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13200138927008606207108213 1237513024407056831916395)
                    ·
                      rfl

theorem cell22_3615072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 1, 5].length) (baseStart_3615072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615072 prefixEnd_3615072 := by exact prefixLift 3615072
  have htrace : WordTrace (prefixWord ++ tailWord_3615072) baseStart_3615072 baseEnd_3615072 := by
    simpa [prefixWord, tailWord_3615072, baseEnd_3615072] using wordTrace_append hprefix tailTrace_3615072
  have hstable : (prefixWord ++ tailWord_3615072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615072).length < 2 ^ (prefixWord ++ tailWord_3615072).sum := by decide
  have hdescent : baseEnd_3615072 < baseStart_3615072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615083 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 2, 7]
def baseStart_3615083 : Nat := 118140960795 + 3615083 * 2 ^ 59
def prefixEnd_3615083 : Nat := 4983230072969 + 3 ^ 40 * 3615083 * 2
def baseEnd_3615083 : Nat := 1237516789931856469891361

theorem tailTrace_3615083 : CollatzResearch.WordTrace tailWord_3615083 prefixEnd_3615083 1237516789931856469891361 := by
  unfold tailWord_3615083
  simp only [CollatzResearch.WordTrace]
  refine ⟨131852909162179172867225903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87901939441452781911483935 131852909162179172867225903)
  ·
    refine ⟨197779363743268759300838855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131852909162179172867225903 197779363743268759300838855)
    ·
      refine ⟨296669045614903138951258283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197779363743268759300838855 296669045614903138951258283)
      ·
        refine ⟨445003568422354708426887425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296669045614903138951258283 445003568422354708426887425)
        ·
          refine ⟨333752676316766031320165569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445003568422354708426887425 333752676316766031320165569)
          ·
            refine ⟨250314507237574523490124177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333752676316766031320165569 250314507237574523490124177)
            ·
              refine ⟨187735880428180892617593133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250314507237574523490124177 187735880428180892617593133)
              ·
                refine ⟨70400955160567834731597425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187735880428180892617593133 70400955160567834731597425)
                ·
                  refine ⟨52800716370425876048698069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70400955160567834731597425 52800716370425876048698069)
                  ·
                    refine ⟨1237516789931856469891361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52800716370425876048698069 1237516789931856469891361)
                    ·
                      rfl

theorem cell22_3615083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 7].length) (baseStart_3615083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615083 prefixEnd_3615083 := by exact prefixLift 3615083
  have htrace : WordTrace (prefixWord ++ tailWord_3615083) baseStart_3615083 baseEnd_3615083 := by
    simpa [prefixWord, tailWord_3615083, baseEnd_3615083] using wordTrace_append hprefix tailTrace_3615083
  have hstable : (prefixWord ++ tailWord_3615083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615083).length < 2 ^ (prefixWord ++ tailWord_3615083).sum := by decide
  have hdescent : baseEnd_3615083 < baseStart_3615083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615106 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_3615106 : Nat := 118140960795 + 3615106 * 2 ^ 59
def prefixEnd_3615106 : Nat := 4983230072969 + 3 ^ 40 * 3615106 * 2
def baseEnd_3615106 : Nat := 1237524663301892076566291

theorem tailTrace_3615106 : CollatzResearch.WordTrace tailWord_3615106 prefixEnd_3615106 1237524663301892076566291 := by
  unfold tailWord_3615106
  simp only [CollatzResearch.WordTrace]
  refine ⟨32963437010273961948828293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87902498694063898530208781 32963437010273961948828293)
  ·
    refine ⟨6180644439426367865405305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32963437010273961948828293 6180644439426367865405305)
    ·
      refine ⟨4635483329569775899053979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6180644439426367865405305 4635483329569775899053979)
      ·
        refine ⟨6953224994354663848580969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4635483329569775899053979 6953224994354663848580969)
        ·
          refine ⟨5214918745765997886435727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6953224994354663848580969 5214918745765997886435727)
          ·
            refine ⟨7822378118648996829653591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5214918745765997886435727 7822378118648996829653591)
            ·
              refine ⟨11733567177973495244480387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7822378118648996829653591 11733567177973495244480387)
              ·
                refine ⟨17600350766960242866720581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11733567177973495244480387 17600350766960242866720581)
                ·
                  refine ⟨3300065768805045537510109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17600350766960242866720581 3300065768805045537510109)
                  ·
                    refine ⟨1237524663301892076566291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3300065768805045537510109 1237524663301892076566291)
                    ·
                      rfl

theorem cell22_3615106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_3615106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615106 prefixEnd_3615106 := by exact prefixLift 3615106
  have htrace : WordTrace (prefixWord ++ tailWord_3615106) baseStart_3615106 baseEnd_3615106 := by
    simpa [prefixWord, tailWord_3615106, baseEnd_3615106] using wordTrace_append hprefix tailTrace_3615106
  have hstable : (prefixWord ++ tailWord_3615106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615106).length < 2 ^ (prefixWord ++ tailWord_3615106).sum := by decide
  have hdescent : baseEnd_3615106 < baseStart_3615106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615160 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 5, 4]
def baseStart_3615160 : Nat := 118140960795 + 3615160 * 2 ^ 59
def prefixEnd_3615160 : Nat := 4983230072969 + 3 ^ 40 * 3615160 * 2
def baseEnd_3615160 : Nat := 1237543148605453935716125

theorem tailTrace_3615160 : CollatzResearch.WordTrace tailWord_3615160 prefixEnd_3615160 1237543148605453935716125 := by
  unfold tailWord_3615160
  simp only [CollatzResearch.WordTrace]
  refine ⟨65927858791450107508889467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87903811721933476678519289 65927858791450107508889467)
  ·
    refine ⟨98891788187175161263334201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65927858791450107508889467 98891788187175161263334201)
    ·
      refine ⟨74168841140381370947500651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98891788187175161263334201 74168841140381370947500651)
      ·
        refine ⟨111253261710572056421250977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74168841140381370947500651 111253261710572056421250977)
        ·
          refine ⟨83439946282929042315938233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111253261710572056421250977 83439946282929042315938233)
          ·
            refine ⟨62579959712196781736953675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83439946282929042315938233 62579959712196781736953675)
            ·
              refine ⟨93869939568295172605430513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62579959712196781736953675 93869939568295172605430513)
              ·
                refine ⟨70402454676221379454072885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93869939568295172605430513 70402454676221379454072885)
                ·
                  refine ⟨6600230125895754323819333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70402454676221379454072885 6600230125895754323819333)
                  ·
                    refine ⟨1237543148605453935716125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6600230125895754323819333 1237543148605453935716125)
                    ·
                      rfl

theorem cell22_3615160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_3615160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615160 prefixEnd_3615160 := by exact prefixLift 3615160
  have htrace : WordTrace (prefixWord ++ tailWord_3615160) baseStart_3615160 baseEnd_3615160 := by
    simpa [prefixWord, tailWord_3615160, baseEnd_3615160] using wordTrace_append hprefix tailTrace_3615160
  have hstable : (prefixWord ++ tailWord_3615160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615160).length < 2 ^ (prefixWord ++ tailWord_3615160).sum := by decide
  have hdescent : baseEnd_3615160 < baseStart_3615160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615207 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 1, 5]
def baseStart_3615207 : Nat := 118140960795 + 3615207 * 2 ^ 59
def prefixEnd_3615207 : Nat := 4983230072969 + 3 ^ 40 * 3615207 * 2
def baseEnd_3615207 : Nat := 1237559237665961479790981

theorem tailTrace_3615207 : CollatzResearch.WordTrace tailWord_3615207 prefixEnd_3615207 1237559237665961479790981 := by
  unfold tailWord_3615207
  simp only [CollatzResearch.WordTrace]
  refine ⟨131857431813729942044739875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87904954542486628029826583 131857431813729942044739875)
  ·
    refine ⟨197786147720594913067109813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131857431813729942044739875 197786147720594913067109813)
    ·
      refine ⟨18542451348805773100041545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197786147720594913067109813 18542451348805773100041545)
      ·
        refine ⟨13906838511604329825031159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18542451348805773100041545 13906838511604329825031159)
        ·
          refine ⟨20860257767406494737546739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13906838511604329825031159 20860257767406494737546739)
          ·
            refine ⟨31290386651109742106320109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20860257767406494737546739 31290386651109742106320109)
            ·
              refine ⟨11733894994166153289870041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31290386651109742106320109 11733894994166153289870041)
              ·
                refine ⟨8800421245624614967402531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11733894994166153289870041 8800421245624614967402531)
                ·
                  refine ⟨13200631868436922451103797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8800421245624614967402531 13200631868436922451103797)
                  ·
                    refine ⟨1237559237665961479790981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13200631868436922451103797 1237559237665961479790981)
                    ·
                      rfl

theorem cell22_3615207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_3615207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615207 prefixEnd_3615207 := by exact prefixLift 3615207
  have htrace : WordTrace (prefixWord ++ tailWord_3615207) baseStart_3615207 baseEnd_3615207 := by
    simpa [prefixWord, tailWord_3615207, baseEnd_3615207] using wordTrace_append hprefix tailTrace_3615207
  have hstable : (prefixWord ++ tailWord_3615207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615207).length < 2 ^ (prefixWord ++ tailWord_3615207).sum := by decide
  have hdescent : baseEnd_3615207 < baseStart_3615207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615224 : List Nat := [2, 1, 2, 1, 1, 4, 4, 2, 2, 3]
def baseStart_3615224 : Nat := 118140960795 + 3615224 * 2 ^ 59
def prefixEnd_3615224 : Nat := 4983230072969 + 3 ^ 40 * 3615224 * 2
def baseEnd_3615224 : Nat := 1237565057113379102115929

theorem tailTrace_3615224 : CollatzResearch.WordTrace tailWord_3615224 prefixEnd_3615224 1237565057113379102115929 := by
  unfold tailWord_3615224
  simp only [CollatzResearch.WordTrace]
  refine ⟨65929025927334176974054363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87905367903112235965405817 65929025927334176974054363)
  ·
    refine ⟨98893538891001265461081545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65929025927334176974054363 98893538891001265461081545)
    ·
      refine ⟨74170154168250949095811159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98893538891001265461081545 74170154168250949095811159)
      ·
        refine ⟨111255231252376423643716739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74170154168250949095811159 111255231252376423643716739)
        ·
          refine ⟨166882846878564635465575109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111255231252376423643716739 166882846878564635465575109)
          ·
            refine ⟨31290533789730869149795333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166882846878564635465575109 31290533789730869149795333)
            ·
              refine ⟨5866975085574537965586625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31290533789730869149795333 5866975085574537965586625)
              ·
                refine ⟨4400231314180903474189969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5866975085574537965586625 4400231314180903474189969)
                ·
                  refine ⟨3300173485635677605642477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4400231314180903474189969 3300173485635677605642477)
                  ·
                    refine ⟨1237565057113379102115929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3300173485635677605642477 1237565057113379102115929)
                    ·
                      rfl

theorem cell22_3615224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_3615224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615224 prefixEnd_3615224 := by exact prefixLift 3615224
  have htrace : WordTrace (prefixWord ++ tailWord_3615224) baseStart_3615224 baseEnd_3615224 := by
    simpa [prefixWord, tailWord_3615224, baseEnd_3615224] using wordTrace_append hprefix tailTrace_3615224
  have hstable : (prefixWord ++ tailWord_3615224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615224).length < 2 ^ (prefixWord ++ tailWord_3615224).sum := by decide
  have hdescent : baseEnd_3615224 < baseStart_3615224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615286 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_3615286 : Nat := 118140960795 + 3615286 * 2 ^ 59
def prefixEnd_3615286 : Nat := 4983230072969 + 3 ^ 40 * 3615286 * 2
def baseEnd_3615286 : Nat := 1237586280980431607065739

theorem tailTrace_3615286 : CollatzResearch.WordTrace tailWord_3615286 prefixEnd_3615286 1237586280980431607065739 := by
  unfold tailWord_3615286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8241269573777733658554107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87906875453629159024577141 8241269573777733658554107)
  ·
    refine ⟨12361904360666600487831161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8241269573777733658554107 12361904360666600487831161)
    ·
      refine ⟨9271428270499950365873371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12361904360666600487831161 9271428270499950365873371)
      ·
        refine ⟨13907142405749925548810057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9271428270499950365873371 13907142405749925548810057)
        ·
          refine ⟨10430356804312444161607543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13907142405749925548810057 10430356804312444161607543)
          ·
            refine ⟨15645535206468666242411315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10430356804312444161607543 15645535206468666242411315)
            ·
              refine ⟨23468302809702999363616973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15645535206468666242411315 23468302809702999363616973)
              ·
                refine ⟨8800613553638624761356365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23468302809702999363616973 8800613553638624761356365)
                ·
                  refine ⟨3300230082614484285508637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8800613553638624761356365 3300230082614484285508637)
                  ·
                    refine ⟨1237586280980431607065739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3300230082614484285508637 1237586280980431607065739)
                    ·
                      rfl

theorem cell22_3615286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_3615286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615286 prefixEnd_3615286 := by exact prefixLift 3615286
  have htrace : WordTrace (prefixWord ++ tailWord_3615286) baseStart_3615286 baseEnd_3615286 := by
    simpa [prefixWord, tailWord_3615286, baseEnd_3615286] using wordTrace_append hprefix tailTrace_3615286
  have hstable : (prefixWord ++ tailWord_3615286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615286).length < 2 ^ (prefixWord ++ tailWord_3615286).sum := by decide
  have hdescent : baseEnd_3615286 < baseStart_3615286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615329 : List Nat := [1, 2, 3, 1, 1, 4, 2, 3, 1, 4]
def baseStart_3615329 : Nat := 118140960795 + 3615329 * 2 ^ 59
def prefixEnd_3615329 : Nat := 4983230072969 + 3 ^ 40 * 3615329 * 2
def baseEnd_3615329 : Nat := 1237601000759193828240607

theorem tailTrace_3615329 : CollatzResearch.WordTrace tailWord_3615329 prefixEnd_3615329 1237601000759193828240607 := by
  unfold tailWord_3615329
  simp only [CollatzResearch.WordTrace]
  refine ⟨131861881519287956880681041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87907921012858637920454027 131861881519287956880681041)
  ·
    refine ⟨98896411139465967660510781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131861881519287956880681041 98896411139465967660510781)
    ·
      refine ⟨37086154177299737872691543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98896411139465967660510781 37086154177299737872691543)
      ·
        refine ⟨55629231265949606809037315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37086154177299737872691543 55629231265949606809037315)
        ·
          refine ⟨83443846898924410213555973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55629231265949606809037315 83443846898924410213555973)
          ·
            refine ⟨15645721293548326915041745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83443846898924410213555973 15645721293548326915041745)
            ·
              refine ⟨11734290970161245186281309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15645721293548326915041745 11734290970161245186281309)
              ·
                refine ⟨4400359113810466944855491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11734290970161245186281309 4400359113810466944855491)
                ·
                  refine ⟨6600538670715700417283237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4400359113810466944855491 6600538670715700417283237)
                  ·
                    refine ⟨1237601000759193828240607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6600538670715700417283237 1237601000759193828240607)
                    ·
                      rfl

theorem cell22_3615329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_3615329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615329 prefixEnd_3615329 := by exact prefixLift 3615329
  have htrace : WordTrace (prefixWord ++ tailWord_3615329) baseStart_3615329 baseEnd_3615329 := by
    simpa [prefixWord, tailWord_3615329, baseEnd_3615329] using wordTrace_append hprefix tailTrace_3615329
  have hstable : (prefixWord ++ tailWord_3615329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615329).length < 2 ^ (prefixWord ++ tailWord_3615329).sum := by decide
  have hdescent : baseEnd_3615329 < baseStart_3615329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615350 : List Nat := [5, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_3615350 : Nat := 118140960795 + 3615350 * 2 ^ 59
def prefixEnd_3615350 : Nat := 4983230072969 + 3 ^ 40 * 3615350 * 2
def baseEnd_3615350 : Nat := 412536063162785591155181

theorem tailTrace_3615350 : CollatzResearch.WordTrace tailWord_3615350 prefixEnd_3615350 412536063162785591155181 := by
  unfold tailWord_3615350
  simp only [CollatzResearch.WordTrace]
  refine ⟨8241415465763242341699719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87908431634807918311463669 8241415465763242341699719)
  ·
    refine ⟨12362123198644863512549579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8241415465763242341699719 12362123198644863512549579)
    ·
      refine ⟨18543184797967295268824369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12362123198644863512549579 18543184797967295268824369)
      ·
        refine ⟨13907388598475471451618277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18543184797967295268824369 13907388598475471451618277)
        ·
          refine ⟨2607635362214150897178427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13907388598475471451618277 2607635362214150897178427)
          ·
            refine ⟨3911453043321226345767641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2607635362214150897178427 3911453043321226345767641)
            ·
              refine ⟨2933589782490919759325731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3911453043321226345767641 2933589782490919759325731)
              ·
                refine ⟨4400384673736379638988597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2933589782490919759325731 4400384673736379638988597)
                ·
                  refine ⟨412536063162785591155181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4400384673736379638988597 412536063162785591155181)
                  ·
                    rfl

theorem cell22_3615350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_3615350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615350 prefixEnd_3615350 := by exact prefixLift 3615350
  have htrace : WordTrace (prefixWord ++ tailWord_3615350) baseStart_3615350 baseEnd_3615350 := by
    simpa [prefixWord, tailWord_3615350, baseEnd_3615350] using wordTrace_append hprefix tailTrace_3615350
  have hstable : (prefixWord ++ tailWord_3615350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615350).length < 2 ^ (prefixWord ++ tailWord_3615350).sum := by decide
  have hdescent : baseEnd_3615350 < baseStart_3615350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615393 : List Nat := [1, 2, 3, 3, 3, 1, 2, 2, 2, 3]
def baseStart_3615393 : Nat := 118140960795 + 3615393 * 2 ^ 59
def prefixEnd_3615393 : Nat := 4983230072969 + 3 ^ 40 * 3615393 * 2
def baseEnd_3615393 : Nat := 1237622909267118994640411

theorem tailTrace_3615393 : CollatzResearch.WordTrace tailWord_3615393 prefixEnd_3615393 1237622909267118994640411 := by
  unfold tailWord_3615393
  simp only [CollatzResearch.WordTrace]
  refine ⟨131864215791056095811010833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87909477194037397207340555 131864215791056095811010833)
  ·
    refine ⟨98898161843292071858258125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131864215791056095811010833 98898161843292071858258125)
    ·
      refine ⟨37086810691234526946846797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98898161843292071858258125 37086810691234526946846797)
      ·
        refine ⟨13907554009212947605067549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37086810691234526946846797 13907554009212947605067549)
        ·
          refine ⟨5215332753454855351900331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13907554009212947605067549 5215332753454855351900331)
          ·
            refine ⟨7822999130182283027850497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5215332753454855351900331 7822999130182283027850497)
            ·
              refine ⟨5867249347636712270887873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7822999130182283027850497 5867249347636712270887873)
              ·
                refine ⟨4400437010727534203165905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5867249347636712270887873 4400437010727534203165905)
                ·
                  refine ⟨3300327758045650652374429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4400437010727534203165905 3300327758045650652374429)
                  ·
                    refine ⟨1237622909267118994640411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3300327758045650652374429 1237622909267118994640411)
                    ·
                      rfl

theorem cell22_3615393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_3615393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615393 prefixEnd_3615393 := by exact prefixLift 3615393
  have htrace : WordTrace (prefixWord ++ tailWord_3615393) baseStart_3615393 baseEnd_3615393 := by
    simpa [prefixWord, tailWord_3615393, baseEnd_3615393] using wordTrace_append hprefix tailTrace_3615393
  have hstable : (prefixWord ++ tailWord_3615393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615393).length < 2 ^ (prefixWord ++ tailWord_3615393).sum := by decide
  have hdescent : baseEnd_3615393 < baseStart_3615393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615406 : List Nat := [4, 1, 4, 1, 1, 1, 3, 7]
def baseStart_3615406 : Nat := 118140960795 + 3615406 * 2 ^ 59
def prefixEnd_3615406 : Nat := 4983230072969 + 3 ^ 40 * 3615406 * 2
def baseEnd_3615406 : Nat := 137514151048087921562819

theorem tailTrace_3615406 : CollatzResearch.WordTrace tailWord_3615406 prefixEnd_3615406 137514151048087921562819 := by
  unfold tailWord_3615406
  simp only [CollatzResearch.WordTrace]
  refine ⟨16483086242501124878904259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87909793293339332687489381 16483086242501124878904259)
  ·
    refine ⟨24724629363751687318356389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16483086242501124878904259 24724629363751687318356389)
    ·
      refine ⟨4635868005703441372191823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24724629363751687318356389 4635868005703441372191823)
      ·
        refine ⟨6953802008555162058287735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4635868005703441372191823 6953802008555162058287735)
        ·
          refine ⟨10430703012832743087431603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6953802008555162058287735 10430703012832743087431603)
          ·
            refine ⟨15646054519249114631147405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10430703012832743087431603 15646054519249114631147405)
            ·
              refine ⟨5867270444718417986680277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15646054519249114631147405 5867270444718417986680277)
              ·
                refine ⟨137514151048087921562819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5867270444718417986680277 137514151048087921562819)
                ·
                  rfl

theorem cell22_3615406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_3615406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615406 prefixEnd_3615406 := by exact prefixLift 3615406
  have htrace : WordTrace (prefixWord ++ tailWord_3615406) baseStart_3615406 baseEnd_3615406 := by
    simpa [prefixWord, tailWord_3615406, baseEnd_3615406] using wordTrace_append hprefix tailTrace_3615406
  have hstable : (prefixWord ++ tailWord_3615406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615406).length < 2 ^ (prefixWord ++ tailWord_3615406).sum := by decide
  have hdescent : baseEnd_3615406 < baseStart_3615406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615417 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 9]
def baseStart_3615417 : Nat := 118140960795 + 3615417 * 2 ^ 59
def prefixEnd_3615417 : Nat := 4983230072969 + 3 ^ 40 * 3615417 * 2
def baseEnd_3615417 : Nat := 412543708319196977346779

theorem tailTrace_3615417 : CollatzResearch.WordTrace tailWord_3615417 prefixEnd_3615417 412543708319196977346779 := by
  unfold tailWord_3615417
  simp only [CollatzResearch.WordTrace]
  refine ⟨131865091142969147909884505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87910060761979431939923003 131865091142969147909884505)
  ·
    refine ⟨98898818357226860932413379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131865091142969147909884505 98898818357226860932413379)
    ·
      refine ⟨148348227535840291398620069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98898818357226860932413379 148348227535840291398620069)
      ·
        refine ⟨27815292662970054637241263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148348227535840291398620069 27815292662970054637241263)
        ·
          refine ⟨41722938994455081955861895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27815292662970054637241263 41722938994455081955861895)
          ·
            refine ⟨62584408491682622933792843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41722938994455081955861895 62584408491682622933792843)
            ·
              refine ⟨93876612737523934400689265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62584408491682622933792843 93876612737523934400689265)
              ·
                refine ⟨70407459553142950800516949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93876612737523934400689265 70407459553142950800516949)
                ·
                  refine ⟨412543708319196977346779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70407459553142950800516949 412543708319196977346779)
                  ·
                    rfl

theorem cell22_3615417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 9].length) (baseStart_3615417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615417 prefixEnd_3615417 := by exact prefixLift 3615417
  have htrace : WordTrace (prefixWord ++ tailWord_3615417) baseStart_3615417 baseEnd_3615417 := by
    simpa [prefixWord, tailWord_3615417, baseEnd_3615417] using wordTrace_append hprefix tailTrace_3615417
  have hstable : (prefixWord ++ tailWord_3615417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615417).length < 2 ^ (prefixWord ++ tailWord_3615417).sum := by decide
  have hdescent : baseEnd_3615417 < baseStart_3615417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615421 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 3, 3]
def baseStart_3615421 : Nat := 118140960795 + 3615421 * 2 ^ 59
def prefixEnd_3615421 : Nat := 4983230072969 + 3 ^ 40 * 3615421 * 2
def baseEnd_3615421 : Nat := 1237632494239336254940325

theorem tailTrace_3615421 : CollatzResearch.WordTrace tailWord_3615421 prefixEnd_3615421 1237632494239336254940325 := by
  unfold tailWord_3615421
  simp only [CollatzResearch.WordTrace]
  refine ⟨131865237034954656593030117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87910158023303104395353411 131865237034954656593030117)
  ·
    refine ⟨24724731944053998111193147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131865237034954656593030117 24724731944053998111193147)
    ·
      refine ⟨37087097916080997166789721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24724731944053998111193147 37087097916080997166789721)
      ·
        refine ⟨27815323437060747875092291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37087097916080997166789721 27815323437060747875092291)
        ·
          refine ⟨41722985155591121812638437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27815323437060747875092291 41722985155591121812638437)
          ·
            refine ⟨7823059716673335339869707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41722985155591121812638437 7823059716673335339869707)
            ·
              refine ⟨11734589575010003009804561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7823059716673335339869707 11734589575010003009804561)
              ·
                refine ⟨8800942181257502257353421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11734589575010003009804561 8800942181257502257353421)
                ·
                  refine ⟨3300353317971563346507533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8800942181257502257353421 3300353317971563346507533)
                  ·
                    refine ⟨1237632494239336254940325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3300353317971563346507533 1237632494239336254940325)
                    ·
                      rfl

theorem cell22_3615421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_3615421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615421 prefixEnd_3615421 := by exact prefixLift 3615421
  have htrace : WordTrace (prefixWord ++ tailWord_3615421) baseStart_3615421 baseEnd_3615421 := by
    simpa [prefixWord, tailWord_3615421, baseEnd_3615421] using wordTrace_append hprefix tailTrace_3615421
  have hstable : (prefixWord ++ tailWord_3615421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615421).length < 2 ^ (prefixWord ++ tailWord_3615421).sum := by decide
  have hdescent : baseEnd_3615421 < baseStart_3615421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615425 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 2, 4]
def baseStart_3615425 : Nat := 118140960795 + 3615425 * 2 ^ 59
def prefixEnd_3615425 : Nat := 4983230072969 + 3 ^ 40 * 3615425 * 2
def baseEnd_3615425 : Nat := 1237633863521081577840313

theorem tailTrace_3615425 : CollatzResearch.WordTrace tailWord_3615425 prefixEnd_3615425 1237633863521081577840313 := by
  unfold tailWord_3615425
  simp only [CollatzResearch.WordTrace]
  refine ⟨131865382926940165276175729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87910255284626776850783819 131865382926940165276175729)
  ·
    refine ⟨98899037195205123957131797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131865382926940165276175729 98899037195205123957131797)
    ·
      refine ⟨4635892368525240185490553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98899037195205123957131797 4635892368525240185490553)
      ·
        refine ⟨3476919276393930139117915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4635892368525240185490553 3476919276393930139117915)
        ·
          refine ⟨5215378914590895208676873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3476919276393930139117915 5215378914590895208676873)
          ·
            refine ⟨3911534185943171406507655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5215378914590895208676873 3911534185943171406507655)
            ·
              refine ⟨5867301278914757109761483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3911534185943171406507655 5867301278914757109761483)
              ·
                refine ⟨8800951918372135664642225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5867301278914757109761483 8800951918372135664642225)
                ·
                  refine ⟨6600713938779101748481669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8800951918372135664642225 6600713938779101748481669)
                  ·
                    refine ⟨1237633863521081577840313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6600713938779101748481669 1237633863521081577840313)
                    ·
                      rfl

theorem cell22_3615425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_3615425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615425 prefixEnd_3615425 := by exact prefixLift 3615425
  have htrace : WordTrace (prefixWord ++ tailWord_3615425) baseStart_3615425 baseEnd_3615425 := by
    simpa [prefixWord, tailWord_3615425, baseEnd_3615425] using wordTrace_append hprefix tailTrace_3615425
  have hstable : (prefixWord ++ tailWord_3615425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615425).length < 2 ^ (prefixWord ++ tailWord_3615425).sum := by decide
  have hdescent : baseEnd_3615425 < baseStart_3615425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615438 : List Nat := [4, 1, 1, 1, 3, 2, 1, 5, 1, 3]
def baseStart_3615438 : Nat := 118140960795 + 3615438 * 2 ^ 59
def prefixEnd_3615438 : Nat := 4983230072969 + 3 ^ 40 * 3615438 * 2
def baseEnd_3615438 : Nat := 1237638313686753877265273

theorem tailTrace_3615438 : CollatzResearch.WordTrace tailWord_3615438 prefixEnd_3615438 1237638313686753877265273 := by
  unfold tailWord_3615438
  simp only [CollatzResearch.WordTrace]
  refine ⟨16483232134486633562049871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87910571383928712330932645 16483232134486633562049871)
  ·
    refine ⟨24724848201729950343074807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16483232134486633562049871 24724848201729950343074807)
    ·
      refine ⟨37087272302594925514612211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24724848201729950343074807 37087272302594925514612211)
      ·
        refine ⟨55630908453892388271918317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37087272302594925514612211 55630908453892388271918317)
        ·
          refine ⟨20861590670209645601969369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55630908453892388271918317 20861590670209645601969369)
          ·
            refine ⟨15646193002657234201477027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20861590670209645601969369 15646193002657234201477027)
            ·
              refine ⟨23469289503985851302215541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15646193002657234201477027 23469289503985851302215541)
              ·
                refine ⟨2200245890998673559582707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23469289503985851302215541 2200245890998673559582707)
                ·
                  refine ⟨3300368836498010339374061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2200245890998673559582707 3300368836498010339374061)
                  ·
                    refine ⟨1237638313686753877265273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3300368836498010339374061 1237638313686753877265273)
                    ·
                      rfl

theorem cell22_3615438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_3615438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615438 prefixEnd_3615438 := by exact prefixLift 3615438
  have htrace : WordTrace (prefixWord ++ tailWord_3615438) baseStart_3615438 baseEnd_3615438 := by
    simpa [prefixWord, tailWord_3615438, baseEnd_3615438] using wordTrace_append hprefix tailTrace_3615438
  have hstable : (prefixWord ++ tailWord_3615438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615438).length < 2 ^ (prefixWord ++ tailWord_3615438).sum := by decide
  have hdescent : baseEnd_3615438 < baseStart_3615438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615528 : List Nat := [2, 1, 5, 1, 1, 1, 3, 3, 2, 3]
def baseStart_3615528 : Nat := 118140960795 + 3615528 * 2 ^ 59
def prefixEnd_3615528 : Nat := 4983230072969 + 3 ^ 40 * 3615528 * 2
def baseEnd_3615528 : Nat := 1237669122526023642514997

theorem tailTrace_3615528 : CollatzResearch.WordTrace tailWord_3615528 prefixEnd_3615528 1237669122526023642514997 := by
  unfold tailWord_3615528
  simp only [CollatzResearch.WordTrace]
  refine ⟨65934569822783506933587619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87912759763711342578116825 65934569822783506933587619)
  ·
    refine ⟨98901854734175260400381429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65934569822783506933587619 98901854734175260400381429)
    ·
      refine ⟨9272048881328930662535759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98901854734175260400381429 9272048881328930662535759)
      ·
        refine ⟨13908073321993395993803639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9272048881328930662535759 13908073321993395993803639)
        ·
          refine ⟨20862109982990093990705459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13908073321993395993803639 20862109982990093990705459)
          ·
            refine ⟨31293164974485140986058189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20862109982990093990705459 31293164974485140986058189)
            ·
              refine ⟨11734936865431927869771821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31293164974485140986058189 11734936865431927869771821)
              ·
                refine ⟨4400601324536972951164433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11734936865431927869771821 4400601324536972951164433)
                ·
                  refine ⟨3300450993402729713373325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4400601324536972951164433 3300450993402729713373325)
                  ·
                    refine ⟨1237669122526023642514997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3300450993402729713373325 1237669122526023642514997)
                    ·
                      rfl

theorem cell22_3615528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_3615528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615528 prefixEnd_3615528 := by exact prefixLift 3615528
  have htrace : WordTrace (prefixWord ++ tailWord_3615528) baseStart_3615528 baseEnd_3615528 := by
    simpa [prefixWord, tailWord_3615528, baseEnd_3615528] using wordTrace_append hprefix tailTrace_3615528
  have hstable : (prefixWord ++ tailWord_3615528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615528).length < 2 ^ (prefixWord ++ tailWord_3615528).sum := by decide
  have hdescent : baseEnd_3615528 < baseStart_3615528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615558 : List Nat := [6, 1, 1, 2, 2, 10]
def baseStart_3615558 : Nat := 118140960795 + 3615558 * 2 ^ 59
def prefixEnd_3615558 : Nat := 4983230072969 + 3 ^ 40 * 3615558 * 2
def baseEnd_3615558 : Nat := 15279992495544611904505

theorem tailTrace_3615558 : CollatzResearch.WordTrace tailWord_3615558 prefixEnd_3615558 15279992495544611904505 := by
  unfold tailWord_3615558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4120944807358072780961479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87913489223638885993844885 4120944807358072780961479)
  ·
    refine ⟨6181417211037109171442219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4120944807358072780961479 6181417211037109171442219)
    ·
      refine ⟨9272125816555663757163329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6181417211037109171442219 9272125816555663757163329)
      ·
        refine ⟨6954094362416747817872497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9272125816555663757163329 6954094362416747817872497)
        ·
          refine ⟨5215570771812560863404373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6954094362416747817872497 5215570771812560863404373)
          ·
            refine ⟨15279992495544611904505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5215570771812560863404373 15279992495544611904505)
            ·
              rfl

theorem cell22_3615558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 10].length) (baseStart_3615558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615558 prefixEnd_3615558 := by exact prefixLift 3615558
  have htrace : WordTrace (prefixWord ++ tailWord_3615558) baseStart_3615558 baseEnd_3615558 := by
    simpa [prefixWord, tailWord_3615558, baseEnd_3615558] using wordTrace_append hprefix tailTrace_3615558
  have hstable : (prefixWord ++ tailWord_3615558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615558).length < 2 ^ (prefixWord ++ tailWord_3615558).sum := by decide
  have hdescent : baseEnd_3615558 < baseStart_3615558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615650 : List Nat := [3, 3, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_3615650 : Nat := 118140960795 + 3615650 * 2 ^ 59
def prefixEnd_3615650 : Nat := 4983230072969 + 3 ^ 40 * 3615650 * 2
def baseEnd_3615650 : Nat := 1237710885619255990964623

theorem tailTrace_3615650 : CollatzResearch.WordTrace tailWord_3615650 prefixEnd_3615650 1237710885619255990964623 := by
  unfold tailWord_3615650
  simp only [CollatzResearch.WordTrace]
  refine ⟨32968397337781257175779101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87915726234083352468744269 32968397337781257175779101)
  ·
    refine ⟨12363149001667971440917163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32968397337781257175779101 12363149001667971440917163)
    ·
      refine ⟨18544723502501957161375745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12363149001667971440917163 18544723502501957161375745)
      ·
        refine ⟨13908542626876467871031809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18544723502501957161375745 13908542626876467871031809)
        ·
          refine ⟨10431406970157350903273857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13908542626876467871031809 10431406970157350903273857)
          ·
            refine ⟨7823555227618013177455393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10431406970157350903273857 7823555227618013177455393)
            ·
              refine ⟨5867666420713509883091545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7823555227618013177455393 5867666420713509883091545)
              ·
                refine ⟨4400749815535132412318659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5867666420713509883091545 4400749815535132412318659)
                ·
                  refine ⟨6601124723302698618477989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4400749815535132412318659 6601124723302698618477989)
                  ·
                    refine ⟨1237710885619255990964623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6601124723302698618477989 1237710885619255990964623)
                    ·
                      rfl

theorem cell22_3615650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_3615650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615650 prefixEnd_3615650 := by exact prefixLift 3615650
  have htrace : WordTrace (prefixWord ++ tailWord_3615650) baseStart_3615650 baseEnd_3615650 := by
    simpa [prefixWord, tailWord_3615650, baseEnd_3615650] using wordTrace_append hprefix tailTrace_3615650
  have hstable : (prefixWord ++ tailWord_3615650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615650).length < 2 ^ (prefixWord ++ tailWord_3615650).sum := by decide
  have hdescent : baseEnd_3615650 < baseStart_3615650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615659 : List Nat := [1, 1, 1, 1, 2, 1, 1, 14]
def baseStart_3615659 : Nat := 118140960795 + 3615659 * 2 ^ 59
def prefixEnd_3615659 : Nat := 4983230072969 + 3 ^ 40 * 3615659 * 2
def baseEnd_3615659 : Nat := 137523774055909218609955

theorem tailTrace_3615659 : CollatzResearch.WordTrace tailWord_3615659 prefixEnd_3615659 137523774055909218609955 := by
  unfold tailWord_3615659
  simp only [CollatzResearch.WordTrace]
  refine ⟨131873917608092423240194031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87915945072061615493462687 131873917608092423240194031)
  ·
    refine ⟨197810876412138634860291047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131873917608092423240194031 197810876412138634860291047)
    ·
      refine ⟨296716314618207952290436571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197810876412138634860291047 296716314618207952290436571)
      ·
        refine ⟨445074471927311928435654857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296716314618207952290436571 445074471927311928435654857)
        ·
          refine ⟨333805853945483946326741143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445074471927311928435654857 333805853945483946326741143)
          ·
            refine ⟨500708780918225919490111715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333805853945483946326741143 500708780918225919490111715)
            ·
              refine ⟨751063171377338879235167573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500708780918225919490111715 751063171377338879235167573)
              ·
                refine ⟨137523774055909218609955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 751063171377338879235167573 137523774055909218609955)
                ·
                  rfl

theorem cell22_3615659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 14].length) (baseStart_3615659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615659 prefixEnd_3615659 := by exact prefixLift 3615659
  have htrace : WordTrace (prefixWord ++ tailWord_3615659) baseStart_3615659 baseEnd_3615659 := by
    simpa [prefixWord, tailWord_3615659, baseEnd_3615659] using wordTrace_append hprefix tailTrace_3615659
  have hstable : (prefixWord ++ tailWord_3615659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615659).length < 2 ^ (prefixWord ++ tailWord_3615659).sum := by decide
  have hdescent : baseEnd_3615659 < baseStart_3615659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615678 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_3615678 : Nat := 118140960795 + 3615678 * 2 ^ 59
def prefixEnd_3615678 : Nat := 4983230072969 + 3 ^ 40 * 3615678 * 2
def baseEnd_3615678 : Nat := 1237720470591473251264537

theorem tailTrace_3615678 : CollatzResearch.WordTrace tailWord_3615678 prefixEnd_3615678 1237720470591473251264537 := by
  unfold tailWord_3615678
  simp only [CollatzResearch.WordTrace]
  refine ⟨16484326324377948685641961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87916407063349059656757125 16484326324377948685641961)
  ·
    refine ⟨12363244743283461514231471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16484326324377948685641961 12363244743283461514231471)
    ·
      refine ⟨18544867114925192271347207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12363244743283461514231471 18544867114925192271347207)
      ·
        refine ⟨27817300672387788407020811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18544867114925192271347207 27817300672387788407020811)
        ·
          refine ⟨41725951008581682610531217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27817300672387788407020811 41725951008581682610531217)
          ·
            refine ⟨31294463256436261957898413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41725951008581682610531217 31294463256436261957898413)
            ·
              refine ⟨11735423721163598234211905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31294463256436261957898413 11735423721163598234211905)
              ·
                refine ⟨8801567790872698675658929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11735423721163598234211905 8801567790872698675658929)
                ·
                  refine ⟨6601175843154524006744197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8801567790872698675658929 6601175843154524006744197)
                  ·
                    refine ⟨1237720470591473251264537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6601175843154524006744197 1237720470591473251264537)
                    ·
                      rfl

theorem cell22_3615678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_3615678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615678 prefixEnd_3615678 := by exact prefixLift 3615678
  have htrace : WordTrace (prefixWord ++ tailWord_3615678) baseStart_3615678 baseEnd_3615678 := by
    simpa [prefixWord, tailWord_3615678, baseEnd_3615678] using wordTrace_append hprefix tailTrace_3615678
  have hstable : (prefixWord ++ tailWord_3615678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615678).length < 2 ^ (prefixWord ++ tailWord_3615678).sum := by decide
  have hdescent : baseEnd_3615678 < baseStart_3615678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615736 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 2, 5]
def baseStart_3615736 : Nat := 118140960795 + 3615736 * 2 ^ 59
def prefixEnd_3615736 : Nat := 4983230072969 + 3 ^ 40 * 3615736 * 2
def baseEnd_3615736 : Nat := 1237740325176780433314359

theorem tailTrace_3615736 : CollatzResearch.WordTrace tailWord_3615736 prefixEnd_3615736 1237740325176780433314359 := by
  unfold tailWord_3615736
  simp only [CollatzResearch.WordTrace]
  refine ⟨65938363014406732695373531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87917817352542310260498041 65938363014406732695373531)
  ·
    refine ⟨98907544521610099043060297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65938363014406732695373531 98907544521610099043060297)
    ·
      refine ⟨74180658391207574282295223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98907544521610099043060297 74180658391207574282295223)
      ·
        refine ⟨111270987586811361423442835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74180658391207574282295223 111270987586811361423442835)
        ·
          refine ⟨166906481380217042135164253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111270987586811361423442835 166906481380217042135164253)
          ·
            refine ⟨62589930517581390800686595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166906481380217042135164253 62589930517581390800686595)
            ·
              refine ⟨93884895776372086201029893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62589930517581390800686595 93884895776372086201029893)
              ·
                refine ⟨17603417958069766162693105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93884895776372086201029893 17603417958069766162693105)
                ·
                  refine ⟨13202563468552324622019829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17603417958069766162693105 13202563468552324622019829)
                  ·
                    refine ⟨1237740325176780433314359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13202563468552324622019829 1237740325176780433314359)
                    ·
                      rfl

theorem cell22_3615736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_3615736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615736 prefixEnd_3615736 := by exact prefixLift 3615736
  have htrace : WordTrace (prefixWord ++ tailWord_3615736) baseStart_3615736 baseEnd_3615736 := by
    simpa [prefixWord, tailWord_3615736, baseEnd_3615736] using wordTrace_append hprefix tailTrace_3615736
  have hstable : (prefixWord ++ tailWord_3615736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615736).length < 2 ^ (prefixWord ++ tailWord_3615736).sum := by decide
  have hdescent : baseEnd_3615736 < baseStart_3615736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615768 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 3, 4]
def baseStart_3615768 : Nat := 118140960795 + 3615768 * 2 ^ 59
def prefixEnd_3615768 : Nat := 4983230072969 + 3 ^ 40 * 3615768 * 2
def baseEnd_3615768 : Nat := 1237751279430743016514261

theorem tailTrace_3615768 : CollatzResearch.WordTrace tailWord_3615768 prefixEnd_3615768 1237751279430743016514261 := by
  unfold tailWord_3615768
  simp only [CollatzResearch.WordTrace]
  refine ⟨65938946582348767427955979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87918595443131689903941305 65938946582348767427955979)
  ·
    refine ⟨98908419873523151141933969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65938946582348767427955979 98908419873523151141933969)
    ·
      refine ⟨74181314905142363356450477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98908419873523151141933969 74181314905142363356450477)
      ·
        refine ⟨27817993089428386258668929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74181314905142363356450477 27817993089428386258668929)
        ·
          refine ⟨20863494817071289694001697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27817993089428386258668929 20863494817071289694001697)
          ·
            refine ⟨15647621112803467270501273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20863494817071289694001697 15647621112803467270501273)
            ·
              refine ⟨11735715834602600452875955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15647621112803467270501273 11735715834602600452875955)
              ·
                refine ⟨17603573751903900679313933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11735715834602600452875955 17603573751903900679313933)
                ·
                  refine ⟨6601340156963962754742725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17603573751903900679313933 6601340156963962754742725)
                  ·
                    refine ⟨1237751279430743016514261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6601340156963962754742725 1237751279430743016514261)
                    ·
                      rfl

theorem cell22_3615768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_3615768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615768 prefixEnd_3615768 := by exact prefixLift 3615768
  have htrace : WordTrace (prefixWord ++ tailWord_3615768) baseStart_3615768 baseEnd_3615768 := by
    simpa [prefixWord, tailWord_3615768, baseEnd_3615768] using wordTrace_append hprefix tailTrace_3615768
  have hstable : (prefixWord ++ tailWord_3615768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615768).length < 2 ^ (prefixWord ++ tailWord_3615768).sum := by decide
  have hdescent : baseEnd_3615768 < baseStart_3615768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615800 : List Nat := [2, 1, 2, 1, 5, 1, 2, 4, 4]
def baseStart_3615800 : Nat := 118140960795 + 3615800 * 2 ^ 59
def prefixEnd_3615800 : Nat := 4983230072969 + 3 ^ 40 * 3615800 * 2
def baseEnd_3615800 : Nat := 412587411228235199904721

theorem tailTrace_3615800 : CollatzResearch.WordTrace tailWord_3615800 prefixEnd_3615800 412587411228235199904721 := by
  unfold tailWord_3615800
  simp only [CollatzResearch.WordTrace]
  refine ⟨65939530150290802160538427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87919373533721069547384569 65939530150290802160538427)
  ·
    refine ⟨98909295225436203240807641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65939530150290802160538427 98909295225436203240807641)
    ·
      refine ⟨74181971419077152430605731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98909295225436203240807641 74181971419077152430605731)
      ·
        refine ⟨111272957128615728645908597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74181971419077152430605731 111272957128615728645908597)
        ·
          refine ⟨10431839730807724560553931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111272957128615728645908597 10431839730807724560553931)
          ·
            refine ⟨15647759596211586840830897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10431839730807724560553931 15647759596211586840830897)
            ·
              refine ⟨11735819697158690130623173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15647759596211586840830897 11735819697158690130623173)
              ·
                refine ⟨2200466193217254399491845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11735819697158690130623173 2200466193217254399491845)
                ·
                  refine ⟨412587411228235199904721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2200466193217254399491845 412587411228235199904721)
                  ·
                    rfl

theorem cell22_3615800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 4].length) (baseStart_3615800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615800 prefixEnd_3615800 := by exact prefixLift 3615800
  have htrace : WordTrace (prefixWord ++ tailWord_3615800) baseStart_3615800 baseEnd_3615800 := by
    simpa [prefixWord, tailWord_3615800, baseEnd_3615800] using wordTrace_append hprefix tailTrace_3615800
  have hstable : (prefixWord ++ tailWord_3615800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615800).length < 2 ^ (prefixWord ++ tailWord_3615800).sum := by decide
  have hdescent : baseEnd_3615800 < baseStart_3615800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615811 : List Nat := [1, 1, 1, 3, 1, 2, 4, 9]
def baseStart_3615811 : Nat := 118140960795 + 3615811 * 2 ^ 59
def prefixEnd_3615811 : Nat := 4983230072969 + 3 ^ 40 * 3615811 * 2
def baseEnd_3615811 : Nat := 137529555467722804187681

theorem tailTrace_3615811 : CollatzResearch.WordTrace tailWord_3615811 prefixEnd_3615811 137529555467722804187681 := by
  unfold tailWord_3615811
  simp only [CollatzResearch.WordTrace]
  refine ⟨131879461503541753199727287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87919641002361168799818191 131879461503541753199727287)
  ·
    refine ⟨197819192255312629799590931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131879461503541753199727287 197819192255312629799590931)
    ·
      refine ⟨296728788382968944699386397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197819192255312629799590931 296728788382968944699386397)
      ·
        refine ⟨111273295643613354262269899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296728788382968944699386397 111273295643613354262269899)
        ·
          refine ⟨166909943465420031393404849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111273295643613354262269899 166909943465420031393404849)
          ·
            refine ⟨125182457599065023545053637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166909943465420031393404849 125182457599065023545053637)
            ·
              refine ⟨23471710799824691914697557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125182457599065023545053637 23471710799824691914697557)
              ·
                refine ⟨137529555467722804187681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23471710799824691914697557 137529555467722804187681)
                ·
                  rfl

theorem cell22_3615811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 9].length) (baseStart_3615811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615811 prefixEnd_3615811 := by exact prefixLift 3615811
  have htrace : WordTrace (prefixWord ++ tailWord_3615811) baseStart_3615811 baseEnd_3615811 := by
    simpa [prefixWord, tailWord_3615811, baseEnd_3615811] using wordTrace_append hprefix tailTrace_3615811
  have hstable : (prefixWord ++ tailWord_3615811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615811).length < 2 ^ (prefixWord ++ tailWord_3615811).sum := by decide
  have hdescent : baseEnd_3615811 < baseStart_3615811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615815 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 1, 5]
def baseStart_3615815 : Nat := 118140960795 + 3615815 * 2 ^ 59
def prefixEnd_3615815 : Nat := 4983230072969 + 3 ^ 40 * 3615815 * 2
def baseEnd_3615815 : Nat := 1237767368491250560589117

theorem tailTrace_3615815 : CollatzResearch.WordTrace tailWord_3615815 prefixEnd_3615815 1237767368491250560589117 := by
  unfold tailWord_3615815
  simp only [CollatzResearch.WordTrace]
  refine ⟨131879607395527261882872899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87919738263684841255248599 131879607395527261882872899)
  ·
    refine ⟨197819411093290892824309349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131879607395527261882872899 197819411093290892824309349)
    ·
      refine ⟨37091139579992042404558003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197819411093290892824309349 37091139579992042404558003)
      ·
        refine ⟨55636709369988063606837005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37091139579992042404558003 55636709369988063606837005)
        ·
          refine ⟨20863766013745523852563877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55636709369988063606837005 20863766013745523852563877)
          ·
            refine ⟨3911956127577285722355727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20863766013745523852563877 3911956127577285722355727)
            ·
              refine ⟨5867934191365928583533591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3911956127577285722355727 5867934191365928583533591)
              ·
                refine ⟨8801901287048892875300387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5867934191365928583533591 8801901287048892875300387)
                ·
                  refine ⟨13202851930573339312950581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8801901287048892875300387 13202851930573339312950581)
                  ·
                    refine ⟨1237767368491250560589117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13202851930573339312950581 1237767368491250560589117)
                    ·
                      rfl

theorem cell22_3615815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_3615815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615815 prefixEnd_3615815 := by exact prefixLift 3615815
  have htrace : WordTrace (prefixWord ++ tailWord_3615815) baseStart_3615815 baseEnd_3615815 := by
    simpa [prefixWord, tailWord_3615815, baseEnd_3615815] using wordTrace_append hprefix tailTrace_3615815
  have hstable : (prefixWord ++ tailWord_3615815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615815).length < 2 ^ (prefixWord ++ tailWord_3615815).sum := by decide
  have hdescent : baseEnd_3615815 < baseStart_3615815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615858 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_3615858 : Nat := 118140960795 + 3615858 * 2 ^ 59
def prefixEnd_3615858 : Nat := 4983230072969 + 3 ^ 40 * 3615858 * 2
def baseEnd_3615858 : Nat := 1237782088270012781763985

theorem tailTrace_3615858 : CollatzResearch.WordTrace tailWord_3615858 prefixEnd_3615858 1237782088270012781763985 := by
  unfold tailWord_3615858
  simp only [CollatzResearch.WordTrace]
  refine ⟨32970293933592870056672057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87920783822914320151125485 32970293933592870056672057)
  ·
    refine ⟨24727720450194652542504043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32970293933592870056672057 24727720450194652542504043)
    ·
      refine ⟨37091580675291978813756065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24727720450194652542504043 37091580675291978813756065)
      ·
        refine ⟨27818685506468984110317049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37091580675291978813756065 27818685506468984110317049)
        ·
          refine ⟨20864014129851738082737787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27818685506468984110317049 20864014129851738082737787)
          ·
            refine ⟨31296021194777607124106681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20864014129851738082737787 31296021194777607124106681)
            ·
              refine ⟨23472015896083205343080011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31296021194777607124106681 23472015896083205343080011)
              ·
                refine ⟨35208023844124808014620017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23472015896083205343080011 35208023844124808014620017)
                ·
                  refine ⟨26406017883093606010965013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35208023844124808014620017 26406017883093606010965013)
                  ·
                    refine ⟨1237782088270012781763985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26406017883093606010965013 1237782088270012781763985)
                    ·
                      rfl

theorem cell22_3615858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_3615858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615858 prefixEnd_3615858 := by exact prefixLift 3615858
  have htrace : WordTrace (prefixWord ++ tailWord_3615858) baseStart_3615858 baseEnd_3615858 := by
    simpa [prefixWord, tailWord_3615858, baseEnd_3615858] using wordTrace_append hprefix tailTrace_3615858
  have hstable : (prefixWord ++ tailWord_3615858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615858).length < 2 ^ (prefixWord ++ tailWord_3615858).sum := by decide
  have hdescent : baseEnd_3615858 < baseStart_3615858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615911 : List Nat := [1, 1, 6, 2, 1, 1, 4, 2, 1, 3]
def baseStart_3615911 : Nat := 118140960795 + 3615911 * 2 ^ 59
def prefixEnd_3615911 : Nat := 4983230072969 + 3 ^ 40 * 3615911 * 2
def baseEnd_3615911 : Nat := 1237800231253138310188823

theorem tailTrace_3615911 : CollatzResearch.WordTrace tailWord_3615911 prefixEnd_3615911 1237800231253138310188823 := by
  unfold tailWord_3615911
  simp only [CollatzResearch.WordTrace]
  refine ⟨131883108803179470278367587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87922072535452980185578391 131883108803179470278367587)
  ·
    refine ⟨197824663204769205417551381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131883108803179470278367587 197824663204769205417551381)
    ·
      refine ⟨9273031087723556503947721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 197824663204769205417551381 9273031087723556503947721)
      ·
        refine ⟨6954773315792667377960791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9273031087723556503947721 6954773315792667377960791)
        ·
          refine ⟨10432159973689001066941187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6954773315792667377960791 10432159973689001066941187)
          ·
            refine ⟨15648239960533501600411781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10432159973689001066941187 15648239960533501600411781)
            ·
              refine ⟨2934044992600031550077209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15648239960533501600411781 2934044992600031550077209)
              ·
                refine ⟨2200533744450023662557907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2934044992600031550077209 2200533744450023662557907)
                ·
                  refine ⟨3300800616675035493836861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2200533744450023662557907 3300800616675035493836861)
                  ·
                    refine ⟨1237800231253138310188823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3300800616675035493836861 1237800231253138310188823)
                    ·
                      rfl

theorem cell22_3615911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_3615911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615911 prefixEnd_3615911 := by exact prefixLift 3615911
  have htrace : WordTrace (prefixWord ++ tailWord_3615911) baseStart_3615911 baseEnd_3615911 := by
    simpa [prefixWord, tailWord_3615911, baseEnd_3615911] using wordTrace_append hprefix tailTrace_3615911
  have hstable : (prefixWord ++ tailWord_3615911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615911).length < 2 ^ (prefixWord ++ tailWord_3615911).sum := by decide
  have hdescent : baseEnd_3615911 < baseStart_3615911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615937 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3615937 : Nat := 118140960795 + 3615937 * 2 ^ 59
def prefixEnd_3615937 : Nat := 4983230072969 + 3 ^ 40 * 3615937 * 2
def baseEnd_3615937 : Nat := 1237809131584482909038743

theorem tailTrace_3615937 : CollatzResearch.WordTrace tailWord_3615937 prefixEnd_3615937 1237809131584482909038743 := by
  unfold tailWord_3615937
  simp only [CollatzResearch.WordTrace]
  refine ⟨131884057101085276718814065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87922704734056851145876043 131884057101085276718814065)
  ·
    refine ⟨98913042825813957539110549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131884057101085276718814065 98913042825813957539110549)
    ·
      refine ⟨4636548882460029259645807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98913042825813957539110549 4636548882460029259645807)
      ·
        refine ⟨6954823323690043889468711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4636548882460029259645807 6954823323690043889468711)
        ·
          refine ⟨10432234985535065834203067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6954823323690043889468711 10432234985535065834203067)
          ·
            refine ⟨15648352478302598751304601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10432234985535065834203067 15648352478302598751304601)
            ·
              refine ⟨11736264358726949063478451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15648352478302598751304601 11736264358726949063478451)
              ·
                refine ⟨17604396538090423595217677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11736264358726949063478451 17604396538090423595217677)
                ·
                  refine ⟨6601648701783908848206629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17604396538090423595217677 6601648701783908848206629)
                  ·
                    refine ⟨1237809131584482909038743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6601648701783908848206629 1237809131584482909038743)
                    ·
                      rfl

theorem cell22_3615937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3615937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615937 prefixEnd_3615937 := by exact prefixLift 3615937
  have htrace : WordTrace (prefixWord ++ tailWord_3615937) baseStart_3615937 baseEnd_3615937 := by
    simpa [prefixWord, tailWord_3615937, baseEnd_3615937] using wordTrace_append hprefix tailTrace_3615937
  have hstable : (prefixWord ++ tailWord_3615937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615937).length < 2 ^ (prefixWord ++ tailWord_3615937).sum := by decide
  have hdescent : baseEnd_3615937 < baseStart_3615937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615967 : List Nat := [1, 1, 2, 3, 2, 1, 5, 2, 2, 3]
def baseStart_3615967 : Nat := 118140960795 + 3615967 * 2 ^ 59
def prefixEnd_3615967 : Nat := 4983230072969 + 3 ^ 40 * 3615967 * 2
def baseEnd_3615967 : Nat := 1237819401197572830788651

theorem tailTrace_3615967 : CollatzResearch.WordTrace tailWord_3615967 prefixEnd_3615967 1237819401197572830788651 := by
  unfold tailWord_3615967
  simp only [CollatzResearch.WordTrace]
  refine ⟨131885151290976591842406155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87923434193984394561604103 131885151290976591842406155)
  ·
    refine ⟨197827726936464887763609233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131885151290976591842406155 197827726936464887763609233)
    ·
      refine ⟨148370795202348665822706925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197827726936464887763609233 148370795202348665822706925)
      ·
        refine ⟨55639048200880749683515097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148370795202348665822706925 55639048200880749683515097)
        ·
          refine ⟨41729286150660562262636323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55639048200880749683515097 41729286150660562262636323)
          ·
            refine ⟨62593929225990843393954485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41729286150660562262636323 62593929225990843393954485)
            ·
              refine ⟨5868180864936641568183233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62593929225990843393954485 5868180864936641568183233)
              ·
                refine ⟨4401135648702481176137425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5868180864936641568183233 4401135648702481176137425)
                ·
                  refine ⟨3300851736526860882103069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4401135648702481176137425 3300851736526860882103069)
                  ·
                    refine ⟨1237819401197572830788651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3300851736526860882103069 1237819401197572830788651)
                    ·
                      rfl

theorem cell22_3615967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 3].length) (baseStart_3615967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615967 prefixEnd_3615967 := by exact prefixLift 3615967
  have htrace : WordTrace (prefixWord ++ tailWord_3615967) baseStart_3615967 baseEnd_3615967 := by
    simpa [prefixWord, tailWord_3615967, baseEnd_3615967] using wordTrace_append hprefix tailTrace_3615967
  have hstable : (prefixWord ++ tailWord_3615967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615967).length < 2 ^ (prefixWord ++ tailWord_3615967).sum := by decide
  have hdescent : baseEnd_3615967 < baseStart_3615967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615988 : List Nat := [2, 6, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3615988 : Nat := 118140960795 + 3615988 * 2 ^ 59
def prefixEnd_3615988 : Nat := 4983230072969 + 3 ^ 40 * 3615988 * 2
def baseEnd_3615988 : Nat := 1237826589926735776013587

theorem tailTrace_3615988 : CollatzResearch.WordTrace tailWord_3615988 prefixEnd_3615988 1237826589926735776013587 := by
  unfold tailWord_3615988
  simp only [CollatzResearch.WordTrace]
  refine ⟨65942958611950256214460309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87923944815933674952613745 65942958611950256214460309)
  ·
    refine ⟨3091076184935168260052827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65942958611950256214460309 3091076184935168260052827)
    ·
      refine ⟨4636614277402752390079241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3091076184935168260052827 4636614277402752390079241)
      ·
        refine ⟨3477460708052064292559431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4636614277402752390079241 3477460708052064292559431)
        ·
          refine ⟨5216191062078096438839147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3477460708052064292559431 5216191062078096438839147)
          ·
            refine ⟨7824286593117144658258721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5216191062078096438839147 7824286593117144658258721)
            ·
              refine ⟨5868214944837858493694041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7824286593117144658258721 5868214944837858493694041)
              ·
                refine ⟨4401161208628393870270531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5868214944837858493694041 4401161208628393870270531)
                ·
                  refine ⟨6601741812942590805405797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4401161208628393870270531 6601741812942590805405797)
                  ·
                    refine ⟨1237826589926735776013587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6601741812942590805405797 1237826589926735776013587)
                    ·
                      rfl

theorem cell22_3615988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3615988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3615988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3615988 prefixEnd_3615988 := by exact prefixLift 3615988
  have htrace : WordTrace (prefixWord ++ tailWord_3615988) baseStart_3615988 baseEnd_3615988 := by
    simpa [prefixWord, tailWord_3615988, baseEnd_3615988] using wordTrace_append hprefix tailTrace_3615988
  have hstable : (prefixWord ++ tailWord_3615988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615988).length < 2 ^ (prefixWord ++ tailWord_3615988).sum := by decide
  have hdescent : baseEnd_3615988 < baseStart_3615988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616029 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 3, 3]
def baseStart_3616029 : Nat := 118140960795 + 3616029 * 2 ^ 59
def prefixEnd_3616029 : Nat := 4983230072969 + 3 ^ 40 * 3616029 * 2
def baseEnd_3616029 : Nat := 1237840625064625335738461

theorem tailTrace_3616029 : CollatzResearch.WordTrace tailWord_3616029 prefixEnd_3616029 1237840625064625335738461 := by
  unfold tailWord_3616029
  simp only [CollatzResearch.WordTrace]
  refine ⟨131887412616751976431163141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87924941744501317620775427 131887412616751976431163141)
  ·
    refine ⟨24728889865640995580843089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131887412616751976431163141 24728889865640995580843089)
    ·
      refine ⟨18546667399230746685632317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24728889865640995580843089 18546667399230746685632317)
      ·
        refine ⟨6955000274711530007112119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18546667399230746685632317 6955000274711530007112119)
        ·
          refine ⟨10432500412067295010668179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6955000274711530007112119 10432500412067295010668179)
          ·
            refine ⟨15648750618100942516002269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10432500412067295010668179 15648750618100942516002269)
            ·
              refine ⟨5868281481787853443500851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15648750618100942516002269 5868281481787853443500851)
              ·
                refine ⟨8802422222681780165251277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5868281481787853443500851 8802422222681780165251277)
                ·
                  refine ⟨3300908333505667561969229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8802422222681780165251277 3300908333505667561969229)
                  ·
                    refine ⟨1237840625064625335738461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3300908333505667561969229 1237840625064625335738461)
                    ·
                      rfl

theorem cell22_3616029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_3616029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616029 prefixEnd_3616029 := by exact prefixLift 3616029
  have htrace : WordTrace (prefixWord ++ tailWord_3616029) baseStart_3616029 baseEnd_3616029 := by
    simpa [prefixWord, tailWord_3616029, baseEnd_3616029] using wordTrace_append hprefix tailTrace_3616029
  have hstable : (prefixWord ++ tailWord_3616029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616029).length < 2 ^ (prefixWord ++ tailWord_3616029).sum := by decide
  have hdescent : baseEnd_3616029 < baseStart_3616029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616136 : List Nat := [2, 1, 3, 3, 1, 4, 1, 2, 2, 3]
def baseStart_3616136 : Nat := 118140960795 + 3616136 * 2 ^ 59
def prefixEnd_3616136 : Nat := 4983230072969 + 3 ^ 40 * 3616136 * 2
def baseEnd_3616136 : Nat := 1237877253351312723313133

theorem tailTrace_3616136 : CollatzResearch.WordTrace tailWord_3616136 prefixEnd_3616136 1237877253351312723313133 := by
  unfold tailWord_3616136
  simp only [CollatzResearch.WordTrace]
  refine ⟨65945657613682166852654131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87927543484909555803538841 65945657613682166852654131)
  ·
    refine ⟨98918486420523250278981197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65945657613682166852654131 98918486420523250278981197)
    ·
      refine ⟨37094432407696218854617949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98918486420523250278981197 37094432407696218854617949)
      ·
        refine ⟨13910412152886082070481731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37094432407696218854617949 13910412152886082070481731)
        ·
          refine ⟨20865618229329123105722597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13910412152886082070481731 20865618229329123105722597)
          ·
            refine ⟨3912303417999210582322987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20865618229329123105722597 3912303417999210582322987)
            ·
              refine ⟨5868455126998815873484481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3912303417999210582322987 5868455126998815873484481)
              ·
                refine ⟨4401341345249111905113361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5868455126998815873484481 4401341345249111905113361)
                ·
                  refine ⟨3301006008936833928835021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4401341345249111905113361 3301006008936833928835021)
                  ·
                    refine ⟨1237877253351312723313133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3301006008936833928835021 1237877253351312723313133)
                    ·
                      rfl

theorem cell22_3616136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_3616136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616136 prefixEnd_3616136 := by exact prefixLift 3616136
  have htrace : WordTrace (prefixWord ++ tailWord_3616136) baseStart_3616136 baseEnd_3616136 := by
    simpa [prefixWord, tailWord_3616136, baseEnd_3616136] using wordTrace_append hprefix tailTrace_3616136
  have hstable : (prefixWord ++ tailWord_3616136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616136).length < 2 ^ (prefixWord ++ tailWord_3616136).sum := by decide
  have hdescent : baseEnd_3616136 < baseStart_3616136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616175 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 1, 7]
def baseStart_3616175 : Nat := 118140960795 + 3616175 * 2 ^ 59
def prefixEnd_3616175 : Nat := 4983230072969 + 3 ^ 40 * 3616175 * 2
def baseEnd_3616175 : Nat := 1237890603848329621588013

theorem tailTrace_3616175 : CollatzResearch.WordTrace tailWord_3616175 prefixEnd_3616175 1237890603848329621588013 := by
  unfold tailWord_3616175
  simp only [CollatzResearch.WordTrace]
  refine ⟨131892737674223043365977979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87928491782815362243985319 131892737674223043365977979)
  ·
    refine ⟨197839106511334565048966969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131892737674223043365977979 197839106511334565048966969)
    ·
      refine ⟨148379329883500923786725227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197839106511334565048966969 148379329883500923786725227)
      ·
        refine ⟨222568994825251385680087841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148379329883500923786725227 222568994825251385680087841)
        ·
          refine ⟨166926746118938539260065881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222568994825251385680087841 166926746118938539260065881)
          ·
            refine ⟨125195059589203904445049411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166926746118938539260065881 125195059589203904445049411)
            ·
              refine ⟨187792589383805856667574117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125195059589203904445049411 187792589383805856667574117)
              ·
                refine ⟨35211110509463598125170147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187792589383805856667574117 35211110509463598125170147)
                ·
                  refine ⟨52816665764195397187755221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35211110509463598125170147 52816665764195397187755221)
                  ·
                    refine ⟨1237890603848329621588013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52816665764195397187755221 1237890603848329621588013)
                    ·
                      rfl

theorem cell22_3616175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_3616175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616175 prefixEnd_3616175 := by exact prefixLift 3616175
  have htrace : WordTrace (prefixWord ++ tailWord_3616175) baseStart_3616175 baseEnd_3616175 := by
    simpa [prefixWord, tailWord_3616175, baseEnd_3616175] using wordTrace_append hprefix tailTrace_3616175
  have hstable : (prefixWord ++ tailWord_3616175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616175).length < 2 ^ (prefixWord ++ tailWord_3616175).sum := by decide
  have hdescent : baseEnd_3616175 < baseStart_3616175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616241 : List Nat := [1, 2, 2, 2, 3, 3, 3, 1, 1, 4]
def baseStart_3616241 : Nat := 118140960795 + 3616241 * 2 ^ 59
def prefixEnd_3616241 : Nat := 4983230072969 + 3 ^ 40 * 3616241 * 2
def baseEnd_3616241 : Nat := 1237913196997127449437811

theorem tailTrace_3616241 : CollatzResearch.WordTrace tailWord_3616241 prefixEnd_3616241 1237913196997127449437811 := by
  unfold tailWord_3616241
  simp only [CollatzResearch.WordTrace]
  refine ⟨131895144891983936637880577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87930096594655957758587051 131895144891983936637880577)
  ·
    refine ⟨98921358668987952478410433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131895144891983936637880577 98921358668987952478410433)
    ·
      refine ⟨74191019001740964358807825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98921358668987952478410433 74191019001740964358807825)
      ·
        refine ⟨55643264251305723269105869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74191019001740964358807825 55643264251305723269105869)
        ·
          refine ⟨20866224094239646225914701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55643264251305723269105869 20866224094239646225914701)
          ·
            refine ⟨7824834035339867334718013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20866224094239646225914701 7824834035339867334718013)
            ·
              refine ⟨2934312763252450250519255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7824834035339867334718013 2934312763252450250519255)
              ·
                refine ⟨4401469144878675375778883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2934312763252450250519255 4401469144878675375778883)
                ·
                  refine ⟨6602203717318013063668325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4401469144878675375778883 6602203717318013063668325)
                  ·
                    refine ⟨1237913196997127449437811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6602203717318013063668325 1237913196997127449437811)
                    ·
                      rfl

theorem cell22_3616241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_3616241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616241 prefixEnd_3616241 := by exact prefixLift 3616241
  have htrace : WordTrace (prefixWord ++ tailWord_3616241) baseStart_3616241 baseEnd_3616241 := by
    simpa [prefixWord, tailWord_3616241, baseEnd_3616241] using wordTrace_append hprefix tailTrace_3616241
  have hstable : (prefixWord ++ tailWord_3616241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616241).length < 2 ^ (prefixWord ++ tailWord_3616241).sum := by decide
  have hdescent : baseEnd_3616241 < baseStart_3616241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616284 : List Nat := [2, 2, 3, 1, 2, 1, 5, 6]
def baseStart_3616284 : Nat := 118140960795 + 3616284 * 2 ^ 59
def prefixEnd_3616284 : Nat := 4983230072969 + 3 ^ 40 * 3616284 * 2
def baseEnd_3616284 : Nat := 137547546308432185623631

theorem tailTrace_3616284 : CollatzResearch.WordTrace tailWord_3616284 prefixEnd_3616284 137547546308432185623631 := by
  unfold tailWord_3616284
  simp only [CollatzResearch.WordTrace]
  refine ⟨65948356615414077490847953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87931142153885436654463937 65948356615414077490847953)
  ·
    refine ⟨49461267461560558118135965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65948356615414077490847953 49461267461560558118135965)
    ·
      refine ⟨18547975298085209294300987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49461267461560558118135965 18547975298085209294300987)
      ·
        refine ⟨27821962947127813941451481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18547975298085209294300987 27821962947127813941451481)
        ·
          refine ⟨20866472210345860456088611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27821962947127813941451481 20866472210345860456088611)
          ·
            refine ⟨31299708315518790684132917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20866472210345860456088611 31299708315518790684132917)
            ·
              refine ⟨2934347654579886626637461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31299708315518790684132917 2934347654579886626637461)
              ·
                refine ⟨137547546308432185623631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2934347654579886626637461 137547546308432185623631)
                ·
                  rfl

theorem cell22_3616284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 6].length) (baseStart_3616284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616284 prefixEnd_3616284 := by exact prefixLift 3616284
  have htrace : WordTrace (prefixWord ++ tailWord_3616284) baseStart_3616284 baseEnd_3616284 := by
    simpa [prefixWord, tailWord_3616284, baseEnd_3616284] using wordTrace_append hprefix tailTrace_3616284
  have hstable : (prefixWord ++ tailWord_3616284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616284).length < 2 ^ (prefixWord ++ tailWord_3616284).sum := by decide
  have hdescent : baseEnd_3616284 < baseStart_3616284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616389 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 1, 5]
def baseStart_3616389 : Nat := 118140960795 + 3616389 * 2 ^ 59
def prefixEnd_3616389 : Nat := 4983230072969 + 3 ^ 40 * 3616389 * 2
def baseEnd_3616389 : Nat := 1237963860421704396737357

theorem tailTrace_3616389 : CollatzResearch.WordTrace tailWord_3616389 prefixEnd_3616389 1237963860421704396737357 := by
  unfold tailWord_3616389
  simp only [CollatzResearch.WordTrace]
  refine ⟨131900542895447757914268221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87933695263631838609512147 131900542895447757914268221)
  ·
    refine ⟨49462703585792909217850583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131900542895447757914268221 49462703585792909217850583)
    ·
      refine ⟨74194055378689363826775875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49462703585792909217850583 74194055378689363826775875)
      ·
        refine ⟨111291083068034045740163813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74194055378689363826775875 111291083068034045740163813)
        ·
          refine ⟨20867078075256383576280715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111291083068034045740163813 20867078075256383576280715)
          ·
            refine ⟨31300617112884575364421073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20867078075256383576280715 31300617112884575364421073)
            ·
              refine ⟨23475462834663431523315805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31300617112884575364421073 23475462834663431523315805)
              ·
                refine ⟨8803298562998786821243427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23475462834663431523315805 8803298562998786821243427)
                ·
                  refine ⟨13204947844498180231865141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8803298562998786821243427 13204947844498180231865141)
                  ·
                    refine ⟨1237963860421704396737357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13204947844498180231865141 1237963860421704396737357)
                    ·
                      rfl

theorem cell22_3616389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_3616389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616389 prefixEnd_3616389 := by exact prefixLift 3616389
  have htrace : WordTrace (prefixWord ++ tailWord_3616389) baseStart_3616389 baseEnd_3616389 := by
    simpa [prefixWord, tailWord_3616389, baseEnd_3616389] using wordTrace_append hprefix tailTrace_3616389
  have hstable : (prefixWord ++ tailWord_3616389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616389).length < 2 ^ (prefixWord ++ tailWord_3616389).sum := by decide
  have hdescent : baseEnd_3616389 < baseStart_3616389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616479 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 4, 5]
def baseStart_3616479 : Nat := 118140960795 + 3616479 * 2 ^ 59
def prefixEnd_3616479 : Nat := 4983230072969 + 3 ^ 40 * 3616479 * 2
def baseEnd_3616479 : Nat := 1237994669260974161987081

theorem tailTrace_3616479 : CollatzResearch.WordTrace tailWord_3616479 prefixEnd_3616479 1237994669260974161987081 := by
  unfold tailWord_3616479
  simp only [CollatzResearch.WordTrace]
  refine ⟨131903825465121703285044491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87935883643414468856696327 131903825465121703285044491)
  ·
    refine ⟨197855738197682554927566737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131903825465121703285044491 197855738197682554927566737)
    ·
      refine ⟨148391803648261916195675053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197855738197682554927566737 148391803648261916195675053)
      ·
        refine ⟨55646926368098218573378145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148391803648261916195675053 55646926368098218573378145)
        ·
          refine ⟨41735194776073663930033609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55646926368098218573378145 41735194776073663930033609)
          ·
            refine ⟨31301396082055247947525207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41735194776073663930033609 31301396082055247947525207)
            ·
              refine ⟨46952094123082871921287811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31301396082055247947525207 46952094123082871921287811)
              ·
                refine ⟨70428141184624307881931717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46952094123082871921287811 70428141184624307881931717)
                ·
                  refine ⟨13205276472117057727862197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70428141184624307881931717 13205276472117057727862197)
                  ·
                    refine ⟨1237994669260974161987081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13205276472117057727862197 1237994669260974161987081)
                    ·
                      rfl

theorem cell22_3616479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_3616479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616479 prefixEnd_3616479 := by exact prefixLift 3616479
  have htrace : WordTrace (prefixWord ++ tailWord_3616479) baseStart_3616479 baseEnd_3616479 := by
    simpa [prefixWord, tailWord_3616479, baseEnd_3616479] using wordTrace_append hprefix tailTrace_3616479
  have hstable : (prefixWord ++ tailWord_3616479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616479).length < 2 ^ (prefixWord ++ tailWord_3616479).sum := by decide
  have hdescent : baseEnd_3616479 < baseStart_3616479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616481 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 7]
def baseStart_3616481 : Nat := 118140960795 + 3616481 * 2 ^ 59
def prefixEnd_3616481 : Nat := 4983230072969 + 3 ^ 40 * 3616481 * 2
def baseEnd_3616481 : Nat := 412665117967282274479025

theorem tailTrace_3616481 : CollatzResearch.WordTrace tailWord_3616481 prefixEnd_3616481 412665117967282274479025 := by
  unfold tailWord_3616481
  simp only [CollatzResearch.WordTrace]
  refine ⟨131903898411114457626617297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87935932274076305084411531 131903898411114457626617297)
  ·
    refine ⟨98927923808335843219962973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131903898411114457626617297 98927923808335843219962973)
    ·
      refine ⟨37097971428125941207486115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98927923808335843219962973 37097971428125941207486115)
      ·
        refine ⟨55646957142188911811229173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37097971428125941207486115 55646957142188911811229173)
        ·
          refine ⟨5216902232080210482302735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55646957142188911811229173 5216902232080210482302735)
          ·
            refine ⟨7825353348120315723454103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5216902232080210482302735 7825353348120315723454103)
            ·
              refine ⟨11738030022180473585181155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7825353348120315723454103 11738030022180473585181155)
              ·
                refine ⟨17607045033270710377771733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11738030022180473585181155 17607045033270710377771733)
                ·
                  refine ⟨412665117967282274479025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17607045033270710377771733 412665117967282274479025)
                  ·
                    rfl

theorem cell22_3616481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 7].length) (baseStart_3616481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616481 prefixEnd_3616481 := by exact prefixLift 3616481
  have htrace : WordTrace (prefixWord ++ tailWord_3616481) baseStart_3616481 baseEnd_3616481 := by
    simpa [prefixWord, tailWord_3616481, baseEnd_3616481] using wordTrace_append hprefix tailTrace_3616481
  have hstable : (prefixWord ++ tailWord_3616481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616481).length < 2 ^ (prefixWord ++ tailWord_3616481).sum := by decide
  have hdescent : baseEnd_3616481 < baseStart_3616481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616498 : List Nat := [3, 2, 1, 3, 1, 1, 5, 1, 5]
def baseStart_3616498 : Nat := 118140960795 + 3616498 * 2 ^ 59
def prefixEnd_3616498 : Nat := 4983230072969 + 3 ^ 40 * 3616498 * 2
def baseEnd_3616498 : Nat := 412667057783088148587341

theorem tailTrace_3616498 : CollatzResearch.WordTrace tailWord_3616498 prefixEnd_3616498 412667057783088148587341 := by
  unfold tailWord_3616498
  simp only [CollatzResearch.WordTrace]
  refine ⟨32976129613013217382496537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87936345634701913019990765 32976129613013217382496537)
  ·
    refine ⟨24732097209759913036872403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32976129613013217382496537 24732097209759913036872403)
    ·
      refine ⟨37098145814639869555308605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24732097209759913036872403 37098145814639869555308605)
      ·
        refine ⟨13911804680489951083240727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37098145814639869555308605 13911804680489951083240727)
        ·
          refine ⟨20867707020734926624861091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13911804680489951083240727 20867707020734926624861091)
          ·
            refine ⟨31301560531102389937291637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20867707020734926624861091 31301560531102389937291637)
            ·
              refine ⟨2934521299790849056621091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31301560531102389937291637 2934521299790849056621091)
              ·
                refine ⟨4401781949686273584931637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2934521299790849056621091 4401781949686273584931637)
                ·
                  refine ⟨412667057783088148587341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4401781949686273584931637 412667057783088148587341)
                  ·
                    rfl

theorem cell22_3616498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_3616498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616498 prefixEnd_3616498 := by exact prefixLift 3616498
  have htrace : WordTrace (prefixWord ++ tailWord_3616498) baseStart_3616498 baseEnd_3616498 := by
    simpa [prefixWord, tailWord_3616498, baseEnd_3616498] using wordTrace_append hprefix tailTrace_3616498
  have hstable : (prefixWord ++ tailWord_3616498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616498).length < 2 ^ (prefixWord ++ tailWord_3616498).sum := by decide
  have hdescent : baseEnd_3616498 < baseStart_3616498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616509 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 8]
def baseStart_3616509 : Nat := 118140960795 + 3616509 * 2 ^ 59
def prefixEnd_3616509 : Nat := 4983230072969 + 3 ^ 40 * 3616509 * 2
def baseEnd_3616509 : Nat := 412668312958021361245663

theorem tailTrace_3616509 : CollatzResearch.WordTrace tailWord_3616509 prefixEnd_3616509 412668312958021361245663 := by
  unfold tailWord_3616509
  simp only [CollatzResearch.WordTrace]
  refine ⟨131904919655013018408636581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87936613103342012272424387 131904919655013018408636581)
  ·
    refine ⟨24732172435314940951619359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131904919655013018408636581 24732172435314940951619359)
    ·
      refine ⟨37098258652972411427429039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24732172435314940951619359 37098258652972411427429039)
      ·
        refine ⟨55647387979458617141143559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37098258652972411427429039 55647387979458617141143559)
        ·
          refine ⟨83471081969187925711715339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55647387979458617141143559 83471081969187925711715339)
          ·
            refine ⟨125206622953781888567573009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83471081969187925711715339 125206622953781888567573009)
            ·
              refine ⟨93904967215336416425679757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125206622953781888567573009 93904967215336416425679757)
              ·
                refine ⟨35214362705751156159629909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93904967215336416425679757 35214362705751156159629909)
                ·
                  refine ⟨412668312958021361245663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35214362705751156159629909 412668312958021361245663)
                  ·
                    rfl

theorem cell22_3616509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_3616509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616509 prefixEnd_3616509 := by exact prefixLift 3616509
  have htrace : WordTrace (prefixWord ++ tailWord_3616509) baseStart_3616509 baseEnd_3616509 := by
    simpa [prefixWord, tailWord_3616509, baseEnd_3616509] using wordTrace_append hprefix tailTrace_3616509
  have hstable : (prefixWord ++ tailWord_3616509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616509).length < 2 ^ (prefixWord ++ tailWord_3616509).sum := by decide
  have hdescent : baseEnd_3616509 < baseStart_3616509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616511 : List Nat := [1, 1, 2, 2, 1, 3, 3, 4, 1, 4]
def baseStart_3616511 : Nat := 118140960795 + 3616511 * 2 ^ 59
def prefixEnd_3616511 : Nat := 4983230072969 + 3 ^ 40 * 3616511 * 2
def baseEnd_3616511 : Nat := 1238005623514936745186983

theorem tailTrace_3616511 : CollatzResearch.WordTrace tailWord_3616511 prefixEnd_3616511 1238005623514936745186983 := by
  unfold tailWord_3616511
  simp only [CollatzResearch.WordTrace]
  refine ⟨131904992601005772750209387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87936661734003848500139591 131904992601005772750209387)
  ·
    refine ⟨197857488901508659125314081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131904992601005772750209387 197857488901508659125314081)
    ·
      refine ⟨148393116676131494343985561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197857488901508659125314081 148393116676131494343985561)
      ·
        refine ⟨111294837507098620757989171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148393116676131494343985561 111294837507098620757989171)
        ·
          refine ⟨166942256260647931136983757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111294837507098620757989171 166942256260647931136983757)
          ·
            refine ⟨62603346097742974176368909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166942256260647931136983757 62603346097742974176368909)
            ·
              refine ⟨23476254786653615316138341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62603346097742974176368909 23476254786653615316138341)
              ·
                refine ⟨4401797772497552871775939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23476254786653615316138341 4401797772497552871775939)
                ·
                  refine ⟨6602696658746329307663909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4401797772497552871775939 6602696658746329307663909)
                  ·
                    refine ⟨1238005623514936745186983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6602696658746329307663909 1238005623514936745186983)
                    ·
                      rfl

theorem cell22_3616511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 4].length) (baseStart_3616511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616511 prefixEnd_3616511 := by exact prefixLift 3616511
  have htrace : WordTrace (prefixWord ++ tailWord_3616511) baseStart_3616511 baseEnd_3616511 := by
    simpa [prefixWord, tailWord_3616511, baseEnd_3616511] using wordTrace_append hprefix tailTrace_3616511
  have hstable : (prefixWord ++ tailWord_3616511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616511).length < 2 ^ (prefixWord ++ tailWord_3616511).sum := by decide
  have hdescent : baseEnd_3616511 < baseStart_3616511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616519 : List Nat := [1, 1, 4, 4, 3, 1, 1, 3, 1, 3]
def baseStart_3616519 : Nat := 118140960795 + 3616519 * 2 ^ 59
def prefixEnd_3616519 : Nat := 4983230072969 + 3 ^ 40 * 3616519 * 2
def baseEnd_3616519 : Nat := 1238008362078427390986959

theorem tailTrace_3616519 : CollatzResearch.WordTrace tailWord_3616519 prefixEnd_3616519 1238008362078427390986959 := by
  unfold tailWord_3616519
  simp only [CollatzResearch.WordTrace]
  refine ⟨131905284384976790116500611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87936856256651193411000407 131905284384976790116500611)
  ·
    refine ⟨197857926577465185174750917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131905284384976790116500611 197857926577465185174750917)
    ·
      refine ⟨37098361233274722220265797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197857926577465185174750917 37098361233274722220265797)
      ·
        refine ⟨6955942731239010416299837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37098361233274722220265797 6955942731239010416299837)
        ·
          refine ⟨2608478524214628906112439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6955942731239010416299837 2608478524214628906112439)
          ·
            refine ⟨3912717786321943359168659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608478524214628906112439 3912717786321943359168659)
            ·
              refine ⟨5869076679482915038752989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3912717786321943359168659 5869076679482915038752989)
              ·
                refine ⟨2200903754806093139532371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5869076679482915038752989 2200903754806093139532371)
                ·
                  refine ⟨3301355632209139709298557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2200903754806093139532371 3301355632209139709298557)
                  ·
                    refine ⟨1238008362078427390986959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3301355632209139709298557 1238008362078427390986959)
                    ·
                      rfl

theorem cell22_3616519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_3616519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616519 prefixEnd_3616519 := by exact prefixLift 3616519
  have htrace : WordTrace (prefixWord ++ tailWord_3616519) baseStart_3616519 baseEnd_3616519 := by
    simpa [prefixWord, tailWord_3616519, baseEnd_3616519] using wordTrace_append hprefix tailTrace_3616519
  have hstable : (prefixWord ++ tailWord_3616519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616519).length < 2 ^ (prefixWord ++ tailWord_3616519).sum := by decide
  have hdescent : baseEnd_3616519 < baseStart_3616519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616573 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_3616573 : Nat := 118140960795 + 3616573 * 2 ^ 59
def prefixEnd_3616573 : Nat := 4983230072969 + 3 ^ 40 * 3616573 * 2
def baseEnd_3616573 : Nat := 1238026847381989250136793

theorem tailTrace_3616573 : CollatzResearch.WordTrace tailWord_3616573 prefixEnd_3616573 1238026847381989250136793 := by
  unfold tailWord_3616573
  simp only [CollatzResearch.WordTrace]
  refine ⟨131907253926781157338966373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87938169284520771559310915 131907253926781157338966373)
  ·
    refine ⟨24732610111271467001056195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131907253926781157338966373 24732610111271467001056195)
    ·
      refine ⟨37098915166907200501584293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24732610111271467001056195 37098915166907200501584293)
      ·
        refine ⟨6956046593795100094047055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37098915166907200501584293 6956046593795100094047055)
        ·
          refine ⟨10434069890692650141070583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6956046593795100094047055 10434069890692650141070583)
          ·
            refine ⟨15651104836038975211605875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10434069890692650141070583 15651104836038975211605875)
            ·
              refine ⟨23476657254058462817408813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15651104836038975211605875 23476657254058462817408813)
              ·
                refine ⟨8803746470271923556528305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23476657254058462817408813 8803746470271923556528305)
                ·
                  refine ⟨6602809852703942667396229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8803746470271923556528305 6602809852703942667396229)
                  ·
                    refine ⟨1238026847381989250136793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6602809852703942667396229 1238026847381989250136793)
                    ·
                      rfl

theorem cell22_3616573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_3616573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616573 prefixEnd_3616573 := by exact prefixLift 3616573
  have htrace : WordTrace (prefixWord ++ tailWord_3616573) baseStart_3616573 baseEnd_3616573 := by
    simpa [prefixWord, tailWord_3616573, baseEnd_3616573] using wordTrace_append hprefix tailTrace_3616573
  have hstable : (prefixWord ++ tailWord_3616573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616573).length < 2 ^ (prefixWord ++ tailWord_3616573).sum := by decide
  have hdescent : baseEnd_3616573 < baseStart_3616573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616691 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 1, 6]
def baseStart_3616691 : Nat := 118140960795 + 3616691 * 2 ^ 59
def prefixEnd_3616691 : Nat := 4983230072969 + 3 ^ 40 * 3616691 * 2
def baseEnd_3616691 : Nat := 1238067241193476275686431

theorem tailTrace_3616691 : CollatzResearch.WordTrace tailWord_3616691 prefixEnd_3616691 1238067241193476275686431 := by
  unfold tailWord_3616691
  simp only [CollatzResearch.WordTrace]
  refine ⟨131911557740353663491761927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87941038493569108994507951 131911557740353663491761927)
  ·
    refine ⟨197867336610530495237642891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131911557740353663491761927 197867336610530495237642891)
    ·
      refine ⟨296801004915795742856464337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197867336610530495237642891 296801004915795742856464337)
      ·
        refine ⟨222600753686846807142348253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296801004915795742856464337 222600753686846807142348253)
        ·
          refine ⟨83475282632567552678380595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222600753686846807142348253 83475282632567552678380595)
          ·
            refine ⟨125212923948851329017570893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83475282632567552678380595 125212923948851329017570893)
            ·
              refine ⟨46954846480819248381589085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125212923948851329017570893 46954846480819248381589085)
              ·
                refine ⟨17608067430307218143095907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46954846480819248381589085 17608067430307218143095907)
                ·
                  refine ⟨26412101145460827214643861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17608067430307218143095907 26412101145460827214643861)
                  ·
                    refine ⟨1238067241193476275686431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26412101145460827214643861 1238067241193476275686431)
                    ·
                      rfl

theorem cell22_3616691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 6].length) (baseStart_3616691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616691 prefixEnd_3616691 := by exact prefixLift 3616691
  have htrace : WordTrace (prefixWord ++ tailWord_3616691) baseStart_3616691 baseEnd_3616691 := by
    simpa [prefixWord, tailWord_3616691, baseEnd_3616691] using wordTrace_append hprefix tailTrace_3616691
  have hstable : (prefixWord ++ tailWord_3616691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616691).length < 2 ^ (prefixWord ++ tailWord_3616691).sum := by decide
  have hdescent : baseEnd_3616691 < baseStart_3616691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616712 : List Nat := [2, 1, 3, 1, 4, 2, 3, 2, 4]
def baseStart_3616712 : Nat := 118140960795 + 3616712 * 2 ^ 59
def prefixEnd_3616712 : Nat := 4983230072969 + 3 ^ 40 * 3616712 * 2
def baseEnd_3616712 : Nat := 412691476640879740303789

theorem tailTrace_3616712 : CollatzResearch.WordTrace tailWord_3616712 prefixEnd_3616712 412691476640879740303789 := by
  unfold tailWord_3616712
  simp only [CollatzResearch.WordTrace]
  refine ⟨65956161836638792039138195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87941549115518389385517593 65956161836638792039138195)
  ·
    refine ⟨98934242754958188058707293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65956161836638792039138195 98934242754958188058707293)
    ·
      refine ⟨37100341033109320522015235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98934242754958188058707293 37100341033109320522015235)
      ·
        refine ⟨55650511549663980783022853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37100341033109320522015235 55650511549663980783022853)
        ·
          refine ⟨10434470915561996396816785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55650511549663980783022853 10434470915561996396816785)
          ·
            refine ⟨7825853186671497297612589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10434470915561996396816785 7825853186671497297612589)
            ·
              refine ⟨2934694945001811486604721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7825853186671497297612589 2934694945001811486604721)
              ·
                refine ⟨2201021208751358614953541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2934694945001811486604721 2201021208751358614953541)
                ·
                  refine ⟨412691476640879740303789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2201021208751358614953541 412691476640879740303789)
                  ·
                    rfl

theorem cell22_3616712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 4].length) (baseStart_3616712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616712 prefixEnd_3616712 := by exact prefixLift 3616712
  have htrace : WordTrace (prefixWord ++ tailWord_3616712) baseStart_3616712 baseEnd_3616712 := by
    simpa [prefixWord, tailWord_3616712, baseEnd_3616712] using wordTrace_append hprefix tailTrace_3616712
  have hstable : (prefixWord ++ tailWord_3616712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616712).length < 2 ^ (prefixWord ++ tailWord_3616712).sum := by decide
  have hdescent : baseEnd_3616712 < baseStart_3616712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616721 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 2, 7]
def baseStart_3616721 : Nat := 118140960795 + 3616721 * 2 ^ 59
def prefixEnd_3616721 : Nat := 4983230072969 + 3 ^ 40 * 3616721 * 2
def baseEnd_3616721 : Nat := 1238077510806566197436339

theorem tailTrace_3616721 : CollatzResearch.WordTrace tailWord_3616721 prefixEnd_3616721 1238077510806566197436339 := by
  unfold tailWord_3616721
  simp only [CollatzResearch.WordTrace]
  refine ⟨131912651930244978615354017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87941767953496652410236011 131912651930244978615354017)
  ·
    refine ⟨98934488947683733961515513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131912651930244978615354017 98934488947683733961515513)
    ·
      refine ⟨74200866710762800471136635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98934488947683733961515513 74200866710762800471136635)
      ·
        refine ⟨111301300066144200706704953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74200866710762800471136635 111301300066144200706704953)
        ·
          refine ⟨83475975049608150530028715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111301300066144200706704953 83475975049608150530028715)
          ·
            refine ⟨125213962574412225795043073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83475975049608150530028715 125213962574412225795043073)
            ·
              refine ⟨93910471930809169346282305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125213962574412225795043073 93910471930809169346282305)
              ·
                refine ⟨70432853948106877009711729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93910471930809169346282305 70432853948106877009711729)
                ·
                  refine ⟨52824640461080157757283797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70432853948106877009711729 52824640461080157757283797)
                  ·
                    refine ⟨1238077510806566197436339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52824640461080157757283797 1238077510806566197436339)
                    ·
                      rfl

theorem cell22_3616721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_3616721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616721 prefixEnd_3616721 := by exact prefixLift 3616721
  have htrace : WordTrace (prefixWord ++ tailWord_3616721) baseStart_3616721 baseEnd_3616721 := by
    simpa [prefixWord, tailWord_3616721, baseEnd_3616721] using wordTrace_append hprefix tailTrace_3616721
  have hstable : (prefixWord ++ tailWord_3616721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616721).length < 2 ^ (prefixWord ++ tailWord_3616721).sum := by decide
  have hdescent : baseEnd_3616721 < baseStart_3616721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616843 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 4, 4]
def baseStart_3616843 : Nat := 118140960795 + 3616843 * 2 ^ 59
def prefixEnd_3616843 : Nat := 4983230072969 + 3 ^ 40 * 3616843 * 2
def baseEnd_3616843 : Nat := 1238119273899798545885965

theorem tailTrace_3616843 : CollatzResearch.WordTrace tailWord_3616843 prefixEnd_3616843 1238119273899798545885965 := by
  unfold tailWord_3616843
  simp only [CollatzResearch.WordTrace]
  refine ⟨131917101635802993451295183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87944734423868662300863455 131917101635802993451295183)
  ·
    refine ⟨197875652453704490176942775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131917101635802993451295183 197875652453704490176942775)
    ·
      refine ⟨296813478680556735265414163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197875652453704490176942775 296813478680556735265414163)
      ·
        refine ⟨445220218020835102898121245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296813478680556735265414163 445220218020835102898121245)
        ·
          refine ⟨166957581757813163586795467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445220218020835102898121245 166957581757813163586795467)
          ·
            refine ⟨250436372636719745380193201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166957581757813163586795467 250436372636719745380193201)
            ·
              refine ⟨187827279477539809035144901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250436372636719745380193201 187827279477539809035144901)
              ·
                refine ⟨35217614902038714194089669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187827279477539809035144901 35217614902038714194089669)
                ·
                  refine ⟨6603302794132258911391813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35217614902038714194089669 6603302794132258911391813)
                  ·
                    refine ⟨1238119273899798545885965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6603302794132258911391813 1238119273899798545885965)
                    ·
                      rfl

theorem cell22_3616843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 4].length) (baseStart_3616843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616843 prefixEnd_3616843 := by exact prefixLift 3616843
  have htrace : WordTrace (prefixWord ++ tailWord_3616843) baseStart_3616843 baseEnd_3616843 := by
    simpa [prefixWord, tailWord_3616843, baseEnd_3616843] using wordTrace_append hprefix tailTrace_3616843
  have hstable : (prefixWord ++ tailWord_3616843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616843).length < 2 ^ (prefixWord ++ tailWord_3616843).sum := by decide
  have hdescent : baseEnd_3616843 < baseStart_3616843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616858 : List Nat := [3, 1, 1, 2, 1, 1, 5, 8]
def baseStart_3616858 : Nat := 118140960795 + 3616858 * 2 ^ 59
def prefixEnd_3616858 : Nat := 4983230072969 + 3 ^ 40 * 3616858 * 2
def baseEnd_3616858 : Nat := 137569378745149278528991

theorem tailTrace_3616858 : CollatzResearch.WordTrace tailWord_3616858 prefixEnd_3616858 137569378745149278528991 := by
  unfold tailWord_3616858
  simp only [CollatzResearch.WordTrace]
  refine ⟨32979412182687162753272807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87945099153832434008727485 32979412182687162753272807)
  ·
    refine ⟨49469118274030744129909211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32979412182687162753272807 49469118274030744129909211)
    ·
      refine ⟨74203677411046116194863817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49469118274030744129909211 74203677411046116194863817)
      ·
        refine ⟨55652758058284587146147863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74203677411046116194863817 55652758058284587146147863)
        ·
          refine ⟨83479137087426880719221795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55652758058284587146147863 83479137087426880719221795)
          ·
            refine ⟨125218705631140321078832693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83479137087426880719221795 125218705631140321078832693)
            ·
              refine ⟨11739253652919405101140565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125218705631140321078832693 11739253652919405101140565)
              ·
                refine ⟨137569378745149278528991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11739253652919405101140565 137569378745149278528991)
                ·
                  rfl

theorem cell22_3616858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 8].length) (baseStart_3616858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616858 prefixEnd_3616858 := by exact prefixLift 3616858
  have htrace : WordTrace (prefixWord ++ tailWord_3616858) baseStart_3616858 baseEnd_3616858 := by
    simpa [prefixWord, tailWord_3616858, baseEnd_3616858] using wordTrace_append hprefix tailTrace_3616858
  have hstable : (prefixWord ++ tailWord_3616858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616858).length < 2 ^ (prefixWord ++ tailWord_3616858).sum := by decide
  have hdescent : baseEnd_3616858 < baseStart_3616858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616860 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 1, 6]
def baseStart_3616860 : Nat := 118140960795 + 3616860 * 2 ^ 59
def prefixEnd_3616860 : Nat := 4983230072969 + 3 ^ 40 * 3616860 * 2
def baseEnd_3616860 : Nat := 1238125093347216168210913

theorem tailTrace_3616860 : CollatzResearch.WordTrace tailWord_3616860 prefixEnd_3616860 1238125093347216168210913 := by
  unfold tailWord_3616860
  simp only [CollatzResearch.WordTrace]
  refine ⟨65958860838370702677332017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87945147784494270236442689 65958860838370702677332017)
  ·
    refine ⟨49469145628778027007999013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65958860838370702677332017 49469145628778027007999013)
    ·
      refine ⟨9275464805395880063999815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49469145628778027007999013 9275464805395880063999815)
      ·
        refine ⟨13913197208093820095999723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9275464805395880063999815 13913197208093820095999723)
        ·
          refine ⟨20869795812140730143999585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13913197208093820095999723 20869795812140730143999585)
          ·
            refine ⟨15652346859105547607999689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20869795812140730143999585 15652346859105547607999689)
            ·
              refine ⟨11739260144329160705999767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15652346859105547607999689 11739260144329160705999767)
              ·
                refine ⟨17608890216493741058999651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11739260144329160705999767 17608890216493741058999651)
                ·
                  refine ⟨26413335324740611588499477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17608890216493741058999651 26413335324740611588499477)
                  ·
                    refine ⟨1238125093347216168210913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26413335324740611588499477 1238125093347216168210913)
                    ·
                      rfl

theorem cell22_3616860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_3616860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616860 prefixEnd_3616860 := by exact prefixLift 3616860
  have htrace : WordTrace (prefixWord ++ tailWord_3616860) baseStart_3616860 baseEnd_3616860 := by
    simpa [prefixWord, tailWord_3616860, baseEnd_3616860] using wordTrace_append hprefix tailTrace_3616860
  have hstable : (prefixWord ++ tailWord_3616860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616860).length < 2 ^ (prefixWord ++ tailWord_3616860).sum := by decide
  have hdescent : baseEnd_3616860 < baseStart_3616860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616888 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 2, 6]
def baseStart_3616888 : Nat := 118140960795 + 3616888 * 2 ^ 59
def prefixEnd_3616888 : Nat := 4983230072969 + 3 ^ 40 * 3616888 * 2
def baseEnd_3616888 : Nat := 1238134678319433428510827

theorem tailTrace_3616888 : CollatzResearch.WordTrace tailWord_3616888 prefixEnd_3616888 1238134678319433428510827 := by
  unfold tailWord_3616888
  simp only [CollatzResearch.WordTrace]
  refine ⟨65959371460319983068341659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87945828613759977424455545 65959371460319983068341659)
  ·
    refine ⟨98939057190479974602512489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65959371460319983068341659 98939057190479974602512489)
    ·
      refine ⟨74204292892859980951884367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98939057190479974602512489 74204292892859980951884367)
      ·
        refine ⟨111306439339289971427826551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74204292892859980951884367 111306439339289971427826551)
        ·
          refine ⟨166959659008934957141739827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111306439339289971427826551 166959659008934957141739827)
          ·
            refine ⟨250439488513402435712609741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166959659008934957141739827 250439488513402435712609741)
            ·
              refine ⟨93914808192525913392228653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250439488513402435712609741 93914808192525913392228653)
              ·
                refine ⟨35218053072197217522085745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93914808192525913392228653 35218053072197217522085745)
                ·
                  refine ⟨26413539804147913141564309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35218053072197217522085745 26413539804147913141564309)
                  ·
                    refine ⟨1238134678319433428510827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26413539804147913141564309 1238134678319433428510827)
                    ·
                      rfl

theorem cell22_3616888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_3616888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616888 prefixEnd_3616888 := by exact prefixLift 3616888
  have htrace : WordTrace (prefixWord ++ tailWord_3616888) baseStart_3616888 baseEnd_3616888 := by
    simpa [prefixWord, tailWord_3616888, baseEnd_3616888] using wordTrace_append hprefix tailTrace_3616888
  have hstable : (prefixWord ++ tailWord_3616888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616888).length < 2 ^ (prefixWord ++ tailWord_3616888).sum := by decide
  have hdescent : baseEnd_3616888 < baseStart_3616888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616924 : List Nat := [2, 2, 3, 2, 1, 1, 2, 5, 1, 3]
def baseStart_3616924 : Nat := 118140960795 + 3616924 * 2 ^ 59
def prefixEnd_3616924 : Nat := 4983230072969 + 3 ^ 40 * 3616924 * 2
def baseEnd_3616924 : Nat := 1238147001855141334610717

theorem tailTrace_3616924 : CollatzResearch.WordTrace tailWord_3616924 prefixEnd_3616924 1238147001855141334610717 := by
  unfold tailWord_3616924
  simp only [CollatzResearch.WordTrace]
  refine ⟨65960027974254772142496913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87946703965673029523329217 65960027974254772142496913)
  ·
    refine ⟨49470020980691079106872685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65960027974254772142496913 49470020980691079106872685)
    ·
      refine ⟨18551257867759154665077257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49470020980691079106872685 18551257867759154665077257)
      ·
        refine ⟨13913443400819365998807943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18551257867759154665077257 13913443400819365998807943)
        ·
          refine ⟨20870165101229048998211915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13913443400819365998807943 20870165101229048998211915)
          ·
            refine ⟨31305247651843573497317873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20870165101229048998211915 31305247651843573497317873)
            ·
              refine ⟨23478935738882680122988405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31305247651843573497317873 23478935738882680122988405)
              ·
                refine ⟨2201150225520251261530163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23478935738882680122988405 2201150225520251261530163)
                ·
                  refine ⟨3301725338280376892295245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201150225520251261530163 3301725338280376892295245)
                  ·
                    refine ⟨1238147001855141334610717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3301725338280376892295245 1238147001855141334610717)
                    ·
                      rfl

theorem cell22_3616924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_3616924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616924 prefixEnd_3616924 := by exact prefixLift 3616924
  have htrace : WordTrace (prefixWord ++ tailWord_3616924) baseStart_3616924 baseEnd_3616924 := by
    simpa [prefixWord, tailWord_3616924, baseEnd_3616924] using wordTrace_append hprefix tailTrace_3616924
  have hstable : (prefixWord ++ tailWord_3616924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616924).length < 2 ^ (prefixWord ++ tailWord_3616924).sum := by decide
  have hdescent : baseEnd_3616924 < baseStart_3616924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616941 : List Nat := [1, 5, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_3616941 : Nat := 118140960795 + 3616941 * 2 ^ 59
def prefixEnd_3616941 : Nat := 4983230072969 + 3 ^ 40 * 3616941 * 2
def baseEnd_3616941 : Nat := 1238152821302558956935665

theorem tailTrace_3616941 : CollatzResearch.WordTrace tailWord_3616941 prefixEnd_3616941 1238152821302558956935665 := by
  unfold tailWord_3616941
  simp only [CollatzResearch.WordTrace]
  refine ⟨131920675989447956188362677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87947117326298637458908451 131920675989447956188362677)
  ·
    refine ⟨12367563374010745892659001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131920675989447956188362677 12367563374010745892659001)
    ·
      refine ⟨9275672530508059419494251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12367563374010745892659001 9275672530508059419494251)
      ·
        refine ⟨13913508795762089129241377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9275672530508059419494251 13913508795762089129241377)
        ·
          refine ⟨10435131596821566846931033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13913508795762089129241377 10435131596821566846931033)
          ·
            refine ⟨7826348697616175135198275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10435131596821566846931033 7826348697616175135198275)
            ·
              refine ⟨11739523046424262702797413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7826348697616175135198275 11739523046424262702797413)
              ·
                refine ⟨2201160571204549256774515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11739523046424262702797413 2201160571204549256774515)
                ·
                  refine ⟨3301740856806823885161773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201160571204549256774515 3301740856806823885161773)
                  ·
                    refine ⟨1238152821302558956935665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3301740856806823885161773 1238152821302558956935665)
                    ·
                      rfl

theorem cell22_3616941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_3616941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616941 prefixEnd_3616941 := by exact prefixLift 3616941
  have htrace : WordTrace (prefixWord ++ tailWord_3616941) baseStart_3616941 baseEnd_3616941 := by
    simpa [prefixWord, tailWord_3616941, baseEnd_3616941] using wordTrace_append hprefix tailTrace_3616941
  have hstable : (prefixWord ++ tailWord_3616941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616941).length < 2 ^ (prefixWord ++ tailWord_3616941).sum := by decide
  have hdescent : baseEnd_3616941 < baseStart_3616941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616984 : List Nat := [2, 1, 2, 2, 4, 1, 4, 1, 1, 4]
def baseStart_3616984 : Nat := 118140960795 + 3616984 * 2 ^ 59
def prefixEnd_3616984 : Nat := 4983230072969 + 3 ^ 40 * 3616984 * 2
def baseEnd_3616984 : Nat := 1238167541081321178110533

theorem tailTrace_3616984 : CollatzResearch.WordTrace tailWord_3616984 prefixEnd_3616984 1238167541081321178110533 := by
  unfold tailWord_3616984
  simp only [CollatzResearch.WordTrace]
  refine ⟨65961122164146087266089003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87948162885528116354785337 65961122164146087266089003)
  ·
    refine ⟨98941683246219130899133505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65961122164146087266089003 98941683246219130899133505)
    ·
      refine ⟨74206262434664348174350129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98941683246219130899133505 74206262434664348174350129)
      ·
        refine ⟨55654696825998261130762597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74206262434664348174350129 55654696825998261130762597)
        ·
          refine ⟨10435255654874673962017987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55654696825998261130762597 10435255654874673962017987)
          ·
            refine ⟨15652883482312010943026981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10435255654874673962017987 15652883482312010943026981)
            ·
              refine ⟨2934915652933502051817559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15652883482312010943026981 2934915652933502051817559)
              ·
                refine ⟨4402373479400253077726339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2934915652933502051817559 4402373479400253077726339)
                ·
                  refine ⟨6603560219100379616589509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4402373479400253077726339 6603560219100379616589509)
                  ·
                    refine ⟨1238167541081321178110533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6603560219100379616589509 1238167541081321178110533)
                    ·
                      rfl

theorem cell22_3616984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_3616984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616984 prefixEnd_3616984 := by exact prefixLift 3616984
  have htrace : WordTrace (prefixWord ++ tailWord_3616984) baseStart_3616984 baseEnd_3616984 := by
    simpa [prefixWord, tailWord_3616984, baseEnd_3616984] using wordTrace_append hprefix tailTrace_3616984
  have hstable : (prefixWord ++ tailWord_3616984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616984).length < 2 ^ (prefixWord ++ tailWord_3616984).sum := by decide
  have hdescent : baseEnd_3616984 < baseStart_3616984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616988 : List Nat := [2, 2, 5, 2, 2, 1, 1, 2, 5]
def baseStart_3616988 : Nat := 118140960795 + 3616988 * 2 ^ 59
def prefixEnd_3616988 : Nat := 4983230072969 + 3 ^ 40 * 3616988 * 2
def baseEnd_3616988 : Nat := 412722970121022167003507

theorem tailTrace_3616988 : CollatzResearch.WordTrace tailWord_3616988 prefixEnd_3616988 412722970121022167003507 := by
  unfold tailWord_3616988
  simp only [CollatzResearch.WordTrace]
  refine ⟨65961195110138841607661809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87948260146851788810215745 65961195110138841607661809)
  ·
    refine ⟨49470896332604131205746357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65961195110138841607661809 49470896332604131205746357)
    ·
      refine ⟨4637896531181637300538721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49470896332604131205746357 4637896531181637300538721)
      ·
        refine ⟨3478422398386227975404041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4637896531181637300538721 3478422398386227975404041)
        ·
          refine ⟨2608816798789670981553031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3478422398386227975404041 2608816798789670981553031)
          ·
            refine ⟨3913225198184506472329547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608816798789670981553031 3913225198184506472329547)
            ·
              refine ⟨5869837797276759708494321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3913225198184506472329547 5869837797276759708494321)
              ·
                refine ⟨4402378347957569781370741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5869837797276759708494321 4402378347957569781370741)
                ·
                  refine ⟨412722970121022167003507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4402378347957569781370741 412722970121022167003507)
                  ·
                    rfl

theorem cell22_3616988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_3616988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616988 prefixEnd_3616988 := by exact prefixLift 3616988
  have htrace : WordTrace (prefixWord ++ tailWord_3616988) baseStart_3616988 baseEnd_3616988 := by
    simpa [prefixWord, tailWord_3616988, baseEnd_3616988] using wordTrace_append hprefix tailTrace_3616988
  have hstable : (prefixWord ++ tailWord_3616988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616988).length < 2 ^ (prefixWord ++ tailWord_3616988).sum := by decide
  have hdescent : baseEnd_3616988 < baseStart_3616988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616999 : List Nat := [1, 1, 5, 3, 1, 1, 2, 4, 4]
def baseStart_3616999 : Nat := 118140960795 + 3616999 * 2 ^ 59
def prefixEnd_3616999 : Nat := 4983230072969 + 3 ^ 40 * 3616999 * 2
def baseEnd_3616999 : Nat := 412724225295955379661829

theorem tailTrace_3616999 : CollatzResearch.WordTrace tailWord_3616999 prefixEnd_3616999 412724225295955379661829 := by
  unfold tailWord_3616999
  simp only [CollatzResearch.WordTrace]
  refine ⟨131922791423237832093974051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87948527615491888062649367 131922791423237832093974051)
  ·
    refine ⟨197884187134856748140961077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131922791423237832093974051 197884187134856748140961077)
    ·
      refine ⟨18551642543892820138215101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197884187134856748140961077 18551642543892820138215101)
      ·
        refine ⟨6956865953959807551830663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18551642543892820138215101 6956865953959807551830663)
        ·
          refine ⟨10435298930939711327745995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6956865953959807551830663 10435298930939711327745995)
          ·
            refine ⟨15652948396409566991618993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10435298930939711327745995 15652948396409566991618993)
            ·
              refine ⟨11739711297307175243714245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15652948396409566991618993 11739711297307175243714245)
              ·
                refine ⟨2201195868245095358196421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11739711297307175243714245 2201195868245095358196421)
                ·
                  refine ⟨412724225295955379661829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2201195868245095358196421 412724225295955379661829)
                  ·
                    rfl

theorem cell22_3616999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 4].length) (baseStart_3616999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3616999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3616999 prefixEnd_3616999 := by exact prefixLift 3616999
  have htrace : WordTrace (prefixWord ++ tailWord_3616999) baseStart_3616999 baseEnd_3616999 := by
    simpa [prefixWord, tailWord_3616999, baseEnd_3616999] using wordTrace_append hprefix tailTrace_3616999
  have hstable : (prefixWord ++ tailWord_3616999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616999).length < 2 ^ (prefixWord ++ tailWord_3616999).sum := by decide
  have hdescent : baseEnd_3616999 < baseStart_3616999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617014 : List Nat := [5, 1, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_3617014 : Nat := 118140960795 + 3617014 * 2 ^ 59
def prefixEnd_3617014 : Nat := 4983230072969 + 3 ^ 40 * 3617014 * 2
def baseEnd_3617014 : Nat := 1238177810694411099860441

theorem tailTrace_3617014 : CollatzResearch.WordTrace tailWord_3617014 prefixEnd_3617014 1238177810694411099860441 := by
  unfold tailWord_3617014
  simp only [CollatzResearch.WordTrace]
  refine ⟨8245208657386468103485631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87948892345455659770513397 8245208657386468103485631)
  ·
    refine ⟨12367812986079702155228447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8245208657386468103485631 12367812986079702155228447)
    ·
      refine ⟨18551719479119553232842671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12367812986079702155228447 18551719479119553232842671)
      ·
        refine ⟨27827579218679329849264007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18551719479119553232842671 27827579218679329849264007)
        ·
          refine ⟨41741368828018994773896011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27827579218679329849264007 41741368828018994773896011)
          ·
            refine ⟨62612053242028492160844017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41741368828018994773896011 62612053242028492160844017)
            ·
              refine ⟨46959039931521369120633013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62612053242028492160844017 46959039931521369120633013)
              ·
                refine ⟨4402409993580128355059345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46959039931521369120633013 4402409993580128355059345)
                ·
                  refine ⟨3301807495185096266294509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4402409993580128355059345 3301807495185096266294509)
                  ·
                    refine ⟨1238177810694411099860441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3301807495185096266294509 1238177810694411099860441)
                    ·
                      rfl

theorem cell22_3617014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_3617014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617014 prefixEnd_3617014 := by exact prefixLift 3617014
  have htrace : WordTrace (prefixWord ++ tailWord_3617014) baseStart_3617014 baseEnd_3617014 := by
    simpa [prefixWord, tailWord_3617014, baseEnd_3617014] using wordTrace_append hprefix tailTrace_3617014
  have hstable : (prefixWord ++ tailWord_3617014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617014).length < 2 ^ (prefixWord ++ tailWord_3617014).sum := by decide
  have hdescent : baseEnd_3617014 < baseStart_3617014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617025 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 2, 7]
def baseStart_3617025 : Nat := 118140960795 + 3617025 * 2 ^ 59
def prefixEnd_3617025 : Nat := 4983230072969 + 3 ^ 40 * 3617025 * 2
def baseEnd_3617025 : Nat := 1238181576219210737835407

theorem tailTrace_3617025 : CollatzResearch.WordTrace tailWord_3617025 prefixEnd_3617025 1238181576219210737835407 := by
  unfold tailWord_3617025
  simp only [CollatzResearch.WordTrace]
  refine ⟨131923739721143638534420529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87949159814095759022947019 131923739721143638534420529)
  ·
    refine ⟨98942804790857728900815397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131923739721143638534420529 98942804790857728900815397)
    ·
      refine ⟨18551775898285824168902887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98942804790857728900815397 18551775898285824168902887)
      ·
        refine ⟨27827663847428736253354331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18551775898285824168902887 27827663847428736253354331)
        ·
          refine ⟨41741495771143104380031497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27827663847428736253354331 41741495771143104380031497)
          ·
            refine ⟨31306121828357328285023623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41741495771143104380031497 31306121828357328285023623)
            ·
              refine ⟨46959182742535992427535435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31306121828357328285023623 46959182742535992427535435)
              ·
                refine ⟨70438774113803988641303153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46959182742535992427535435 70438774113803988641303153)
                ·
                  refine ⟨52829080585352991480977365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70438774113803988641303153 52829080585352991480977365)
                  ·
                    refine ⟨1238181576219210737835407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52829080585352991480977365 1238181576219210737835407)
                    ·
                      rfl

theorem cell22_3617025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_3617025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617025 prefixEnd_3617025 := by exact prefixLift 3617025
  have htrace : WordTrace (prefixWord ++ tailWord_3617025) baseStart_3617025 baseEnd_3617025 := by
    simpa [prefixWord, tailWord_3617025, baseEnd_3617025] using wordTrace_append hprefix tailTrace_3617025
  have hstable : (prefixWord ++ tailWord_3617025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617025).length < 2 ^ (prefixWord ++ tailWord_3617025).sum := by decide
  have hdescent : baseEnd_3617025 < baseStart_3617025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617147 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 1, 6]
def baseStart_3617147 : Nat := 118140960795 + 3617147 * 2 ^ 59
def prefixEnd_3617147 : Nat := 4983230072969 + 3 ^ 40 * 3617147 * 2
def baseEnd_3617147 : Nat := 1238223339312443086285033

theorem tailTrace_3617147 : CollatzResearch.WordTrace tailWord_3617147 prefixEnd_3617147 1238223339312443086285033 := by
  unfold tailWord_3617147
  simp only [CollatzResearch.WordTrace]
  refine ⟨131928189426701653370361695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87952126284467768913574463 131928189426701653370361695)
  ·
    refine ⟨197892284140052480055542543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131928189426701653370361695 197892284140052480055542543)
    ·
      refine ⟨296838426210078720083313815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197892284140052480055542543 296838426210078720083313815)
      ·
        refine ⟨445257639315118080124970723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296838426210078720083313815 445257639315118080124970723)
        ·
          refine ⟨667886458972677120187456085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445257639315118080124970723 667886458972677120187456085)
          ·
            refine ⟨7826794441086060002196751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 667886458972677120187456085 7826794441086060002196751)
            ·
              refine ⟨11740191661629090003295127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7826794441086060002196751 11740191661629090003295127)
              ·
                refine ⟨17610287492443635004942691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11740191661629090003295127 17610287492443635004942691)
                ·
                  refine ⟨26415431238665452507414037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17610287492443635004942691 26415431238665452507414037)
                  ·
                    refine ⟨1238223339312443086285033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26415431238665452507414037 1238223339312443086285033)
                    ·
                      rfl

theorem cell22_3617147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 6].length) (baseStart_3617147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617147 prefixEnd_3617147 := by exact prefixLift 3617147
  have htrace : WordTrace (prefixWord ++ tailWord_3617147) baseStart_3617147 baseEnd_3617147 := by
    simpa [prefixWord, tailWord_3617147, baseEnd_3617147] using wordTrace_append hprefix tailTrace_3617147
  have hstable : (prefixWord ++ tailWord_3617147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617147).length < 2 ^ (prefixWord ++ tailWord_3617147).sum := by decide
  have hdescent : baseEnd_3617147 < baseStart_3617147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617153 : List Nat := [1, 2, 4, 3, 1, 3, 2, 1, 1, 4]
def baseStart_3617153 : Nat := 118140960795 + 3617153 * 2 ^ 59
def prefixEnd_3617153 : Nat := 4983230072969 + 3 ^ 40 * 3617153 * 2
def baseEnd_3617153 : Nat := 1238225393235061070635015

theorem tailTrace_3617153 : CollatzResearch.WordTrace tailWord_3617153 prefixEnd_3617153 1238225393235061070635015 := by
  unfold tailWord_3617153
  simp only [CollatzResearch.WordTrace]
  refine ⟨131928408264679916395080113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87952272176453277596720075 131928408264679916395080113)
  ·
    refine ⟨98946306198509937296310085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131928408264679916395080113 98946306198509937296310085)
    ·
      refine ⟨18552432412220613243058141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98946306198509937296310085 18552432412220613243058141)
      ·
        refine ⟨6957162154582729966146803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18552432412220613243058141 6957162154582729966146803)
        ·
          refine ⟨10435743231874094949220205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6957162154582729966146803 10435743231874094949220205)
          ·
            refine ⟨3913403711952785605957577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10435743231874094949220205 3913403711952785605957577)
            ·
              refine ⟨2935052783964589204468183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3913403711952785605957577 2935052783964589204468183)
              ·
                refine ⟨4402579175946883806702275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2935052783964589204468183 4402579175946883806702275)
                ·
                  refine ⟨6603868763920325710053413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4402579175946883806702275 6603868763920325710053413)
                  ·
                    refine ⟨1238225393235061070635015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6603868763920325710053413 1238225393235061070635015)
                    ·
                      rfl

theorem cell22_3617153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_3617153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617153 prefixEnd_3617153 := by exact prefixLift 3617153
  have htrace : WordTrace (prefixWord ++ tailWord_3617153) baseStart_3617153 baseEnd_3617153 := by
    simpa [prefixWord, tailWord_3617153, baseEnd_3617153] using wordTrace_append hprefix tailTrace_3617153
  have hstable : (prefixWord ++ tailWord_3617153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617153).length < 2 ^ (prefixWord ++ tailWord_3617153).sum := by decide
  have hdescent : baseEnd_3617153 < baseStart_3617153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617166 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 4, 3]
def baseStart_3617166 : Nat := 118140960795 + 3617166 * 2 ^ 59
def prefixEnd_3617166 : Nat := 4983230072969 + 3 ^ 40 * 3617166 * 2
def baseEnd_3617166 : Nat := 1238229843400733370059975

theorem tailTrace_3617166 : CollatzResearch.WordTrace tailWord_3617166 prefixEnd_3617166 1238229843400733370059975 := by
  unfold tailWord_3617166
  simp only [CollatzResearch.WordTrace]
  refine ⟨16491110301704102451912919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87952588275755213076868901 16491110301704102451912919)
  ·
    refine ⟨24736665452556153677869379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16491110301704102451912919 24736665452556153677869379)
    ·
      refine ⟨37104998178834230516804069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24736665452556153677869379 37104998178834230516804069)
      ·
        refine ⟨6957187158531418221900763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37104998178834230516804069 6957187158531418221900763)
        ·
          refine ⟨10435780737797127332851145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6957187158531418221900763 10435780737797127332851145)
          ·
            refine ⟨7826835553347845499638359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10435780737797127332851145 7826835553347845499638359)
            ·
              refine ⟨11740253330021768249457539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7826835553347845499638359 11740253330021768249457539)
              ·
                refine ⟨17610379995032652374186309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11740253330021768249457539 17610379995032652374186309)
                ·
                  refine ⟨3301946249068622320159933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17610379995032652374186309 3301946249068622320159933)
                  ·
                    refine ⟨1238229843400733370059975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3301946249068622320159933 1238229843400733370059975)
                    ·
                      rfl

theorem cell22_3617166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_3617166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617166 prefixEnd_3617166 := by exact prefixLift 3617166
  have htrace : WordTrace (prefixWord ++ tailWord_3617166) baseStart_3617166 baseEnd_3617166 := by
    simpa [prefixWord, tailWord_3617166, baseEnd_3617166] using wordTrace_append hprefix tailTrace_3617166
  have hstable : (prefixWord ++ tailWord_3617166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617166).length < 2 ^ (prefixWord ++ tailWord_3617166).sum := by decide
  have hdescent : baseEnd_3617166 < baseStart_3617166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617207 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 7]
def baseStart_3617207 : Nat := 118140960795 + 3617207 * 2 ^ 59
def prefixEnd_3617207 : Nat := 4983230072969 + 3 ^ 40 * 3617207 * 2
def baseEnd_3617207 : Nat := 412747959512874309928283

theorem tailTrace_3617207 : CollatzResearch.WordTrace tailWord_3617207 prefixEnd_3617207 412747959512874309928283 := by
  unfold tailWord_3617207
  simp only [CollatzResearch.WordTrace]
  refine ⟨131930377806484283617545875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87953585204322855745030583 131930377806484283617545875)
  ·
    refine ⟨197895566709726425426318813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131930377806484283617545875 197895566709726425426318813)
    ·
      refine ⟨74210837516147409534869555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197895566709726425426318813 74210837516147409534869555)
      ·
        refine ⟨111316256274221114302304333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74210837516147409534869555 111316256274221114302304333)
        ·
          refine ⟨41743596102832917863364125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111316256274221114302304333 41743596102832917863364125)
          ·
            refine ⟨15653848538562344198761547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41743596102832917863364125 15653848538562344198761547)
            ·
              refine ⟨23480772807843516298142321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15653848538562344198761547 23480772807843516298142321)
              ·
                refine ⟨17610579605882637223606741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23480772807843516298142321 17610579605882637223606741)
                ·
                  refine ⟨412747959512874309928283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17610579605882637223606741 412747959512874309928283)
                  ·
                    rfl

theorem cell22_3617207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 7].length) (baseStart_3617207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617207 prefixEnd_3617207 := by exact prefixLift 3617207
  have htrace : WordTrace (prefixWord ++ tailWord_3617207) baseStart_3617207 baseEnd_3617207 := by
    simpa [prefixWord, tailWord_3617207, baseEnd_3617207] using wordTrace_append hprefix tailTrace_3617207
  have hstable : (prefixWord ++ tailWord_3617207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617207).length < 2 ^ (prefixWord ++ tailWord_3617207).sum := by decide
  have hdescent : baseEnd_3617207 < baseStart_3617207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617228 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 3, 3]
def baseStart_3617228 : Nat := 118140960795 + 3617228 * 2 ^ 59
def prefixEnd_3617228 : Nat := 4983230072969 + 3 ^ 40 * 3617228 * 2
def baseEnd_3617228 : Nat := 1238251067267785875009785

theorem tailTrace_3617228 : CollatzResearch.WordTrace tailWord_3617228 prefixEnd_3617228 1238251067267785875009785 := by
  unfold tailWord_3617228
  simp only [CollatzResearch.WordTrace]
  refine ⟨65965571869704102102030169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87954095826272136136040225 65965571869704102102030169)
  ·
    refine ⟨49474178902278076576522627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65965571869704102102030169 49474178902278076576522627)
    ·
      refine ⟨74211268353417114864783941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49474178902278076576522627 74211268353417114864783941)
      ·
        refine ⟨13914612816265709037146989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74211268353417114864783941 13914612816265709037146989)
        ·
          refine ⟨5217979806099640888930121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13914612816265709037146989 5217979806099640888930121)
          ·
            refine ⟨3913484854574730666697591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5217979806099640888930121 3913484854574730666697591)
            ·
              refine ⟨5870227281862096000046387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3913484854574730666697591 5870227281862096000046387)
              ·
                refine ⟨8805340922793144000069581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5870227281862096000046387 8805340922793144000069581)
                ·
                  refine ⟨3302002846047429000026093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8805340922793144000069581 3302002846047429000026093)
                  ·
                    refine ⟨1238251067267785875009785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3302002846047429000026093 1238251067267785875009785)
                    ·
                      rfl

theorem cell22_3617228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_3617228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617228 prefixEnd_3617228 := by exact prefixLift 3617228
  have htrace : WordTrace (prefixWord ++ tailWord_3617228) baseStart_3617228 baseEnd_3617228 := by
    simpa [prefixWord, tailWord_3617228, baseEnd_3617228] using wordTrace_append hprefix tailTrace_3617228
  have hstable : (prefixWord ++ tailWord_3617228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617228).length < 2 ^ (prefixWord ++ tailWord_3617228).sum := by decide
  have hdescent : baseEnd_3617228 < baseStart_3617228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617297 : List Nat := [1, 2, 2, 1, 1, 2, 2, 11]
def baseStart_3617297 : Nat := 118140960795 + 3617297 * 2 ^ 59
def prefixEnd_3617297 : Nat := 4983230072969 + 3 ^ 40 * 3617297 * 2
def baseEnd_3617297 : Nat := 137586076375321410559397

theorem tailTrace_3617297 : CollatzResearch.WordTrace tailWord_3617297 prefixEnd_3617297 137586076375321410559397 := by
  unfold tailWord_3617297
  simp only [CollatzResearch.WordTrace]
  refine ⟨131933660376158228988322145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87955773584105485992214763 131933660376158228988322145)
  ·
    refine ⟨98950245282118671741241609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131933660376158228988322145 98950245282118671741241609)
    ·
      refine ⟨74212683961589003805931207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98950245282118671741241609 74212683961589003805931207)
      ·
        refine ⟨111319025942383505708896811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74212683961589003805931207 111319025942383505708896811)
        ·
          refine ⟨166978538913575258563345217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111319025942383505708896811 166978538913575258563345217)
          ·
            refine ⟨125233904185181443922508913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166978538913575258563345217 125233904185181443922508913)
            ·
              refine ⟨93925428138886082941881685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125233904185181443922508913 93925428138886082941881685)
              ·
                refine ⟨137586076375321410559397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 93925428138886082941881685 137586076375321410559397)
                ·
                  rfl

theorem cell22_3617297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 11].length) (baseStart_3617297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617297 prefixEnd_3617297 := by exact prefixLift 3617297
  have htrace : WordTrace (prefixWord ++ tailWord_3617297) baseStart_3617297 baseEnd_3617297 := by
    simpa [prefixWord, tailWord_3617297, baseEnd_3617297] using wordTrace_append hprefix tailTrace_3617297
  have hstable : (prefixWord ++ tailWord_3617297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617297).length < 2 ^ (prefixWord ++ tailWord_3617297).sum := by decide
  have hdescent : baseEnd_3617297 < baseStart_3617297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617301 : List Nat := [1, 3, 2, 1, 3, 1, 1, 5, 2, 3]
def baseStart_3617301 : Nat := 118140960795 + 3617301 * 2 ^ 59
def prefixEnd_3617301 : Nat := 4983230072969 + 3 ^ 40 * 3617301 * 2
def baseEnd_3617301 : Nat := 1238276056659638017934561

theorem tailTrace_3617301 : CollatzResearch.WordTrace tailWord_3617301 prefixEnd_3617301 1238276056659638017934561 := by
  unfold tailWord_3617301
  simp only [CollatzResearch.WordTrace]
  refine ⟨131933806268143737671467757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87955870845429158447645171 131933806268143737671467757)
  ·
    refine ⟨49475177350553901626800409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131933806268143737671467757 49475177350553901626800409)
    ·
      refine ⟨37106383012915426220100307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49475177350553901626800409 37106383012915426220100307)
      ·
        refine ⟨55659574519373139330150461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37106383012915426220100307 55659574519373139330150461)
        ·
          refine ⟨20872340444764927248806423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55659574519373139330150461 20872340444764927248806423)
          ·
            refine ⟨31308510667147390873209635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20872340444764927248806423 31308510667147390873209635)
            ·
              refine ⟨46962766000721086309814453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31308510667147390873209635 46962766000721086309814453)
              ·
                refine ⟨4402759312567601841545105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46962766000721086309814453 4402759312567601841545105)
                ·
                  refine ⟨3302069484425701381158829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4402759312567601841545105 3302069484425701381158829)
                  ·
                    refine ⟨1238276056659638017934561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3302069484425701381158829 1238276056659638017934561)
                    ·
                      rfl

theorem cell22_3617301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_3617301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617301 prefixEnd_3617301 := by exact prefixLift 3617301
  have htrace : WordTrace (prefixWord ++ tailWord_3617301) baseStart_3617301 baseEnd_3617301 := by
    simpa [prefixWord, tailWord_3617301, baseEnd_3617301] using wordTrace_append hprefix tailTrace_3617301
  have hstable : (prefixWord ++ tailWord_3617301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617301).length < 2 ^ (prefixWord ++ tailWord_3617301).sum := by decide
  have hdescent : baseEnd_3617301 < baseStart_3617301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617359 : List Nat := [1, 1, 2, 1, 1, 2, 4, 5, 5]
def baseStart_3617359 : Nat := 118140960795 + 3617359 * 2 ^ 59
def prefixEnd_3617359 : Nat := 4983230072969 + 3 ^ 40 * 3617359 * 2
def baseEnd_3617359 : Nat := 412765303748315066661461

theorem tailTrace_3617359 : CollatzResearch.WordTrace tailWord_3617359 prefixEnd_3617359 412765303748315066661461 := by
  unfold tailWord_3617359
  simp only [CollatzResearch.WordTrace]
  refine ⟨131935921701933613577079131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87957281134622409051386087 131935921701933613577079131)
  ·
    refine ⟨197903882552900420365618697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131935921701933613577079131 197903882552900420365618697)
    ·
      refine ⟨148427911914675315274214023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197903882552900420365618697 148427911914675315274214023)
      ·
        refine ⟨222641867872012972911321035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148427911914675315274214023 222641867872012972911321035)
        ·
          refine ⟨333962801808019459366981553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222641867872012972911321035 333962801808019459366981553)
          ·
            refine ⟨250472101356014594525236165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333962801808019459366981553 250472101356014594525236165)
            ·
              refine ⟨46963519004252736473481781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250472101356014594525236165 46963519004252736473481781)
              ·
                refine ⟨4402829906648694044388917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46963519004252736473481781 4402829906648694044388917)
                ·
                  refine ⟨412765303748315066661461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4402829906648694044388917 412765303748315066661461)
                  ·
                    rfl

theorem cell22_3617359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 5].length) (baseStart_3617359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617359 prefixEnd_3617359 := by exact prefixLift 3617359
  have htrace : WordTrace (prefixWord ++ tailWord_3617359) baseStart_3617359 baseEnd_3617359 := by
    simpa [prefixWord, tailWord_3617359, baseEnd_3617359] using wordTrace_append hprefix tailTrace_3617359
  have hstable : (prefixWord ++ tailWord_3617359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617359).length < 2 ^ (prefixWord ++ tailWord_3617359).sum := by decide
  have hdescent : baseEnd_3617359 < baseStart_3617359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617397 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 3, 3]
def baseStart_3617397 : Nat := 118140960795 + 3617397 * 2 ^ 59
def prefixEnd_3617397 : Nat := 4983230072969 + 3 ^ 40 * 3617397 * 2
def baseEnd_3617397 : Nat := 1238308919421525767534267

theorem tailTrace_3617397 : CollatzResearch.WordTrace tailWord_3617397 prefixEnd_3617397 1238308919421525767534267 := by
  unfold tailWord_3617397
  simp only [CollatzResearch.WordTrace]
  refine ⟨131937307675795946066962445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87958205117197297377974963 131937307675795946066962445)
  ·
    refine ⟨49476490378423479775110917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131937307675795946066962445 49476490378423479775110917)
    ·
      refine ⟨9276841945954402457833297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49476490378423479775110917 9276841945954402457833297)
      ·
        refine ⟨6957631459465801843374973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9276841945954402457833297 6957631459465801843374973)
        ·
          refine ⟨2609111797299675691265615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6957631459465801843374973 2609111797299675691265615)
          ·
            refine ⟨3913667695949513536898423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609111797299675691265615 3913667695949513536898423)
            ·
              refine ⟨5870501543924270305347635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3913667695949513536898423 5870501543924270305347635)
              ·
                refine ⟨8805752315886405458021453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5870501543924270305347635 8805752315886405458021453)
                ·
                  refine ⟨3302157118457402046758045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8805752315886405458021453 3302157118457402046758045)
                  ·
                    refine ⟨1238308919421525767534267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3302157118457402046758045 1238308919421525767534267)
                    ·
                      rfl

theorem cell22_3617397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_3617397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617397 prefixEnd_3617397 := by exact prefixLift 3617397
  have htrace : WordTrace (prefixWord ++ tailWord_3617397) baseStart_3617397 baseEnd_3617397 := by
    simpa [prefixWord, tailWord_3617397, baseEnd_3617397] using wordTrace_append hprefix tailTrace_3617397
  have hstable : (prefixWord ++ tailWord_3617397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617397).length < 2 ^ (prefixWord ++ tailWord_3617397).sum := by decide
  have hdescent : baseEnd_3617397 < baseStart_3617397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617436 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 3, 5]
def baseStart_3617436 : Nat := 118140960795 + 3617436 * 2 ^ 59
def prefixEnd_3617436 : Nat := 4983230072969 + 3 ^ 40 * 3617436 * 2
def baseEnd_3617436 : Nat := 1238322269918542665809147

theorem tailTrace_3617436 : CollatzResearch.WordTrace tailWord_3617436 prefixEnd_3617436 1238322269918542665809147 := by
  unfold tailWord_3617436
  simp only [CollatzResearch.WordTrace]
  refine ⟨65969365061327327863816081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87959153415103103818421441 65969365061327327863816081)
  ·
    refine ⟨49477023795995495897862061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65969365061327327863816081 49477023795995495897862061)
    ·
      refine ⟨18553883923498310961698273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49477023795995495897862061 18553883923498310961698273)
      ·
        refine ⟨13915412942623733221273705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18553883923498310961698273 13915412942623733221273705)
        ·
          refine ⟨10436559706967799915955279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13915412942623733221273705 10436559706967799915955279)
          ·
            refine ⟨15654839560451699873932919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10436559706967799915955279 15654839560451699873932919)
            ·
              refine ⟨23482259340677549810899379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15654839560451699873932919 23482259340677549810899379)
              ·
                refine ⟨35223389011016324716349069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23482259340677549810899379 35223389011016324716349069)
                ·
                  refine ⟨13208770879131121768630901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35223389011016324716349069 13208770879131121768630901)
                  ·
                    refine ⟨1238322269918542665809147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13208770879131121768630901 1238322269918542665809147)
                    ·
                      rfl

theorem cell22_3617436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_3617436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617436 prefixEnd_3617436 := by exact prefixLift 3617436
  have htrace : WordTrace (prefixWord ++ tailWord_3617436) baseStart_3617436 baseEnd_3617436 := by
    simpa [prefixWord, tailWord_3617436, baseEnd_3617436] using wordTrace_append hprefix tailTrace_3617436
  have hstable : (prefixWord ++ tailWord_3617436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617436).length < 2 ^ (prefixWord ++ tailWord_3617436).sum := by decide
  have hdescent : baseEnd_3617436 < baseStart_3617436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617440 : List Nat := [2, 1, 1, 4, 4, 1, 3, 1, 1, 4]
def baseStart_3617440 : Nat := 118140960795 + 3617440 * 2 ^ 59
def prefixEnd_3617440 : Nat := 4983230072969 + 3 ^ 40 * 3617440 * 2
def baseEnd_3617440 : Nat := 1238323639200287988709135

theorem tailTrace_3617440 : CollatzResearch.WordTrace tailWord_3617440 prefixEnd_3617440 1238323639200287988709135 := by
  unfold tailWord_3617440
  simp only [CollatzResearch.WordTrace]
  refine ⟨65969438007320082205388887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87959250676426776273851849 65969438007320082205388887)
  ·
    refine ⟨98954157010980123308083331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65969438007320082205388887 98954157010980123308083331)
    ·
      refine ⟨148431235516470184962124997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98954157010980123308083331 148431235516470184962124997)
      ·
        refine ⟨27830856659338159680398437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148431235516470184962124997 27830856659338159680398437)
        ·
          refine ⟨5218285623625904940074707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27830856659338159680398437 5218285623625904940074707)
          ·
            refine ⟨7827428435438857410112061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5218285623625904940074707 7827428435438857410112061)
            ·
              refine ⟨2935285663289571528792023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7827428435438857410112061 2935285663289571528792023)
              ·
                refine ⟨4402928494934357293188035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2935285663289571528792023 4402928494934357293188035)
                ·
                  refine ⟨6604392742401535939782053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4402928494934357293188035 6604392742401535939782053)
                  ·
                    refine ⟨1238323639200287988709135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6604392742401535939782053 1238323639200287988709135)
                    ·
                      rfl

theorem cell22_3617440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 1, 4].length) (baseStart_3617440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617440 prefixEnd_3617440 := by exact prefixLift 3617440
  have htrace : WordTrace (prefixWord ++ tailWord_3617440) baseStart_3617440 baseEnd_3617440 := by
    simpa [prefixWord, tailWord_3617440, baseEnd_3617440] using wordTrace_append hprefix tailTrace_3617440
  have hstable : (prefixWord ++ tailWord_3617440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617440).length < 2 ^ (prefixWord ++ tailWord_3617440).sum := by decide
  have hdescent : baseEnd_3617440 < baseStart_3617440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617455 : List Nat := [1, 1, 2, 1, 2, 7, 2, 2, 4]
def baseStart_3617455 : Nat := 118140960795 + 3617455 * 2 ^ 59
def prefixEnd_3617455 : Nat := 4983230072969 + 3 ^ 40 * 3617455 * 2
def baseEnd_3617455 : Nat := 412776258002277649861363

theorem tailTrace_3617455 : CollatzResearch.WordTrace tailWord_3617455 prefixEnd_3617455 412776258002277649861363 := by
  unfold tailWord_3617455
  simp only [CollatzResearch.WordTrace]
  refine ⟨131939423109585821972573819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87959615406390547981715879 131939423109585821972573819)
  ·
    refine ⟨197909134664378732958860729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131939423109585821972573819 197909134664378732958860729)
    ·
      refine ⟨148431850998284049719145547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197909134664378732958860729 148431850998284049719145547)
      ·
        refine ⟨222647776497426074578718321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148431850998284049719145547 222647776497426074578718321)
        ·
          refine ⟨166985832373069555934038741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222647776497426074578718321 166985832373069555934038741)
          ·
            refine ⟨3913730446243817717204033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 166985832373069555934038741 3913730446243817717204033)
            ·
              refine ⟨2935297834682863287903025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3913730446243817717204033 2935297834682863287903025)
              ·
                refine ⟨2201473376012147465927269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2935297834682863287903025 2201473376012147465927269)
                ·
                  refine ⟨412776258002277649861363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2201473376012147465927269 412776258002277649861363)
                  ·
                    rfl

theorem cell22_3617455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 4].length) (baseStart_3617455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617455 prefixEnd_3617455 := by exact prefixLift 3617455
  have htrace : WordTrace (prefixWord ++ tailWord_3617455) baseStart_3617455 baseEnd_3617455 := by
    simpa [prefixWord, tailWord_3617455, baseEnd_3617455] using wordTrace_append hprefix tailTrace_3617455
  have hstable : (prefixWord ++ tailWord_3617455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617455).length < 2 ^ (prefixWord ++ tailWord_3617455).sum := by decide
  have hdescent : baseEnd_3617455 < baseStart_3617455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617464 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 4, 7]
def baseStart_3617464 : Nat := 118140960795 + 3617464 * 2 ^ 59
def prefixEnd_3617464 : Nat := 4983230072969 + 3 ^ 40 * 3617464 * 2
def baseEnd_3617464 : Nat := 1238331854890759926109061

theorem tailTrace_3617464 : CollatzResearch.WordTrace tailWord_3617464 prefixEnd_3617464 1238331854890759926109061 := by
  unfold tailWord_3617464
  simp only [CollatzResearch.WordTrace]
  refine ⟨65969875683276608254825723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87959834244368811006434297 65969875683276608254825723)
  ·
    refine ⟨98954813524914912382238585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65969875683276608254825723 98954813524914912382238585)
    ·
      refine ⟨74216110143686184286678939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98954813524914912382238585 74216110143686184286678939)
      ·
        refine ⟨111324165215529276430018409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74216110143686184286678939 111324165215529276430018409)
        ·
          refine ⟨83493123911646957322513807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111324165215529276430018409 83493123911646957322513807)
          ·
            refine ⟨125239685867470435983770711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83493123911646957322513807 125239685867470435983770711)
            ·
              refine ⟨187859528801205653975656067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125239685867470435983770711 187859528801205653975656067)
              ·
                refine ⟨281789293201808480963484101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187859528801205653975656067 281789293201808480963484101)
                ·
                  refine ⟨52835492475339090180653269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281789293201808480963484101 52835492475339090180653269)
                  ·
                    refine ⟨1238331854890759926109061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52835492475339090180653269 1238331854890759926109061)
                    ·
                      rfl

theorem cell22_3617464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_3617464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617464 prefixEnd_3617464 := by exact prefixLift 3617464
  have htrace : WordTrace (prefixWord ++ tailWord_3617464) baseStart_3617464 baseEnd_3617464 := by
    simpa [prefixWord, tailWord_3617464, baseEnd_3617464] using wordTrace_append hprefix tailTrace_3617464
  have hstable : (prefixWord ++ tailWord_3617464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617464).length < 2 ^ (prefixWord ++ tailWord_3617464).sum := by decide
  have hdescent : baseEnd_3617464 < baseStart_3617464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617485 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_3617485 : Nat := 118140960795 + 3617485 * 2 ^ 59
def prefixEnd_3617485 : Nat := 4983230072969 + 3 ^ 40 * 3617485 * 2
def baseEnd_3617485 : Nat := 1238339043619922871333997

theorem tailTrace_3617485 : CollatzResearch.WordTrace tailWord_3617485 prefixEnd_3617485 1238339043619922871333997 := by
  unfold tailWord_3617485
  simp only [CollatzResearch.WordTrace]
  refine ⟨131940517299477137096165909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87960344866318091397443939 131940517299477137096165909)
  ·
    refine ⟨6184711748412990801382777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131940517299477137096165909 6184711748412990801382777)
    ·
      refine ⟨4638533811309743101037083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6184711748412990801382777 4638533811309743101037083)
      ·
        refine ⟨6957800716964614651555625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4638533811309743101037083 6957800716964614651555625)
        ·
          refine ⟨5218350537723460988666719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6957800716964614651555625 5218350537723460988666719)
          ·
            refine ⟨7827525806585191483000079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5218350537723460988666719 7827525806585191483000079)
            ·
              refine ⟨11741288709877787224500119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7827525806585191483000079 11741288709877787224500119)
              ·
                refine ⟨17611933064816680836750179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11741288709877787224500119 17611933064816680836750179)
                ·
                  refine ⟨26417899597225021255125269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17611933064816680836750179 26417899597225021255125269)
                  ·
                    refine ⟨1238339043619922871333997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26417899597225021255125269 1238339043619922871333997)
                    ·
                      rfl

theorem cell22_3617485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_3617485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617485 prefixEnd_3617485 := by exact prefixLift 3617485
  have htrace : WordTrace (prefixWord ++ tailWord_3617485) baseStart_3617485 baseEnd_3617485 := by
    simpa [prefixWord, tailWord_3617485, baseEnd_3617485] using wordTrace_append hprefix tailTrace_3617485
  have hstable : (prefixWord ++ tailWord_3617485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617485).length < 2 ^ (prefixWord ++ tailWord_3617485).sum := by decide
  have hdescent : baseEnd_3617485 < baseStart_3617485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617528 : List Nat := [2, 1, 2, 1, 1, 2, 7, 1, 5]
def baseStart_3617528 : Nat := 118140960795 + 3617528 * 2 ^ 59
def prefixEnd_3617528 : Nat := 4983230072969 + 3 ^ 40 * 3617528 * 2
def baseEnd_3617528 : Nat := 412784587799561697502955

theorem tailTrace_3617528 : CollatzResearch.WordTrace tailWord_3617528 prefixEnd_3617528 412784587799561697502955 := by
  unfold tailWord_3617528
  simp only [CollatzResearch.WordTrace]
  refine ⟨65971042819160677719990619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87961390425547570293320825 65971042819160677719990619)
  ·
    refine ⟨98956564228741016579985929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65971042819160677719990619 98956564228741016579985929)
    ·
      refine ⟨74217423171555762434989447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98956564228741016579985929 74217423171555762434989447)
      ·
        refine ⟨111326134757333643652484171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74217423171555762434989447 111326134757333643652484171)
        ·
          refine ⟨166989202136000465478726257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111326134757333643652484171 166989202136000465478726257)
          ·
            refine ⟨125241901602000349109044693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166989202136000465478726257 125241901602000349109044693)
            ·
              refine ⟨2935357068796883182243235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 125241901602000349109044693 2935357068796883182243235)
              ·
                refine ⟨4403035603195324773364853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2935357068796883182243235 4403035603195324773364853)
                ·
                  refine ⟨412784587799561697502955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4403035603195324773364853 412784587799561697502955)
                  ·
                    rfl

theorem cell22_3617528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 5].length) (baseStart_3617528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617528 prefixEnd_3617528 := by exact prefixLift 3617528
  have htrace : WordTrace (prefixWord ++ tailWord_3617528) baseStart_3617528 baseEnd_3617528 := by
    simpa [prefixWord, tailWord_3617528, baseEnd_3617528] using wordTrace_append hprefix tailTrace_3617528
  have hstable : (prefixWord ++ tailWord_3617528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617528).length < 2 ^ (prefixWord ++ tailWord_3617528).sum := by decide
  have hdescent : baseEnd_3617528 < baseStart_3617528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617541 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 3, 4]
def baseStart_3617541 : Nat := 118140960795 + 3617541 * 2 ^ 59
def prefixEnd_3617541 : Nat := 4983230072969 + 3 ^ 40 * 3617541 * 2
def baseEnd_3617541 : Nat := 1238358213564357391933825

theorem tailTrace_3617541 : CollatzResearch.WordTrace tailWord_3617541 prefixEnd_3617541 1238358213564357391933825 := by
  unfold tailWord_3617541
  simp only [CollatzResearch.WordTrace]
  refine ⟨131942559787274258660204477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87961706524849505773469651 131942559787274258660204477)
  ·
    refine ⟨49478459920227846997576679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131942559787274258660204477 49478459920227846997576679)
    ·
      refine ⟨74217689880341770496365019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49478459920227846997576679 74217689880341770496365019)
      ·
        refine ⟨111326534820512655744547529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74217689880341770496365019 111326534820512655744547529)
        ·
          refine ⟨83494901115384491808410647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111326534820512655744547529 83494901115384491808410647)
          ·
            refine ⟨125242351673076737712615971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83494901115384491808410647 125242351673076737712615971)
            ·
              refine ⟨187863527509615106568923957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125242351673076737712615971 187863527509615106568923957)
              ·
                refine ⟨17612205704026416240836621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187863527509615106568923957 17612205704026416240836621)
                ·
                  refine ⟨6604577139009906090313733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17612205704026416240836621 6604577139009906090313733)
                  ·
                    refine ⟨1238358213564357391933825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6604577139009906090313733 1238358213564357391933825)
                    ·
                      rfl

theorem cell22_3617541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_3617541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617541 prefixEnd_3617541 := by exact prefixLift 3617541
  have htrace : WordTrace (prefixWord ++ tailWord_3617541) baseStart_3617541 baseEnd_3617541 := by
    simpa [prefixWord, tailWord_3617541, baseEnd_3617541] using wordTrace_append hprefix tailTrace_3617541
  have hstable : (prefixWord ++ tailWord_3617541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617541).length < 2 ^ (prefixWord ++ tailWord_3617541).sum := by decide
  have hdescent : baseEnd_3617541 < baseStart_3617541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617603 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 2, 4]
def baseStart_3617603 : Nat := 118140960795 + 3617603 * 2 ^ 59
def prefixEnd_3617603 : Nat := 4983230072969 + 3 ^ 40 * 3617603 * 2
def baseEnd_3617603 : Nat := 1238379437431409896883635

theorem tailTrace_3617603 : CollatzResearch.WordTrace tailWord_3617603 prefixEnd_3617603 1238379437431409896883635 := by
  unfold tailWord_3617603
  simp only [CollatzResearch.WordTrace]
  refine ⟨131944821113049643248961463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87963214075366428832640975 131944821113049643248961463)
  ·
    refine ⟨197917231669574464873442195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131944821113049643248961463 197917231669574464873442195)
    ·
      refine ⟨296875847504361697310163293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197917231669574464873442195 296875847504361697310163293)
      ·
        refine ⟨111328442814135636491311235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296875847504361697310163293 111328442814135636491311235)
        ·
          refine ⟨166992664221203454736966853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111328442814135636491311235 166992664221203454736966853)
          ·
            refine ⟨31311124541475647763181285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166992664221203454736966853 31311124541475647763181285)
            ·
              refine ⟨5870835851526683955596491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31311124541475647763181285 5870835851526683955596491)
              ·
                refine ⟨8806253777290025933394737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5870835851526683955596491 8806253777290025933394737)
                ·
                  refine ⟨6604690332967519450046053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8806253777290025933394737 6604690332967519450046053)
                  ·
                    refine ⟨1238379437431409896883635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6604690332967519450046053 1238379437431409896883635)
                    ·
                      rfl

theorem cell22_3617603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 4].length) (baseStart_3617603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617603 prefixEnd_3617603 := by exact prefixLift 3617603
  have htrace : WordTrace (prefixWord ++ tailWord_3617603) baseStart_3617603 baseEnd_3617603 := by
    simpa [prefixWord, tailWord_3617603, baseEnd_3617603] using wordTrace_append hprefix tailTrace_3617603
  have hstable : (prefixWord ++ tailWord_3617603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617603).length < 2 ^ (prefixWord ++ tailWord_3617603).sum := by decide
  have hdescent : baseEnd_3617603 < baseStart_3617603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617631 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 1, 8]
def baseStart_3617631 : Nat := 118140960795 + 3617631 * 2 ^ 59
def prefixEnd_3617631 : Nat := 4983230072969 + 3 ^ 40 * 3617631 * 2
def baseEnd_3617631 : Nat := 1238389022403627157183549

theorem tailTrace_3617631 : CollatzResearch.WordTrace tailWord_3617631 prefixEnd_3617631 1238389022403627157183549 := by
  unfold tailWord_3617631
  simp only [CollatzResearch.WordTrace]
  refine ⟨131945842356948204030980747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87963894904632136020653831 131945842356948204030980747)
  ·
    refine ⟨197918763535422306046471121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131945842356948204030980747 197918763535422306046471121)
    ·
      refine ⟨148439072651566729534853341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197918763535422306046471121 148439072651566729534853341)
      ·
        refine ⟨55664652244337523575570003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148439072651566729534853341 55664652244337523575570003)
        ·
          refine ⟨83496978366506285363355005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55664652244337523575570003 83496978366506285363355005)
          ·
            refine ⟨31311366887439857011258127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83496978366506285363355005 31311366887439857011258127)
            ·
              refine ⟨46967050331159785516887191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31311366887439857011258127 46967050331159785516887191)
              ·
                refine ⟨70450575496739678275330787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46967050331159785516887191 70450575496739678275330787)
                ·
                  refine ⟨105675863245109517412996181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70450575496739678275330787 105675863245109517412996181)
                  ·
                    refine ⟨1238389022403627157183549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105675863245109517412996181 1238389022403627157183549)
                    ·
                      rfl

theorem cell22_3617631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_3617631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617631 prefixEnd_3617631 := by exact prefixLift 3617631
  have htrace : WordTrace (prefixWord ++ tailWord_3617631) baseStart_3617631 baseEnd_3617631 := by
    simpa [prefixWord, tailWord_3617631, baseEnd_3617631] using wordTrace_append hprefix tailTrace_3617631
  have hstable : (prefixWord ++ tailWord_3617631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617631).length < 2 ^ (prefixWord ++ tailWord_3617631).sum := by decide
  have hdescent : baseEnd_3617631 < baseStart_3617631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617667 : List Nat := [1, 1, 1, 3, 4, 1, 4, 3, 1, 3]
def baseStart_3617667 : Nat := 118140960795 + 3617667 * 2 ^ 59
def prefixEnd_3617667 : Nat := 4983230072969 + 3 ^ 40 * 3617667 * 2
def baseEnd_3617667 : Nat := 1238401345939335063283439

theorem tailTrace_3617667 : CollatzResearch.WordTrace tailWord_3617667 prefixEnd_3617667 1238401345939335063283439 := by
  unfold tailWord_3617667
  simp only [CollatzResearch.WordTrace]
  refine ⟨131947155384817782179291255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87964770256545188119527503 131947155384817782179291255)
  ·
    refine ⟨197920733077226673268936883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131947155384817782179291255 197920733077226673268936883)
    ·
      refine ⟨296881099615840009903405325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197920733077226673268936883 296881099615840009903405325)
      ·
        refine ⟨111330412355940003713776997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296881099615840009903405325 111330412355940003713776997)
        ·
          refine ⟨20874452316738750696333187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111330412355940003713776997 20874452316738750696333187)
          ·
            refine ⟨31311678475108126044499781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20874452316738750696333187 31311678475108126044499781)
            ·
              refine ⟨5870939714082773633343709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31311678475108126044499781 5870939714082773633343709)
              ·
                refine ⟨2201602392781040112503891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5870939714082773633343709 2201602392781040112503891)
                ·
                  refine ⟨3302403589171560168755837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201602392781040112503891 3302403589171560168755837)
                  ·
                    refine ⟨1238401345939335063283439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3302403589171560168755837 1238401345939335063283439)
                    ·
                      rfl

theorem cell22_3617667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 1, 3].length) (baseStart_3617667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617667 prefixEnd_3617667 := by exact prefixLift 3617667
  have htrace : WordTrace (prefixWord ++ tailWord_3617667) baseStart_3617667 baseEnd_3617667 := by
    simpa [prefixWord, tailWord_3617667, baseEnd_3617667] using wordTrace_append hprefix tailTrace_3617667
  have hstable : (prefixWord ++ tailWord_3617667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617667).length < 2 ^ (prefixWord ++ tailWord_3617667).sum := by decide
  have hdescent : baseEnd_3617667 < baseStart_3617667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617697 : List Nat := [1, 2, 3, 4, 1, 2, 3, 1, 5]
def baseStart_3617697 : Nat := 118140960795 + 3617697 * 2 ^ 59
def prefixEnd_3617697 : Nat := 4983230072969 + 3 ^ 40 * 3617697 * 2
def baseEnd_3617697 : Nat := 412803871850808328344449

theorem tailTrace_3617697 : CollatzResearch.WordTrace tailWord_3617697 prefixEnd_3617697 412803871850808328344449 := by
  unfold tailWord_3617697
  simp only [CollatzResearch.WordTrace]
  refine ⟨131948249574709097302883345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87965499716472731535255563 131948249574709097302883345)
  ·
    refine ⟨98961187181031822977162509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131948249574709097302883345 98961187181031822977162509)
    ·
      refine ⟨37110445192886933616435941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98961187181031822977162509 37110445192886933616435941)
      ·
        refine ⟨6958208473666300053081739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37110445192886933616435941 6958208473666300053081739)
        ·
          refine ⟨10437312710499450079622609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6958208473666300053081739 10437312710499450079622609)
          ·
            refine ⟨7827984532874587559716957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10437312710499450079622609 7827984532874587559716957)
            ·
              refine ⟨2935494199827970334893859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7827984532874587559716957 2935494199827970334893859)
              ·
                refine ⟨4403241299741955502340789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2935494199827970334893859 4403241299741955502340789)
                ·
                  refine ⟨412803871850808328344449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4403241299741955502340789 412803871850808328344449)
                  ·
                    rfl

theorem cell22_3617697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 5].length) (baseStart_3617697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617697 prefixEnd_3617697 := by exact prefixLift 3617697
  have htrace : WordTrace (prefixWord ++ tailWord_3617697) baseStart_3617697 baseEnd_3617697 := by
    simpa [prefixWord, tailWord_3617697, baseEnd_3617697] using wordTrace_append hprefix tailTrace_3617697
  have hstable : (prefixWord ++ tailWord_3617697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617697).length < 2 ^ (prefixWord ++ tailWord_3617697).sum := by decide
  have hdescent : baseEnd_3617697 < baseStart_3617697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617740 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 4, 3]
def baseStart_3617740 : Nat := 118140960795 + 3617740 * 2 ^ 59
def prefixEnd_3617740 : Nat := 4983230072969 + 3 ^ 40 * 3617740 * 2
def baseEnd_3617740 : Nat := 1238426335331187206208215

theorem tailTrace_3617740 : CollatzResearch.WordTrace tailWord_3617740 prefixEnd_3617740 1238426335331187206208215 := by
  unfold tailWord_3617740
  simp only [CollatzResearch.WordTrace]
  refine ⟨65974908956776657823349337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87966545275702210431132449 65974908956776657823349337)
  ·
    refine ⟨49481181717582493367512003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65974908956776657823349337 49481181717582493367512003)
    ·
      refine ⟨74221772576373740051268005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49481181717582493367512003 74221772576373740051268005)
      ·
        refine ⟨13916582358070076259612751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74221772576373740051268005 13916582358070076259612751)
        ·
          refine ⟨20874873537105114389419127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13916582358070076259612751 20874873537105114389419127)
          ·
            refine ⟨31312310305657671584128691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20874873537105114389419127 31312310305657671584128691)
            ·
              refine ⟨46968465458486507376193037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31312310305657671584128691 46968465458486507376193037)
              ·
                refine ⟨17613174546932440266072389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46968465458486507376193037 17613174546932440266072389)
                ·
                  refine ⟨3302470227549832549888573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17613174546932440266072389 3302470227549832549888573)
                  ·
                    refine ⟨1238426335331187206208215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3302470227549832549888573 1238426335331187206208215)
                    ·
                      rfl

theorem cell22_3617740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_3617740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617740 prefixEnd_3617740 := by exact prefixLift 3617740
  have htrace : WordTrace (prefixWord ++ tailWord_3617740) baseStart_3617740 baseEnd_3617740 := by
    simpa [prefixWord, tailWord_3617740, baseEnd_3617740] using wordTrace_append hprefix tailTrace_3617740
  have hstable : (prefixWord ++ tailWord_3617740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617740).length < 2 ^ (prefixWord ++ tailWord_3617740).sum := by decide
  have hdescent : baseEnd_3617740 < baseStart_3617740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617753 : List Nat := [1, 2, 1, 2, 5, 1, 1, 9]
def baseStart_3617753 : Nat := 118140960795 + 3617753 * 2 ^ 59
def prefixEnd_3617753 : Nat := 4983230072969 + 3 ^ 40 * 3617753 * 2
def baseEnd_3617753 : Nat := 137603420610762167292575

theorem tailTrace_3617753 : CollatzResearch.WordTrace tailWord_3617753 prefixEnd_3617753 137603420610762167292575 := by
  unfold tailWord_3617753
  simp only [CollatzResearch.WordTrace]
  refine ⟨131950292062506218866921913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87966861375004145911281275 131950292062506218866921913)
  ·
    refine ⟨98962719046879664150191435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131950292062506218866921913 98962719046879664150191435)
    ·
      refine ⟨148444078570319496225287153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98962719046879664150191435 148444078570319496225287153)
      ·
        refine ⟨111333058927739622168965365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148444078570319496225287153 111333058927739622168965365)
        ·
          refine ⟨10437474274475589578340503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111333058927739622168965365 10437474274475589578340503)
          ·
            refine ⟨15656211411713384367510755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10437474274475589578340503 15656211411713384367510755)
            ·
              refine ⟨23484317117570076551266133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15656211411713384367510755 23484317117570076551266133)
              ·
                refine ⟨137603420610762167292575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23484317117570076551266133 137603420610762167292575)
                ·
                  rfl

theorem cell22_3617753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 9].length) (baseStart_3617753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617753 prefixEnd_3617753 := by exact prefixLift 3617753
  have htrace : WordTrace (prefixWord ++ tailWord_3617753) baseStart_3617753 baseEnd_3617753 := by
    simpa [prefixWord, tailWord_3617753, baseEnd_3617753] using wordTrace_append hprefix tailTrace_3617753
  have hstable : (prefixWord ++ tailWord_3617753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617753).length < 2 ^ (prefixWord ++ tailWord_3617753).sum := by decide
  have hdescent : baseEnd_3617753 < baseStart_3617753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617768 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 2, 7]
def baseStart_3617768 : Nat := 118140960795 + 3617768 * 2 ^ 59
def prefixEnd_3617768 : Nat := 4983230072969 + 3 ^ 40 * 3617768 * 2
def baseEnd_3617768 : Nat := 1238435920303404466508129

theorem tailTrace_3617768 : CollatzResearch.WordTrace tailWord_3617768 prefixEnd_3617768 1238435920303404466508129 := by
  unfold tailWord_3617768
  simp only [CollatzResearch.WordTrace]
  refine ⟨65975419578725938214358979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87967226104967917619145305 65975419578725938214358979)
  ·
    refine ⟨98963129368088907321538469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65975419578725938214358979 98963129368088907321538469)
    ·
      refine ⟨18555586756516670122788463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98963129368088907321538469 18555586756516670122788463)
      ·
        refine ⟨27833380134775005184182695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18555586756516670122788463 27833380134775005184182695)
        ·
          refine ⟨41750070202162507776274043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27833380134775005184182695 41750070202162507776274043)
          ·
            refine ⟨62625105303243761664411065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41750070202162507776274043 62625105303243761664411065)
            ·
              refine ⟨46968828977432821248308299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62625105303243761664411065 46968828977432821248308299)
              ·
                refine ⟨70453243466149231872462449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46968828977432821248308299 70453243466149231872462449)
                ·
                  refine ⟨52839932599611923904346837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70453243466149231872462449 52839932599611923904346837)
                  ·
                    refine ⟨1238435920303404466508129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52839932599611923904346837 1238435920303404466508129)
                    ·
                      rfl

theorem cell22_3617768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_3617768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617768 prefixEnd_3617768 := by exact prefixLift 3617768
  have htrace : WordTrace (prefixWord ++ tailWord_3617768) baseStart_3617768 baseEnd_3617768 := by
    simpa [prefixWord, tailWord_3617768, baseEnd_3617768] using wordTrace_append hprefix tailTrace_3617768
  have hstable : (prefixWord ++ tailWord_3617768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617768).length < 2 ^ (prefixWord ++ tailWord_3617768).sum := by decide
  have hdescent : baseEnd_3617768 < baseStart_3617768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617843 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 10]
def baseStart_3617843 : Nat := 118140960795 + 3617843 * 2 ^ 59
def prefixEnd_3617843 : Nat := 4983230072969 + 3 ^ 40 * 3617843 * 2
def baseEnd_3617843 : Nat := 412820531445376423627633

theorem tailTrace_3617843 : CollatzResearch.WordTrace tailWord_3617843 prefixEnd_3617843 412820531445376423627633 := by
  unfold tailWord_3617843
  simp only [CollatzResearch.WordTrace]
  refine ⟨131953574632180164237698183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87969049754786776158465455 131953574632180164237698183)
  ·
    refine ⟨197930361948270246356547275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131953574632180164237698183 197930361948270246356547275)
    ·
      refine ⟨296895542922405369534820913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197930361948270246356547275 296895542922405369534820913)
      ·
        refine ⟨222671657191804027151115685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296895542922405369534820913 222671657191804027151115685)
        ·
          refine ⟨41750935723463255090834191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222671657191804027151115685 41750935723463255090834191)
          ·
            refine ⟨62626403585194882636251287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41750935723463255090834191 62626403585194882636251287)
            ·
              refine ⟨93939605377792323954376931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62626403585194882636251287 93939605377792323954376931)
              ·
                refine ⟨140909408066688485931565397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93939605377792323954376931 140909408066688485931565397)
                ·
                  refine ⟨412820531445376423627633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 140909408066688485931565397 412820531445376423627633)
                  ·
                    rfl

theorem cell22_3617843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 10].length) (baseStart_3617843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617843 prefixEnd_3617843 := by exact prefixLift 3617843
  have htrace : WordTrace (prefixWord ++ tailWord_3617843) baseStart_3617843 baseEnd_3617843 := by
    simpa [prefixWord, tailWord_3617843, baseEnd_3617843] using wordTrace_append hprefix tailTrace_3617843
  have hstable : (prefixWord ++ tailWord_3617843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617843).length < 2 ^ (prefixWord ++ tailWord_3617843).sum := by decide
  have hdescent : baseEnd_3617843 < baseStart_3617843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617875 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 6, 3]
def baseStart_3617875 : Nat := 118140960795 + 3617875 * 2 ^ 59
def prefixEnd_3617875 : Nat := 4983230072969 + 3 ^ 40 * 3617875 * 2
def baseEnd_3617875 : Nat := 1238472548590091854082801

theorem tailTrace_3617875 : CollatzResearch.WordTrace tailWord_3617875 prefixEnd_3617875 1238472548590091854082801 := by
  unfold tailWord_3617875
  simp only [CollatzResearch.WordTrace]
  refine ⟨131954741768064233702863079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87969827845376155801908719 131954741768064233702863079)
  ·
    refine ⟨197932112652096350554294619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131954741768064233702863079 197932112652096350554294619)
    ·
      refine ⟨296898168978144525831441929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197932112652096350554294619 296898168978144525831441929)
      ·
        refine ⟨222673626733608394373581447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296898168978144525831441929 222673626733608394373581447)
        ·
          refine ⟨334010440100412591560372171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222673626733608394373581447 334010440100412591560372171)
          ·
            refine ⟨501015660150618887340558257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334010440100412591560372171 501015660150618887340558257)
            ·
              refine ⟨375761745112964165505418693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501015660150618887340558257 375761745112964165505418693)
              ·
                refine ⟨70455327208680781032266005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 375761745112964165505418693 70455327208680781032266005)
                ·
                  refine ⟨3302593462906911610887469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70455327208680781032266005 3302593462906911610887469)
                  ·
                    refine ⟨1238472548590091854082801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3302593462906911610887469 1238472548590091854082801)
                    ·
                      rfl

theorem cell22_3617875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 3].length) (baseStart_3617875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617875 prefixEnd_3617875 := by exact prefixLift 3617875
  have htrace : WordTrace (prefixWord ++ tailWord_3617875) baseStart_3617875 baseEnd_3617875 := by
    simpa [prefixWord, tailWord_3617875, baseEnd_3617875] using wordTrace_append hprefix tailTrace_3617875
  have hstable : (prefixWord ++ tailWord_3617875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617875).length < 2 ^ (prefixWord ++ tailWord_3617875).sum := by decide
  have hdescent : baseEnd_3617875 < baseStart_3617875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617971 : List Nat := [1, 1, 1, 2, 3, 2, 6, 2, 1, 3]
def baseStart_3617971 : Nat := 118140960795 + 3617971 * 2 ^ 59
def prefixEnd_3617971 : Nat := 4983230072969 + 3 ^ 40 * 3617971 * 2
def baseEnd_3617971 : Nat := 1238505411351979603682507

theorem tailTrace_3617971 : CollatzResearch.WordTrace tailWord_3617971 prefixEnd_3617971 1238505411351979603682507 := by
  unfold tailWord_3617971
  simp only [CollatzResearch.WordTrace]
  refine ⟨131958243175716442098357767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87972162117144294732238511 131958243175716442098357767)
  ·
    refine ⟨197937364763574663147536651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131958243175716442098357767 197937364763574663147536651)
    ·
      refine ⟨296906047145361994721304977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197937364763574663147536651 296906047145361994721304977)
      ·
        refine ⟨222679535359021496040978733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296906047145361994721304977 222679535359021496040978733)
        ·
          refine ⟨83504825759633061015367025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222679535359021496040978733 83504825759633061015367025)
          ·
            refine ⟨62628619319724795761525269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83504825759633061015367025 62628619319724795761525269)
            ·
              refine ⟨2935716530612099801321497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62628619319724795761525269 2935716530612099801321497)
              ·
                refine ⟨2201787397959074850991123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2935716530612099801321497 2201787397959074850991123)
                ·
                  refine ⟨3302681096938612276486685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201787397959074850991123 3302681096938612276486685)
                  ·
                    refine ⟨1238505411351979603682507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3302681096938612276486685 1238505411351979603682507)
                    ·
                      rfl

theorem cell22_3617971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 1, 3].length) (baseStart_3617971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617971 prefixEnd_3617971 := by exact prefixLift 3617971
  have htrace : WordTrace (prefixWord ++ tailWord_3617971) baseStart_3617971 baseEnd_3617971 := by
    simpa [prefixWord, tailWord_3617971, baseEnd_3617971] using wordTrace_append hprefix tailTrace_3617971
  have hstable : (prefixWord ++ tailWord_3617971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617971).length < 2 ^ (prefixWord ++ tailWord_3617971).sum := by decide
  have hdescent : baseEnd_3617971 < baseStart_3617971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617982 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_3617982 : Nat := 118140960795 + 3617982 * 2 ^ 59
def prefixEnd_3617982 : Nat := 4983230072969 + 3 ^ 40 * 3617982 * 2
def baseEnd_3617982 : Nat := 1238509176876779241657473

theorem tailTrace_3617982 : CollatzResearch.WordTrace tailWord_3617982 prefixEnd_3617982 1238509176876779241657473 := by
  unfold tailWord_3617982
  simp only [CollatzResearch.WordTrace]
  refine ⟨16494830547334573872126025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87972429585784393984672133 16494830547334573872126025)
  ·
    refine ⟨12371122910500930404094519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16494830547334573872126025 12371122910500930404094519)
    ·
      refine ⟨18556684365751395606141779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12371122910500930404094519 18556684365751395606141779)
      ·
        refine ⟨27835026548627093409212669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18556684365751395606141779 27835026548627093409212669)
        ·
          refine ⟨10438134955735160028454751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27835026548627093409212669 10438134955735160028454751)
          ·
            refine ⟨15657202433602740042682127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10438134955735160028454751 15657202433602740042682127)
            ·
              refine ⟨23485803650404110064023191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15657202433602740042682127 23485803650404110064023191)
              ·
                refine ⟨35228705475606165096034787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23485803650404110064023191 35228705475606165096034787)
                ·
                  refine ⟨52843058213409247644052181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35228705475606165096034787 52843058213409247644052181)
                  ·
                    refine ⟨1238509176876779241657473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52843058213409247644052181 1238509176876779241657473)
                    ·
                      rfl

theorem cell22_3617982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_3617982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3617982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3617982 prefixEnd_3617982 := by exact prefixLift 3617982
  have htrace : WordTrace (prefixWord ++ tailWord_3617982) baseStart_3617982 baseEnd_3617982 := by
    simpa [prefixWord, tailWord_3617982, baseEnd_3617982] using wordTrace_append hprefix tailTrace_3617982
  have hstable : (prefixWord ++ tailWord_3617982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617982).length < 2 ^ (prefixWord ++ tailWord_3617982).sum := by decide
  have hdescent : baseEnd_3617982 < baseStart_3617982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618025 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 5, 6]
def baseStart_3618025 : Nat := 118140960795 + 3618025 * 2 ^ 59
def prefixEnd_3618025 : Nat := 4983230072969 + 3 ^ 40 * 3618025 * 2
def baseEnd_3618025 : Nat := 1238523896655541462832341

theorem tailTrace_3618025 : CollatzResearch.WordTrace tailWord_3618025 prefixEnd_3618025 1238523896655541462832341 := by
  unfold tailWord_3618025
  simp only [CollatzResearch.WordTrace]
  refine ⟨131960212717520809320823529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87973475145013872880549019 131960212717520809320823529)
  ·
    refine ⟨98970159538140606990617647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131960212717520809320823529 98970159538140606990617647)
    ·
      refine ⟨148455239307210910485926471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98970159538140606990617647 148455239307210910485926471)
      ·
        refine ⟨222682858960816365728889707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148455239307210910485926471 222682858960816365728889707)
        ·
          refine ⟨334024288441224548593334561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222682858960816365728889707 334024288441224548593334561)
          ·
            refine ⟨250518216330918411445000921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334024288441224548593334561 250518216330918411445000921)
            ·
              refine ⟨187888662248188808583750691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250518216330918411445000921 187888662248188808583750691)
              ·
                refine ⟨281832993372283212875626037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187888662248188808583750691 281832993372283212875626037)
                ·
                  refine ⟨26421843128651551207089941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 281832993372283212875626037 26421843128651551207089941)
                  ·
                    refine ⟨1238523896655541462832341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26421843128651551207089941 1238523896655541462832341)
                    ·
                      rfl

theorem cell22_3618025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_3618025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618025 prefixEnd_3618025 := by exact prefixLift 3618025
  have htrace : WordTrace (prefixWord ++ tailWord_3618025) baseStart_3618025 baseEnd_3618025 := by
    simpa [prefixWord, tailWord_3618025, baseEnd_3618025] using wordTrace_append hprefix tailTrace_3618025
  have hstable : (prefixWord ++ tailWord_3618025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618025).length < 2 ^ (prefixWord ++ tailWord_3618025).sum := by decide
  have hdescent : baseEnd_3618025 < baseStart_3618025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618029 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 6]
def baseStart_3618029 : Nat := 118140960795 + 3618029 * 2 ^ 59
def prefixEnd_3618029 : Nat := 4983230072969 + 3 ^ 40 * 3618029 * 2
def baseEnd_3618029 : Nat := 412841755312428928577443

theorem tailTrace_3618029 : CollatzResearch.WordTrace tailWord_3618029 prefixEnd_3618029 412841755312428928577443 := by
  unfold tailWord_3618029
  simp only [CollatzResearch.WordTrace]
  refine ⟨131960358609506318003969141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87973572406337545335979427 131960358609506318003969141)
  ·
    refine ⟨12371283619641217312872107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131960358609506318003969141 12371283619641217312872107)
    ·
      refine ⟨18556925429461825969308161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12371283619641217312872107 18556925429461825969308161)
      ·
        refine ⟨13917694072096369476981121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18556925429461825969308161 13917694072096369476981121)
        ·
          refine ⟨10438270554072277107735841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13917694072096369476981121 10438270554072277107735841)
          ·
            refine ⟨7828702915554207830801881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10438270554072277107735841 7828702915554207830801881)
            ·
              refine ⟨5871527186665655873101411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7828702915554207830801881 5871527186665655873101411)
              ·
                refine ⟨8807290779998483809652117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5871527186665655873101411 8807290779998483809652117)
                ·
                  refine ⟨412841755312428928577443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8807290779998483809652117 412841755312428928577443)
                  ·
                    rfl

theorem cell22_3618029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_3618029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618029 prefixEnd_3618029 := by exact prefixLift 3618029
  have htrace : WordTrace (prefixWord ++ tailWord_3618029) baseStart_3618029 baseEnd_3618029 := by
    simpa [prefixWord, tailWord_3618029, baseEnd_3618029] using wordTrace_append hprefix tailTrace_3618029
  have hstable : (prefixWord ++ tailWord_3618029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618029).length < 2 ^ (prefixWord ++ tailWord_3618029).sum := by decide
  have hdescent : baseEnd_3618029 < baseStart_3618029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618179 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 1, 5]
def baseStart_3618179 : Nat := 118140960795 + 3618179 * 2 ^ 59
def prefixEnd_3618179 : Nat := 4983230072969 + 3 ^ 40 * 3618179 * 2
def baseEnd_3618179 : Nat := 1238576614002736394481869

theorem tailTrace_3618179 : CollatzResearch.WordTrace tailWord_3618179 prefixEnd_3618179 1238576614002736394481869 := by
  unfold tailWord_3618179
  simp only [CollatzResearch.WordTrace]
  refine ⟨131965829558962893621929591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87977219705975262414619727 131965829558962893621929591)
  ·
    refine ⟨197948744338444340432894387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131965829558962893621929591 197948744338444340432894387)
    ·
      refine ⟨296923116507666510649341581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197948744338444340432894387 296923116507666510649341581)
      ·
        refine ⟨111346168690374941493503093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296923116507666510649341581 111346168690374941493503093)
        ·
          refine ⟨10438703314722650765015915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111346168690374941493503093 10438703314722650765015915)
          ·
            refine ⟨15658054972083976147523873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10438703314722650765015915 15658054972083976147523873)
            ·
              refine ⟨11743541229062982110642905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15658054972083976147523873 11743541229062982110642905)
              ·
                refine ⟨8807655921797236582982179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11743541229062982110642905 8807655921797236582982179)
                ·
                  refine ⟨13211483882695854874473269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8807655921797236582982179 13211483882695854874473269)
                  ·
                    refine ⟨1238576614002736394481869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13211483882695854874473269 1238576614002736394481869)
                    ·
                      rfl

theorem cell22_3618179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 5].length) (baseStart_3618179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618179 prefixEnd_3618179 := by exact prefixLift 3618179
  have htrace : WordTrace (prefixWord ++ tailWord_3618179) baseStart_3618179 baseEnd_3618179 := by
    simpa [prefixWord, tailWord_3618179, baseEnd_3618179] using wordTrace_append hprefix tailTrace_3618179
  have hstable : (prefixWord ++ tailWord_3618179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618179).length < 2 ^ (prefixWord ++ tailWord_3618179).sum := by decide
  have hdescent : baseEnd_3618179 < baseStart_3618179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618183 : List Nat := [1, 1, 4, 2, 2, 4, 2, 1, 1, 4]
def baseStart_3618183 : Nat := 118140960795 + 3618183 * 2 ^ 59
def prefixEnd_3618183 : Nat := 4983230072969 + 3 ^ 40 * 3618183 * 2
def baseEnd_3618183 : Nat := 1238577983284481717381857

theorem tailTrace_3618183 : CollatzResearch.WordTrace tailWord_3618183 prefixEnd_3618183 1238577983284481717381857 := by
  unfold tailWord_3618183
  simp only [CollatzResearch.WordTrace]
  refine ⟨131965975450948402305075203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87977316967298934870050135 131965975450948402305075203)
  ·
    refine ⟨197948963176422603457612805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131965975450948402305075203 197948963176422603457612805)
    ·
      refine ⟨37115430595579238148302401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197948963176422603457612805 37115430595579238148302401)
      ·
        refine ⟨27836572946684428611226801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37115430595579238148302401 27836572946684428611226801)
        ·
          refine ⟨20877429710013321458420101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27836572946684428611226801 20877429710013321458420101)
          ·
            refine ⟨3914518070627497773453769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20877429710013321458420101 3914518070627497773453769)
            ·
              refine ⟨2935888552970623330090327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3914518070627497773453769 2935888552970623330090327)
              ·
                refine ⟨4403832829455934995135491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2935888552970623330090327 4403832829455934995135491)
                ·
                  refine ⟨6605749244183902492703237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4403832829455934995135491 6605749244183902492703237)
                  ·
                    refine ⟨1238577983284481717381857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6605749244183902492703237 1238577983284481717381857)
                    ·
                      rfl

theorem cell22_3618183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_3618183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618183 prefixEnd_3618183 := by exact prefixLift 3618183
  have htrace : WordTrace (prefixWord ++ tailWord_3618183) baseStart_3618183 baseEnd_3618183 := by
    simpa [prefixWord, tailWord_3618183, baseEnd_3618183] using wordTrace_append hprefix tailTrace_3618183
  have hstable : (prefixWord ++ tailWord_3618183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618183).length < 2 ^ (prefixWord ++ tailWord_3618183).sum := by decide
  have hdescent : baseEnd_3618183 < baseStart_3618183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618224 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 5, 3]
def baseStart_3618224 : Nat := 118140960795 + 3618224 * 2 ^ 59
def prefixEnd_3618224 : Nat := 4983230072969 + 3 ^ 40 * 3618224 * 2
def baseEnd_3618224 : Nat := 1238592018422371277106731

theorem tailTrace_3618224 : CollatzResearch.WordTrace tailWord_3618224 prefixEnd_3618224 1238592018422371277106731 := by
  unfold tailWord_3618224
  simp only [CollatzResearch.WordTrace]
  refine ⟨65983735421899933153658863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87978313895866577538211817 65983735421899933153658863)
  ·
    refine ⟨98975603132849899730488295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65983735421899933153658863 98975603132849899730488295)
    ·
      refine ⟨148463404699274849595732443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98975603132849899730488295 148463404699274849595732443)
      ·
        refine ⟨222695107048912274393598665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148463404699274849595732443 222695107048912274393598665)
        ·
          refine ⟨167021330286684205795198999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222695107048912274393598665 167021330286684205795198999)
          ·
            refine ⟨250531995430026308692798499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167021330286684205795198999 250531995430026308692798499)
            ·
              refine ⟨375797993145039463039197749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250531995430026308692798499 375797993145039463039197749)
              ·
                refine ⟨35231061857347449659924789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 375797993145039463039197749 35231061857347449659924789)
                ·
                  refine ⟨3302912049126323405617949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35231061857347449659924789 3302912049126323405617949)
                  ·
                    refine ⟨1238592018422371277106731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3302912049126323405617949 1238592018422371277106731)
                    ·
                      rfl

theorem cell22_3618224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 5, 3].length) (baseStart_3618224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618224 prefixEnd_3618224 := by exact prefixLift 3618224
  have htrace : WordTrace (prefixWord ++ tailWord_3618224) baseStart_3618224 baseEnd_3618224 := by
    simpa [prefixWord, tailWord_3618224, baseEnd_3618224] using wordTrace_append hprefix tailTrace_3618224
  have hstable : (prefixWord ++ tailWord_3618224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618224).length < 2 ^ (prefixWord ++ tailWord_3618224).sum := by decide
  have hdescent : baseEnd_3618224 < baseStart_3618224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618254 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 7]
def baseStart_3618254 : Nat := 118140960795 + 3618254 * 2 ^ 59
def prefixEnd_3618254 : Nat := 4983230072969 + 3 ^ 40 * 3618254 * 2
def baseEnd_3618254 : Nat := 412867429345153732952213

theorem tailTrace_3618254 : CollatzResearch.WordTrace tailWord_3618254 prefixEnd_3618254 412867429345153732952213 := by
  unfold tailWord_3618254
  simp only [CollatzResearch.WordTrace]
  refine ⟨16496070629211397678863727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87979043355794120953939877 16496070629211397678863727)
  ·
    refine ⟨24744105943817096518295591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16496070629211397678863727 24744105943817096518295591)
    ·
      refine ⟨37116158915725644777443387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24744105943817096518295591 37116158915725644777443387)
      ·
        refine ⟨55674238373588467166165081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37116158915725644777443387 55674238373588467166165081)
        ·
          refine ⟨41755678780191350374623811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55674238373588467166165081 41755678780191350374623811)
          ·
            refine ⟨62633518170287025561935717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41755678780191350374623811 62633518170287025561935717)
            ·
              refine ⟨11743784656928817292862947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62633518170287025561935717 11743784656928817292862947)
              ·
                refine ⟨17615676985393225939294421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11743784656928817292862947 17615676985393225939294421)
                ·
                  refine ⟨412867429345153732952213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17615676985393225939294421 412867429345153732952213)
                  ·
                    rfl

theorem cell22_3618254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_3618254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618254 prefixEnd_3618254 := by exact prefixLift 3618254
  have htrace : WordTrace (prefixWord ++ tailWord_3618254) baseStart_3618254 baseEnd_3618254 := by
    simpa [prefixWord, tailWord_3618254, baseEnd_3618254] using wordTrace_append hprefix tailTrace_3618254
  have hstable : (prefixWord ++ tailWord_3618254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618254).length < 2 ^ (prefixWord ++ tailWord_3618254).sum := by decide
  have hdescent : baseEnd_3618254 < baseStart_3618254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618346 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 1, 6]
def baseStart_3618346 : Nat := 118140960795 + 3618346 * 2 ^ 59
def prefixEnd_3618346 : Nat := 4983230072969 + 3 ^ 40 * 3618346 * 2
def baseEnd_3618346 : Nat := 1238633781515603625556357

theorem tailTrace_3618346 : CollatzResearch.WordTrace tailWord_3618346 prefixEnd_3618346 1238633781515603625556357 := by
  unfold tailWord_3618346
  simp only [CollatzResearch.WordTrace]
  refine ⟨32992980137339470285814723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87981280366238587428839261 32992980137339470285814723)
  ·
    refine ⟨49489470206009205428722085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32992980137339470285814723 49489470206009205428722085)
    ·
      refine ⟨9279275663626726017885391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49489470206009205428722085 9279275663626726017885391)
      ·
        refine ⟨13918913495440089026828087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9279275663626726017885391 13918913495440089026828087)
        ·
          refine ⟨20878370243160133540242131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13918913495440089026828087 20878370243160133540242131)
          ·
            refine ⟨31317555364740200310363197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20878370243160133540242131 31317555364740200310363197)
            ·
              refine ⟨11744083261777575116386199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31317555364740200310363197 11744083261777575116386199)
              ·
                refine ⟨17616124892666362674579299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11744083261777575116386199 17616124892666362674579299)
                ·
                  refine ⟨26424187338999544011868949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17616124892666362674579299 26424187338999544011868949)
                  ·
                    refine ⟨1238633781515603625556357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26424187338999544011868949 1238633781515603625556357)
                    ·
                      rfl

theorem cell22_3618346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_3618346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618346 prefixEnd_3618346 := by exact prefixLift 3618346
  have htrace : WordTrace (prefixWord ++ tailWord_3618346) baseStart_3618346 baseEnd_3618346 := by
    simpa [prefixWord, tailWord_3618346, baseEnd_3618346] using wordTrace_append hprefix tailTrace_3618346
  have hstable : (prefixWord ++ tailWord_3618346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618346).length < 2 ^ (prefixWord ++ tailWord_3618346).sum := by decide
  have hdescent : baseEnd_3618346 < baseStart_3618346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618350 : List Nat := [4, 1, 3, 1, 2, 2, 2, 3, 4]
def baseStart_3618350 : Nat := 118140960795 + 3618350 * 2 ^ 59
def prefixEnd_3618350 : Nat := 4983230072969 + 3 ^ 40 * 3618350 * 2
def baseEnd_3618350 : Nat := 412878383599116316152115

theorem tailTrace_3618350 : CollatzResearch.WordTrace tailWord_3618350 prefixEnd_3618350 412878383599116316152115 := by
  unfold tailWord_3618350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16496508305167923728300563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87981377627562259884269669 16496508305167923728300563)
  ·
    refine ⟨24744762457751885592450845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16496508305167923728300563 24744762457751885592450845)
    ·
      refine ⟨9279285921656957097169067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24744762457751885592450845 9279285921656957097169067)
      ·
        refine ⟨13918928882485435645753601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9279285921656957097169067 13918928882485435645753601)
        ·
          refine ⟨10439196661864076734315201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13918928882485435645753601 10439196661864076734315201)
          ·
            refine ⟨7829397496398057550736401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10439196661864076734315201 7829397496398057550736401)
            ·
              refine ⟨5872048122298543163052301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7829397496398057550736401 5872048122298543163052301)
              ·
                refine ⟨2202018045861953686144613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5872048122298543163052301 2202018045861953686144613)
                ·
                  refine ⟨412878383599116316152115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2202018045861953686144613 412878383599116316152115)
                  ·
                    rfl

theorem cell22_3618350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_3618350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618350 prefixEnd_3618350 := by exact prefixLift 3618350
  have htrace : WordTrace (prefixWord ++ tailWord_3618350) baseStart_3618350 baseEnd_3618350 := by
    simpa [prefixWord, tailWord_3618350, baseEnd_3618350] using wordTrace_append hprefix tailTrace_3618350
  have hstable : (prefixWord ++ tailWord_3618350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618350).length < 2 ^ (prefixWord ++ tailWord_3618350).sum := by decide
  have hdescent : baseEnd_3618350 < baseStart_3618350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618419 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 1, 10]
def baseStart_3618419 : Nat := 118140960795 + 3618419 * 2 ^ 59
def prefixEnd_3618419 : Nat := 4983230072969 + 3 ^ 40 * 3618419 * 2
def baseEnd_3618419 : Nat := 1238658770907455768481133

theorem tailTrace_3618419 : CollatzResearch.WordTrace tailWord_3618419 prefixEnd_3618419 1238658770907455768481133 := by
  unfold tailWord_3618419
  simp only [CollatzResearch.WordTrace]
  refine ⟨131974583078093414610666311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87983055385395609740444207 131974583078093414610666311)
  ·
    refine ⟨197961874617140121915999467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131974583078093414610666311 197961874617140121915999467)
    ·
      refine ⟨296942811925710182873999201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197961874617140121915999467 296942811925710182873999201)
      ·
        refine ⟨222707108944282637155499401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296942811925710182873999201 222707108944282637155499401)
        ·
          refine ⟨167030331708211977866624551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222707108944282637155499401 167030331708211977866624551)
          ·
            refine ⟨250545497562317966799936827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167030331708211977866624551 250545497562317966799936827)
            ·
              refine ⟨375818246343476950199905241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250545497562317966799936827 375818246343476950199905241)
              ·
                refine ⟨281863684757607712649928931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375818246343476950199905241 281863684757607712649928931)
                ·
                  refine ⟨422795527136411568974893397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281863684757607712649928931 422795527136411568974893397)
                  ·
                    refine ⟨1238658770907455768481133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 422795527136411568974893397 1238658770907455768481133)
                    ·
                      rfl

theorem cell22_3618419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 10].length) (baseStart_3618419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618419 prefixEnd_3618419 := by exact prefixLift 3618419
  have htrace : WordTrace (prefixWord ++ tailWord_3618419) baseStart_3618419 baseEnd_3618419 := by
    simpa [prefixWord, tailWord_3618419, baseEnd_3618419] using wordTrace_append hprefix tailTrace_3618419
  have hstable : (prefixWord ++ tailWord_3618419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618419).length < 2 ^ (prefixWord ++ tailWord_3618419).sum := by decide
  have hdescent : baseEnd_3618419 < baseStart_3618419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618440 : List Nat := [2, 1, 3, 5, 1, 1, 1, 3, 5]
def baseStart_3618440 : Nat := 118140960795 + 3618440 * 2 ^ 59
def prefixEnd_3618440 : Nat := 4983230072969 + 3 ^ 40 * 3618440 * 2
def baseEnd_3618440 : Nat := 412888653212206237902023

theorem tailTrace_3618440 : CollatzResearch.WordTrace tailWord_3618440 prefixEnd_3618440 412888653212206237902023 := by
  unfold tailWord_3618440
  simp only [CollatzResearch.WordTrace]
  refine ⟨65987674505508667598590387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87983566007344890131453849 65987674505508667598590387)
  ·
    refine ⟨98981511758263001397885581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65987674505508667598590387 98981511758263001397885581)
    ·
      refine ⟨37118066909348625524207093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98981511758263001397885581 37118066909348625524207093)
      ·
        refine ⟨3479818772751433642894415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37118066909348625524207093 3479818772751433642894415)
        ·
          refine ⟨5219728159127150464341623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3479818772751433642894415 5219728159127150464341623)
          ·
            refine ⟨7829592238690725696512435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5219728159127150464341623 7829592238690725696512435)
            ·
              refine ⟨11744388358036088544768653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7829592238690725696512435 11744388358036088544768653)
              ·
                refine ⟨4404145634263533204288245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11744388358036088544768653 4404145634263533204288245)
                ·
                  refine ⟨412888653212206237902023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4404145634263533204288245 412888653212206237902023)
                  ·
                    rfl

theorem cell22_3618440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 5].length) (baseStart_3618440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618440 prefixEnd_3618440 := by exact prefixLift 3618440
  have htrace : WordTrace (prefixWord ++ tailWord_3618440) baseStart_3618440 baseEnd_3618440 := by
    simpa [prefixWord, tailWord_3618440, baseEnd_3618440] using wordTrace_append hprefix tailTrace_3618440
  have hstable : (prefixWord ++ tailWord_3618440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618440).length < 2 ^ (prefixWord ++ tailWord_3618440).sum := by decide
  have hdescent : baseEnd_3618440 < baseStart_3618440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618478 : List Nat := [4, 1, 4, 1, 3, 1, 2, 2, 1, 3]
def baseStart_3618478 : Nat := 118140960795 + 3618478 * 2 ^ 59
def prefixEnd_3618478 : Nat := 4983230072969 + 3 ^ 40 * 3618478 * 2
def baseEnd_3618478 : Nat := 1238678967813199281255953

theorem tailTrace_3618478 : CollatzResearch.WordTrace tailWord_3618478 prefixEnd_3618478 1238678967813199281255953 := by
  unfold tailWord_3618478
  simp only [CollatzResearch.WordTrace]
  refine ⟨16497091873109958460883011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87984489989919778458042725 16497091873109958460883011)
  ·
    refine ⟨24745637809664937691324517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16497091873109958460883011 24745637809664937691324517)
    ·
      refine ⟨4639807089312175817123347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24745637809664937691324517 4639807089312175817123347)
      ·
        refine ⟨6959710633968263725685021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4639807089312175817123347 6959710633968263725685021)
        ·
          refine ⟨2609891487738098897131883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6959710633968263725685021 2609891487738098897131883)
          ·
            refine ⟨3914837231607148345697825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609891487738098897131883 3914837231607148345697825)
            ·
              refine ⟨2936127923705361259273369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3914837231607148345697825 2936127923705361259273369)
              ·
                refine ⟨2202095942779020944455027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2936127923705361259273369 2202095942779020944455027)
                ·
                  refine ⟨3303143914168531416682541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202095942779020944455027 3303143914168531416682541)
                  ·
                    refine ⟨1238678967813199281255953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3303143914168531416682541 1238678967813199281255953)
                    ·
                      rfl

theorem cell22_3618478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_3618478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618478 prefixEnd_3618478 := by exact prefixLift 3618478
  have htrace : WordTrace (prefixWord ++ tailWord_3618478) baseStart_3618478 baseEnd_3618478 := by
    simpa [prefixWord, tailWord_3618478, baseEnd_3618478] using wordTrace_append hprefix tailTrace_3618478
  have hstable : (prefixWord ++ tailWord_3618478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618478).length < 2 ^ (prefixWord ++ tailWord_3618478).sum := by decide
  have hdescent : baseEnd_3618478 < baseStart_3618478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618500 : List Nat := [2, 3, 3, 1, 1, 1, 1, 5, 2, 3]
def baseStart_3618500 : Nat := 118140960795 + 3618500 * 2 ^ 59
def prefixEnd_3618500 : Nat := 4983230072969 + 3 ^ 40 * 3618500 * 2
def baseEnd_3618500 : Nat := 1238686498862798557205885

theorem tailTrace_3618500 : CollatzResearch.WordTrace tailWord_3618500 prefixEnd_3618500 1238686498862798557205885 := by
  unfold tailWord_3618500
  simp only [CollatzResearch.WordTrace]
  refine ⟨65988768695399982722182477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87985024927199976962909969 65988768695399982722182477)
  ·
    refine ⟨24745788260774993520818429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65988768695399982722182477 24745788260774993520818429)
    ·
      refine ⟨9279670597790622570306911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24745788260774993520818429 9279670597790622570306911)
      ·
        refine ⟨13919505896685933855460367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9279670597790622570306911 13919505896685933855460367)
        ·
          refine ⟨20879258845028900783190551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13919505896685933855460367 20879258845028900783190551)
          ·
            refine ⟨31318888267543351174785827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20879258845028900783190551 31318888267543351174785827)
            ·
              refine ⟨46978332401315026762178741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31318888267543351174785827 46978332401315026762178741)
              ·
                refine ⟨4404218662623283758954257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46978332401315026762178741 4404218662623283758954257)
                ·
                  refine ⟨3303163996967462819215693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4404218662623283758954257 3303163996967462819215693)
                  ·
                    refine ⟨1238686498862798557205885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3303163996967462819215693 1238686498862798557205885)
                    ·
                      rfl

theorem cell22_3618500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_3618500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618500 prefixEnd_3618500 := by exact prefixLift 3618500
  have htrace : WordTrace (prefixWord ++ tailWord_3618500) baseStart_3618500 baseEnd_3618500 := by
    simpa [prefixWord, tailWord_3618500, baseEnd_3618500] using wordTrace_append hprefix tailTrace_3618500
  have hstable : (prefixWord ++ tailWord_3618500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618500).length < 2 ^ (prefixWord ++ tailWord_3618500).sum := by decide
  have hdescent : baseEnd_3618500 < baseStart_3618500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618502 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_3618502 : Nat := 118140960795 + 3618502 * 2 ^ 59
def prefixEnd_3618502 : Nat := 4983230072969 + 3 ^ 40 * 3618502 * 2
def baseEnd_3618502 : Nat := 412895727834557072885293

theorem tailTrace_3618502 : CollatzResearch.WordTrace tailWord_3618502 prefixEnd_3618502 412895727834557072885293 := by
  unfold tailWord_3618502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4124300323024772493310555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87985073557861813190625173 4124300323024772493310555)
  ·
    refine ⟨6186450484537158739965833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4124300323024772493310555 6186450484537158739965833)
    ·
      refine ⟨4639837863402869054974375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6186450484537158739965833 4639837863402869054974375)
      ·
        refine ⟨6959756795104303582461563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4639837863402869054974375 6959756795104303582461563)
        ·
          refine ⟨10439635192656455373692345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6959756795104303582461563 10439635192656455373692345)
          ·
            refine ⟨7829726394492341530269259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10439635192656455373692345 7829726394492341530269259)
            ·
              refine ⟨11744589591738512295403889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7829726394492341530269259 11744589591738512295403889)
              ·
                refine ⟨8808442193803884221552917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11744589591738512295403889 8808442193803884221552917)
                ·
                  refine ⟨412895727834557072885293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8808442193803884221552917 412895727834557072885293)
                  ·
                    rfl

theorem cell22_3618502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_3618502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618502 prefixEnd_3618502 := by exact prefixLift 3618502
  have htrace : WordTrace (prefixWord ++ tailWord_3618502) baseStart_3618502 baseEnd_3618502 := by
    simpa [prefixWord, tailWord_3618502, baseEnd_3618502] using wordTrace_append hprefix tailTrace_3618502
  have hstable : (prefixWord ++ tailWord_3618502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618502).length < 2 ^ (prefixWord ++ tailWord_3618502).sum := by decide
  have hdescent : baseEnd_3618502 < baseStart_3618502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618513 : List Nat := [1, 2, 2, 1, 2, 5, 3, 6]
def baseStart_3618513 : Nat := 118140960795 + 3618513 * 2 ^ 59
def prefixEnd_3618513 : Nat := 4983230072969 + 3 ^ 40 * 3618513 * 2
def baseEnd_3618513 : Nat := 137632327669830095181205

theorem tailTrace_3618513 : CollatzResearch.WordTrace tailWord_3618513 prefixEnd_3618513 137632327669830095181205 := by
  unfold tailWord_3618513
  simp only [CollatzResearch.WordTrace]
  refine ⟨131978011539752868664588193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87985341026501912443058795 131978011539752868664588193)
  ·
    refine ⟨98983508654814651498441145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131978011539752868664588193 98983508654814651498441145)
    ·
      refine ⟨74237631491110988623830859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98983508654814651498441145 74237631491110988623830859)
      ·
        refine ⟨111356447236666482935746289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74237631491110988623830859 111356447236666482935746289)
        ·
          refine ⟨83517335427499862201809717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111356447236666482935746289 83517335427499862201809717)
          ·
            refine ⟨7829750196328112081419661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83517335427499862201809717 7829750196328112081419661)
            ·
              refine ⟨2936156323623042030532373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7829750196328112081419661 2936156323623042030532373)
              ·
                refine ⟨137632327669830095181205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2936156323623042030532373 137632327669830095181205)
                ·
                  rfl

theorem cell22_3618513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 6].length) (baseStart_3618513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618513 prefixEnd_3618513 := by exact prefixLift 3618513
  have htrace : WordTrace (prefixWord ++ tailWord_3618513) baseStart_3618513 baseEnd_3618513 := by
    simpa [prefixWord, tailWord_3618513, baseEnd_3618513] using wordTrace_append hprefix tailTrace_3618513
  have hstable : (prefixWord ++ tailWord_3618513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618513).length < 2 ^ (prefixWord ++ tailWord_3618513).sum := by decide
  have hdescent : baseEnd_3618513 < baseStart_3618513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618545 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 3, 3]
def baseStart_3618545 : Nat := 118140960795 + 3618545 * 2 ^ 59
def prefixEnd_3618545 : Nat := 4983230072969 + 3 ^ 40 * 3618545 * 2
def baseEnd_3618545 : Nat := 1238701903282433439830747

theorem tailTrace_3618545 : CollatzResearch.WordTrace tailWord_3618545 prefixEnd_3618545 1238701903282433439830747 := by
  unfold tailWord_3618545
  simp only [CollatzResearch.WordTrace]
  refine ⟨131979178675636938129753089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87986119117091292086502059 131979178675636938129753089)
  ·
    refine ⟨98984384006727703597314817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131979178675636938129753089 98984384006727703597314817)
    ·
      refine ⟨74238288005045777697986113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98984384006727703597314817 74238288005045777697986113)
      ·
        refine ⟨55678716003784333273489585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74238288005045777697986113 55678716003784333273489585)
        ·
          refine ⟨41759037002838249955117189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55678716003784333273489585 41759037002838249955117189)
          ·
            refine ⟨7829819438032171866584473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41759037002838249955117189 7829819438032171866584473)
            ·
              refine ⟨5872364578524128899938355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7829819438032171866584473 5872364578524128899938355)
              ·
                refine ⟨8808546867786193349907533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5872364578524128899938355 8808546867786193349907533)
                ·
                  refine ⟨3303205075419822506215325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8808546867786193349907533 3303205075419822506215325)
                  ·
                    refine ⟨1238701903282433439830747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3303205075419822506215325 1238701903282433439830747)
                    ·
                      rfl

theorem cell22_3618545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_3618545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618545 prefixEnd_3618545 := by exact prefixLift 3618545
  have htrace : WordTrace (prefixWord ++ tailWord_3618545) baseStart_3618545 baseEnd_3618545 := by
    simpa [prefixWord, tailWord_3618545, baseEnd_3618545] using wordTrace_append hprefix tailTrace_3618545
  have hstable : (prefixWord ++ tailWord_3618545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618545).length < 2 ^ (prefixWord ++ tailWord_3618545).sum := by decide
  have hdescent : baseEnd_3618545 < baseStart_3618545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618601 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 2, 9]
def baseStart_3618601 : Nat := 118140960795 + 3618601 * 2 ^ 59
def prefixEnd_3618601 : Nat := 4983230072969 + 3 ^ 40 * 3618601 * 2
def baseEnd_3618601 : Nat := 1238721073226867960430575

theorem tailTrace_3618601 : CollatzResearch.WordTrace tailWord_3618601 prefixEnd_3618601 1238721073226867960430575 := by
  unfold tailWord_3618601
  simp only [CollatzResearch.WordTrace]
  refine ⟨131981221163434059693791657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87987480775622706462527771 131981221163434059693791657)
  ·
    refine ⟨98985915872575544770343743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131981221163434059693791657 98985915872575544770343743)
    ·
      refine ⟨148478873808863317155515615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98985915872575544770343743 148478873808863317155515615)
      ·
        refine ⟨222718310713294975733273423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148478873808863317155515615 222718310713294975733273423)
        ·
          refine ⟨334077466069942463599910135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222718310713294975733273423 334077466069942463599910135)
          ·
            refine ⟨501116199104913695399865203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334077466069942463599910135 501116199104913695399865203)
            ·
              refine ⟨751674298657370543099797805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501116199104913695399865203 751674298657370543099797805)
              ·
                refine ⟨281877861996513953662424177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 751674298657370543099797805 281877861996513953662424177)
                ·
                  refine ⟨211408396497385465246818133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281877861996513953662424177 211408396497385465246818133)
                  ·
                    refine ⟨1238721073226867960430575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 211408396497385465246818133 1238721073226867960430575)
                    ·
                      rfl

theorem cell22_3618601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_3618601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618601 prefixEnd_3618601 := by exact prefixLift 3618601
  have htrace : WordTrace (prefixWord ++ tailWord_3618601) baseStart_3618601 baseEnd_3618601 := by
    simpa [prefixWord, tailWord_3618601, baseEnd_3618601] using wordTrace_append hprefix tailTrace_3618601
  have hstable : (prefixWord ++ tailWord_3618601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618601).length < 2 ^ (prefixWord ++ tailWord_3618601).sum := by decide
  have hdescent : baseEnd_3618601 < baseStart_3618601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618622 : List Nat := [4, 2, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_3618622 : Nat := 118140960795 + 3618622 * 2 ^ 59
def prefixEnd_3618622 : Nat := 4983230072969 + 3 ^ 40 * 3618622 * 2
def baseEnd_3618622 : Nat := 1238728261956030905655511

theorem tailTrace_3618622 : CollatzResearch.WordTrace tailWord_3618622 prefixEnd_3618622 1238728261956030905655511 := by
  unfold tailWord_3618622
  simp only [CollatzResearch.WordTrace]
  refine ⟨16497748387044747535038265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87987991397571986853537413 16497748387044747535038265)
  ·
    refine ⟨12373311290283560651278699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16497748387044747535038265 12373311290283560651278699)
    ·
      refine ⟨18559966935425340976918049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12373311290283560651278699 18559966935425340976918049)
      ·
        refine ⟨13919975201569005732688537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18559966935425340976918049 13919975201569005732688537)
        ·
          refine ⟨10439981401176754299516403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13919975201569005732688537 10439981401176754299516403)
          ·
            refine ⟨15659972101765131449274605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10439981401176754299516403 15659972101765131449274605)
            ·
              refine ⟨5872489538161924293477977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15659972101765131449274605 5872489538161924293477977)
              ·
                refine ⟨4404367153621443220108483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5872489538161924293477977 4404367153621443220108483)
                ·
                  refine ⟨6606550730432164830162725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4404367153621443220108483 6606550730432164830162725)
                  ·
                    refine ⟨1238728261956030905655511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6606550730432164830162725 1238728261956030905655511)
                    ·
                      rfl

theorem cell22_3618622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_3618622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618622 prefixEnd_3618622 := by exact prefixLift 3618622
  have htrace : WordTrace (prefixWord ++ tailWord_3618622) baseStart_3618622 baseEnd_3618622 := by
    simpa [prefixWord, tailWord_3618622, baseEnd_3618622] using wordTrace_append hprefix tailTrace_3618622
  have hstable : (prefixWord ++ tailWord_3618622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618622).length < 2 ^ (prefixWord ++ tailWord_3618622).sum := by decide
  have hdescent : baseEnd_3618622 < baseStart_3618622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618693 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 7]
def baseStart_3618693 : Nat := 118140960795 + 3618693 * 2 ^ 59
def prefixEnd_3618693 : Nat := 4983230072969 + 3 ^ 40 * 3618693 * 2
def baseEnd_3618693 : Nat := 412917522235670129043431

theorem tailTrace_3618693 : CollatzResearch.WordTrace tailWord_3618693 prefixEnd_3618693 412917522235670129043431 := by
  unfold tailWord_3618693
  simp only [CollatzResearch.WordTrace]
  refine ⟨131984576679100759406140733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87989717786067172937427155 131984576679100759406140733)
  ·
    refine ⟨49494216254662784777302775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131984576679100759406140733 49494216254662784777302775)
    ·
      refine ⟨74241324381994177165954163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49494216254662784777302775 74241324381994177165954163)
      ·
        refine ⟨111361986572991265748931245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74241324381994177165954163 111361986572991265748931245)
        ·
          refine ⟨41760744964871724655849217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111361986572991265748931245 41760744964871724655849217)
          ·
            refine ⟨31320558723653793491886913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41760744964871724655849217 31320558723653793491886913)
            ·
              refine ⟨23490419042740345118915185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31320558723653793491886913 23490419042740345118915185)
              ·
                refine ⟨17617814282055258839186389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23490419042740345118915185 17617814282055258839186389)
                ·
                  refine ⟨412917522235670129043431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17617814282055258839186389 412917522235670129043431)
                  ·
                    rfl

theorem cell22_3618693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_3618693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618693 prefixEnd_3618693 := by exact prefixLift 3618693
  have htrace : WordTrace (prefixWord ++ tailWord_3618693) baseStart_3618693 baseEnd_3618693 := by
    simpa [prefixWord, tailWord_3618693, baseEnd_3618693] using wordTrace_append hprefix tailTrace_3618693
  have hstable : (prefixWord ++ tailWord_3618693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618693).length < 2 ^ (prefixWord ++ tailWord_3618693).sum := by decide
  have hdescent : baseEnd_3618693 < baseStart_3618693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618714 : List Nat := [3, 1, 1, 4, 2, 1, 2, 4, 1, 3]
def baseStart_3618714 : Nat := 118140960795 + 3618714 * 2 ^ 59
def prefixEnd_3618714 : Nat := 4983230072969 + 3 ^ 40 * 3618714 * 2
def baseEnd_3618714 : Nat := 1238759755436173332355229

theorem tailTrace_3618714 : CollatzResearch.WordTrace tailWord_3618714 prefixEnd_3618714 1238759755436173332355229 := by
  unfold tailWord_3618714
  simp only [CollatzResearch.WordTrace]
  refine ⟨32996335653006169998163799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87990228408016453328436797 32996335653006169998163799)
  ·
    refine ⟨49494503479509254997245699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32996335653006169998163799 49494503479509254997245699)
    ·
      refine ⟨74241755219263882495868549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49494503479509254997245699 74241755219263882495868549)
      ·
        refine ⟨13920329103611977967975353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74241755219263882495868549 13920329103611977967975353)
        ·
          refine ⟨10440246827708983475981515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13920329103611977967975353 10440246827708983475981515)
          ·
            refine ⟨15660370241563475213972273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10440246827708983475981515 15660370241563475213972273)
            ·
              refine ⟨11745277681172606410479205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15660370241563475213972273 11745277681172606410479205)
              ·
                refine ⟨2202239565219863701964851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11745277681172606410479205 2202239565219863701964851)
                ·
                  refine ⟨3303359347829795552947277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202239565219863701964851 3303359347829795552947277)
                  ·
                    refine ⟨1238759755436173332355229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3303359347829795552947277 1238759755436173332355229)
                    ·
                      rfl

theorem cell22_3618714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 1, 3].length) (baseStart_3618714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618714 prefixEnd_3618714 := by exact prefixLift 3618714
  have htrace : WordTrace (prefixWord ++ tailWord_3618714) baseStart_3618714 baseEnd_3618714 := by
    simpa [prefixWord, tailWord_3618714, baseEnd_3618714] using wordTrace_append hprefix tailTrace_3618714
  have hstable : (prefixWord ++ tailWord_3618714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618714).length < 2 ^ (prefixWord ++ tailWord_3618714).sum := by decide
  have hdescent : baseEnd_3618714 < baseStart_3618714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618748 : List Nat := [2, 2, 2, 5, 1, 2, 1, 3, 1, 3]
def baseStart_3618748 : Nat := 118140960795 + 3618748 * 2 ^ 59
def prefixEnd_3618748 : Nat := 4983230072969 + 3 ^ 40 * 3618748 * 2
def baseEnd_3618748 : Nat := 1238771394331008577005125

theorem tailTrace_3618748 : CollatzResearch.WordTrace tailWord_3618748 prefixEnd_3618748 1238771394331008577005125 := by
  unfold tailWord_3618748
  simp only [CollatzResearch.WordTrace]
  refine ⟨65993291346950751899696449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87991055129267669199595265 65993291346950751899696449)
  ·
    refine ⟨49494968510213063924772337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65993291346950751899696449 49494968510213063924772337)
    ·
      refine ⟨37121226382659797943579253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49494968510213063924772337 37121226382659797943579253)
      ·
        refine ⟨3480114973374356057210555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37121226382659797943579253 3480114973374356057210555)
        ·
          refine ⟨5220172460061534085815833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3480114973374356057210555 5220172460061534085815833)
          ·
            refine ⟨3915129345046150564361875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5220172460061534085815833 3915129345046150564361875)
            ·
              refine ⟨5872694017569225846542813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3915129345046150564361875 5872694017569225846542813)
              ·
                refine ⟨2202260256588459692453555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5872694017569225846542813 2202260256588459692453555)
                ·
                  refine ⟨3303390384882689538680333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202260256588459692453555 3303390384882689538680333)
                  ·
                    refine ⟨1238771394331008577005125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3303390384882689538680333 1238771394331008577005125)
                    ·
                      rfl

theorem cell22_3618748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_3618748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618748 prefixEnd_3618748 := by exact prefixLift 3618748
  have htrace : WordTrace (prefixWord ++ tailWord_3618748) baseStart_3618748 baseEnd_3618748 := by
    simpa [prefixWord, tailWord_3618748, baseEnd_3618748] using wordTrace_append hprefix tailTrace_3618748
  have hstable : (prefixWord ++ tailWord_3618748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618748).length < 2 ^ (prefixWord ++ tailWord_3618748).sum := by decide
  have hdescent : baseEnd_3618748 < baseStart_3618748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618791 : List Nat := [1, 1, 5, 2, 4, 1, 1, 2, 1, 4]
def baseStart_3618791 : Nat := 118140960795 + 3618791 * 2 ^ 59
def prefixEnd_3618791 : Nat := 4983230072969 + 3 ^ 40 * 3618791 * 2
def baseEnd_3618791 : Nat := 1238786114109770798179993

theorem tailTrace_3618791 : CollatzResearch.WordTrace tailWord_3618791 prefixEnd_3618791 1238786114109770798179993 := by
  unfold tailWord_3618791
  simp only [CollatzResearch.WordTrace]
  refine ⟨131988151032745722143208227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87992100688497148095472151 131988151032745722143208227)
  ·
    refine ⟨197982226549118583214812341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131988151032745722143208227 197982226549118583214812341)
    ·
      refine ⟨18560833738979867176388657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197982226549118583214812341 18560833738979867176388657)
      ·
        refine ⟨13920625304234900382291493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18560833738979867176388657 13920625304234900382291493)
        ·
          refine ⟨2610117244544043821679655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13920625304234900382291493 2610117244544043821679655)
          ·
            refine ⟨3915175866816065732519483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610117244544043821679655 3915175866816065732519483)
            ·
              refine ⟨5872763800224098598779225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3915175866816065732519483 5872763800224098598779225)
              ·
                refine ⟨4404572850168073949084419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5872763800224098598779225 4404572850168073949084419)
                ·
                  refine ⟨6606859275252110923626629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4404572850168073949084419 6606859275252110923626629)
                  ·
                    refine ⟨1238786114109770798179993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6606859275252110923626629 1238786114109770798179993)
                    ·
                      rfl

theorem cell22_3618791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_3618791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618791 prefixEnd_3618791 := by exact prefixLift 3618791
  have htrace : WordTrace (prefixWord ++ tailWord_3618791) baseStart_3618791 baseEnd_3618791 := by
    simpa [prefixWord, tailWord_3618791, baseEnd_3618791] using wordTrace_append hprefix tailTrace_3618791
  have hstable : (prefixWord ++ tailWord_3618791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618791).length < 2 ^ (prefixWord ++ tailWord_3618791).sum := by decide
  have hdescent : baseEnd_3618791 < baseStart_3618791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618830 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_3618830 : Nat := 118140960795 + 3618830 * 2 ^ 59
def prefixEnd_3618830 : Nat := 4983230072969 + 3 ^ 40 * 3618830 * 2
def baseEnd_3618830 : Nat := 1238799464606787696454873

theorem tailTrace_3618830 : CollatzResearch.WordTrace tailWord_3618830 prefixEnd_3618830 1238799464606787696454873 := by
  unfold tailWord_3618830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16498696684950553975484743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87993048986402954535918629 16498696684950553975484743)
  ·
    refine ⟨24748045027425830963227115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16498696684950553975484743 24748045027425830963227115)
    ·
      refine ⟨37122067541138746444840673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24748045027425830963227115 37122067541138746444840673)
      ·
        refine ⟨27841550655854059833630505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37122067541138746444840673 27841550655854059833630505)
        ·
          refine ⟨20881162991890544875222879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27841550655854059833630505 20881162991890544875222879)
          ·
            refine ⟨31321744487835817312834319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20881162991890544875222879 31321744487835817312834319)
            ·
              refine ⟨46982616731753725969251479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31321744487835817312834319 46982616731753725969251479)
              ·
                refine ⟨70473925097630588953877219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46982616731753725969251479 70473925097630588953877219)
                ·
                  refine ⟨105710887646445883430815829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70473925097630588953877219 105710887646445883430815829)
                  ·
                    refine ⟨1238799464606787696454873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105710887646445883430815829 1238799464606787696454873)
                    ·
                      rfl

theorem cell22_3618830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_3618830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618830 prefixEnd_3618830 := by exact prefixLift 3618830
  have htrace : WordTrace (prefixWord ++ tailWord_3618830) baseStart_3618830 baseEnd_3618830 := by
    simpa [prefixWord, tailWord_3618830, baseEnd_3618830] using wordTrace_append hprefix tailTrace_3618830
  have hstable : (prefixWord ++ tailWord_3618830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618830).length < 2 ^ (prefixWord ++ tailWord_3618830).sum := by decide
  have hdescent : baseEnd_3618830 < baseStart_3618830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618849 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 3, 3]
def baseStart_3618849 : Nat := 118140960795 + 3618849 * 2 ^ 59
def prefixEnd_3618849 : Nat := 4983230072969 + 3 ^ 40 * 3618849 * 2
def baseEnd_3618849 : Nat := 1238805968695077980229815

theorem tailTrace_3618849 : CollatzResearch.WordTrace tailWord_3618849 prefixEnd_3618849 1238805968695077980229815 := by
  unfold tailWord_3618849
  simp only [CollatzResearch.WordTrace]
  refine ⟨131990266466535598048819601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87993510977690398699213067 131990266466535598048819601)
  ·
    refine ⟨98992699849901698536614701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131990266466535598048819601 98992699849901698536614701)
    ·
      refine ⟨37122262443713136951230513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98992699849901698536614701 37122262443713136951230513)
      ·
        refine ⟨27841696832784852713422885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37122262443713136951230513 27841696832784852713422885)
        ·
          refine ⟨5220318156147159883766791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27841696832784852713422885 5220318156147159883766791)
          ·
            refine ⟨7830477234220739825650187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5220318156147159883766791 7830477234220739825650187)
            ·
              refine ⟨11745715851331109738475281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7830477234220739825650187 11745715851331109738475281)
              ·
                refine ⟨8809286888498332303856461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11745715851331109738475281 8809286888498332303856461)
                ·
                  refine ⟨3303482583186874613946173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8809286888498332303856461 3303482583186874613946173)
                  ·
                    refine ⟨1238805968695077980229815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3303482583186874613946173 1238805968695077980229815)
                    ·
                      rfl

theorem cell22_3618849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_3618849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618849 prefixEnd_3618849 := by exact prefixLift 3618849
  have htrace : WordTrace (prefixWord ++ tailWord_3618849) baseStart_3618849 baseEnd_3618849 := by
    simpa [prefixWord, tailWord_3618849, baseEnd_3618849] using wordTrace_append hprefix tailTrace_3618849
  have hstable : (prefixWord ++ tailWord_3618849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618849).length < 2 ^ (prefixWord ++ tailWord_3618849).sum := by decide
  have hdescent : baseEnd_3618849 < baseStart_3618849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618866 : List Nat := [3, 2, 1, 1, 2, 4, 2, 3, 1, 3]
def baseStart_3618866 : Nat := 118140960795 + 3618866 * 2 ^ 59
def prefixEnd_3618866 : Nat := 4983230072969 + 3 ^ 40 * 3618866 * 2
def baseEnd_3618866 : Nat := 1238811788142495602554763

theorem tailTrace_3618866 : CollatzResearch.WordTrace tailWord_3618866 prefixEnd_3618866 1238811788142495602554763 := by
  unfold tailWord_3618866
  simp only [CollatzResearch.WordTrace]
  refine ⟨32997721626868502488047113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87993924338316006634792301 32997721626868502488047113)
  ·
    refine ⟨24748291220151376866035335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32997721626868502488047113 24748291220151376866035335)
    ·
      refine ⟨37122436830227065299053003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24748291220151376866035335 37122436830227065299053003)
      ·
        refine ⟨55683655245340597948579505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37122436830227065299053003 55683655245340597948579505)
        ·
          refine ⟨41762741434005448461434629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55683655245340597948579505 41762741434005448461434629)
          ·
            refine ⟨7830514018876021586518993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41762741434005448461434629 7830514018876021586518993)
            ·
              refine ⟨5872885514157016189889245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7830514018876021586518993 5872885514157016189889245)
              ·
                refine ⟨2202332067808881071208467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5872885514157016189889245 2202332067808881071208467)
                ·
                  refine ⟨3303498101713321606812701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202332067808881071208467 3303498101713321606812701)
                  ·
                    refine ⟨1238811788142495602554763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3303498101713321606812701 1238811788142495602554763)
                    ·
                      rfl

theorem cell22_3618866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_3618866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618866 prefixEnd_3618866 := by exact prefixLift 3618866
  have htrace : WordTrace (prefixWord ++ tailWord_3618866) baseStart_3618866 baseEnd_3618866 := by
    simpa [prefixWord, tailWord_3618866, baseEnd_3618866] using wordTrace_append hprefix tailTrace_3618866
  have hstable : (prefixWord ++ tailWord_3618866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618866).length < 2 ^ (prefixWord ++ tailWord_3618866).sum := by decide
  have hdescent : baseEnd_3618866 < baseStart_3618866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618924 : List Nat := [2, 2, 1, 1, 3, 3, 3, 3, 4]
def baseStart_3618924 : Nat := 118140960795 + 3618924 * 2 ^ 59
def prefixEnd_3618924 : Nat := 4983230072969 + 3 ^ 40 * 3618924 * 2
def baseEnd_3618924 : Nat := 412943880909267594868195

theorem tailTrace_3618924 : CollatzResearch.WordTrace tailWord_3618924 prefixEnd_3618924 412943880909267594868195 := by
  unfold tailWord_3618924
  simp only [CollatzResearch.WordTrace]
  refine ⟨65996500970631942928899913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87995334627509257238533217 65996500970631942928899913)
  ·
    refine ⟨49497375727973957196674935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65996500970631942928899913 49497375727973957196674935)
    ·
      refine ⟨74246063591960935795012403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49497375727973957196674935 74246063591960935795012403)
      ·
        refine ⟨111369095387941403692518605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74246063591960935795012403 111369095387941403692518605)
        ·
          refine ⟨41763410770478026384694477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111369095387941403692518605 41763410770478026384694477)
          ·
            refine ⟨15661279038929259894260429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41763410770478026384694477 15661279038929259894260429)
            ·
              refine ⟨5872979639598472460347661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15661279038929259894260429 5872979639598472460347661)
              ·
                refine ⟨2202367364849427172630373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5872979639598472460347661 2202367364849427172630373)
                ·
                  refine ⟨412943880909267594868195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2202367364849427172630373 412943880909267594868195)
                  ·
                    rfl

theorem cell22_3618924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_3618924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618924 prefixEnd_3618924 := by exact prefixLift 3618924
  have htrace : WordTrace (prefixWord ++ tailWord_3618924) baseStart_3618924 baseEnd_3618924 := by
    simpa [prefixWord, tailWord_3618924, baseEnd_3618924] using wordTrace_append hprefix tailTrace_3618924
  have hstable : (prefixWord ++ tailWord_3618924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618924).length < 2 ^ (prefixWord ++ tailWord_3618924).sum := by decide
  have hdescent : baseEnd_3618924 < baseStart_3618924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618935 : List Nat := [1, 1, 3, 1, 1, 5, 10]
def baseStart_3618935 : Nat := 118140960795 + 3618935 * 2 ^ 59
def prefixEnd_3618935 : Nat := 4983230072969 + 3 ^ 40 * 3618935 * 2
def baseEnd_3618935 : Nat := 45882792898244534169613

theorem tailTrace_3618935 : CollatzResearch.WordTrace tailWord_3618935 prefixEnd_3618935 45882792898244534169613 := by
  unfold tailWord_3618935
  simp only [CollatzResearch.WordTrace]
  refine ⟨131993403144224034736450259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87995602096149356490966839 131993403144224034736450259)
  ·
    refine ⟨197990104716336052104675389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131993403144224034736450259 197990104716336052104675389)
    ·
      refine ⟨74246289268626019539253271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197990104716336052104675389 74246289268626019539253271)
      ·
        refine ⟨111369433902939029308879907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74246289268626019539253271 111369433902939029308879907)
        ·
          refine ⟨167054150854408543963319861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111369433902939029308879907 167054150854408543963319861)
          ·
            refine ⟨15661326642600800996561237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167054150854408543963319861 15661326642600800996561237)
            ·
              refine ⟨45882792898244534169613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15661326642600800996561237 45882792898244534169613)
              ·
                rfl

theorem cell22_3618935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 10].length) (baseStart_3618935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618935 prefixEnd_3618935 := by exact prefixLift 3618935
  have htrace : WordTrace (prefixWord ++ tailWord_3618935) baseStart_3618935 baseEnd_3618935 := by
    simpa [prefixWord, tailWord_3618935, baseEnd_3618935] using wordTrace_append hprefix tailTrace_3618935
  have hstable : (prefixWord ++ tailWord_3618935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618935).length < 2 ^ (prefixWord ++ tailWord_3618935).sum := by decide
  have hdescent : baseEnd_3618935 < baseStart_3618935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618937 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 4, 4]
def baseStart_3618937 : Nat := 118140960795 + 3618937 * 2 ^ 59
def prefixEnd_3618937 : Nat := 4983230072969 + 3 ^ 40 * 3618937 * 2
def baseEnd_3618937 : Nat := 1238836092893475084029545

theorem tailTrace_3618937 : CollatzResearch.WordTrace tailWord_3618937 prefixEnd_3618937 1238836092893475084029545 := by
  unfold tailWord_3618937
  simp only [CollatzResearch.WordTrace]
  refine ⟨131993476090216789078023065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87995650726811192718682043 131993476090216789078023065)
  ·
    refine ⟨98995107067662591808517299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131993476090216789078023065 98995107067662591808517299)
    ·
      refine ⟨148492660601493887712775949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98995107067662591808517299 148492660601493887712775949)
      ·
        refine ⟨55684747725560207892290981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148492660601493887712775949 55684747725560207892290981)
        ·
          refine ⟨10440890198542538979804559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55684747725560207892290981 10440890198542538979804559)
          ·
            refine ⟨15661335297813808469706839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10440890198542538979804559 15661335297813808469706839)
            ·
              refine ⟨23492002946720712704560259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15661335297813808469706839 23492002946720712704560259)
              ·
                refine ⟨35238004420081069056840389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23492002946720712704560259 35238004420081069056840389)
                ·
                  refine ⟨6607125828765200448157573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35238004420081069056840389 6607125828765200448157573)
                  ·
                    refine ⟨1238836092893475084029545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6607125828765200448157573 1238836092893475084029545)
                    ·
                      rfl

theorem cell22_3618937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_3618937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618937 prefixEnd_3618937 := by exact prefixLift 3618937
  have htrace : WordTrace (prefixWord ++ tailWord_3618937) baseStart_3618937 baseEnd_3618937 := by
    simpa [prefixWord, tailWord_3618937, baseEnd_3618937] using wordTrace_append hprefix tailTrace_3618937
  have hstable : (prefixWord ++ tailWord_3618937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618937).length < 2 ^ (prefixWord ++ tailWord_3618937).sum := by decide
  have hdescent : baseEnd_3618937 < baseStart_3618937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618941 : List Nat := [1, 4, 1, 1, 3, 3, 3, 2, 4]
def baseStart_3618941 : Nat := 118140960795 + 3618941 * 2 ^ 59
def prefixEnd_3618941 : Nat := 4983230072969 + 3 ^ 40 * 3618941 * 2
def baseEnd_3618941 : Nat := 412945820725073468976511

theorem tailTrace_3618941 : CollatzResearch.WordTrace tailWord_3618941 prefixEnd_3618941 412945820725073468976511 := by
  unfold tailWord_3618941
  simp only [CollatzResearch.WordTrace]
  refine ⟨131993621982202297761168677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87995747988134865174112451 131993621982202297761168677)
  ·
    refine ⟨24748804121662930830219127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131993621982202297761168677 24748804121662930830219127)
    ·
      refine ⟨37123206182494396245328691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24748804121662930830219127 37123206182494396245328691)
      ·
        refine ⟨55684809273741594367993037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37123206182494396245328691 55684809273741594367993037)
        ·
          refine ⟨20881803477653097887997389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55684809273741594367993037 20881803477653097887997389)
          ·
            refine ⟨7830676304119911707999021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20881803477653097887997389 7830676304119911707999021)
            ·
              refine ⟨2936503614044966890499633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7830676304119911707999021 2936503614044966890499633)
              ·
                refine ⟨2202377710533725167874725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2936503614044966890499633 2202377710533725167874725)
                ·
                  refine ⟨412945820725073468976511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2202377710533725167874725 412945820725073468976511)
                  ·
                    rfl

theorem cell22_3618941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_3618941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618941 prefixEnd_3618941 := by exact prefixLift 3618941
  have htrace : WordTrace (prefixWord ++ tailWord_3618941) baseStart_3618941 baseEnd_3618941 := by
    simpa [prefixWord, tailWord_3618941, baseEnd_3618941] using wordTrace_append hprefix tailTrace_3618941
  have hstable : (prefixWord ++ tailWord_3618941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618941).length < 2 ^ (prefixWord ++ tailWord_3618941).sum := by decide
  have hdescent : baseEnd_3618941 < baseStart_3618941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618952 : List Nat := [2, 1, 3, 4, 1, 1, 1, 9]
def baseStart_3618952 : Nat := 118140960795 + 3618952 * 2 ^ 59
def prefixEnd_3618952 : Nat := 4983230072969 + 3 ^ 40 * 3618952 * 2
def baseEnd_3618952 : Nat := 137649025300002227211611

theorem tailTrace_3618952 : CollatzResearch.WordTrace tailWord_3618952 prefixEnd_3618952 137649025300002227211611 := by
  unfold tailWord_3618952
  simp only [CollatzResearch.WordTrace]
  refine ⟨65997011592581223319909555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87996015456774964426546073 65997011592581223319909555)
  ·
    refine ⟨98995517388871834979864333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65997011592581223319909555 98995517388871834979864333)
    ·
      refine ⟨37123319020826938117449125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98995517388871834979864333 37123319020826938117449125)
      ·
        refine ⟨6960622316405050897021711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37123319020826938117449125 6960622316405050897021711)
        ·
          refine ⟨10440933474607576345532567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6960622316405050897021711 10440933474607576345532567)
          ·
            refine ⟨15661400211911364518298851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10440933474607576345532567 15661400211911364518298851)
            ·
              refine ⟨23492100317867046777448277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15661400211911364518298851 23492100317867046777448277)
              ·
                refine ⟨137649025300002227211611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23492100317867046777448277 137649025300002227211611)
                ·
                  rfl

theorem cell22_3618952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 9].length) (baseStart_3618952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618952 prefixEnd_3618952 := by exact prefixLift 3618952
  have htrace : WordTrace (prefixWord ++ tailWord_3618952) baseStart_3618952 baseEnd_3618952 := by
    simpa [prefixWord, tailWord_3618952, baseEnd_3618952] using wordTrace_append hprefix tailTrace_3618952
  have hstable : (prefixWord ++ tailWord_3618952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618952).length < 2 ^ (prefixWord ++ tailWord_3618952).sum := by decide
  have hdescent : baseEnd_3618952 < baseStart_3618952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618990 : List Nat := [4, 1, 4, 2, 1, 1, 2, 2, 2, 3]
def baseStart_3618990 : Nat := 118140960795 + 3618990 * 2 ^ 59
def prefixEnd_3618990 : Nat := 4983230072969 + 3 ^ 40 * 3618990 * 2
def baseEnd_3618990 : Nat := 1238854235876600612454383

theorem tailTrace_3618990 : CollatzResearch.WordTrace tailWord_3618990 prefixEnd_3618990 1238854235876600612454383 := by
  unfold tailWord_3618990
  simp only [CollatzResearch.WordTrace]
  refine ⟨16499426144878097391212803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87996939439349852753134949 16499426144878097391212803)
  ·
    refine ⟨24749139217317146086819205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16499426144878097391212803 24749139217317146086819205)
    ·
      refine ⟨4640463603246964891278601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24749139217317146086819205 4640463603246964891278601)
      ·
        refine ⟨3480347702435223668458951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4640463603246964891278601 3480347702435223668458951)
        ·
          refine ⟨5220521553652835502688427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3480347702435223668458951 5220521553652835502688427)
          ·
            refine ⟨7830782330479253254032641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5220521553652835502688427 7830782330479253254032641)
            ·
              refine ⟨5873086747859439940524481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7830782330479253254032641 5873086747859439940524481)
              ·
                refine ⟨4404815060894579955393361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5873086747859439940524481 4404815060894579955393361)
                ·
                  refine ⟨3303611295670934966545021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4404815060894579955393361 3303611295670934966545021)
                  ·
                    refine ⟨1238854235876600612454383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3303611295670934966545021 1238854235876600612454383)
                    ·
                      rfl

theorem cell22_3618990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_3618990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3618990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3618990 prefixEnd_3618990 := by exact prefixLift 3618990
  have htrace : WordTrace (prefixWord ++ tailWord_3618990) baseStart_3618990 baseEnd_3618990 := by
    simpa [prefixWord, tailWord_3618990, baseEnd_3618990] using wordTrace_append hprefix tailTrace_3618990
  have hstable : (prefixWord ++ tailWord_3618990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618990).length < 2 ^ (prefixWord ++ tailWord_3618990).sum := by decide
  have hdescent : baseEnd_3618990 < baseStart_3618990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619001 : List Nat := [1, 2, 1, 4, 1, 2, 3, 4, 1, 3]
def baseStart_3619001 : Nat := 118140960795 + 3619001 * 2 ^ 59
def prefixEnd_3619001 : Nat := 4983230072969 + 3 ^ 40 * 3619001 * 2
def baseEnd_3619001 : Nat := 1238858001401400250429349

theorem tailTrace_3619001 : CollatzResearch.WordTrace tailWord_3619001 prefixEnd_3619001 1238858001401400250429349 := by
  unfold tailWord_3619001
  simp only [CollatzResearch.WordTrace]
  refine ⟨131995810361984928008352857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87997206907989952005568571 131995810361984928008352857)
  ·
    refine ⟨98996857771488696006264643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131995810361984928008352857 98996857771488696006264643)
    ·
      refine ⟨148495286657233044009396965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98996857771488696006264643 148495286657233044009396965)
      ·
        refine ⟨27842866248231195751761931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148495286657233044009396965 27842866248231195751761931)
        ·
          refine ⟨41764299372346793627642897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27842866248231195751761931 41764299372346793627642897)
          ·
            refine ⟨31323224529260095220732173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41764299372346793627642897 31323224529260095220732173)
            ·
              refine ⟨11746209198472535707774565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31323224529260095220732173 11746209198472535707774565)
              ·
                refine ⟨2202414224713600445207731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11746209198472535707774565 2202414224713600445207731)
                ·
                  refine ⟨3303621337070400667811597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202414224713600445207731 3303621337070400667811597)
                  ·
                    refine ⟨1238858001401400250429349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3303621337070400667811597 1238858001401400250429349)
                    ·
                      rfl

theorem cell22_3619001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 1, 3].length) (baseStart_3619001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619001 prefixEnd_3619001 := by exact prefixLift 3619001
  have htrace : WordTrace (prefixWord ++ tailWord_3619001) baseStart_3619001 baseEnd_3619001 := by
    simpa [prefixWord, tailWord_3619001, baseEnd_3619001] using wordTrace_append hprefix tailTrace_3619001
  have hstable : (prefixWord ++ tailWord_3619001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619001).length < 2 ^ (prefixWord ++ tailWord_3619001).sum := by decide
  have hdescent : baseEnd_3619001 < baseStart_3619001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619057 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 3, 5]
def baseStart_3619057 : Nat := 118140960795 + 3619057 * 2 ^ 59
def prefixEnd_3619057 : Nat := 4983230072969 + 3 ^ 40 * 3619057 * 2
def baseEnd_3619057 : Nat := 1238877171345834771029177

theorem tailTrace_3619057 : CollatzResearch.WordTrace tailWord_3619057 prefixEnd_3619057 1238877171345834771029177 := by
  unfold tailWord_3619057
  simp only [CollatzResearch.WordTrace]
  refine ⟨131997852849782049572391425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87998568566521366381594283 131997852849782049572391425)
  ·
    refine ⟨98998389637336537179293569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131997852849782049572391425 98998389637336537179293569)
    ·
      refine ⟨74248792228002402884470177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98998389637336537179293569 74248792228002402884470177)
      ·
        refine ⟨55686594171001802163352633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74248792228002402884470177 55686594171001802163352633)
        ·
          refine ⟨41764945628251351622514475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55686594171001802163352633 41764945628251351622514475)
          ·
            refine ⟨62647418442377027433771713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41764945628251351622514475 62647418442377027433771713)
            ·
              refine ⟨46985563831782770575328785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62647418442377027433771713 46985563831782770575328785)
              ·
                refine ⟨35239172873837077931496589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46985563831782770575328785 35239172873837077931496589)
                ·
                  refine ⟨13214689827688904224311221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35239172873837077931496589 13214689827688904224311221)
                  ·
                    refine ⟨1238877171345834771029177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13214689827688904224311221 1238877171345834771029177)
                    ·
                      rfl

theorem cell22_3619057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_3619057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619057 prefixEnd_3619057 := by exact prefixLift 3619057
  have htrace : WordTrace (prefixWord ++ tailWord_3619057) baseStart_3619057 baseEnd_3619057 := by
    simpa [prefixWord, tailWord_3619057, baseEnd_3619057] using wordTrace_append hprefix tailTrace_3619057
  have hstable : (prefixWord ++ tailWord_3619057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619057).length < 2 ^ (prefixWord ++ tailWord_3619057).sum := by decide
  have hdescent : baseEnd_3619057 < baseStart_3619057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619059 : List Nat := [1, 1, 1, 2, 2, 4, 1, 6, 4]
def baseStart_3619059 : Nat := 118140960795 + 3619059 * 2 ^ 59
def prefixEnd_3619059 : Nat := 4983230072969 + 3 ^ 40 * 3619059 * 2
def baseEnd_3619059 : Nat := 412959285328902477493057

theorem tailTrace_3619059 : CollatzResearch.WordTrace tailWord_3619059 prefixEnd_3619059 412959285328902477493057 := by
  unfold tailWord_3619059
  simp only [CollatzResearch.WordTrace]
  refine ⟨131997925795774803913964231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87998617197183202609309487 131997925795774803913964231)
  ·
    refine ⟨197996888693662205870946347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131997925795774803913964231 197996888693662205870946347)
    ·
      refine ⟨296995333040493308806419521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197996888693662205870946347 296995333040493308806419521)
      ·
        refine ⟨222746499780369981604814641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296995333040493308806419521 222746499780369981604814641)
        ·
          refine ⟨167059874835277486203610981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222746499780369981604814641 167059874835277486203610981)
          ·
            refine ⟨31323726531614528663177059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167059874835277486203610981 31323726531614528663177059)
            ·
              refine ⟨46985589797421792994765589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31323726531614528663177059 46985589797421792994765589)
              ·
                refine ⟨2202449521754146546629637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46985589797421792994765589 2202449521754146546629637)
                ·
                  refine ⟨412959285328902477493057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2202449521754146546629637 412959285328902477493057)
                  ·
                    rfl

theorem cell22_3619059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 4].length) (baseStart_3619059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619059 prefixEnd_3619059 := by exact prefixLift 3619059
  have htrace : WordTrace (prefixWord ++ tailWord_3619059) baseStart_3619059 baseEnd_3619059 := by
    simpa [prefixWord, tailWord_3619059, baseEnd_3619059] using wordTrace_append hprefix tailTrace_3619059
  have hstable : (prefixWord ++ tailWord_3619059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619059).length < 2 ^ (prefixWord ++ tailWord_3619059).sum := by decide
  have hdescent : baseEnd_3619059 < baseStart_3619059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619072 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 1, 6]
def baseStart_3619072 : Nat := 118140960795 + 3619072 * 2 ^ 59
def prefixEnd_3619072 : Nat := 4983230072969 + 3 ^ 40 * 3619072 * 2
def baseEnd_3619072 : Nat := 1238882306152379731904131

theorem tailTrace_3619072 : CollatzResearch.WordTrace tailWord_3619072 prefixEnd_3619072 1238882306152379731904131 := by
  unfold tailWord_3619072
  simp only [CollatzResearch.WordTrace]
  refine ⟨65999199972363853567093735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87998933296485138089458313 65999199972363853567093735)
  ·
    refine ⟨98998799958545780350640603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65999199972363853567093735 98998799958545780350640603)
    ·
      refine ⟨148498199937818670525960905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98998799958545780350640603 148498199937818670525960905)
      ·
        refine ⟨111373649953364002894470679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148498199937818670525960905 111373649953364002894470679)
        ·
          refine ⟨167060474930046004341706019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111373649953364002894470679 167060474930046004341706019)
          ·
            refine ⟨250590712395069006512559029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167060474930046004341706019 250590712395069006512559029)
            ·
              refine ⟨23492879287037719360552409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 250590712395069006512559029 23492879287037719360552409)
              ·
                refine ⟨17619659465278289520414307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23492879287037719360552409 17619659465278289520414307)
                ·
                  refine ⟨26429489197917434280621461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17619659465278289520414307 26429489197917434280621461)
                  ·
                    refine ⟨1238882306152379731904131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26429489197917434280621461 1238882306152379731904131)
                    ·
                      rfl

theorem cell22_3619072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_3619072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619072 prefixEnd_3619072 := by exact prefixLift 3619072
  have htrace : WordTrace (prefixWord ++ tailWord_3619072) baseStart_3619072 baseEnd_3619072 := by
    simpa [prefixWord, tailWord_3619072, baseEnd_3619072] using wordTrace_append hprefix tailTrace_3619072
  have hstable : (prefixWord ++ tailWord_3619072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619072).length < 2 ^ (prefixWord ++ tailWord_3619072).sum := by decide
  have hdescent : baseEnd_3619072 < baseStart_3619072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619104 : List Nat := [2, 1, 1, 5, 2, 3, 8]
def baseStart_3619104 : Nat := 118140960795 + 3619104 * 2 ^ 59
def prefixEnd_3619104 : Nat := 4983230072969 + 3 ^ 40 * 3619104 * 2
def baseEnd_3619104 : Nat := 45884935570605270929779

theorem tailTrace_3619104 : CollatzResearch.WordTrace tailWord_3619104 prefixEnd_3619104 45884935570605270929779 := by
  unfold tailWord_3619104
  simp only [CollatzResearch.WordTrace]
  refine ⟨65999783540305888299676183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87999711387074517732901577 65999783540305888299676183)
  ·
    refine ⟨98999675310458832449514275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65999783540305888299676183 98999675310458832449514275)
    ·
      refine ⟨148499512965688248674271413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98999675310458832449514275 148499512965688248674271413)
      ·
        refine ⟨13921829340533273313212945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148499512965688248674271413 13921829340533273313212945)
        ·
          refine ⟨10441372005399954984909709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13921829340533273313212945 10441372005399954984909709)
          ·
            refine ⟨3915514502024983119341141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10441372005399954984909709 3915514502024983119341141)
            ·
              refine ⟨45884935570605270929779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3915514502024983119341141 45884935570605270929779)
              ·
                rfl

theorem cell22_3619104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 8].length) (baseStart_3619104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619104 prefixEnd_3619104 := by exact prefixLift 3619104
  have htrace : WordTrace (prefixWord ++ tailWord_3619104) baseStart_3619104 baseEnd_3619104 := by
    simpa [prefixWord, tailWord_3619104, baseEnd_3619104] using wordTrace_append hprefix tailTrace_3619104
  have hstable : (prefixWord ++ tailWord_3619104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619104).length < 2 ^ (prefixWord ++ tailWord_3619104).sum := by decide
  have hdescent : baseEnd_3619104 < baseStart_3619104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619106 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_3619106 : Nat := 118140960795 + 3619106 * 2 ^ 59
def prefixEnd_3619106 : Nat := 4983230072969 + 3 ^ 40 * 3619106 * 2
def baseEnd_3619106 : Nat := 1238893945047214976554027

theorem tailTrace_3619106 : CollatzResearch.WordTrace tailWord_3619106 prefixEnd_3619106 1238893945047214976554027 := by
  unfold tailWord_3619106
  simp only [CollatzResearch.WordTrace]
  refine ⟨32999910006651132735231293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87999760017736353960616781 32999910006651132735231293)
  ·
    refine ⟨12374966252494174775711735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32999910006651132735231293 12374966252494174775711735)
    ·
      refine ⟨18562449378741262163567603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12374966252494174775711735 18562449378741262163567603)
      ·
        refine ⟨27843674068111893245351405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18562449378741262163567603 27843674068111893245351405)
        ·
          refine ⟨10441377775541959967006777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27843674068111893245351405 10441377775541959967006777)
          ·
            refine ⟨7831033331656469975255083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10441377775541959967006777 7831033331656469975255083)
            ·
              refine ⟨11746549997484704962882625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7831033331656469975255083 11746549997484704962882625)
              ·
                refine ⟨8809912498113528722161969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11746549997484704962882625 8809912498113528722161969)
                ·
                  refine ⟨6607434373585146541621477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8809912498113528722161969 6607434373585146541621477)
                  ·
                    refine ⟨1238893945047214976554027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6607434373585146541621477 1238893945047214976554027)
                    ·
                      rfl

theorem cell22_3619106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_3619106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619106 prefixEnd_3619106 := by exact prefixLift 3619106
  have htrace : WordTrace (prefixWord ++ tailWord_3619106) baseStart_3619106 baseEnd_3619106 := by
    simpa [prefixWord, tailWord_3619106, baseEnd_3619106] using wordTrace_append hprefix tailTrace_3619106
  have hstable : (prefixWord ++ tailWord_3619106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619106).length < 2 ^ (prefixWord ++ tailWord_3619106).sum := by decide
  have hdescent : baseEnd_3619106 < baseStart_3619106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619147 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 3, 7]
def baseStart_3619147 : Nat := 118140960795 + 3619147 * 2 ^ 59
def prefixEnd_3619147 : Nat := 4983230072969 + 3 ^ 40 * 3619147 * 2
def baseEnd_3619147 : Nat := 1238907980185104536278901

theorem tailTrace_3619147 : CollatzResearch.WordTrace tailWord_3619147 prefixEnd_3619147 1238907980185104536278901 := by
  unfold tailWord_3619147
  simp only [CollatzResearch.WordTrace]
  refine ⟨132001135419455994943167695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88000756946303996628778463 132001135419455994943167695)
  ·
    refine ⟨198001703129183992414751543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132001135419455994943167695 198001703129183992414751543)
    ·
      refine ⟨297002554693775988622127315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198001703129183992414751543 297002554693775988622127315)
      ·
        refine ⟨445503832040663982933190973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297002554693775988622127315 445503832040663982933190973)
        ·
          refine ⟨167063937015248993599946615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445503832040663982933190973 167063937015248993599946615)
          ·
            refine ⟨250595905522873490399919923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167063937015248993599946615 250595905522873490399919923)
            ·
              refine ⟨375893858284310235599879885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250595905522873490399919923 375893858284310235599879885)
              ·
                refine ⟨140960196856616338349954957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375893858284310235599879885 140960196856616338349954957)
                ·
                  refine ⟨52860073821231126881233109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140960196856616338349954957 52860073821231126881233109)
                  ·
                    refine ⟨1238907980185104536278901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52860073821231126881233109 1238907980185104536278901)
                    ·
                      rfl

theorem cell22_3619147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 7].length) (baseStart_3619147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619147 prefixEnd_3619147 := by exact prefixLift 3619147
  have htrace : WordTrace (prefixWord ++ tailWord_3619147) baseStart_3619147 baseEnd_3619147 := by
    simpa [prefixWord, tailWord_3619147, baseEnd_3619147] using wordTrace_append hprefix tailTrace_3619147
  have hstable : (prefixWord ++ tailWord_3619147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619147).length < 2 ^ (prefixWord ++ tailWord_3619147).sum := by decide
  have hdescent : baseEnd_3619147 < baseStart_3619147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619170 : List Nat := [3, 3, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_3619170 : Nat := 118140960795 + 3619170 * 2 ^ 59
def prefixEnd_3619170 : Nat := 4983230072969 + 3 ^ 40 * 3619170 * 2
def baseEnd_3619170 : Nat := 1238915853555140142953831

theorem tailTrace_3619170 : CollatzResearch.WordTrace tailWord_3619170 prefixEnd_3619170 1238915853555140142953831 := by
  unfold tailWord_3619170
  simp only [CollatzResearch.WordTrace]
  refine ⟨33000493574593167467813741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88001316198915113247503309 33000493574593167467813741)
  ·
    refine ⟨12375185090472437800430153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33000493574593167467813741 12375185090472437800430153)
    ·
      refine ⟨9281388817854328350322615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12375185090472437800430153 9281388817854328350322615)
      ·
        refine ⟨13922083226781492525483923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9281388817854328350322615 13922083226781492525483923)
        ·
          refine ⟨20883124840172238788225885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13922083226781492525483923 20883124840172238788225885)
          ·
            refine ⟨7831171815064589545584707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20883124840172238788225885 7831171815064589545584707)
            ·
              refine ⟨11746757722596884318377061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7831171815064589545584707 11746757722596884318377061)
              ·
                refine ⟨2202517072986915809695699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11746757722596884318377061 2202517072986915809695699)
                ·
                  refine ⟨3303775609480373714543549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202517072986915809695699 3303775609480373714543549)
                  ·
                    refine ⟨1238915853555140142953831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3303775609480373714543549 1238915853555140142953831)
                    ·
                      rfl

theorem cell22_3619170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_3619170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619170 prefixEnd_3619170 := by exact prefixLift 3619170
  have htrace : WordTrace (prefixWord ++ tailWord_3619170) baseStart_3619170 baseEnd_3619170 := by
    simpa [prefixWord, tailWord_3619170, baseEnd_3619170] using wordTrace_append hprefix tailTrace_3619170
  have hstable : (prefixWord ++ tailWord_3619170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619170).length < 2 ^ (prefixWord ++ tailWord_3619170).sum := by decide
  have hdescent : baseEnd_3619170 < baseStart_3619170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619211 : List Nat := [1, 1, 1, 1, 4, 4, 1, 5, 4]
def baseStart_3619211 : Nat := 118140960795 + 3619211 * 2 ^ 59
def prefixEnd_3619211 : Nat := 4983230072969 + 3 ^ 40 * 3619211 * 2
def baseEnd_3619211 : Nat := 412976629564343234226235

theorem tailTrace_3619211 : CollatzResearch.WordTrace tailWord_3619211 prefixEnd_3619211 412976629564343234226235 := by
  unfold tailWord_3619211
  simp only [CollatzResearch.WordTrace]
  refine ⟨132003469691224133873497487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88002313127482755915664991 132003469691224133873497487)
  ·
    refine ⟨198005204536836200810246231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132003469691224133873497487 198005204536836200810246231)
    ·
      refine ⟨297007806805254301215369347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198005204536836200810246231 297007806805254301215369347)
      ·
        refine ⟨445511710207881451823054021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297007806805254301215369347 445511710207881451823054021)
        ·
          refine ⟨83533445663977772216822629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 445511710207881451823054021 83533445663977772216822629)
          ·
            refine ⟨15662521061995832290654243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83533445663977772216822629 15662521061995832290654243)
            ·
              refine ⟨23493781592993748435981365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15662521061995832290654243 23493781592993748435981365)
              ·
                refine ⟨2202542024343163915873253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23493781592993748435981365 2202542024343163915873253)
                ·
                  refine ⟨412976629564343234226235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2202542024343163915873253 412976629564343234226235)
                  ·
                    rfl

theorem cell22_3619211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 4].length) (baseStart_3619211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619211 prefixEnd_3619211 := by exact prefixLift 3619211
  have htrace : WordTrace (prefixWord ++ tailWord_3619211) baseStart_3619211 baseEnd_3619211 := by
    simpa [prefixWord, tailWord_3619211, baseEnd_3619211] using wordTrace_append hprefix tailTrace_3619211
  have hstable : (prefixWord ++ tailWord_3619211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619211).length < 2 ^ (prefixWord ++ tailWord_3619211).sum := by decide
  have hdescent : baseEnd_3619211 < baseStart_3619211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619382 : List Nat := [5, 1, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_3619382 : Nat := 118140960795 + 3619382 * 2 ^ 59
def prefixEnd_3619382 : Nat := 4983230072969 + 3 ^ 40 * 3619382 * 2
def baseEnd_3619382 : Nat := 1238988425487642256653181

theorem tailTrace_3619382 : CollatzResearch.WordTrace tailWord_3619382 prefixEnd_3619382 1238988425487642256653181 := by
  unfold tailWord_3619382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8250606660850289379873275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88006471049069753385314933 8250606660850289379873275)
  ·
    refine ⟨12375909991275434069809913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8250606660850289379873275 12375909991275434069809913)
    ·
      refine ⟨9281932493456575552357435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12375909991275434069809913 9281932493456575552357435)
      ·
        refine ⟨13922898740184863328536153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9281932493456575552357435 13922898740184863328536153)
        ·
          refine ⟨10442174055138647496402115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13922898740184863328536153 10442174055138647496402115)
          ·
            refine ⟨15663261082707971244603173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10442174055138647496402115 15663261082707971244603173)
            ·
              refine ⟨2936861453007744608363095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15663261082707971244603173 2936861453007744608363095)
              ·
                refine ⟨4405292179511616912544643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2936861453007744608363095 4405292179511616912544643)
                ·
                  refine ⟨6607938269267425368816965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405292179511616912544643 6607938269267425368816965)
                  ·
                    refine ⟨1238988425487642256653181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6607938269267425368816965 1238988425487642256653181)
                    ·
                      rfl

theorem cell22_3619382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_3619382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619382 prefixEnd_3619382 := by exact prefixLift 3619382
  have htrace : WordTrace (prefixWord ++ tailWord_3619382) baseStart_3619382 baseEnd_3619382 := by
    simpa [prefixWord, tailWord_3619382, baseEnd_3619382] using wordTrace_append hprefix tailTrace_3619382
  have hstable : (prefixWord ++ tailWord_3619382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619382).length < 2 ^ (prefixWord ++ tailWord_3619382).sum := by decide
  have hdescent : baseEnd_3619382 < baseStart_3619382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619412 : List Nat := [2, 4, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_3619412 : Nat := 118140960795 + 3619412 * 2 ^ 59
def prefixEnd_3619412 : Nat := 4983230072969 + 3 ^ 40 * 3619412 * 2
def baseEnd_3619412 : Nat := 1238998695100732178403089

theorem tailTrace_3619412 : CollatzResearch.WordTrace tailWord_3619412 prefixEnd_3619412 1238998695100732178403089 := by
  unfold tailWord_3619412
  simp only [CollatzResearch.WordTrace]
  refine ⟨66005400381747972600782245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88007200508997296801042993 66005400381747972600782245)
  ·
    refine ⟨12376012571577744862646671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66005400381747972600782245 12376012571577744862646671)
    ·
      refine ⟨18564018857366617293970007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12376012571577744862646671 18564018857366617293970007)
      ·
        refine ⟨27846028286049925940955011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18564018857366617293970007 27846028286049925940955011)
        ·
          refine ⟨41769042429074888911432517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27846028286049925940955011 41769042429074888911432517)
          ·
            refine ⟨7831695455451541670893597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41769042429074888911432517 7831695455451541670893597)
            ·
              refine ⟨2936885795794328126585099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7831695455451541670893597 2936885795794328126585099)
              ·
                refine ⟨4405328693691492189877649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2936885795794328126585099 4405328693691492189877649)
                ·
                  refine ⟨3303996520268619142408237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4405328693691492189877649 3303996520268619142408237)
                  ·
                    refine ⟨1238998695100732178403089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3303996520268619142408237 1238998695100732178403089)
                    ·
                      rfl

theorem cell22_3619412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_3619412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619412 prefixEnd_3619412 := by exact prefixLift 3619412
  have htrace : WordTrace (prefixWord ++ tailWord_3619412) baseStart_3619412 baseEnd_3619412 := by
    simpa [prefixWord, tailWord_3619412, baseEnd_3619412] using wordTrace_append hprefix tailTrace_3619412
  have hstable : (prefixWord ++ tailWord_3619412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619412).length < 2 ^ (prefixWord ++ tailWord_3619412).sum := by decide
  have hdescent : baseEnd_3619412 < baseStart_3619412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619436 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 7]
def baseStart_3619436 : Nat := 118140960795 + 3619436 * 2 ^ 59
def prefixEnd_3619436 : Nat := 4983230072969 + 3 ^ 40 * 3619436 * 2
def baseEnd_3619436 : Nat := 413002303597068038601005

theorem tailTrace_3619436 : CollatzResearch.WordTrace tailWord_3619436 prefixEnd_3619436 413002303597068038601005 := by
  unfold tailWord_3619436
  simp only [CollatzResearch.WordTrace]
  refine ⟨66005838057704498650219081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88007784076939331533625441 66005838057704498650219081)
  ·
    refine ⟨49504378543278373987664311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66005838057704498650219081 49504378543278373987664311)
    ·
      refine ⟨74256567814917560981496467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49504378543278373987664311 74256567814917560981496467)
      ·
        refine ⟨111384851722376341472244701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74256567814917560981496467 111384851722376341472244701)
        ·
          refine ⟨41769319395891128052091763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111384851722376341472244701 41769319395891128052091763)
          ·
            refine ⟨62653979093836692078137645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41769319395891128052091763 62653979093836692078137645)
            ·
              refine ⟨23495242160188759529301617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62653979093836692078137645 23495242160188759529301617)
              ·
                refine ⟨17621431620141569646976213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23495242160188759529301617 17621431620141569646976213)
                ·
                  refine ⟨413002303597068038601005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17621431620141569646976213 413002303597068038601005)
                  ·
                    rfl

theorem cell22_3619436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_3619436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619436 prefixEnd_3619436 := by exact prefixLift 3619436
  have htrace : WordTrace (prefixWord ++ tailWord_3619436) baseStart_3619436 baseEnd_3619436 := by
    simpa [prefixWord, tailWord_3619436, baseEnd_3619436] using wordTrace_append hprefix tailTrace_3619436
  have hstable : (prefixWord ++ tailWord_3619436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619436).length < 2 ^ (prefixWord ++ tailWord_3619436).sum := by decide
  have hdescent : baseEnd_3619436 < baseStart_3619436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619451 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 2, 5]
def baseStart_3619451 : Nat := 118140960795 + 3619451 * 2 ^ 59
def prefixEnd_3619451 : Nat := 4983230072969 + 3 ^ 40 * 3619451 * 2
def baseEnd_3619451 : Nat := 1239012045597749076677969

theorem tailTrace_3619451 : CollatzResearch.WordTrace tailWord_3619451 prefixEnd_3619451 1239012045597749076677969 := by
  unfold tailWord_3619451
  simp only [CollatzResearch.WordTrace]
  refine ⟨132012223210354654862234207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88008148806903103241489471 132012223210354654862234207)
  ·
    refine ⟨198018334815531982293351311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132012223210354654862234207 198018334815531982293351311)
    ·
      refine ⟨297027502223297973440026967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198018334815531982293351311 297027502223297973440026967)
      ·
        refine ⟨445541253334946960160040451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297027502223297973440026967 445541253334946960160040451)
        ·
          refine ⟨668311880002420440240060677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445541253334946960160040451 668311880002420440240060677)
          ·
            refine ⟨125308477500453832545011377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 668311880002420440240060677 125308477500453832545011377)
            ·
              refine ⟨93981358125340374408758533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125308477500453832545011377 93981358125340374408758533)
              ·
                refine ⟨17621504648501320201642225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93981358125340374408758533 17621504648501320201642225)
                ·
                  refine ⟨13216128486375990151231669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17621504648501320201642225 13216128486375990151231669)
                  ·
                    refine ⟨1239012045597749076677969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13216128486375990151231669 1239012045597749076677969)
                    ·
                      rfl

theorem cell22_3619451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 5].length) (baseStart_3619451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619451 prefixEnd_3619451 := by exact prefixLift 3619451
  have htrace : WordTrace (prefixWord ++ tailWord_3619451) baseStart_3619451 baseEnd_3619451 := by
    simpa [prefixWord, tailWord_3619451, baseEnd_3619451] using wordTrace_append hprefix tailTrace_3619451
  have hstable : (prefixWord ++ tailWord_3619451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619451).length < 2 ^ (prefixWord ++ tailWord_3619451).sum := by decide
  have hdescent : baseEnd_3619451 < baseStart_3619451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619481 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 8]
def baseStart_3619481 : Nat := 118140960795 + 3619481 * 2 ^ 59
def prefixEnd_3619481 : Nat := 4983230072969 + 3 ^ 40 * 3619481 * 2
def baseEnd_3619481 : Nat := 413007438403612999475959

theorem tailTrace_3619481 : CollatzResearch.WordTrace tailWord_3619481 prefixEnd_3619481 413007438403612999475959 := by
  unfold tailWord_3619481
  simp only [CollatzResearch.WordTrace]
  refine ⟨132013317400245969985826297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88008878266830646657217531 132013317400245969985826297)
  ·
    refine ⟨99009988050184477489369723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132013317400245969985826297 99009988050184477489369723)
    ·
      refine ⟨148514982075276716234054585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99009988050184477489369723 148514982075276716234054585)
      ·
        refine ⟨111386236556457537175540939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148514982075276716234054585 111386236556457537175540939)
        ·
          refine ⟨167079354834686305763311409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111386236556457537175540939 167079354834686305763311409)
          ·
            refine ⟨125309516126014729322483557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167079354834686305763311409 125309516126014729322483557)
            ·
              refine ⟨23495534273627761747965667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125309516126014729322483557 23495534273627761747965667)
              ·
                refine ⟨35243301410441642621948501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23495534273627761747965667 35243301410441642621948501)
                ·
                  refine ⟨413007438403612999475959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35243301410441642621948501 413007438403612999475959)
                  ·
                    rfl

theorem cell22_3619481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 8].length) (baseStart_3619481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619481 prefixEnd_3619481 := by exact prefixLift 3619481
  have htrace : WordTrace (prefixWord ++ tailWord_3619481) baseStart_3619481 baseEnd_3619481 := by
    simpa [prefixWord, tailWord_3619481, baseEnd_3619481] using wordTrace_append hprefix tailTrace_3619481
  have hstable : (prefixWord ++ tailWord_3619481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619481).length < 2 ^ (prefixWord ++ tailWord_3619481).sum := by decide
  have hdescent : baseEnd_3619481 < baseStart_3619481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619530 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 1, 5]
def baseStart_3619530 : Nat := 118140960795 + 3619530 * 2 ^ 59
def prefixEnd_3619530 : Nat := 4983230072969 + 3 ^ 40 * 3619530 * 2
def baseEnd_3619530 : Nat := 1239039088912219203952727

theorem tailTrace_3619530 : CollatzResearch.WordTrace tailWord_3619530 prefixEnd_3619530 1239039088912219203952727 := by
  unfold tailWord_3619530
  simp only [CollatzResearch.WordTrace]
  refine ⟨33003776144267112838590011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88010069718045634236240029 33003776144267112838590011)
  ·
    refine ⟨49505664216400669257885017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33003776144267112838590011 49505664216400669257885017)
    ·
      refine ⟨37129248162300501943413763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49505664216400669257885017 37129248162300501943413763)
      ·
        refine ⟨55693872243450752915120645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37129248162300501943413763 55693872243450752915120645)
        ·
          refine ⟨10442601045647016171585121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55693872243450752915120645 10442601045647016171585121)
          ·
            refine ⟨7831950784235262128688841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10442601045647016171585121 7831950784235262128688841)
            ·
              refine ⟨5873963088176446596516631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7831950784235262128688841 5873963088176446596516631)
              ·
                refine ⟨8810944632264669894774947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5873963088176446596516631 8810944632264669894774947)
                ·
                  refine ⟨13216416948397004842162421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8810944632264669894774947 13216416948397004842162421)
                  ·
                    refine ⟨1239039088912219203952727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13216416948397004842162421 1239039088912219203952727)
                    ·
                      rfl

theorem cell22_3619530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_3619530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619530 prefixEnd_3619530 := by exact prefixLift 3619530
  have htrace : WordTrace (prefixWord ++ tailWord_3619530) baseStart_3619530 baseEnd_3619530 := by
    simpa [prefixWord, tailWord_3619530, baseEnd_3619530] using wordTrace_append hprefix tailTrace_3619530
  have hstable : (prefixWord ++ tailWord_3619530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619530).length < 2 ^ (prefixWord ++ tailWord_3619530).sum := by decide
  have hdescent : baseEnd_3619530 < baseStart_3619530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619626 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 3, 3]
def baseStart_3619626 : Nat := 118140960795 + 3619626 * 2 ^ 59
def prefixEnd_3619626 : Nat := 4983230072969 + 3 ^ 40 * 3619626 * 2
def baseEnd_3619626 : Nat := 1239071951674106953552433

theorem tailTrace_3619626 : CollatzResearch.WordTrace tailWord_3619626 prefixEnd_3619626 1239071951674106953552433 := by
  unfold tailWord_3619626
  simp only [CollatzResearch.WordTrace]
  refine ⟨33004651496180164937463683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88012403989813773166569821 33004651496180164937463683)
  ·
    refine ⟨49506977244270247406195525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33004651496180164937463683 49506977244270247406195525)
    ·
      refine ⟨9282558233300671388661661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49506977244270247406195525 9282558233300671388661661)
      ·
        refine ⟨3480959337487751770748123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9282558233300671388661661 3480959337487751770748123)
        ·
          refine ⟨5221439006231627656122185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3480959337487751770748123 5221439006231627656122185)
          ·
            refine ⟨3916079254673720742091639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5221439006231627656122185 3916079254673720742091639)
            ·
              refine ⟨5874118882010581113137459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3916079254673720742091639 5874118882010581113137459)
              ·
                refine ⟨8811178323015871669706189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5874118882010581113137459 8811178323015871669706189)
                ·
                  refine ⟨3304191871130951876139821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8811178323015871669706189 3304191871130951876139821)
                  ·
                    refine ⟨1239071951674106953552433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3304191871130951876139821 1239071951674106953552433)
                    ·
                      rfl

theorem cell22_3619626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_3619626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619626 prefixEnd_3619626 := by exact prefixLift 3619626
  have htrace : WordTrace (prefixWord ++ tailWord_3619626) baseStart_3619626 baseEnd_3619626 := by
    simpa [prefixWord, tailWord_3619626, baseEnd_3619626] using wordTrace_append hprefix tailTrace_3619626
  have hstable : (prefixWord ++ tailWord_3619626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619626).length < 2 ^ (prefixWord ++ tailWord_3619626).sum := by decide
  have hdescent : baseEnd_3619626 < baseStart_3619626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619648 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 5, 5]
def baseStart_3619648 : Nat := 118140960795 + 3619648 * 2 ^ 59
def prefixEnd_3619648 : Nat := 4983230072969 + 3 ^ 40 * 3619648 * 2
def baseEnd_3619648 : Nat := 1239079482723706229502365

theorem tailTrace_3619648 : CollatzResearch.WordTrace tailWord_3619648 prefixEnd_3619648 1239079482723706229502365 := by
  unfold tailWord_3619648
  simp only [CollatzResearch.WordTrace]
  refine ⟨66009704195320478753577799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88012938927093971671437065 66009704195320478753577799)
  ·
    refine ⟨99014556292980718130366699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66009704195320478753577799 99014556292980718130366699)
    ·
      refine ⟨148521834439471077195550049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99014556292980718130366699 148521834439471077195550049)
      ·
        refine ⟨111391375829603307896662537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148521834439471077195550049 111391375829603307896662537)
        ·
          refine ⟨83543531872202480922496903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111391375829603307896662537 83543531872202480922496903)
          ·
            refine ⟨125315297808303721383745355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83543531872202480922496903 125315297808303721383745355)
            ·
              refine ⟨187972946712455582075618033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125315297808303721383745355 187972946712455582075618033)
              ·
                refine ⟨140979710034341686556713525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187972946712455582075618033 140979710034341686556713525)
                ·
                  refine ⟨13216847815719533114691893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140979710034341686556713525 13216847815719533114691893)
                  ·
                    refine ⟨1239079482723706229502365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13216847815719533114691893 1239079482723706229502365)
                    ·
                      rfl

theorem cell22_3619648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_3619648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619648 prefixEnd_3619648 := by exact prefixLift 3619648
  have htrace : WordTrace (prefixWord ++ tailWord_3619648) baseStart_3619648 baseEnd_3619648 := by
    simpa [prefixWord, tailWord_3619648, baseEnd_3619648] using wordTrace_append hprefix tailTrace_3619648
  have hstable : (prefixWord ++ tailWord_3619648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619648).length < 2 ^ (prefixWord ++ tailWord_3619648).sum := by decide
  have hdescent : baseEnd_3619648 < baseStart_3619648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619680 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 2, 4]
def baseStart_3619680 : Nat := 118140960795 + 3619680 * 2 ^ 59
def prefixEnd_3619680 : Nat := 4983230072969 + 3 ^ 40 * 3619680 * 2
def baseEnd_3619680 : Nat := 1239090436977668812702267

theorem tailTrace_3619680 : CollatzResearch.WordTrace tailWord_3619680 prefixEnd_3619680 1239090436977668812702267 := by
  unfold tailWord_3619680
  simp only [CollatzResearch.WordTrace]
  refine ⟨66010287763262513486160247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88013717017683351314880329 66010287763262513486160247)
  ·
    refine ⟨99015431644893770229240371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66010287763262513486160247 99015431644893770229240371)
    ·
      refine ⟨148523147467340655343860557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99015431644893770229240371 148523147467340655343860557)
      ·
        refine ⟨55696180300252745753947709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148523147467340655343860557 55696180300252745753947709)
        ·
          refine ⟨20886067612594779657730391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55696180300252745753947709 20886067612594779657730391)
          ·
            refine ⟨31329101418892169486595587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20886067612594779657730391 31329101418892169486595587)
            ·
              refine ⟨46993652128338254229893381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31329101418892169486595587 46993652128338254229893381)
              ·
                refine ⟨8811309774063422668105009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46993652128338254229893381 8811309774063422668105009)
                ·
                  refine ⟨6608482330547567001078757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8811309774063422668105009 6608482330547567001078757)
                  ·
                    refine ⟨1239090436977668812702267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6608482330547567001078757 1239090436977668812702267)
                    ·
                      rfl

theorem cell22_3619680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_3619680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619680 prefixEnd_3619680 := by exact prefixLift 3619680
  have htrace : WordTrace (prefixWord ++ tailWord_3619680) baseStart_3619680 baseEnd_3619680 := by
    simpa [prefixWord, tailWord_3619680, baseEnd_3619680] using wordTrace_append hprefix tailTrace_3619680
  have hstable : (prefixWord ++ tailWord_3619680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619680).length < 2 ^ (prefixWord ++ tailWord_3619680).sum := by decide
  have hdescent : baseEnd_3619680 < baseStart_3619680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619684 : List Nat := [2, 3, 1, 1, 4, 1, 4, 2, 4]
def baseStart_3619684 : Nat := 118140960795 + 3619684 * 2 ^ 59
def prefixEnd_3619684 : Nat := 4983230072969 + 3 ^ 40 * 3619684 * 2
def baseEnd_3619684 : Nat := 413030602086471378534085

theorem tailTrace_3619684 : CollatzResearch.WordTrace tailWord_3619684 prefixEnd_3619684 413030602086471378534085 := by
  unfold tailWord_3619684
  simp only [CollatzResearch.WordTrace]
  refine ⟨66010360709255267827733053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88013814279007023770310737 66010360709255267827733053)
  ·
    refine ⟨24753885265970725435399895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66010360709255267827733053 24753885265970725435399895)
    ·
      refine ⟨37130827898956088153099843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24753885265970725435399895 37130827898956088153099843)
      ·
        refine ⟨55696241848434132229649765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37130827898956088153099843 55696241848434132229649765)
        ·
          refine ⟨10443045346581399793059331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55696241848434132229649765 10443045346581399793059331)
          ·
            refine ⟨15664568019872099689588997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10443045346581399793059331 15664568019872099689588997)
            ·
              refine ⟨2937106503726018691797937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15664568019872099689588997 2937106503726018691797937)
              ·
                refine ⟨2202829877794514018848453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2937106503726018691797937 2202829877794514018848453)
                ·
                  refine ⟨413030602086471378534085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2202829877794514018848453 413030602086471378534085)
                  ·
                    rfl

theorem cell22_3619684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_3619684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619684 prefixEnd_3619684 := by exact prefixLift 3619684
  have htrace : WordTrace (prefixWord ++ tailWord_3619684) baseStart_3619684 baseEnd_3619684 := by
    simpa [prefixWord, tailWord_3619684, baseEnd_3619684] using wordTrace_append hprefix tailTrace_3619684
  have hstable : (prefixWord ++ tailWord_3619684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619684).length < 2 ^ (prefixWord ++ tailWord_3619684).sum := by decide
  have hdescent : baseEnd_3619684 < baseStart_3619684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619744 : List Nat := [2, 1, 1, 4, 1, 1, 4, 4, 1, 3]
def baseStart_3619744 : Nat := 118140960795 + 3619744 * 2 ^ 59
def prefixEnd_3619744 : Nat := 4983230072969 + 3 ^ 40 * 3619744 * 2
def baseEnd_3619744 : Nat := 1239112345485593979102071

theorem tailTrace_3619744 : CollatzResearch.WordTrace tailWord_3619744 prefixEnd_3619744 1239112345485593979102071 := by
  unfold tailWord_3619744
  simp only [CollatzResearch.WordTrace]
  refine ⟨66011454899146582951325143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88015273198862110601766857 66011454899146582951325143)
  ·
    refine ⟨99017182348719874426987715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66011454899146582951325143 99017182348719874426987715)
    ·
      refine ⟨148525773523079811640481573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99017182348719874426987715 148525773523079811640481573)
      ·
        refine ⟨27848582535577464682590295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148525773523079811640481573 27848582535577464682590295)
        ·
          refine ⟨41772873803366197023885443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27848582535577464682590295 41772873803366197023885443)
          ·
            refine ⟨62659310705049295535828165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41772873803366197023885443 62659310705049295535828165)
            ·
              refine ⟨11748620757196742912967781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62659310705049295535828165 11748620757196742912967781)
              ·
                refine ⟨2202866391974389296181459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11748620757196742912967781 2202866391974389296181459)
                ·
                  refine ⟨3304299587961583944272189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202866391974389296181459 3304299587961583944272189)
                  ·
                    refine ⟨1239112345485593979102071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3304299587961583944272189 1239112345485593979102071)
                    ·
                      rfl

theorem cell22_3619744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 1, 3].length) (baseStart_3619744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619744 prefixEnd_3619744 := by exact prefixLift 3619744
  have htrace : WordTrace (prefixWord ++ tailWord_3619744) baseStart_3619744 baseEnd_3619744 := by
    simpa [prefixWord, tailWord_3619744, baseEnd_3619744] using wordTrace_append hprefix tailTrace_3619744
  have hstable : (prefixWord ++ tailWord_3619744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619744).length < 2 ^ (prefixWord ++ tailWord_3619744).sum := by decide
  have hdescent : baseEnd_3619744 < baseStart_3619744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619787 : List Nat := [1, 1, 1, 1, 3, 5, 2, 3, 1, 4]
def baseStart_3619787 : Nat := 118140960795 + 3619787 * 2 ^ 59
def prefixEnd_3619787 : Nat := 4983230072969 + 3 ^ 40 * 3619787 * 2
def baseEnd_3619787 : Nat := 1239127065264356200276939

theorem tailTrace_3619787 : CollatzResearch.WordTrace tailWord_3619787 prefixEnd_3619787 1239127065264356200276939 := by
  unfold tailWord_3619787
  simp only [CollatzResearch.WordTrace]
  refine ⟨132024478137137384246465615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88016318758091589497643743 132024478137137384246465615)
  ·
    refine ⟨198036717205706076369698423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132024478137137384246465615 198036717205706076369698423)
    ·
      refine ⟨297055075808559114554547635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198036717205706076369698423 297055075808559114554547635)
      ·
        refine ⟨445582613712838671831821453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297055075808559114554547635 445582613712838671831821453)
        ·
          refine ⟨167093480142314501936933045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445582613712838671831821453 167093480142314501936933045)
          ·
            refine ⟨15665013763341984556587473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167093480142314501936933045 15665013763341984556587473)
            ·
              refine ⟨11748760322506488417440605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15665013763341984556587473 11748760322506488417440605)
              ·
                refine ⟨4405785120939933156540227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11748760322506488417440605 4405785120939933156540227)
                ·
                  refine ⟨6608677681409899734810341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405785120939933156540227 6608677681409899734810341)
                  ·
                    refine ⟨1239127065264356200276939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6608677681409899734810341 1239127065264356200276939)
                    ·
                      rfl

theorem cell22_3619787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 4].length) (baseStart_3619787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619787 prefixEnd_3619787 := by exact prefixLift 3619787
  have htrace : WordTrace (prefixWord ++ tailWord_3619787) baseStart_3619787 baseEnd_3619787 := by
    simpa [prefixWord, tailWord_3619787, baseEnd_3619787] using wordTrace_append hprefix tailTrace_3619787
  have hstable : (prefixWord ++ tailWord_3619787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619787).length < 2 ^ (prefixWord ++ tailWord_3619787).sum := by decide
  have hdescent : baseEnd_3619787 < baseStart_3619787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619802 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 6]
def baseStart_3619802 : Nat := 118140960795 + 3619802 * 2 ^ 59
def prefixEnd_3619802 : Nat := 4983230072969 + 3 ^ 40 * 3619802 * 2
def baseEnd_3619802 : Nat := 413044066690300387050631

theorem tailTrace_3619802 : CollatzResearch.WordTrace tailWord_3619802 prefixEnd_3619802 413044066690300387050631 := by
  unfold tailWord_3619802
  simp only [CollatzResearch.WordTrace]
  refine ⟨33006256308020760452065415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88016683488055361205507773 33006256308020760452065415)
  ·
    refine ⟨49509384462031140678098123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33006256308020760452065415 49509384462031140678098123)
    ·
      refine ⟨74264076693046711017147185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49509384462031140678098123 74264076693046711017147185)
      ·
        refine ⟨55698057519785033262860389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74264076693046711017147185 55698057519785033262860389)
        ·
          refine ⟨10443385784959693736786323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55698057519785033262860389 10443385784959693736786323)
          ·
            refine ⟨15665078677439540605179485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10443385784959693736786323 15665078677439540605179485)
            ·
              refine ⟨5874404504039827726942307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15665078677439540605179485 5874404504039827726942307)
              ·
                refine ⟨8811606756059741590413461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5874404504039827726942307 8811606756059741590413461)
                ·
                  refine ⟨413044066690300387050631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8811606756059741590413461 413044066690300387050631)
                  ·
                    rfl

theorem cell22_3619802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_3619802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619802 prefixEnd_3619802 := by exact prefixLift 3619802
  have htrace : WordTrace (prefixWord ++ tailWord_3619802) baseStart_3619802 baseEnd_3619802 := by
    simpa [prefixWord, tailWord_3619802, baseEnd_3619802] using wordTrace_append hprefix tailTrace_3619802
  have hstable : (prefixWord ++ tailWord_3619802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619802).length < 2 ^ (prefixWord ++ tailWord_3619802).sum := by decide
  have hdescent : baseEnd_3619802 < baseStart_3619802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619838 : List Nat := [4, 2, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_3619838 : Nat := 118140960795 + 3619838 * 2 ^ 59
def prefixEnd_3619838 : Nat := 4983230072969 + 3 ^ 40 * 3619838 * 2
def baseEnd_3619838 : Nat := 1239144523606609067251783

theorem tailTrace_3619838 : CollatzResearch.WordTrace tailWord_3619838 prefixEnd_3619838 1239144523606609067251783 := by
  unfold tailWord_3619838
  simp only [CollatzResearch.WordTrace]
  refine ⟨16503292282494077494571521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88017558839968413304381445 16503292282494077494571521)
  ·
    refine ⟨12377469211870558120928641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16503292282494077494571521 12377469211870558120928641)
    ·
      refine ⟨9283101908902918590696481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12377469211870558120928641 9283101908902918590696481)
      ·
        refine ⟨6962326431677188943022361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9283101908902918590696481 6962326431677188943022361)
        ·
          refine ⟨5221744823757891707266771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6962326431677188943022361 5221744823757891707266771)
          ·
            refine ⟨7832617235636837560900157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5221744823757891707266771 7832617235636837560900157)
            ·
              refine ⟨2937231463363814085337559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7832617235636837560900157 2937231463363814085337559)
              ·
                refine ⟨4405847195045721128006339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937231463363814085337559 4405847195045721128006339)
                ·
                  refine ⟨6608770792568581692009509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405847195045721128006339 6608770792568581692009509)
                  ·
                    refine ⟨1239144523606609067251783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6608770792568581692009509 1239144523606609067251783)
                    ·
                      rfl

theorem cell22_3619838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_3619838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619838 prefixEnd_3619838 := by exact prefixLift 3619838
  have htrace : WordTrace (prefixWord ++ tailWord_3619838) baseStart_3619838 baseEnd_3619838 := by
    simpa [prefixWord, tailWord_3619838, baseEnd_3619838] using wordTrace_append hprefix tailTrace_3619838
  have hstable : (prefixWord ++ tailWord_3619838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619838).length < 2 ^ (prefixWord ++ tailWord_3619838).sum := by decide
  have hdescent : baseEnd_3619838 < baseStart_3619838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619896 : List Nat := [2, 1, 2, 1, 5, 1, 1, 5, 1, 3]
def baseStart_3619896 : Nat := 118140960795 + 3619896 * 2 ^ 59
def prefixEnd_3619896 : Nat := 4983230072969 + 3 ^ 40 * 3619896 * 2
def baseEnd_3619896 : Nat := 1239164378191916249301605

theorem tailTrace_3619896 : CollatzResearch.WordTrace tailWord_3619896 prefixEnd_3619896 1239164378191916249301605 := by
  unfold tailWord_3619896
  simp only [CollatzResearch.WordTrace]
  refine ⟨66014226846871247931091771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88018969129161663908122361 66014226846871247931091771)
  ·
    refine ⟨99021340270306871896637657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66014226846871247931091771 99021340270306871896637657)
    ·
      refine ⟨74266005202730153922478243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99021340270306871896637657 74266005202730153922478243)
      ·
        refine ⟨111399007804095230883717365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74266005202730153922478243 111399007804095230883717365)
        ·
          refine ⟨10443656981633927895348503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111399007804095230883717365 10443656981633927895348503)
          ·
            refine ⟨15665485472450891843022755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10443656981633927895348503 15665485472450891843022755)
            ·
              refine ⟨23498228208676337764534133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15665485472450891843022755 23498228208676337764534133)
              ·
                refine ⟨2202958894563406665425075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23498228208676337764534133 2202958894563406665425075)
                ·
                  refine ⟨3304438341845109998137613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202958894563406665425075 3304438341845109998137613)
                  ·
                    refine ⟨1239164378191916249301605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3304438341845109998137613 1239164378191916249301605)
                    ·
                      rfl

theorem cell22_3619896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 1, 3].length) (baseStart_3619896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619896 prefixEnd_3619896 := by exact prefixLift 3619896
  have htrace : WordTrace (prefixWord ++ tailWord_3619896) baseStart_3619896 baseEnd_3619896 := by
    simpa [prefixWord, tailWord_3619896, baseEnd_3619896] using wordTrace_append hprefix tailTrace_3619896
  have hstable : (prefixWord ++ tailWord_3619896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619896).length < 2 ^ (prefixWord ++ tailWord_3619896).sum := by decide
  have hdescent : baseEnd_3619896 < baseStart_3619896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619937 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 6]
def baseStart_3619937 : Nat := 118140960795 + 3619937 * 2 ^ 59
def prefixEnd_3619937 : Nat := 4983230072969 + 3 ^ 40 * 3619937 * 2
def baseEnd_3619937 : Nat := 413059471109935269675493

theorem tailTrace_3619937 : CollatzResearch.WordTrace tailWord_3619937 prefixEnd_3619937 413059471109935269675493 := by
  unfold tailWord_3619937
  simp only [CollatzResearch.WordTrace]
  refine ⟨132029949086593959864426065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88019966057729306576284043 132029949086593959864426065)
  ·
    refine ⟨99022461814945469898319549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132029949086593959864426065 99022461814945469898319549)
    ·
      refine ⟨37133423180604551211869831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99022461814945469898319549 37133423180604551211869831)
      ·
        refine ⟨55700134770906826817804747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37133423180604551211869831 55700134770906826817804747)
        ·
          refine ⟨83550202156360240226707121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55700134770906826817804747 83550202156360240226707121)
          ·
            refine ⟨62662651617270180170030341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83550202156360240226707121 62662651617270180170030341)
            ·
              refine ⟨11749247178238158781880689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62662651617270180170030341 11749247178238158781880689)
              ·
                refine ⟨8811935383678619086410517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11749247178238158781880689 8811935383678619086410517)
                ·
                  refine ⟨413059471109935269675493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8811935383678619086410517 413059471109935269675493)
                  ·
                    rfl

theorem cell22_3619937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 6].length) (baseStart_3619937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619937 prefixEnd_3619937 := by exact prefixLift 3619937
  have htrace : WordTrace (prefixWord ++ tailWord_3619937) baseStart_3619937 baseEnd_3619937 := by
    simpa [prefixWord, tailWord_3619937, baseEnd_3619937] using wordTrace_append hprefix tailTrace_3619937
  have hstable : (prefixWord ++ tailWord_3619937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619937).length < 2 ^ (prefixWord ++ tailWord_3619937).sum := by decide
  have hdescent : baseEnd_3619937 < baseStart_3619937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619952 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 3, 5]
def baseStart_3619952 : Nat := 118140960795 + 3619952 * 2 ^ 59
def prefixEnd_3619952 : Nat := 4983230072969 + 3 ^ 40 * 3619952 * 2
def baseEnd_3619952 : Nat := 1239183548136350769901433

theorem tailTrace_3619952 : CollatzResearch.WordTrace tailWord_3619952 prefixEnd_3619952 1239183548136350769901433 := by
  unfold tailWord_3619952
  simp only [CollatzResearch.WordTrace]
  refine ⟨66015248090769808713111055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88020330787693078284148073 66015248090769808713111055)
  ·
    refine ⟨99022872136154713069666583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66015248090769808713111055 99022872136154713069666583)
    ·
      refine ⟨148534308204232069604499875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99022872136154713069666583 148534308204232069604499875)
      ·
        refine ⟨222801462306348104406749813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148534308204232069604499875 222801462306348104406749813)
        ·
          refine ⟨20887637091220134788132795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222801462306348104406749813 20887637091220134788132795)
          ·
            refine ⟨31331455636830202182199193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20887637091220134788132795 31331455636830202182199193)
            ·
              refine ⟨23498591727622651636649395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31331455636830202182199193 23498591727622651636649395)
              ·
                refine ⟨35247887591433977454974093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23498591727622651636649395 35247887591433977454974093)
                ·
                  refine ⟨13217957846787741545615285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35247887591433977454974093 13217957846787741545615285)
                  ·
                    refine ⟨1239183548136350769901433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13217957846787741545615285 1239183548136350769901433)
                    ·
                      rfl

theorem cell22_3619952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_3619952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619952 prefixEnd_3619952 := by exact prefixLift 3619952
  have htrace : WordTrace (prefixWord ++ tailWord_3619952) baseStart_3619952 baseEnd_3619952 := by
    simpa [prefixWord, tailWord_3619952, baseEnd_3619952] using wordTrace_append hprefix tailTrace_3619952
  have hstable : (prefixWord ++ tailWord_3619952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619952).length < 2 ^ (prefixWord ++ tailWord_3619952).sum := by decide
  have hdescent : baseEnd_3619952 < baseStart_3619952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619971 : List Nat := [1, 1, 1, 3, 3, 2, 5, 2, 4]
def baseStart_3619971 : Nat := 118140960795 + 3619971 * 2 ^ 59
def prefixEnd_3619971 : Nat := 4983230072969 + 3 ^ 40 * 3619971 * 2
def baseEnd_3619971 : Nat := 413063350741547017892125

theorem tailTrace_3619971 : CollatzResearch.WordTrace tailWord_3619971 prefixEnd_3619971 413063350741547017892125 := by
  unfold tailWord_3619971
  simp only [CollatzResearch.WordTrace]
  refine ⟨132031189168470783671163767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88020792778980522447442511 132031189168470783671163767)
  ·
    refine ⟨198046783752706175506745651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132031189168470783671163767 198046783752706175506745651)
    ·
      refine ⟨297070175629059263260118477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198046783752706175506745651 297070175629059263260118477)
      ·
        refine ⟨111401315860897223722544429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297070175629059263260118477 111401315860897223722544429)
        ·
          refine ⟨41775493447836458895954161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111401315860897223722544429 41775493447836458895954161)
          ·
            refine ⟨31331620085877344171965621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41775493447836458895954161 31331620085877344171965621)
            ·
              refine ⟨2937339383051001016121777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31331620085877344171965621 2937339383051001016121777)
              ·
                refine ⟨2203004537288250762091333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2937339383051001016121777 2203004537288250762091333)
                ·
                  refine ⟨413063350741547017892125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2203004537288250762091333 413063350741547017892125)
                  ·
                    rfl

theorem cell22_3619971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 4].length) (baseStart_3619971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3619971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3619971 prefixEnd_3619971 := by exact prefixLift 3619971
  have htrace : WordTrace (prefixWord ++ tailWord_3619971) baseStart_3619971 baseEnd_3619971 := by
    simpa [prefixWord, tailWord_3619971, baseEnd_3619971] using wordTrace_append hprefix tailTrace_3619971
  have hstable : (prefixWord ++ tailWord_3619971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619971).length < 2 ^ (prefixWord ++ tailWord_3619971).sum := by decide
  have hdescent : baseEnd_3619971 < baseStart_3619971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620089 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 6]
def baseStart_3620089 : Nat := 118140960795 + 3620089 * 2 ^ 59
def prefixEnd_3620089 : Nat := 4983230072969 + 3 ^ 40 * 3620089 * 2
def baseEnd_3620089 : Nat := 413076815345376026408671

theorem tailTrace_3620089 : CollatzResearch.WordTrace tailWord_3620089 prefixEnd_3620089 413076815345376026408671 := by
  unfold tailWord_3620089
  simp only [CollatzResearch.WordTrace]
  refine ⟨132035492982043289823959321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88023661988028859882639547 132035492982043289823959321)
  ·
    refine ⟨99026619736532467367969491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132035492982043289823959321 99026619736532467367969491)
    ·
      refine ⟨148539929604798701051954237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99026619736532467367969491 148539929604798701051954237)
      ·
        refine ⟨55702473601799512894482839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148539929604798701051954237 55702473601799512894482839)
        ·
          refine ⟨83553710402699269341724259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55702473601799512894482839 83553710402699269341724259)
          ·
            refine ⟨125330565604048904012586389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83553710402699269341724259 125330565604048904012586389)
            ·
              refine ⟨5874870262689792375589987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125330565604048904012586389 5874870262689792375589987)
              ·
                refine ⟨8812305394034688563384981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5874870262689792375589987 8812305394034688563384981)
                ·
                  refine ⟨413076815345376026408671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8812305394034688563384981 413076815345376026408671)
                  ·
                    rfl

theorem cell22_3620089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 6].length) (baseStart_3620089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620089 prefixEnd_3620089 := by exact prefixLift 3620089
  have htrace : WordTrace (prefixWord ++ tailWord_3620089) baseStart_3620089 baseEnd_3620089 := by
    simpa [prefixWord, tailWord_3620089, baseEnd_3620089] using wordTrace_append hprefix tailTrace_3620089
  have hstable : (prefixWord ++ tailWord_3620089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620089).length < 2 ^ (prefixWord ++ tailWord_3620089).sum := by decide
  have hdescent : baseEnd_3620089 < baseStart_3620089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620119 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 1, 6]
def baseStart_3620119 : Nat := 118140960795 + 3620119 * 2 ^ 59
def prefixEnd_3620119 : Nat := 4983230072969 + 3 ^ 40 * 3620119 * 2
def baseEnd_3620119 : Nat := 1239240715649218000975921

theorem tailTrace_3620119 : CollatzResearch.WordTrace tailWord_3620119 prefixEnd_3620119 1239240715649218000975921 := by
  unfold tailWord_3620119
  simp only [CollatzResearch.WordTrace]
  refine ⟨132036587171934604947551411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88024391447956403298367607 132036587171934604947551411)
  ·
    refine ⟨198054880757901907421327117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132036587171934604947551411 198054880757901907421327117)
    ·
      refine ⟨74270580284213215282997669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198054880757901907421327117 74270580284213215282997669)
      ·
        refine ⟨13925733803289977865562063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74270580284213215282997669 13925733803289977865562063)
        ·
          refine ⟨20888600704934966798343095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13925733803289977865562063 20888600704934966798343095)
          ·
            refine ⟨31332901057402450197514643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20888600704934966798343095 31332901057402450197514643)
            ·
              refine ⟨46999351586103675296271965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31332901057402450197514643 46999351586103675296271965)
              ·
                refine ⟨17624756844788878236101987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46999351586103675296271965 17624756844788878236101987)
                ·
                  refine ⟨26437135267183317354152981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17624756844788878236101987 26437135267183317354152981)
                  ·
                    refine ⟨1239240715649218000975921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26437135267183317354152981 1239240715649218000975921)
                    ·
                      rfl

theorem cell22_3620119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_3620119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620119 prefixEnd_3620119 := by exact prefixLift 3620119
  have htrace : WordTrace (prefixWord ++ tailWord_3620119) baseStart_3620119 baseEnd_3620119 := by
    simpa [prefixWord, tailWord_3620119, baseEnd_3620119] using wordTrace_append hprefix tailTrace_3620119
  have hstable : (prefixWord ++ tailWord_3620119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620119).length < 2 ^ (prefixWord ++ tailWord_3620119).sum := by decide
  have hdescent : baseEnd_3620119 < baseStart_3620119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620136 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 4, 4]
def baseStart_3620136 : Nat := 118140960795 + 3620136 * 2 ^ 59
def prefixEnd_3620136 : Nat := 4983230072969 + 3 ^ 40 * 3620136 * 2
def baseEnd_3620136 : Nat := 1239246535096635623300869

theorem tailTrace_3620136 : CollatzResearch.WordTrace tailWord_3620136 prefixEnd_3620136 1239246535096635623300869 := by
  unfold tailWord_3620136
  simp only [CollatzResearch.WordTrace]
  refine ⟨66018603606436508425460131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88024804808582011233946841 66018603606436508425460131)
  ·
    refine ⟨99027905409654762638190197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66018603606436508425460131 99027905409654762638190197)
    ·
      refine ⟨9283866132155133997330331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99027905409654762638190197 9283866132155133997330331)
      ·
        refine ⟨13925799198232700995995497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9283866132155133997330331 13925799198232700995995497)
        ·
          refine ⟨10444349398674525746996623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13925799198232700995995497 10444349398674525746996623)
          ·
            refine ⟨15666524098011788620494935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10444349398674525746996623 15666524098011788620494935)
            ·
              refine ⟨23499786147017682930742403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15666524098011788620494935 23499786147017682930742403)
              ·
                refine ⟨35249679220526524396113605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23499786147017682930742403 35249679220526524396113605)
                ·
                  refine ⟨6609314853848723324271301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35249679220526524396113605 6609314853848723324271301)
                  ·
                    refine ⟨1239246535096635623300869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6609314853848723324271301 1239246535096635623300869)
                    ·
                      rfl

theorem cell22_3620136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_3620136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620136 prefixEnd_3620136 := by exact prefixLift 3620136
  have htrace : WordTrace (prefixWord ++ tailWord_3620136) baseStart_3620136 baseEnd_3620136 := by
    simpa [prefixWord, tailWord_3620136, baseEnd_3620136] using wordTrace_append hprefix tailTrace_3620136
  have hstable : (prefixWord ++ tailWord_3620136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620136).length < 2 ^ (prefixWord ++ tailWord_3620136).sum := by decide
  have hdescent : baseEnd_3620136 < baseStart_3620136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620138 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 4, 3]
def baseStart_3620138 : Nat := 118140960795 + 3620138 * 2 ^ 59
def prefixEnd_3620138 : Nat := 4983230072969 + 3 ^ 40 * 3620138 * 2
def baseEnd_3620138 : Nat := 1239247219737508284750863

theorem tailTrace_3620138 : CollatzResearch.WordTrace tailWord_3620138 prefixEnd_3620138 1239247219737508284750863 := by
  unfold tailWord_3620138
  simp only [CollatzResearch.WordTrace]
  refine ⟨33009320039716442798123267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88024853439243847461662045 33009320039716442798123267)
  ·
    refine ⟨49513980059574664197184901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33009320039716442798123267 49513980059574664197184901)
    ·
      refine ⟨9283871261170249536972169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49513980059574664197184901 9283871261170249536972169)
      ·
        refine ⟨6962903445877687152729127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9283871261170249536972169 6962903445877687152729127)
        ·
          refine ⟨10444355168816530729093691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6962903445877687152729127 10444355168816530729093691)
          ·
            refine ⟨15666532753224796093640537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10444355168816530729093691 15666532753224796093640537)
            ·
              refine ⟨11749899564918597070230403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15666532753224796093640537 11749899564918597070230403)
              ·
                refine ⟨17624849347377895605345605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11749899564918597070230403 17624849347377895605345605)
                ·
                  refine ⟨3304659252633355426002301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17624849347377895605345605 3304659252633355426002301)
                  ·
                    refine ⟨1239247219737508284750863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3304659252633355426002301 1239247219737508284750863)
                    ·
                      rfl

theorem cell22_3620138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_3620138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620138 prefixEnd_3620138 := by exact prefixLift 3620138
  have htrace : WordTrace (prefixWord ++ tailWord_3620138) baseStart_3620138 baseEnd_3620138 := by
    simpa [prefixWord, tailWord_3620138, baseEnd_3620138] using wordTrace_append hprefix tailTrace_3620138
  have hstable : (prefixWord ++ tailWord_3620138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620138).length < 2 ^ (prefixWord ++ tailWord_3620138).sum := by decide
  have hdescent : baseEnd_3620138 < baseStart_3620138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620189 : List Nat := [1, 4, 5, 1, 1, 1, 2, 2, 2, 3]
def baseStart_3620189 : Nat := 118140960795 + 3620189 * 2 ^ 59
def prefixEnd_3620189 : Nat := 4983230072969 + 3 ^ 40 * 3620189 * 2
def baseEnd_3620189 : Nat := 1239264678079761151725707

theorem tailTrace_3620189 : CollatzResearch.WordTrace tailWord_3620189 prefixEnd_3620189 1239264678079761151725707 := by
  unfold tailWord_3620189
  simp only [CollatzResearch.WordTrace]
  refine ⟨132039140281681006902599621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88026093521120671268399747 132039140281681006902599621)
  ·
    refine ⟨24757338802815188794237429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132039140281681006902599621 24757338802815188794237429)
    ·
      refine ⟨2321000512763923949459759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24757338802815188794237429 2321000512763923949459759)
      ·
        refine ⟨3481500769145885924189639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2321000512763923949459759 3481500769145885924189639)
        ·
          refine ⟨5222251153718828886284459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3481500769145885924189639 5222251153718828886284459)
          ·
            refine ⟨7833376730578243329426689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5222251153718828886284459 7833376730578243329426689)
            ·
              refine ⟨5875032547933682497070017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7833376730578243329426689 5875032547933682497070017)
              ·
                refine ⟨4406274410950261872802513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5875032547933682497070017 4406274410950261872802513)
                ·
                  refine ⟨3304705808212696404601885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4406274410950261872802513 3304705808212696404601885)
                  ·
                    refine ⟨1239264678079761151725707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3304705808212696404601885 1239264678079761151725707)
                    ·
                      rfl

theorem cell22_3620189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_3620189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620189 prefixEnd_3620189 := by exact prefixLift 3620189
  have htrace : WordTrace (prefixWord ++ tailWord_3620189) baseStart_3620189 baseEnd_3620189 := by
    simpa [prefixWord, tailWord_3620189, baseEnd_3620189] using wordTrace_append hprefix tailTrace_3620189
  have hstable : (prefixWord ++ tailWord_3620189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620189).length < 2 ^ (prefixWord ++ tailWord_3620189).sum := by decide
  have hdescent : baseEnd_3620189 < baseStart_3620189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620196 : List Nat := [2, 3, 1, 1, 3, 2, 1, 4, 5]
def baseStart_3620196 : Nat := 118140960795 + 3620196 * 2 ^ 59
def prefixEnd_3620196 : Nat := 4983230072969 + 3 ^ 40 * 3620196 * 2
def baseEnd_3620196 : Nat := 413089024774271822266895

theorem tailTrace_3620196 : CollatzResearch.WordTrace tailWord_3620196 prefixEnd_3620196 413089024774271822266895 := by
  unfold tailWord_3620196
  simp only [CollatzResearch.WordTrace]
  refine ⟨66019697796327823549052221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88026263728437098065402961 66019697796327823549052221)
  ·
    refine ⟨24757386673622933830894583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66019697796327823549052221 24757386673622933830894583)
    ·
      refine ⟨37136080010434400746341875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24757386673622933830894583 37136080010434400746341875)
      ·
        refine ⟨55704120015651601119512813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37136080010434400746341875 55704120015651601119512813)
        ·
          refine ⟨20889045005869350419817305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55704120015651601119512813 20889045005869350419817305)
          ·
            refine ⟨15666783754402012814862979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20889045005869350419817305 15666783754402012814862979)
            ·
              refine ⟨23500175631603019222294469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15666783754402012814862979 23500175631603019222294469)
              ·
                refine ⟨4406282930925566104180213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23500175631603019222294469 4406282930925566104180213)
                ·
                  refine ⟨413089024774271822266895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4406282930925566104180213 413089024774271822266895)
                  ·
                    rfl

theorem cell22_3620196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_3620196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620196 prefixEnd_3620196 := by exact prefixLift 3620196
  have htrace : WordTrace (prefixWord ++ tailWord_3620196) baseStart_3620196 baseEnd_3620196 := by
    simpa [prefixWord, tailWord_3620196, baseEnd_3620196] using wordTrace_append hprefix tailTrace_3620196
  have hstable : (prefixWord ++ tailWord_3620196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620196).length < 2 ^ (prefixWord ++ tailWord_3620196).sum := by decide
  have hdescent : baseEnd_3620196 < baseStart_3620196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620258 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 6]
def baseStart_3620258 : Nat := 118140960795 + 3620258 * 2 ^ 59
def prefixEnd_3620258 : Nat := 4983230072969 + 3 ^ 40 * 3620258 * 2
def baseEnd_3620258 : Nat := 413096099396622657250165

theorem tailTrace_3620258 : CollatzResearch.WordTrace tailWord_3620258 prefixEnd_3620258 413096099396622657250165 := by
  unfold tailWord_3620258
  simp only [CollatzResearch.WordTrace]
  refine ⟨33010414229607757921715357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88027771278954021124574285 33010414229607757921715357)
  ·
    refine ⟨12378905336102909220643259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33010414229607757921715357 12378905336102909220643259)
    ·
      refine ⟨18568358004154363830964889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12378905336102909220643259 18568358004154363830964889)
      ·
        refine ⟨13926268503115772873223667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18568358004154363830964889 13926268503115772873223667)
        ·
          refine ⟨20889402754673659309835501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13926268503115772873223667 20889402754673659309835501)
          ·
            refine ⟨7833526033002622241188313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20889402754673659309835501 7833526033002622241188313)
            ·
              refine ⟨5875144524751966680891235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7833526033002622241188313 5875144524751966680891235)
              ·
                refine ⟨8812716787127950021336853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5875144524751966680891235 8812716787127950021336853)
                ·
                  refine ⟨413096099396622657250165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8812716787127950021336853 413096099396622657250165)
                  ·
                    rfl

theorem cell22_3620258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_3620258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620258 prefixEnd_3620258 := by exact prefixLift 3620258
  have htrace : WordTrace (prefixWord ++ tailWord_3620258) baseStart_3620258 baseEnd_3620258 := by
    simpa [prefixWord, tailWord_3620258, baseEnd_3620258] using wordTrace_append hprefix tailTrace_3620258
  have hstable : (prefixWord ++ tailWord_3620258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620258).length < 2 ^ (prefixWord ++ tailWord_3620258).sum := by decide
  have hdescent : baseEnd_3620258 < baseStart_3620258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620292 : List Nat := [2, 3, 3, 2, 1, 3, 1, 3, 4]
def baseStart_3620292 : Nat := 118140960795 + 3620292 * 2 ^ 59
def prefixEnd_3620292 : Nat := 4983230072969 + 3 ^ 40 * 3620292 * 2
def baseEnd_3620292 : Nat := 413099979028234405466797

theorem tailTrace_3620292 : CollatzResearch.WordTrace tailWord_3620292 prefixEnd_3620292 413099979028234405466797 := by
  unfold tailWord_3620292
  simp only [CollatzResearch.WordTrace]
  refine ⟨66021448500153927746799565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88028598000205236995732753 66021448500153927746799565)
  ·
    refine ⟨24758043187557722905049837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66021448500153927746799565 24758043187557722905049837)
    ·
      refine ⟨9284266195334146089393689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24758043187557722905049837 9284266195334146089393689)
      ·
        refine ⟨6963199646500609567045267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9284266195334146089393689 6963199646500609567045267)
        ·
          refine ⟨10444799469750914350567901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6963199646500609567045267 10444799469750914350567901)
          ·
            refine ⟨3916799801156592881462963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10444799469750914350567901 3916799801156592881462963)
            ·
              refine ⟨5875199701734889322194445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3916799801156592881462963 5875199701734889322194445)
              ·
                refine ⟨2203199888150583495822917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5875199701734889322194445 2203199888150583495822917)
                ·
                  refine ⟨413099979028234405466797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2203199888150583495822917 413099979028234405466797)
                  ·
                    rfl

theorem cell22_3620292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_3620292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620292 prefixEnd_3620292 := by exact prefixLift 3620292
  have htrace : WordTrace (prefixWord ++ tailWord_3620292) baseStart_3620292 baseEnd_3620292 := by
    simpa [prefixWord, tailWord_3620292, baseEnd_3620292] using wordTrace_append hprefix tailTrace_3620292
  have hstable : (prefixWord ++ tailWord_3620292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620292).length < 2 ^ (prefixWord ++ tailWord_3620292).sum := by decide
  have hdescent : baseEnd_3620292 < baseStart_3620292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620408 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 1, 5]
def baseStart_3620408 : Nat := 118140960795 + 3620408 * 2 ^ 59
def prefixEnd_3620408 : Nat := 4983230072969 + 3 ^ 40 * 3620408 * 2
def baseEnd_3620408 : Nat := 1239339646255317580500035

theorem tailTrace_3620408 : CollatzResearch.WordTrace tailWord_3620408 prefixEnd_3620408 1239339646255317580500035 := by
  unfold tailWord_3620408
  simp only [CollatzResearch.WordTrace]
  refine ⟨66023563933943803652410939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88031418578591738203214585 66023563933943803652410939)
  ·
    refine ⟨99035345900915705478616409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66023563933943803652410939 99035345900915705478616409)
    ·
      refine ⟨74276509425686779108962307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99035345900915705478616409 74276509425686779108962307)
      ·
        refine ⟨111414764138530168663443461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74276509425686779108962307 111414764138530168663443461)
        ·
          refine ⟨20890268275974406624395649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111414764138530168663443461 20890268275974406624395649)
          ·
            refine ⟨15667701206980804968296737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20890268275974406624395649 15667701206980804968296737)
            ·
              refine ⟨11750775905235603726222553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15667701206980804968296737 11750775905235603726222553)
              ·
                refine ⟨8813081928926702794666915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11750775905235603726222553 8813081928926702794666915)
                ·
                  refine ⟨13219622893390054192000373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8813081928926702794666915 13219622893390054192000373)
                  ·
                    refine ⟨1239339646255317580500035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13219622893390054192000373 1239339646255317580500035)
                    ·
                      rfl

theorem cell22_3620408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_3620408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620408 prefixEnd_3620408 := by exact prefixLift 3620408
  have htrace : WordTrace (prefixWord ++ tailWord_3620408) baseStart_3620408 baseEnd_3620408 := by
    simpa [prefixWord, tailWord_3620408, baseEnd_3620408] using wordTrace_append hprefix tailTrace_3620408
  have hstable : (prefixWord ++ tailWord_3620408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620408).length < 2 ^ (prefixWord ++ tailWord_3620408).sum := by decide
  have hdescent : baseEnd_3620408 < baseStart_3620408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620410 : List Nat := [3, 1, 1, 1, 3, 2, 4, 3, 4]
def baseStart_3620410 : Nat := 118140960795 + 3620410 * 2 ^ 59
def prefixEnd_3620410 : Nat := 4983230072969 + 3 ^ 40 * 3620410 * 2
def baseEnd_3620410 : Nat := 413113443632063413983343

theorem tailTrace_3620410 : CollatzResearch.WordTrace tailWord_3620410 prefixEnd_3620410 413113443632063413983343 := by
  unfold tailWord_3620410
  simp only [CollatzResearch.WordTrace]
  refine ⟨33011800203470090411598671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88031467209253574430929789 33011800203470090411598671)
  ·
    refine ⟨49517700305205135617398007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33011800203470090411598671 49517700305205135617398007)
    ·
      refine ⟨74276550457807703426097011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49517700305205135617398007 74276550457807703426097011)
      ·
        refine ⟨111414825686711555139145517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74276550457807703426097011 111414825686711555139145517)
        ·
          refine ⟨41780559632516833177179569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111414825686711555139145517 41780559632516833177179569)
          ·
            refine ⟨31335419724387624882884677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41780559632516833177179569 31335419724387624882884677)
            ·
              refine ⟨5875391198322679665540877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31335419724387624882884677 5875391198322679665540877)
              ·
                refine ⟨2203271699371004874577829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5875391198322679665540877 2203271699371004874577829)
                ·
                  refine ⟨413113443632063413983343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2203271699371004874577829 413113443632063413983343)
                  ·
                    rfl

theorem cell22_3620410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_3620410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620410 prefixEnd_3620410 := by exact prefixLift 3620410
  have htrace : WordTrace (prefixWord ++ tailWord_3620410) baseStart_3620410 baseEnd_3620410 := by
    simpa [prefixWord, tailWord_3620410, baseEnd_3620410] using wordTrace_append hprefix tailTrace_3620410
  have hstable : (prefixWord ++ tailWord_3620410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620410).length < 2 ^ (prefixWord ++ tailWord_3620410).sum := by decide
  have hdescent : baseEnd_3620410 < baseStart_3620410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620421 : List Nat := [1, 3, 1, 1, 1, 4, 11]
def baseStart_3620421 : Nat := 118140960795 + 3620421 * 2 ^ 59
def prefixEnd_3620421 : Nat := 4983230072969 + 3 ^ 40 * 3620421 * 2
def baseEnd_3620421 : Nat := 45901633200777402960185

theorem tailTrace_3620421 : CollatzResearch.WordTrace tailWord_3620421 prefixEnd_3620421 45901633200777402960185 := by
  unfold tailWord_3620421
  simp only [CollatzResearch.WordTrace]
  refine ⟨132047602016840510525045117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88031734677893673683363411 132047602016840510525045117)
  ·
    refine ⟨49517850756315191446891919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132047602016840510525045117 49517850756315191446891919)
    ·
      refine ⟨74276776134472787170337879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49517850756315191446891919 74276776134472787170337879)
      ·
        refine ⟨111415164201709180755506819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74276776134472787170337879 111415164201709180755506819)
        ·
          refine ⟨167122746302563771133260229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111415164201709180755506819 167122746302563771133260229)
          ·
            refine ⟨31335514931730707087486293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167122746302563771133260229 31335514931730707087486293)
            ·
              refine ⟨45901633200777402960185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31335514931730707087486293 45901633200777402960185)
              ·
                rfl

theorem cell22_3620421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 11].length) (baseStart_3620421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620421 prefixEnd_3620421 := by exact prefixLift 3620421
  have htrace : WordTrace (prefixWord ++ tailWord_3620421) baseStart_3620421 baseEnd_3620421 := by
    simpa [prefixWord, tailWord_3620421, baseEnd_3620421] using wordTrace_append hprefix tailTrace_3620421
  have hstable : (prefixWord ++ tailWord_3620421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620421).length < 2 ^ (prefixWord ++ tailWord_3620421).sum := by decide
  have hdescent : baseEnd_3620421 < baseStart_3620421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620483 : List Nat := [1, 1, 1, 3, 3, 1, 1, 6, 5]
def baseStart_3620483 : Nat := 118140960795 + 3620483 * 2 ^ 59
def prefixEnd_3620483 : Nat := 4983230072969 + 3 ^ 40 * 3620483 * 2
def baseEnd_3620483 : Nat := 413121773429347461624935

theorem tailTrace_3620483 : CollatzResearch.WordTrace tailWord_3620483 prefixEnd_3620483 413121773429347461624935 := by
  unfold tailWord_3620483
  simp only [CollatzResearch.WordTrace]
  refine ⟨132049863342615895113802103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88033242228410596742534735 132049863342615895113802103)
  ·
    refine ⟨198074795013923842670703155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132049863342615895113802103 198074795013923842670703155)
    ·
      refine ⟨297112192520885764006054733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198074795013923842670703155 297112192520885764006054733)
      ·
        refine ⟨111417072195332161502270525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297112192520885764006054733 111417072195332161502270525)
        ·
          refine ⟨41781402073249560563351447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111417072195332161502270525 41781402073249560563351447)
          ·
            refine ⟨62672103109874340845027171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41781402073249560563351447 62672103109874340845027171)
            ·
              refine ⟨94008154664811511267540757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62672103109874340845027171 94008154664811511267540757)
              ·
                refine ⟨4406632249913039590665973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94008154664811511267540757 4406632249913039590665973)
                ·
                  refine ⟨413121773429347461624935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4406632249913039590665973 413121773429347461624935)
                  ·
                    rfl

theorem cell22_3620483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 5].length) (baseStart_3620483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620483 prefixEnd_3620483 := by exact prefixLift 3620483
  have htrace : WordTrace (prefixWord ++ tailWord_3620483) baseStart_3620483 baseEnd_3620483 := by
    simpa [prefixWord, tailWord_3620483, baseEnd_3620483] using wordTrace_append hprefix tailTrace_3620483
  have hstable : (prefixWord ++ tailWord_3620483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620483).length < 2 ^ (prefixWord ++ tailWord_3620483).sum := by decide
  have hdescent : baseEnd_3620483 < baseStart_3620483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620487 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 3, 3]
def baseStart_3620487 : Nat := 118140960795 + 3620487 * 2 ^ 59
def prefixEnd_3620487 : Nat := 4983230072969 + 3 ^ 40 * 3620487 * 2
def baseEnd_3620487 : Nat := 1239366689569787707774793

theorem tailTrace_3620487 : CollatzResearch.WordTrace tailWord_3620487 prefixEnd_3620487 1239366689569787707774793 := by
  unfold tailWord_3620487
  simp only [CollatzResearch.WordTrace]
  refine ⟨132050009234601403796947715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88033339489734269197965143 132050009234601403796947715)
  ·
    refine ⟨198075013851902105695421573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132050009234601403796947715 198075013851902105695421573)
    ·
      refine ⟨37139065097231644817891545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198075013851902105695421573 37139065097231644817891545)
      ·
        refine ⟨27854298822923733613418659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37139065097231644817891545 27854298822923733613418659)
        ·
          refine ⟨41781448234385600420127989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27854298822923733613418659 41781448234385600420127989)
          ·
            refine ⟨3917010771973650039386999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41781448234385600420127989 3917010771973650039386999)
            ·
              refine ⟨5875516157960475059080499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3917010771973650039386999 5875516157960475059080499)
              ·
                refine ⟨8813274236940712588620749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5875516157960475059080499 8813274236940712588620749)
                ·
                  refine ⟨3304977838852767220732781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8813274236940712588620749 3304977838852767220732781)
                  ·
                    refine ⟨1239366689569787707774793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3304977838852767220732781 1239366689569787707774793)
                    ·
                      rfl

theorem cell22_3620487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_3620487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620487 prefixEnd_3620487 := by exact prefixLift 3620487
  have htrace : WordTrace (prefixWord ++ tailWord_3620487) baseStart_3620487 baseEnd_3620487 := by
    simpa [prefixWord, tailWord_3620487, baseEnd_3620487] using wordTrace_append hprefix tailTrace_3620487
  have hstable : (prefixWord ++ tailWord_3620487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620487).length < 2 ^ (prefixWord ++ tailWord_3620487).sum := by decide
  have hdescent : baseEnd_3620487 < baseStart_3620487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620530 : List Nat := [3, 2, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_3620530 : Nat := 118140960795 + 3620530 * 2 ^ 59
def prefixEnd_3620530 : Nat := 4983230072969 + 3 ^ 40 * 3620530 * 2
def baseEnd_3620530 : Nat := 1239381409348549928949661

theorem tailTrace_3620530 : CollatzResearch.WordTrace tailWord_3620530 prefixEnd_3620530 1239381409348549928949661 := by
  unfold tailWord_3620530
  simp only [CollatzResearch.WordTrace]
  refine ⟨33012894393361405535190761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88034385048963748093842029 33012894393361405535190761)
  ·
    refine ⟨24759670795021054151393071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33012894393361405535190761 24759670795021054151393071)
    ·
      refine ⟨37139506192531581227089607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24759670795021054151393071 37139506192531581227089607)
      ·
        refine ⟨55709259288797371840634411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37139506192531581227089607 55709259288797371840634411)
        ·
          refine ⟨83563888933196057760951617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55709259288797371840634411 83563888933196057760951617)
          ·
            refine ⟨62672916699897043320713713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83563888933196057760951617 62672916699897043320713713)
            ·
              refine ⟨47004687524922782490535285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62672916699897043320713713 47004687524922782490535285)
              ·
                refine ⟨4406689455461510858487683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47004687524922782490535285 4406689455461510858487683)
                ·
                  refine ⟨6610034183192266287731525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4406689455461510858487683 6610034183192266287731525)
                  ·
                    refine ⟨1239381409348549928949661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6610034183192266287731525 1239381409348549928949661)
                    ·
                      rfl

theorem cell22_3620530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_3620530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620530 prefixEnd_3620530 := by exact prefixLift 3620530
  have htrace : WordTrace (prefixWord ++ tailWord_3620530) baseStart_3620530 baseEnd_3620530 := by
    simpa [prefixWord, tailWord_3620530, baseEnd_3620530] using wordTrace_append hprefix tailTrace_3620530
  have hstable : (prefixWord ++ tailWord_3620530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620530).length < 2 ^ (prefixWord ++ tailWord_3620530).sum := by decide
  have hdescent : baseEnd_3620530 < baseStart_3620530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620534 : List Nat := [5, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_3620534 : Nat := 118140960795 + 3620534 * 2 ^ 59
def prefixEnd_3620534 : Nat := 4983230072969 + 3 ^ 40 * 3620534 * 2
def baseEnd_3620534 : Nat := 413127592876765083949883

theorem tailTrace_3620534 : CollatzResearch.WordTrace tailWord_3620534 prefixEnd_3620534 413127592876765083949883 := by
  unfold tailWord_3620534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8253232716589445676494291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88034482310287420549272437 8253232716589445676494291)
  ·
    refine ⟨12379849074884168514741437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8253232716589445676494291 12379849074884168514741437)
    ·
      refine ⟨4642443403081563193028039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12379849074884168514741437 4642443403081563193028039)
      ·
        refine ⟨6963665104622344789542059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4642443403081563193028039 6963665104622344789542059)
        ·
          refine ⟨10445497656933517184313089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6963665104622344789542059 10445497656933517184313089)
          ·
            refine ⟨7834123242700137888234817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10445497656933517184313089 7834123242700137888234817)
            ·
              refine ⟨5875592432025103416176113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7834123242700137888234817 5875592432025103416176113)
              ·
                refine ⟨4406694324018827562132085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5875592432025103416176113 4406694324018827562132085)
                ·
                  refine ⟨413127592876765083949883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4406694324018827562132085 413127592876765083949883)
                  ·
                    rfl

theorem cell22_3620534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_3620534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620534 prefixEnd_3620534 := by exact prefixLift 3620534
  have htrace : WordTrace (prefixWord ++ tailWord_3620534) baseStart_3620534 baseEnd_3620534 := by
    simpa [prefixWord, tailWord_3620534, baseEnd_3620534] using wordTrace_append hprefix tailTrace_3620534
  have hstable : (prefixWord ++ tailWord_3620534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620534).length < 2 ^ (prefixWord ++ tailWord_3620534).sum := by decide
  have hdescent : baseEnd_3620534 < baseStart_3620534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620543 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 3, 5]
def baseStart_3620543 : Nat := 118140960795 + 3620543 * 2 ^ 59
def prefixEnd_3620543 : Nat := 4983230072969 + 3 ^ 40 * 3620543 * 2
def baseEnd_3620543 : Nat := 1239385859514222228374621

theorem tailTrace_3620543 : CollatzResearch.WordTrace tailWord_3620543 prefixEnd_3620543 1239385859514222228374621 := by
  unfold tailWord_3620543
  simp only [CollatzResearch.WordTrace]
  refine ⟨132052051722398525360986283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88034701148265683573990855 132052051722398525360986283)
  ·
    refine ⟨198078077583597788041479425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132052051722398525360986283 198078077583597788041479425)
    ·
      refine ⟨148558558187698341031109569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198078077583597788041479425 148558558187698341031109569)
      ·
        refine ⟨111418918640773755773332177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148558558187698341031109569 111418918640773755773332177)
        ·
          refine ⟨83564188980580316829999133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111418918640773755773332177 83564188980580316829999133)
          ·
            refine ⟨31336570867717618811249675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83564188980580316829999133 31336570867717618811249675)
            ·
              refine ⟨47004856301576428216874513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31336570867717618811249675 47004856301576428216874513)
              ·
                refine ⟨35253642226182321162655885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47004856301576428216874513 35253642226182321162655885)
                ·
                  refine ⟨13220115834818370435995957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35253642226182321162655885 13220115834818370435995957)
                  ·
                    refine ⟨1239385859514222228374621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13220115834818370435995957 1239385859514222228374621)
                    ·
                      rfl

theorem cell22_3620543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_3620543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620543 prefixEnd_3620543 := by exact prefixLift 3620543
  have htrace : WordTrace (prefixWord ++ tailWord_3620543) baseStart_3620543 baseEnd_3620543 := by
    simpa [prefixWord, tailWord_3620543, baseEnd_3620543] using wordTrace_append hprefix tailTrace_3620543
  have hstable : (prefixWord ++ tailWord_3620543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620543).length < 2 ^ (prefixWord ++ tailWord_3620543).sum := by decide
  have hdescent : baseEnd_3620543 < baseStart_3620543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620579 : List Nat := [1, 1, 1, 7, 2, 1, 2, 3, 4]
def baseStart_3620579 : Nat := 118140960795 + 3620579 * 2 ^ 59
def prefixEnd_3620579 : Nat := 4983230072969 + 3 ^ 40 * 3620579 * 2
def baseEnd_3620579 : Nat := 413132727683310044824837

theorem tailTrace_3620579 : CollatzResearch.WordTrace tailWord_3620579 prefixEnd_3620579 413132727683310044824837 := by
  unfold tailWord_3620579
  simp only [CollatzResearch.WordTrace]
  refine ⟨132053364750268103509296791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88035576500178735672864527 132053364750268103509296791)
  ·
    refine ⟨198080047125402155263945187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132053364750268103509296791 198080047125402155263945187)
    ·
      refine ⟨297120070688103232895917781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198080047125402155263945187 297120070688103232895917781)
      ·
        refine ⟨6963751656752419520998073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 297120070688103232895917781 6963751656752419520998073)
        ·
          refine ⟨5222813742564314640748555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6963751656752419520998073 5222813742564314640748555)
          ·
            refine ⟨7834220613846471961122833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5222813742564314640748555 7834220613846471961122833)
            ·
              refine ⟨5875665460384853970842125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7834220613846471961122833 5875665460384853970842125)
              ·
                refine ⟨2203374547644320239065797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5875665460384853970842125 2203374547644320239065797)
                ·
                  refine ⟨413132727683310044824837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2203374547644320239065797 413132727683310044824837)
                  ·
                    rfl

theorem cell22_3620579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 4].length) (baseStart_3620579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620579 prefixEnd_3620579 := by exact prefixLift 3620579
  have htrace : WordTrace (prefixWord ++ tailWord_3620579) baseStart_3620579 baseEnd_3620579 := by
    simpa [prefixWord, tailWord_3620579, baseEnd_3620579] using wordTrace_append hprefix tailTrace_3620579
  have hstable : (prefixWord ++ tailWord_3620579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620579).length < 2 ^ (prefixWord ++ tailWord_3620579).sum := by decide
  have hdescent : baseEnd_3620579 < baseStart_3620579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620596 : List Nat := [2, 6, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3620596 : Nat := 118140960795 + 3620596 * 2 ^ 59
def prefixEnd_3620596 : Nat := 4983230072969 + 3 ^ 40 * 3620596 * 2
def baseEnd_3620596 : Nat := 413134667499115918933153

theorem tailTrace_3620596 : CollatzResearch.WordTrace tailWord_3620596 prefixEnd_3620596 413134667499115918933153 := by
  unfold tailWord_3620596
  simp only [CollatzResearch.WordTrace]
  refine ⟨66026992395603257706332821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88035989860804343608443761 66026992395603257706332821)
  ·
    refine ⟨3095015268543902704984351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66026992395603257706332821 3095015268543902704984351)
    ·
      refine ⟨4642522902815854057476527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3095015268543902704984351 4642522902815854057476527)
      ·
        refine ⟨6963784354223781086214791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4642522902815854057476527 6963784354223781086214791)
        ·
          refine ⟨10445676531335671629322187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6963784354223781086214791 10445676531335671629322187)
          ·
            refine ⟨15668514797003507443983281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10445676531335671629322187 15668514797003507443983281)
            ·
              refine ⟨11751386097752630582987461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15668514797003507443983281 11751386097752630582987461)
              ·
                refine ⟨2203384893328618234310149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11751386097752630582987461 2203384893328618234310149)
                ·
                  refine ⟨413134667499115918933153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2203384893328618234310149 413134667499115918933153)
                  ·
                    rfl

theorem cell22_3620596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3620596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620596 prefixEnd_3620596 := by exact prefixLift 3620596
  have htrace : WordTrace (prefixWord ++ tailWord_3620596) baseStart_3620596 baseEnd_3620596 := by
    simpa [prefixWord, tailWord_3620596, baseEnd_3620596] using wordTrace_append hprefix tailTrace_3620596
  have hstable : (prefixWord ++ tailWord_3620596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620596).length < 2 ^ (prefixWord ++ tailWord_3620596).sum := by decide
  have hdescent : baseEnd_3620596 < baseStart_3620596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620603 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 2, 6]
def baseStart_3620603 : Nat := 118140960795 + 3620603 * 2 ^ 59
def prefixEnd_3620603 : Nat := 4983230072969 + 3 ^ 40 * 3620603 * 2
def baseEnd_3620603 : Nat := 1239406398740402071874437

theorem tailTrace_3620603 : CollatzResearch.WordTrace tailWord_3620603 prefixEnd_3620603 1239406398740402071874437 := by
  unfold tailWord_3620603
  simp only [CollatzResearch.WordTrace]
  refine ⟨132054240102181155608170463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88036160068120770405446975 132054240102181155608170463)
  ·
    refine ⟨198081360153271733412255695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132054240102181155608170463 198081360153271733412255695)
    ·
      refine ⟨297122040229907600118383543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198081360153271733412255695 297122040229907600118383543)
      ·
        refine ⟨445683060344861400177575315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297122040229907600118383543 445683060344861400177575315)
        ·
          refine ⟨668524590517292100266362973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445683060344861400177575315 668524590517292100266362973)
          ·
            refine ⟨250696721443984537599886115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 668524590517292100266362973 250696721443984537599886115)
            ·
              refine ⟨376045082165976806399829173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250696721443984537599886115 376045082165976806399829173)
              ·
                refine ⟨35254226453060325599983985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 376045082165976806399829173 35254226453060325599983985)
                ·
                  refine ⟨26440669839795244199987989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35254226453060325599983985 26440669839795244199987989)
                  ·
                    refine ⟨1239406398740402071874437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26440669839795244199987989 1239406398740402071874437)
                    ·
                      rfl

theorem cell22_3620603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 6].length) (baseStart_3620603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620603 prefixEnd_3620603 := by exact prefixLift 3620603
  have htrace : WordTrace (prefixWord ++ tailWord_3620603) baseStart_3620603 baseEnd_3620603 := by
    simpa [prefixWord, tailWord_3620603, baseEnd_3620603] using wordTrace_append hprefix tailTrace_3620603
  have hstable : (prefixWord ++ tailWord_3620603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620603).length < 2 ^ (prefixWord ++ tailWord_3620603).sum := by decide
  have hdescent : baseEnd_3620603 < baseStart_3620603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620622 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 3, 3]
def baseStart_3620622 : Nat := 118140960795 + 3620622 * 2 ^ 59
def prefixEnd_3620622 : Nat := 4983230072969 + 3 ^ 40 * 3620622 * 2
def baseEnd_3620622 : Nat := 1239412902828692355649379

theorem tailTrace_3620622 : CollatzResearch.WordTrace tailWord_3620622 prefixEnd_3620622 1239412902828692355649379 := by
  unfold tailWord_3620622
  simp only [CollatzResearch.WordTrace]
  refine ⟨16506866636139040231639015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88036622059408214568741413 16506866636139040231639015)
  ·
    refine ⟨24760299954208560347458523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16506866636139040231639015 24760299954208560347458523)
    ·
      refine ⟨37140449931312840521187785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24760299954208560347458523 37140449931312840521187785)
      ·
        refine ⟨27855337448484630390890839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37140449931312840521187785 27855337448484630390890839)
        ·
          refine ⟨41783006172726945586336259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27855337448484630390890839 41783006172726945586336259)
          ·
            refine ⟨62674509259090418379504389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41783006172726945586336259 62674509259090418379504389)
            ·
              refine ⟨11751470486079453446157073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62674509259090418379504389 11751470486079453446157073)
              ·
                refine ⟨8813602864559590084617805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11751470486079453446157073 8813602864559590084617805)
                ·
                  refine ⟨3305101074209846281731677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8813602864559590084617805 3305101074209846281731677)
                  ·
                    refine ⟨1239412902828692355649379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3305101074209846281731677 1239412902828692355649379)
                    ·
                      rfl

theorem cell22_3620622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_3620622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620622 prefixEnd_3620622 := by exact prefixLift 3620622
  have htrace : WordTrace (prefixWord ++ tailWord_3620622) baseStart_3620622 baseEnd_3620622 := by
    simpa [prefixWord, tailWord_3620622, baseEnd_3620622] using wordTrace_append hprefix tailTrace_3620622
  have hstable : (prefixWord ++ tailWord_3620622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620622).length < 2 ^ (prefixWord ++ tailWord_3620622).sum := by decide
  have hdescent : baseEnd_3620622 < baseStart_3620622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620669 : List Nat := [1, 4, 1, 4, 1, 1, 4, 1, 5]
def baseStart_3620669 : Nat := 118140960795 + 3620669 * 2 ^ 59
def prefixEnd_3620669 : Nat := 4983230072969 + 3 ^ 40 * 3620669 * 2
def baseEnd_3620669 : Nat := 413142997296399966574745

theorem tailTrace_3620669 : CollatzResearch.WordTrace tailWord_3620669 prefixEnd_3620669 413142997296399966574745 := by
  unfold tailWord_3620669
  simp only [CollatzResearch.WordTrace]
  refine ⟨132056647319942048880073061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88037764879961365920048707 132056647319942048880073061)
  ·
    refine ⟨24760621372489134165013699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132056647319942048880073061 24760621372489134165013699)
    ·
      refine ⟨37140932058733701247520549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24760621372489134165013699 37140932058733701247520549)
      ·
        refine ⟨6963924761012568983910103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37140932058733701247520549 6963924761012568983910103)
        ·
          refine ⟨10445887141518853475865155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6963924761012568983910103 10445887141518853475865155)
          ·
            refine ⟨15668830712278280213797733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10445887141518853475865155 15668830712278280213797733)
            ·
              refine ⟨2937905758552177540087075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15668830712278280213797733 2937905758552177540087075)
              ·
                refine ⟨4406858637828266310130613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937905758552177540087075 4406858637828266310130613)
                ·
                  refine ⟨413142997296399966574745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4406858637828266310130613 413142997296399966574745)
                  ·
                    rfl

theorem cell22_3620669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_3620669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620669 prefixEnd_3620669 := by exact prefixLift 3620669
  have htrace : WordTrace (prefixWord ++ tailWord_3620669) baseStart_3620669 baseEnd_3620669 := by
    simpa [prefixWord, tailWord_3620669, baseEnd_3620669] using wordTrace_append hprefix tailTrace_3620669
  have hstable : (prefixWord ++ tailWord_3620669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620669).length < 2 ^ (prefixWord ++ tailWord_3620669).sum := by decide
  have hdescent : baseEnd_3620669 < baseStart_3620669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620697 : List Nat := [1, 2, 1, 2, 2, 3, 2, 5, 4]
def baseStart_3620697 : Nat := 118140960795 + 3620697 * 2 ^ 59
def prefixEnd_3620697 : Nat := 4983230072969 + 3 ^ 40 * 3620697 * 2
def baseEnd_3620697 : Nat := 413146192287139053341383

theorem tailTrace_3620697 : CollatzResearch.WordTrace tailWord_3620697 prefixEnd_3620697 413146192287139053341383 := by
  unfold tailWord_3620697
  simp only [CollatzResearch.WordTrace]
  refine ⟨132057668563840609662092345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88038445709227073108061563 132057668563840609662092345)
  ·
    refine ⟨99043251422880457246569259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132057668563840609662092345 99043251422880457246569259)
    ·
      refine ⟨148564877134320685869853889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99043251422880457246569259 148564877134320685869853889)
      ·
        refine ⟨111423657850740514402390417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148564877134320685869853889 111423657850740514402390417)
        ·
          refine ⟨83567743388055385801792813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111423657850740514402390417 83567743388055385801792813)
          ·
            refine ⟨31337903770520769675672305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83567743388055385801792813 31337903770520769675672305)
            ·
              refine ⟨23503427827890577256754229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31337903770520769675672305 23503427827890577256754229)
              ·
                refine ⟨2203446358864741617820709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23503427827890577256754229 2203446358864741617820709)
                ·
                  refine ⟨413146192287139053341383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2203446358864741617820709 413146192287139053341383)
                  ·
                    rfl

theorem cell22_3620697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 4].length) (baseStart_3620697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620697 prefixEnd_3620697 := by exact prefixLift 3620697
  have htrace : WordTrace (prefixWord ++ tailWord_3620697) baseStart_3620697 baseEnd_3620697 := by
    simpa [prefixWord, tailWord_3620697, baseEnd_3620697] using wordTrace_append hprefix tailTrace_3620697
  have hstable : (prefixWord ++ tailWord_3620697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620697).length < 2 ^ (prefixWord ++ tailWord_3620697).sum := by decide
  have hdescent : baseEnd_3620697 < baseStart_3620697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620750 : List Nat := [4, 1, 1, 5, 2, 1, 2, 1, 1, 4]
def baseStart_3620750 : Nat := 118140960795 + 3620750 * 2 ^ 59
def prefixEnd_3620750 : Nat := 4983230072969 + 3 ^ 40 * 3620750 * 2
def baseEnd_3620750 : Nat := 1239456719844542688448987

theorem tailTrace_3620750 : CollatzResearch.WordTrace tailWord_3620750 prefixEnd_3620750 1239456719844542688448987 := by
  unfold tailWord_3620750
  simp only [CollatzResearch.WordTrace]
  refine ⟨16507450204081074964221463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88039734421765733142514469 16507450204081074964221463)
  ·
    refine ⟨24761175306121612446332195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16507450204081074964221463 24761175306121612446332195)
    ·
      refine ⟨37141762959182418669498293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24761175306121612446332195 37141762959182418669498293)
      ·
        refine ⟨3482040277423351750265465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37141762959182418669498293 3482040277423351750265465)
        ·
          refine ⟨2611530208067513812699099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3482040277423351750265465 2611530208067513812699099)
          ·
            refine ⟨3917295312101270719048649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2611530208067513812699099 3917295312101270719048649)
            ·
              refine ⟨2937971484075953039286487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3917295312101270719048649 2937971484075953039286487)
              ·
                refine ⟨4406957226113929558929731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937971484075953039286487 4406957226113929558929731)
                ·
                  refine ⟨6610435839170894338394597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4406957226113929558929731 6610435839170894338394597)
                  ·
                    refine ⟨1239456719844542688448987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6610435839170894338394597 1239456719844542688448987)
                    ·
                      rfl

theorem cell22_3620750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_3620750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620750 prefixEnd_3620750 := by exact prefixLift 3620750
  have htrace : WordTrace (prefixWord ++ tailWord_3620750) baseStart_3620750 baseEnd_3620750 := by
    simpa [prefixWord, tailWord_3620750, baseEnd_3620750] using wordTrace_append hprefix tailTrace_3620750
  have hstable : (prefixWord ++ tailWord_3620750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620750).length < 2 ^ (prefixWord ++ tailWord_3620750).sum := by decide
  have hdescent : baseEnd_3620750 < baseStart_3620750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620757 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 5, 3]
def baseStart_3620757 : Nat := 118140960795 + 3620757 * 2 ^ 59
def prefixEnd_3620757 : Nat := 4983230072969 + 3 ^ 40 * 3620757 * 2
def baseEnd_3620757 : Nat := 1239459116087597003523965

theorem tailTrace_3620757 : CollatzResearch.WordTrace tailWord_3620757 prefixEnd_3620757 1239459116087597003523965 := by
  unfold tailWord_3620757
  simp only [CollatzResearch.WordTrace]
  refine ⟨132059856943623239909276525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88039904629082159939517683 132059856943623239909276525)
  ·
    refine ⟨49522446353858714965978697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132059856943623239909276525 49522446353858714965978697)
    ·
      refine ⟨37141834765394036224484023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49522446353858714965978697 37141834765394036224484023)
      ·
        refine ⟨55712752148091054336726035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37141834765394036224484023 55712752148091054336726035)
        ·
          refine ⟨83569128222136581505089053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55712752148091054336726035 83569128222136581505089053)
          ·
            refine ⟨31338423083301218064408395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83569128222136581505089053 31338423083301218064408395)
            ·
              refine ⟨47007634624951827096612593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31338423083301218064408395 47007634624951827096612593)
              ·
                refine ⟨35255725968713870322459445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47007634624951827096612593 35255725968713870322459445)
                ·
                  refine ⟨3305224309566925342730573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35255725968713870322459445 3305224309566925342730573)
                  ·
                    refine ⟨1239459116087597003523965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3305224309566925342730573 1239459116087597003523965)
                    ·
                      rfl

theorem cell22_3620757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_3620757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620757 prefixEnd_3620757 := by exact prefixLift 3620757
  have htrace : WordTrace (prefixWord ++ tailWord_3620757) baseStart_3620757 baseEnd_3620757 := by
    simpa [prefixWord, tailWord_3620757, baseEnd_3620757] using wordTrace_append hprefix tailTrace_3620757
  have hstable : (prefixWord ++ tailWord_3620757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620757).length < 2 ^ (prefixWord ++ tailWord_3620757).sum := by decide
  have hdescent : baseEnd_3620757 < baseStart_3620757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620808 : List Nat := [2, 1, 3, 1, 4, 3, 1, 3, 1, 3]
def baseStart_3620808 : Nat := 118140960795 + 3620808 * 2 ^ 59
def prefixEnd_3620808 : Nat := 4983230072969 + 3 ^ 40 * 3620808 * 2
def baseEnd_3620808 : Nat := 1239476574429849870498809

theorem tailTrace_3620808 : CollatzResearch.WordTrace tailWord_3620808 prefixEnd_3620808 1239476574429849870498809 := by
  unfold tailWord_3620808
  simp only [CollatzResearch.WordTrace]
  refine ⟨66030858533219237809691539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88041144710958983746255385 66030858533219237809691539)
  ·
    refine ⟨99046287799828856714537309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66030858533219237809691539 99046287799828856714537309)
    ·
      refine ⟨37142357924935821267951491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99046287799828856714537309 37142357924935821267951491)
      ·
        refine ⟨55713536887403731901927237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37142357924935821267951491 55713536887403731901927237)
        ·
          refine ⟨10446288166388199731611357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55713536887403731901927237 10446288166388199731611357)
          ·
            refine ⟨3917358062395574899354259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10446288166388199731611357 3917358062395574899354259)
            ·
              refine ⟨5876037093593362349031389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3917358062395574899354259 5876037093593362349031389)
              ·
                refine ⟨2203513910097510880886771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5876037093593362349031389 2203513910097510880886771)
                ·
                  refine ⟨3305270865146266321330157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2203513910097510880886771 3305270865146266321330157)
                  ·
                    refine ⟨1239476574429849870498809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3305270865146266321330157 1239476574429849870498809)
                    ·
                      rfl

theorem cell22_3620808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_3620808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620808 prefixEnd_3620808 := by exact prefixLift 3620808
  have htrace : WordTrace (prefixWord ++ tailWord_3620808) baseStart_3620808 baseEnd_3620808 := by
    simpa [prefixWord, tailWord_3620808, baseEnd_3620808] using wordTrace_append hprefix tailTrace_3620808
  have hstable : (prefixWord ++ tailWord_3620808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620808).length < 2 ^ (prefixWord ++ tailWord_3620808).sum := by decide
  have hdescent : baseEnd_3620808 < baseStart_3620808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620847 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 1, 5]
def baseStart_3620847 : Nat := 118140960795 + 3620847 * 2 ^ 59
def prefixEnd_3620847 : Nat := 4983230072969 + 3 ^ 40 * 3620847 * 2
def baseEnd_3620847 : Nat := 1239489924926866768773689

theorem tailTrace_3620847 : CollatzResearch.WordTrace tailWord_3620847 prefixEnd_3620847 1239489924926866768773689 := by
  unfold tailWord_3620847
  simp only [CollatzResearch.WordTrace]
  refine ⟨132063139513297185280052795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88042093008864790186701863 132063139513297185280052795)
  ·
    refine ⟨198094709269945777920079193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132063139513297185280052795 198094709269945777920079193)
    ·
      refine ⟨148571031952459333440059395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198094709269945777920079193 148571031952459333440059395)
      ·
        refine ⟨222856547928689000160089093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148571031952459333440059395 222856547928689000160089093)
        ·
          refine ⟨41785602736629187530016705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222856547928689000160089093 41785602736629187530016705)
          ·
            refine ⟨31339202052471890647512529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41785602736629187530016705 31339202052471890647512529)
            ·
              refine ⟨23504401539353917985634397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31339202052471890647512529 23504401539353917985634397)
              ·
                refine ⟨8814150577257719244612899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23504401539353917985634397 8814150577257719244612899)
                ·
                  refine ⟨13221225865886578866919349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8814150577257719244612899 13221225865886578866919349)
                  ·
                    refine ⟨1239489924926866768773689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13221225865886578866919349 1239489924926866768773689)
                    ·
                      rfl

theorem cell22_3620847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_3620847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620847 prefixEnd_3620847 := by exact prefixLift 3620847
  have htrace : WordTrace (prefixWord ++ tailWord_3620847) baseStart_3620847 baseEnd_3620847 := by
    simpa [prefixWord, tailWord_3620847, baseEnd_3620847] using wordTrace_append hprefix tailTrace_3620847
  have hstable : (prefixWord ++ tailWord_3620847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620847).length < 2 ^ (prefixWord ++ tailWord_3620847).sum := by decide
  have hdescent : baseEnd_3620847 < baseStart_3620847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620922 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 7]
def baseStart_3620922 : Nat := 118140960795 + 3620922 * 2 ^ 59
def prefixEnd_3620922 : Nat := 4983230072969 + 3 ^ 40 * 3620922 * 2
def baseEnd_3620922 : Nat := 413171866319863857716153

theorem tailTrace_3620922 : CollatzResearch.WordTrace tailWord_3620922 prefixEnd_3620922 413171866319863857716153 := by
  unfold tailWord_3620922
  simp only [CollatzResearch.WordTrace]
  refine ⟨33016468747006368272258255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88043916658683648726022013 33016468747006368272258255)
  ·
    refine ⟨49524703120509552408387383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33016468747006368272258255 49524703120509552408387383)
    ·
      refine ⟨74287054680764328612581075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49524703120509552408387383 74287054680764328612581075)
      ·
        refine ⟨111430582021146492918871613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74287054680764328612581075 111430582021146492918871613)
        ·
          refine ⟨41786468257929934844576855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111430582021146492918871613 41786468257929934844576855)
          ·
            refine ⟨62679702386894902266865283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41786468257929934844576855 62679702386894902266865283)
            ·
              refine ⟨94019553580342353400297925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62679702386894902266865283 94019553580342353400297925)
              ·
                refine ⟨17628666296314191262555861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94019553580342353400297925 17628666296314191262555861)
                ·
                  refine ⟨413171866319863857716153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17628666296314191262555861 413171866319863857716153)
                  ·
                    rfl

theorem cell22_3620922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_3620922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620922 prefixEnd_3620922 := by exact prefixLift 3620922
  have htrace : WordTrace (prefixWord ++ tailWord_3620922) baseStart_3620922 baseEnd_3620922 := by
    simpa [prefixWord, tailWord_3620922, baseEnd_3620922] using wordTrace_append hprefix tailTrace_3620922
  have hstable : (prefixWord ++ tailWord_3620922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620922).length < 2 ^ (prefixWord ++ tailWord_3620922).sum := by decide
  have hdescent : baseEnd_3620922 < baseStart_3620922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620937 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 4, 5]
def baseStart_3620937 : Nat := 118140960795 + 3620937 * 2 ^ 59
def prefixEnd_3620937 : Nat := 4983230072969 + 3 ^ 40 * 3620937 * 2
def baseEnd_3620937 : Nat := 1239520733766136534023413

theorem tailTrace_3620937 : CollatzResearch.WordTrace tailWord_3620937 prefixEnd_3620937 1239520733766136534023413 := by
  unfold tailWord_3620937
  simp only [CollatzResearch.WordTrace]
  refine ⟨132066422082971130650829065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88044281388647420433886043 132066422082971130650829065)
  ·
    refine ⟨99049816562228347988121799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132066422082971130650829065 99049816562228347988121799)
    ·
      refine ⟨148574724843342521982182699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99049816562228347988121799 148574724843342521982182699)
      ·
        refine ⟨222862087265013782973274049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148574724843342521982182699 222862087265013782973274049)
        ·
          refine ⟨167146565448760337229955537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222862087265013782973274049 167146565448760337229955537)
          ·
            refine ⟨125359924086570252922466653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167146565448760337229955537 125359924086570252922466653)
            ·
              refine ⟨47009971532463844845924995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125359924086570252922466653 47009971532463844845924995)
              ·
                refine ⟨70514957298695767268887493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47009971532463844845924995 70514957298695767268887493)
                ·
                  refine ⟨13221554493505456362916405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70514957298695767268887493 13221554493505456362916405)
                  ·
                    refine ⟨1239520733766136534023413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13221554493505456362916405 1239520733766136534023413)
                    ·
                      rfl

theorem cell22_3620937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_3620937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3620937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3620937 prefixEnd_3620937 := by exact prefixLift 3620937
  have htrace : WordTrace (prefixWord ++ tailWord_3620937) baseStart_3620937 baseEnd_3620937 := by
    simpa [prefixWord, tailWord_3620937, baseEnd_3620937] using wordTrace_append hprefix tailTrace_3620937
  have hstable : (prefixWord ++ tailWord_3620937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620937).length < 2 ^ (prefixWord ++ tailWord_3620937).sum := by decide
  have hdescent : baseEnd_3620937 < baseStart_3620937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621052 : List Nat := [2, 2, 2, 3, 4, 1, 2, 2, 4]
def baseStart_3621052 : Nat := 118140960795 + 3621052 * 2 ^ 59
def prefixEnd_3621052 : Nat := 4983230072969 + 3 ^ 40 * 3621052 * 2
def baseEnd_3621052 : Nat := 413186700205438189132687

theorem tailTrace_3621052 : CollatzResearch.WordTrace tailWord_3621052 prefixEnd_3621052 413186700205438189132687 := by
  unfold tailWord_3621052
  simp only [CollatzResearch.WordTrace]
  refine ⟨66035308238777252645632705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88047077651703003527510273 66035308238777252645632705)
  ·
    refine ⟨49526481179082939484224529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66035308238777252645632705 49526481179082939484224529)
    ·
      refine ⟨37144860884312204613168397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49526481179082939484224529 37144860884312204613168397)
      ·
        refine ⟨13929322831617076729938149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37144860884312204613168397 13929322831617076729938149)
        ·
          refine ⟨2611748030928201886863403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13929322831617076729938149 2611748030928201886863403)
          ·
            refine ⟨3917622046392302830295105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2611748030928201886863403 3917622046392302830295105)
            ·
              refine ⟨2938216534794227122721329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3917622046392302830295105 2938216534794227122721329)
              ·
                refine ⟨2203662401095670342040997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2938216534794227122721329 2203662401095670342040997)
                ·
                  refine ⟨413186700205438189132687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2203662401095670342040997 413186700205438189132687)
                  ·
                    rfl

theorem cell22_3621052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_3621052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621052 prefixEnd_3621052 := by exact prefixLift 3621052
  have htrace : WordTrace (prefixWord ++ tailWord_3621052) baseStart_3621052 baseEnd_3621052 := by
    simpa [prefixWord, tailWord_3621052, baseEnd_3621052] using wordTrace_append hprefix tailTrace_3621052
  have hstable : (prefixWord ++ tailWord_3621052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621052).length < 2 ^ (prefixWord ++ tailWord_3621052).sum := by decide
  have hdescent : baseEnd_3621052 < baseStart_3621052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621089 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 1, 7]
def baseStart_3621089 : Nat := 118140960795 + 3621089 * 2 ^ 59
def prefixEnd_3621089 : Nat := 4983230072969 + 3 ^ 40 * 3621089 * 2
def baseEnd_3621089 : Nat := 1239572766472458804222947

theorem tailTrace_3621089 : CollatzResearch.WordTrace tailWord_3621089 prefixEnd_3621089 1239572766472458804222947 := by
  unfold tailWord_3621089
  simp only [CollatzResearch.WordTrace]
  refine ⟨132071965978420460610362321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88047977318946973740241547 132071965978420460610362321)
  ·
    refine ⟨99053974483815345457771741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132071965978420460610362321 99053974483815345457771741)
    ·
      refine ⟨37145240431430754546664403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99053974483815345457771741 37145240431430754546664403)
      ·
        refine ⟨55717860647146131819996605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37145240431430754546664403 55717860647146131819996605)
        ·
          refine ⟨20894197742679799432498727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55717860647146131819996605 20894197742679799432498727)
          ·
            refine ⟨31341296614019699148748091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20894197742679799432498727 31341296614019699148748091)
            ·
              refine ⟨47011944921029548723122137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31341296614019699148748091 47011944921029548723122137)
              ·
                refine ⟨35258958690772161542341603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47011944921029548723122137 35258958690772161542341603)
                ·
                  refine ⟨52888438036158242313512405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35258958690772161542341603 52888438036158242313512405)
                  ·
                    refine ⟨1239572766472458804222947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52888438036158242313512405 1239572766472458804222947)
                    ·
                      rfl

theorem cell22_3621089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_3621089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621089 prefixEnd_3621089 := by exact prefixLift 3621089
  have htrace : WordTrace (prefixWord ++ tailWord_3621089) baseStart_3621089 baseEnd_3621089 := by
    simpa [prefixWord, tailWord_3621089, baseEnd_3621089] using wordTrace_append hprefix tailTrace_3621089
  have hstable : (prefixWord ++ tailWord_3621089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621089).length < 2 ^ (prefixWord ++ tailWord_3621089).sum := by decide
  have hdescent : baseEnd_3621089 < baseStart_3621089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621095 : List Nat := [1, 1, 5, 3, 1, 1, 1, 5, 1, 3]
def baseStart_3621095 : Nat := 118140960795 + 3621095 * 2 ^ 59
def prefixEnd_3621095 : Nat := 4983230072969 + 3 ^ 40 * 3621095 * 2
def baseEnd_3621095 : Nat := 1239574820395076788572929

theorem tailTrace_3621095 : CollatzResearch.WordTrace tailWord_3621095 prefixEnd_3621095 1239574820395076788572929 := by
  unfold tailWord_3621095
  simp only [CollatzResearch.WordTrace]
  refine ⟨132072184816398723635080739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88048123210932482423387159 132072184816398723635080739)
  ·
    refine ⟨198108277224598085452621109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132072184816398723635080739 198108277224598085452621109)
    ·
      refine ⟨18572650989806070511183229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198108277224598085452621109 18572650989806070511183229)
      ·
        refine ⟨6964744121177276441693711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18572650989806070511183229 6964744121177276441693711)
        ·
          refine ⟨10447116181765914662540567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6964744121177276441693711 10447116181765914662540567)
          ·
            refine ⟨15670674272648871993810851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10447116181765914662540567 15670674272648871993810851)
            ·
              refine ⟨23506011408973307990716277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15670674272648871993810851 23506011408973307990716277)
              ·
                refine ⟨2203688569591247624129651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23506011408973307990716277 2203688569591247624129651)
                ·
                  refine ⟨3305532854386871436194477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2203688569591247624129651 3305532854386871436194477)
                  ·
                    refine ⟨1239574820395076788572929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3305532854386871436194477 1239574820395076788572929)
                    ·
                      rfl

theorem cell22_3621095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_3621095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621095 prefixEnd_3621095 := by exact prefixLift 3621095
  have htrace : WordTrace (prefixWord ++ tailWord_3621095) baseStart_3621095 baseEnd_3621095 := by
    simpa [prefixWord, tailWord_3621095, baseEnd_3621095] using wordTrace_append hprefix tailTrace_3621095
  have hstable : (prefixWord ++ tailWord_3621095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621095).length < 2 ^ (prefixWord ++ tailWord_3621095).sum := by decide
  have hdescent : baseEnd_3621095 < baseStart_3621095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621106 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_3621106 : Nat := 118140960795 + 3621106 * 2 ^ 59
def prefixEnd_3621106 : Nat := 4983230072969 + 3 ^ 40 * 3621106 * 2
def baseEnd_3621106 : Nat := 1239578585919876426547895

theorem tailTrace_3621106 : CollatzResearch.WordTrace tailWord_3621106 prefixEnd_3621106 1239578585919876426547895 := by
  unfold tailWord_3621106
  simp only [CollatzResearch.WordTrace]
  refine ⟨33018146504839718128432793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88048390679572581675820781 33018146504839718128432793)
  ·
    refine ⟨24763609878629788596324595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33018146504839718128432793 24763609878629788596324595)
    ·
      refine ⟨37145414817944682894486893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24763609878629788596324595 37145414817944682894486893)
      ·
        refine ⟨13929530556729256085432585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37145414817944682894486893 13929530556729256085432585)
        ·
          refine ⟨10447147917546942064074439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13929530556729256085432585 10447147917546942064074439)
          ·
            refine ⟨15670721876320413096111659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10447147917546942064074439 15670721876320413096111659)
            ·
              refine ⟨23506082814480619644167489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15670721876320413096111659 23506082814480619644167489)
              ·
                refine ⟨17629562110860464733125617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23506082814480619644167489 17629562110860464733125617)
                ·
                  refine ⟨13222171583145348549844213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17629562110860464733125617 13222171583145348549844213)
                  ·
                    refine ⟨1239578585919876426547895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13222171583145348549844213 1239578585919876426547895)
                    ·
                      rfl

theorem cell22_3621106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_3621106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621106 prefixEnd_3621106 := by exact prefixLift 3621106
  have htrace : WordTrace (prefixWord ++ tailWord_3621106) baseStart_3621106 baseEnd_3621106 := by
    simpa [prefixWord, tailWord_3621106, baseEnd_3621106] using wordTrace_append hprefix tailTrace_3621106
  have hstable : (prefixWord ++ tailWord_3621106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621106).length < 2 ^ (prefixWord ++ tailWord_3621106).sum := by decide
  have hdescent : baseEnd_3621106 < baseStart_3621106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621153 : List Nat := [1, 2, 3, 2, 1, 1, 5, 3, 4]
def baseStart_3621153 : Nat := 118140960795 + 3621153 * 2 ^ 59
def prefixEnd_3621153 : Nat := 4983230072969 + 3 ^ 40 * 3621153 * 2
def baseEnd_3621153 : Nat := 413198224993461323540917

theorem tailTrace_3621153 : CollatzResearch.WordTrace tailWord_3621153 prefixEnd_3621153 413198224993461323540917 := by
  unfold tailWord_3621153
  simp only [CollatzResearch.WordTrace]
  refine ⟨132074300250188599540692113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88049533500125733027128075 132074300250188599540692113)
  ·
    refine ⟨99055725187641449655519085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132074300250188599540692113 99055725187641449655519085)
    ·
      refine ⟨37145896945365543620819657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99055725187641449655519085 37145896945365543620819657)
      ·
        refine ⟨27859422709024157715614743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37145896945365543620819657 27859422709024157715614743)
        ·
          refine ⟨41789134063536236573422115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27859422709024157715614743 41789134063536236573422115)
          ·
            refine ⟨62683701095304354860133173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41789134063536236573422115 62683701095304354860133173)
            ·
              refine ⟨5876596977684783268137485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62683701095304354860133173 5876596977684783268137485)
              ·
                refine ⟨2203723866631793725551557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5876596977684783268137485 2203723866631793725551557)
                ·
                  refine ⟨413198224993461323540917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2203723866631793725551557 413198224993461323540917)
                  ·
                    rfl

theorem cell22_3621153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 4].length) (baseStart_3621153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621153 prefixEnd_3621153 := by exact prefixLift 3621153
  have htrace : WordTrace (prefixWord ++ tailWord_3621153) baseStart_3621153 baseEnd_3621153 := by
    simpa [prefixWord, tailWord_3621153, baseEnd_3621153] using wordTrace_append hprefix tailTrace_3621153
  have hstable : (prefixWord ++ tailWord_3621153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621153).length < 2 ^ (prefixWord ++ tailWord_3621153).sum := by decide
  have hdescent : baseEnd_3621153 < baseStart_3621153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621164 : List Nat := [2, 2, 1, 1, 1, 3, 12]
def baseStart_3621164 : Nat := 118140960795 + 3621164 * 2 ^ 59
def prefixEnd_3621164 : Nat := 4983230072969 + 3 ^ 40 * 3621164 * 2
def baseEnd_3621164 : Nat := 45911053352043837355471

theorem tailTrace_3621164 : CollatzResearch.WordTrace tailWord_3621164 prefixEnd_3621164 45911053352043837355471 := by
  unfold tailWord_3621164
  simp only [CollatzResearch.WordTrace]
  refine ⟨66037350726574374209671273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88049800968765832279561697 66037350726574374209671273)
  ·
    refine ⟨49528013044930780657253455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66037350726574374209671273 49528013044930780657253455)
    ·
      refine ⟨74292019567396170985880183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49528013044930780657253455 74292019567396170985880183)
      ·
        refine ⟨111438029351094256478820275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74292019567396170985880183 111438029351094256478820275)
        ·
          refine ⟨167157044026641384718230413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111438029351094256478820275 167157044026641384718230413)
          ·
            refine ⟨62683891509990519269336405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167157044026641384718230413 62683891509990519269336405)
            ·
              refine ⟨45911053352043837355471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 62683891509990519269336405 45911053352043837355471)
              ·
                rfl

theorem cell22_3621164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 12].length) (baseStart_3621164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621164 prefixEnd_3621164 := by exact prefixLift 3621164
  have htrace : WordTrace (prefixWord ++ tailWord_3621164) baseStart_3621164 baseEnd_3621164 := by
    simpa [prefixWord, tailWord_3621164, baseEnd_3621164] using wordTrace_append hprefix tailTrace_3621164
  have hstable : (prefixWord ++ tailWord_3621164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621164).length < 2 ^ (prefixWord ++ tailWord_3621164).sum := by decide
  have hdescent : baseEnd_3621164 < baseStart_3621164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621170 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 6]
def baseStart_3621170 : Nat := 118140960795 + 3621170 * 2 ^ 59
def prefixEnd_3621170 : Nat := 4983230072969 + 3 ^ 40 * 3621170 * 2
def baseEnd_3621170 : Nat := 413200164809267197649233

theorem tailTrace_3621170 : CollatzResearch.WordTrace tailWord_3621170 prefixEnd_3621170 413200164809267197649233 := by
  unfold tailWord_3621170
  simp only [CollatzResearch.WordTrace]
  refine ⟨33018730072781752861015241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88049946860751340962707309 33018730072781752861015241)
  ·
    refine ⟨24764047554586314645761431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33018730072781752861015241 24764047554586314645761431)
    ·
      refine ⟨37146071331879471968642147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24764047554586314645761431 37146071331879471968642147)
      ·
        refine ⟨55719106997819207952963221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37146071331879471968642147 55719106997819207952963221)
        ·
          refine ⟨2611833140522775372795151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55719106997819207952963221 2611833140522775372795151)
          ·
            refine ⟨3917749710784163059192727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2611833140522775372795151 3917749710784163059192727)
            ·
              refine ⟨5876624566176244588789091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3917749710784163059192727 5876624566176244588789091)
              ·
                refine ⟨8814936849264366883183637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5876624566176244588789091 8814936849264366883183637)
                ·
                  refine ⟨413200164809267197649233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8814936849264366883183637 413200164809267197649233)
                  ·
                    rfl

theorem cell22_3621170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_3621170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621170 prefixEnd_3621170 := by exact prefixLift 3621170
  have htrace : WordTrace (prefixWord ++ tailWord_3621170) baseStart_3621170 baseEnd_3621170 := by
    simpa [prefixWord, tailWord_3621170, baseEnd_3621170] using wordTrace_append hprefix tailTrace_3621170
  have hstable : (prefixWord ++ tailWord_3621170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621170).length < 2 ^ (prefixWord ++ tailWord_3621170).sum := by decide
  have hdescent : baseEnd_3621170 < baseStart_3621170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621273 : List Nat := [1, 2, 1, 2, 1, 4, 3, 3, 1, 4]
def baseStart_3621273 : Nat := 118140960795 + 3621273 * 2 ^ 59
def prefixEnd_3621273 : Nat := 4983230072969 + 3 ^ 40 * 3621273 * 2
def baseEnd_3621273 : Nat := 1239635753432743657622383

theorem tailTrace_3621273 : CollatzResearch.WordTrace tailWord_3621273 prefixEnd_3621273 1239635753432743657622383 := by
  unfold tailWord_3621273
  simp only [CollatzResearch.WordTrace]
  refine ⟨132078677009753860035060473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88052451339835906690040315 132078677009753860035060473)
  ·
    refine ⟨99059007757315395026295355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132078677009753860035060473 99059007757315395026295355)
    ·
      refine ⟨148588511635973092539443033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99059007757315395026295355 148588511635973092539443033)
      ·
        refine ⟨111441383726979819404582275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148588511635973092539443033 111441383726979819404582275)
        ·
          refine ⟨167162075590469729106873413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111441383726979819404582275 167162075590469729106873413)
          ·
            refine ⟨31342889173213074207538765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167162075590469729106873413 31342889173213074207538765)
            ·
              refine ⟨11753583439954902827827037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31342889173213074207538765 11753583439954902827827037)
              ·
                refine ⟨4407593789983088560435139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11753583439954902827827037 4407593789983088560435139)
                ·
                  refine ⟨6611390684974632840652709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4407593789983088560435139 6611390684974632840652709)
                  ·
                    refine ⟨1239635753432743657622383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6611390684974632840652709 1239635753432743657622383)
                    ·
                      rfl

theorem cell22_3621273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 4].length) (baseStart_3621273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621273 prefixEnd_3621273 := by exact prefixLift 3621273
  have htrace : WordTrace (prefixWord ++ tailWord_3621273) baseStart_3621273 baseEnd_3621273 := by
    simpa [prefixWord, tailWord_3621273, baseEnd_3621273] using wordTrace_append hprefix tailTrace_3621273
  have hstable : (prefixWord ++ tailWord_3621273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621273).length < 2 ^ (prefixWord ++ tailWord_3621273).sum := by decide
  have hdescent : baseEnd_3621273 < baseStart_3621273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621277 : List Nat := [1, 4, 2, 1, 5, 1, 1, 2, 5]
def baseStart_3621277 : Nat := 118140960795 + 3621277 * 2 ^ 59
def prefixEnd_3621277 : Nat := 4983230072969 + 3 ^ 40 * 3621277 * 2
def baseEnd_3621277 : Nat := 413212374238162993507457

theorem tailTrace_3621277 : CollatzResearch.WordTrace tailWord_3621277 prefixEnd_3621277 413212374238162993507457 := by
  unfold tailWord_3621277
  simp only [CollatzResearch.WordTrace]
  refine ⟨132078822901739368718206085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88052548601159579145470723 132078822901739368718206085)
  ·
    refine ⟨24764779294076131634663641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132078822901739368718206085 24764779294076131634663641)
    ·
      refine ⟨18573584470557098725997731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24764779294076131634663641 18573584470557098725997731)
      ·
        refine ⟨27860376705835648088996597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18573584470557098725997731 27860376705835648088996597)
        ·
          refine ⟨2611910316172092008343431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27860376705835648088996597 2611910316172092008343431)
          ·
            refine ⟨3917865474258138012515147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2611910316172092008343431 3917865474258138012515147)
            ·
              refine ⟨5876798211387207018772721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3917865474258138012515147 5876798211387207018772721)
              ·
                refine ⟨4407598658540405264079541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5876798211387207018772721 4407598658540405264079541)
                ·
                  refine ⟨413212374238162993507457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4407598658540405264079541 413212374238162993507457)
                  ·
                    rfl

theorem cell22_3621277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_3621277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621277 prefixEnd_3621277 := by exact prefixLift 3621277
  have htrace : WordTrace (prefixWord ++ tailWord_3621277) baseStart_3621277 baseEnd_3621277 := by
    simpa [prefixWord, tailWord_3621277, baseEnd_3621277] using wordTrace_append hprefix tailTrace_3621277
  have hstable : (prefixWord ++ tailWord_3621277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621277).length < 2 ^ (prefixWord ++ tailWord_3621277).sum := by decide
  have hdescent : baseEnd_3621277 < baseStart_3621277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621303 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 1, 5]
def baseStart_3621303 : Nat := 118140960795 + 3621303 * 2 ^ 59
def prefixEnd_3621303 : Nat := 4983230072969 + 3 ^ 40 * 3621303 * 2
def baseEnd_3621303 : Nat := 1239646023045833579372291

theorem tailTrace_3621303 : CollatzResearch.WordTrace tailWord_3621303 prefixEnd_3621303 1239646023045833579372291 := by
  unfold tailWord_3621303
  simp only [CollatzResearch.WordTrace]
  refine ⟨132079771199645175158652563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88053180799763450105768375 132079771199645175158652563)
  ·
    refine ⟨198119656799467762737978845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132079771199645175158652563 198119656799467762737978845)
    ·
      refine ⟨74294871299800411026742067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198119656799467762737978845 74294871299800411026742067)
      ·
        refine ⟨111442306949700616540113101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74294871299800411026742067 111442306949700616540113101)
        ·
          refine ⟨41790865106137731202542413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111442306949700616540113101 41790865106137731202542413)
          ·
            refine ⟨15671574414801649200953405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41790865106137731202542413 15671574414801649200953405)
            ·
              refine ⟨5876840405550618450357527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15671574414801649200953405 5876840405550618450357527)
              ·
                refine ⟨8815260608325927675536291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5876840405550618450357527 8815260608325927675536291)
                ·
                  refine ⟨13222890912488891513304437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8815260608325927675536291 13222890912488891513304437)
                  ·
                    refine ⟨1239646023045833579372291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13222890912488891513304437 1239646023045833579372291)
                    ·
                      rfl

theorem cell22_3621303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_3621303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621303 prefixEnd_3621303 := by exact prefixLift 3621303
  have htrace : WordTrace (prefixWord ++ tailWord_3621303) baseStart_3621303 baseEnd_3621303 := by
    simpa [prefixWord, tailWord_3621303, baseEnd_3621303] using wordTrace_append hprefix tailTrace_3621303
  have hstable : (prefixWord ++ tailWord_3621303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621303).length < 2 ^ (prefixWord ++ tailWord_3621303).sum := by decide
  have hdescent : baseEnd_3621303 < baseStart_3621303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
