import V185TrunkScan23Chunk1145

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6788743 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_6788743 : Nat := 118140960795 + 6788743 * 2 ^ 59
def prefixEnd_6788743 : Nat := 4983230072969 + 3 ^ 40 * 6788743 * 2
def baseEnd_6788743 : Nat := 3485888198845837745491645

theorem tailTrace_6788743 : CollatzResearch.WordTrace tailWord_6788743 prefixEnd_6788743 3485888198845837745491645 := by
  unfold tailWord_6788743
  simp only [CollatzResearch.WordTrace]
  refine ⟨247605798844551010842970883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165070532563034007228647255 247605798844551010842970883)
  ·
    refine ⟨371408698266826516264456325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247605798844551010842970883 371408698266826516264456325)
    ·
      refine ⟨69639130925029971799585561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371408698266826516264456325 69639130925029971799585561)
      ·
        refine ⟨52229348193772478849689171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69639130925029971799585561 52229348193772478849689171)
        ·
          refine ⟨78344022290658718274533757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52229348193772478849689171 78344022290658718274533757)
          ·
            refine ⟨29379008358997019352950159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78344022290658718274533757 29379008358997019352950159)
            ·
              refine ⟨44068512538495529029425239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29379008358997019352950159 44068512538495529029425239)
              ·
                refine ⟨66102768807743293544137859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44068512538495529029425239 66102768807743293544137859)
                ·
                  refine ⟨99154153211614940316206789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66102768807743293544137859 99154153211614940316206789)
                  ·
                    refine ⟨18591403727177801309288773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99154153211614940316206789 18591403727177801309288773)
                    ·
                      refine ⟨3485888198845837745491645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18591403727177801309288773 3485888198845837745491645)
                      ·
                        rfl

theorem cell23_6788743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_6788743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788743 prefixEnd_6788743 := by exact prefixLift 6788743
  have htrace : WordTrace (prefixWord ++ tailWord_6788743) baseStart_6788743 baseEnd_6788743 := by
    simpa [prefixWord, tailWord_6788743, baseEnd_6788743] using wordTrace_append hprefix tailTrace_6788743
  have hstable : (prefixWord ++ tailWord_6788743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788743).length < 2 ^ (prefixWord ++ tailWord_6788743).sum := by decide
  have hdescent : baseEnd_6788743 < baseStart_6788743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788747 : List Nat := [1, 1, 1, 1, 4, 1, 3, 5, 2, 2, 2]
def baseStart_6788747 : Nat := 118140960795 + 6788747 * 2 ^ 59
def prefixEnd_6788747 : Nat := 4983230072969 + 3 ^ 40 * 6788747 * 2
def baseEnd_6788747 : Nat := 3485890252768455729841627

theorem tailTrace_6788747 : CollatzResearch.WordTrace tailWord_6788747 prefixEnd_6788747 3485890252768455729841627 := by
  unfold tailWord_6788747
  simp only [CollatzResearch.WordTrace]
  refine ⟨247605944736536519526116495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165070629824357679684077663 247605944736536519526116495)
  ·
    refine ⟨371408917104804779289174743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247605944736536519526116495 371408917104804779289174743)
    ·
      refine ⟨557113375657207168933762115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371408917104804779289174743 557113375657207168933762115)
      ·
        refine ⟨835670063485810753400643173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557113375657207168933762115 835670063485810753400643173)
        ·
          refine ⟨156688136903589516262620595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 835670063485810753400643173 156688136903589516262620595)
          ·
            refine ⟨235032205355384274393930893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156688136903589516262620595 235032205355384274393930893)
            ·
              refine ⟨88137077008269102897724085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235032205355384274393930893 88137077008269102897724085)
              ·
                refine ⟨8262850969525228396661633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88137077008269102897724085 8262850969525228396661633)
                ·
                  refine ⟨6197138227143921297496225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8262850969525228396661633 6197138227143921297496225)
                  ·
                    refine ⟨4647853670357940973122169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6197138227143921297496225 4647853670357940973122169)
                    ·
                      refine ⟨3485890252768455729841627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4647853670357940973122169 3485890252768455729841627)
                      ·
                        rfl

theorem cell23_6788747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 2, 2].length) (baseStart_6788747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788747 prefixEnd_6788747 := by exact prefixLift 6788747
  have htrace : WordTrace (prefixWord ++ tailWord_6788747) baseStart_6788747 baseEnd_6788747 := by
    simpa [prefixWord, tailWord_6788747, baseEnd_6788747] using wordTrace_append hprefix tailTrace_6788747
  have hstable : (prefixWord ++ tailWord_6788747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788747).length < 2 ^ (prefixWord ++ tailWord_6788747).sum := by decide
  have hdescent : baseEnd_6788747 < baseStart_6788747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788783 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 4, 5]
def baseStart_6788783 : Nat := 118140960795 + 6788783 * 2 ^ 59
def prefixEnd_6788783 : Nat := 4983230072969 + 3 ^ 40 * 6788783 * 2
def baseEnd_6788783 : Nat := 1161969579357339196330487

theorem tailTrace_6788783 : CollatzResearch.WordTrace tailWord_6788783 prefixEnd_6788783 1161969579357339196330487 := by
  unfold tailWord_6788783
  simp only [CollatzResearch.WordTrace]
  refine ⟨247607257764406097674427003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165071505176270731782951335 247607257764406097674427003)
  ·
    refine ⟨371410886646609146511640505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247607257764406097674427003 371410886646609146511640505)
    ·
      refine ⟨278558164984956859883730379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371410886646609146511640505 278558164984956859883730379)
      ·
        refine ⟨417837247477435289825595569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278558164984956859883730379 417837247477435289825595569)
        ·
          refine ⟨313377935608076467369196677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417837247477435289825595569 313377935608076467369196677)
          ·
            refine ⟨58758362926514337631724377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313377935608076467369196677 58758362926514337631724377)
            ·
              refine ⟨44068772194885753223793283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58758362926514337631724377 44068772194885753223793283)
              ·
                refine ⟨66103158292328629835689925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44068772194885753223793283 66103158292328629835689925)
                ·
                  refine ⟨12394342179811618094191861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66103158292328629835689925 12394342179811618094191861)
                  ·
                    refine ⟨1161969579357339196330487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12394342179811618094191861 1161969579357339196330487)
                    ·
                      rfl

theorem cell23_6788783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 5].length) (baseStart_6788783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788783 prefixEnd_6788783 := by exact prefixLift 6788783
  have htrace : WordTrace (prefixWord ++ tailWord_6788783) baseStart_6788783 baseEnd_6788783 := by
    simpa [prefixWord, tailWord_6788783, baseEnd_6788783] using wordTrace_append hprefix tailTrace_6788783
  have hstable : (prefixWord ++ tailWord_6788783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788783).length < 2 ^ (prefixWord ++ tailWord_6788783).sum := by decide
  have hdescent : baseEnd_6788783 < baseStart_6788783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788793 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 1, 2, 5]
def baseStart_6788793 : Nat := 118140960795 + 6788793 * 2 ^ 59
def prefixEnd_6788793 : Nat := 4983230072969 + 3 ^ 40 * 6788793 * 2
def baseEnd_6788793 : Nat := 3485913872878562549866415

theorem tailTrace_6788793 : CollatzResearch.WordTrace tailWord_6788793 prefixEnd_6788793 3485913872878562549866415 := by
  unfold tailWord_6788793
  simp only [CollatzResearch.WordTrace]
  refine ⟨247607622494369869382291033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165071748329579912921527355 247607622494369869382291033)
  ·
    refine ⟨185705716870777402036718275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247607622494369869382291033 185705716870777402036718275)
    ·
      refine ⟨278558575306166103055077413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185705716870777402036718275 278558575306166103055077413)
      ·
        refine ⟨52229732869906144322827015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278558575306166103055077413 52229732869906144322827015)
        ·
          refine ⟨78344599304859216484240523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52229732869906144322827015 78344599304859216484240523)
          ·
            refine ⟨117516898957288824726360785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78344599304859216484240523 117516898957288824726360785)
            ·
              refine ⟨88137674217966618544770589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117516898957288824726360785 88137674217966618544770589)
              ·
                refine ⟨33051627831737481954288971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88137674217966618544770589 33051627831737481954288971)
                ·
                  refine ⟨49577441747606222931433457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33051627831737481954288971 49577441747606222931433457)
                  ·
                    refine ⟨37183081310704667198575093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49577441747606222931433457 37183081310704667198575093)
                    ·
                      refine ⟨3485913872878562549866415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37183081310704667198575093 3485913872878562549866415)
                      ·
                        rfl

theorem cell23_6788793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_6788793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788793 prefixEnd_6788793 := by exact prefixLift 6788793
  have htrace : WordTrace (prefixWord ++ tailWord_6788793) baseStart_6788793 baseEnd_6788793 := by
    simpa [prefixWord, tailWord_6788793, baseEnd_6788793] using wordTrace_append hprefix tailTrace_6788793
  have hstable : (prefixWord ++ tailWord_6788793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788793).length < 2 ^ (prefixWord ++ tailWord_6788793).sum := by decide
  have hdescent : baseEnd_6788793 < baseStart_6788793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788843 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 8]
def baseStart_6788843 : Nat := 118140960795 + 6788843 * 2 ^ 59
def prefixEnd_6788843 : Nat := 4983230072969 + 3 ^ 40 * 6788843 * 2
def baseEnd_6788843 : Nat := 387326616323476372693465

theorem tailTrace_6788843 : CollatzResearch.WordTrace tailWord_6788843 prefixEnd_6788843 387326616323476372693465 := by
  unfold tailWord_6788843
  simp only [CollatzResearch.WordTrace]
  refine ⟨247609446144188727921611183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165072964096125818614407455 247609446144188727921611183)
  ·
    refine ⟨371414169216283091882416775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247609446144188727921611183 371414169216283091882416775)
    ·
      refine ⟨557121253824424637823625163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371414169216283091882416775 557121253824424637823625163)
      ·
        refine ⟨835681880736636956735437745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557121253824424637823625163 835681880736636956735437745)
        ·
          refine ⟨626761410552477717551578309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835681880736636956735437745 626761410552477717551578309)
          ·
            refine ⟨117517764478589572040920933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 626761410552477717551578309 117517764478589572040920933)
            ·
              refine ⟨22034580839735544757672675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117517764478589572040920933 22034580839735544757672675)
              ·
                refine ⟨33051871259603317136509013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22034580839735544757672675 33051871259603317136509013)
                ·
                  refine ⟨387326616323476372693465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33051871259603317136509013 387326616323476372693465)
                  ·
                    rfl

theorem cell23_6788843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 8].length) (baseStart_6788843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788843 prefixEnd_6788843 := by exact prefixLift 6788843
  have htrace : WordTrace (prefixWord ++ tailWord_6788843) baseStart_6788843 baseEnd_6788843 := by
    simpa [prefixWord, tailWord_6788843, baseEnd_6788843] using wordTrace_append hprefix tailTrace_6788843
  have hstable : (prefixWord ++ tailWord_6788843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788843).length < 2 ^ (prefixWord ++ tailWord_6788843).sum := by decide
  have hdescent : baseEnd_6788843 < baseStart_6788843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788860 : List Nat := [2, 2, 2, 1, 3, 1, 3, 3, 6]
def baseStart_6788860 : Nat := 118140960795 + 6788860 * 2 ^ 59
def prefixEnd_6788860 : Nat := 4983230072969 + 3 ^ 40 * 6788860 * 2
def baseEnd_6788860 : Nat := 387327586231379309747623

theorem tailTrace_6788860 : CollatzResearch.WordTrace tailWord_6788860 prefixEnd_6788860 387327586231379309747623 := by
  unfold tailWord_6788860
  simp only [CollatzResearch.WordTrace]
  refine ⟨123805033092563569912490017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165073377456751426549986689 123805033092563569912490017)
  ·
    refine ⟨92853774819422677434367513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123805033092563569912490017 92853774819422677434367513)
    ·
      refine ⟨69640331114567008075775635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92853774819422677434367513 69640331114567008075775635)
      ·
        refine ⟨104460496671850512113663453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69640331114567008075775635 104460496671850512113663453)
        ·
          refine ⟨39172686251943942042623795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104460496671850512113663453 39172686251943942042623795)
          ·
            refine ⟨58759029377915913063935693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39172686251943942042623795 58759029377915913063935693)
            ·
              refine ⟨22034636016718467398975885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58759029377915913063935693 22034636016718467398975885)
              ·
                refine ⟨8262988506269425274615957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22034636016718467398975885 8262988506269425274615957)
                ·
                  refine ⟨387327586231379309747623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8262988506269425274615957 387327586231379309747623)
                  ·
                    rfl

theorem cell23_6788860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 6].length) (baseStart_6788860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788860 prefixEnd_6788860 := by exact prefixLift 6788860
  have htrace : WordTrace (prefixWord ++ tailWord_6788860) baseStart_6788860 baseEnd_6788860 := by
    simpa [prefixWord, tailWord_6788860, baseEnd_6788860] using wordTrace_append hprefix tailTrace_6788860
  have hstable : (prefixWord ++ tailWord_6788860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788860).length < 2 ^ (prefixWord ++ tailWord_6788860).sum := by decide
  have hdescent : baseEnd_6788860 < baseStart_6788860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788863 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 6]
def baseStart_6788863 : Nat := 118140960795 + 6788863 * 2 ^ 59
def prefixEnd_6788863 : Nat := 4983230072969 + 3 ^ 40 * 6788863 * 2
def baseEnd_6788863 : Nat := 3485949816524377275991093

theorem tailTrace_6788863 : CollatzResearch.WordTrace tailWord_6788863 prefixEnd_6788863 3485949816524377275991093 := by
  unfold tailWord_6788863
  simp only [CollatzResearch.WordTrace]
  refine ⟨247610175604116271337339243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165073450402744180891559495 247610175604116271337339243)
  ·
    refine ⟨371415263406174407006008865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247610175604116271337339243 371415263406174407006008865)
    ·
      refine ⟨278561447554630805254506649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371415263406174407006008865 278561447554630805254506649)
      ·
        refine ⟨208921085665973103940879987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278561447554630805254506649 208921085665973103940879987)
        ·
          refine ⟨313381628498959655911319981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208921085665973103940879987 313381628498959655911319981)
          ·
            refine ⟨117518110687109870966744993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313381628498959655911319981 117518110687109870966744993)
            ·
              refine ⟨88138583015332403225058745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117518110687109870966744993 88138583015332403225058745)
              ·
                refine ⟨66103937261499302418794059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88138583015332403225058745 66103937261499302418794059)
                ·
                  refine ⟨99155905892248953628191089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66103937261499302418794059 99155905892248953628191089)
                  ·
                    refine ⟨74366929419186715221143317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99155905892248953628191089 74366929419186715221143317)
                    ·
                      refine ⟨3485949816524377275991093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74366929419186715221143317 3485949816524377275991093)
                      ·
                        rfl

theorem cell23_6788863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_6788863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788863 prefixEnd_6788863 := by exact prefixLift 6788863
  have htrace : WordTrace (prefixWord ++ tailWord_6788863) baseStart_6788863 baseEnd_6788863 := by
    simpa [prefixWord, tailWord_6788863, baseEnd_6788863] using wordTrace_append hprefix tailTrace_6788863
  have hstable : (prefixWord ++ tailWord_6788863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788863).length < 2 ^ (prefixWord ++ tailWord_6788863).sum := by decide
  have hdescent : baseEnd_6788863 < baseStart_6788863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788883 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 5]
def baseStart_6788883 : Nat := 118140960795 + 6788883 * 2 ^ 59
def prefixEnd_6788883 : Nat := 4983230072969 + 3 ^ 40 * 6788883 * 2
def baseEnd_6788883 : Nat := 3485960086137467197741001

theorem tailTrace_6788883 : CollatzResearch.WordTrace tailWord_6788883 prefixEnd_6788883 3485960086137467197741001 := by
  unfold tailWord_6788883
  simp only [CollatzResearch.WordTrace]
  refine ⟨247610905064043814753067303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165073936709362543168711535 247610905064043814753067303)
  ·
    refine ⟨371416357596065722129600955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247610905064043814753067303 371416357596065722129600955)
    ·
      refine ⟨557124536394098583194401433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371416357596065722129600955 557124536394098583194401433)
      ·
        refine ⟨417843402295573937395801075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557124536394098583194401433 417843402295573937395801075)
        ·
          refine ⟨626765103443360906093701613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417843402295573937395801075 626765103443360906093701613)
          ·
            refine ⟨235036913791260339785138105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 626765103443360906093701613 235036913791260339785138105)
            ·
              refine ⟨176277685343445254838853579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235036913791260339785138105 176277685343445254838853579)
              ·
                refine ⟨264416528015167882258280369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176277685343445254838853579 264416528015167882258280369)
                ·
                  refine ⟨198312396011375911693710277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264416528015167882258280369 198312396011375911693710277)
                  ·
                    refine ⟨37183574252132983442570677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 198312396011375911693710277 37183574252132983442570677)
                    ·
                      refine ⟨3485960086137467197741001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37183574252132983442570677 3485960086137467197741001)
                      ·
                        rfl

theorem cell23_6788883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_6788883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788883 prefixEnd_6788883 := by exact prefixLift 6788883
  have htrace : WordTrace (prefixWord ++ tailWord_6788883) baseStart_6788883 baseEnd_6788883 := by
    simpa [prefixWord, tailWord_6788883, baseEnd_6788883] using wordTrace_append hprefix tailTrace_6788883
  have hstable : (prefixWord ++ tailWord_6788883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788883).length < 2 ^ (prefixWord ++ tailWord_6788883).sum := by decide
  have hdescent : baseEnd_6788883 < baseStart_6788883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788920 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 1, 6]
def baseStart_6788920 : Nat := 118140960795 + 6788920 * 2 ^ 59
def prefixEnd_6788920 : Nat := 4983230072969 + 3 ^ 40 * 6788920 * 2
def baseEnd_6788920 : Nat := 1161993028307227850992777

theorem tailTrace_6788920 : CollatzResearch.WordTrace tailWord_6788920 prefixEnd_6788920 1161993028307227850992777 := by
  unfold tailWord_6788920
  simp only [CollatzResearch.WordTrace]
  refine ⟨123806127282454885036082107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165074836376606513381442809 123806127282454885036082107)
  ·
    refine ⟨185709190923682327554123161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123806127282454885036082107 185709190923682327554123161)
    ·
      refine ⟨139281893192761745665592371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185709190923682327554123161 139281893192761745665592371)
      ·
        refine ⟨208922839789142618498388557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139281893192761745665592371 208922839789142618498388557)
        ·
          refine ⟨78346064920928481936895709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208922839789142618498388557 78346064920928481936895709)
          ·
            refine ⟨29379774345348180726335891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78346064920928481936895709 29379774345348180726335891)
            ·
              refine ⟨44069661518022271089503837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29379774345348180726335891 44069661518022271089503837)
              ·
                refine ⟨16526123069258351658563939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44069661518022271089503837 16526123069258351658563939)
                ·
                  refine ⟨24789184603887527487845909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16526123069258351658563939 24789184603887527487845909)
                  ·
                    refine ⟨1161993028307227850992777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24789184603887527487845909 1161993028307227850992777)
                    ·
                      rfl

theorem cell23_6788920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_6788920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788920 prefixEnd_6788920 := by exact prefixLift 6788920
  have htrace : WordTrace (prefixWord ++ tailWord_6788920) baseStart_6788920 baseEnd_6788920 := by
    simpa [prefixWord, tailWord_6788920, baseEnd_6788920] using wordTrace_append hprefix tailTrace_6788920
  have hstable : (prefixWord ++ tailWord_6788920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788920).length < 2 ^ (prefixWord ++ tailWord_6788920).sum := by decide
  have hdescent : baseEnd_6788920 < baseStart_6788920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788921 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 3, 1, 3]
def baseStart_6788921 : Nat := 118140960795 + 6788921 * 2 ^ 59
def prefixEnd_6788921 : Nat := 4983230072969 + 3 ^ 40 * 6788921 * 2
def baseEnd_6788921 : Nat := 3485979598402338049065827

theorem tailTrace_6788921 : CollatzResearch.WordTrace tailWord_6788921 prefixEnd_6788921 3485979598402338049065827 := by
  unfold tailWord_6788921
  simp only [CollatzResearch.WordTrace]
  refine ⟨247612291037906147242950617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165074860691937431495300411 247612291037906147242950617)
  ·
    refine ⟨185709218278429610432212963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247612291037906147242950617 185709218278429610432212963)
    ·
      refine ⟨278563827417644415648319445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185709218278429610432212963 278563827417644415648319445)
      ·
        refine ⟨6528839705101040991757487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 278563827417644415648319445 6528839705101040991757487)
        ·
          refine ⟨9793259557651561487636231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6528839705101040991757487 9793259557651561487636231)
          ·
            refine ⟨14689889336477342231454347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9793259557651561487636231 14689889336477342231454347)
            ·
              refine ⟨22034834004716013347181521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14689889336477342231454347 22034834004716013347181521)
              ·
                refine ⟨16526125503537010010386141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22034834004716013347181521 16526125503537010010386141)
                ·
                  refine ⟨6197297063826378753894803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16526125503537010010386141 6197297063826378753894803)
                  ·
                    refine ⟨9295945595739568130842205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6197297063826378753894803 9295945595739568130842205)
                    ·
                      refine ⟨3485979598402338049065827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9295945595739568130842205 3485979598402338049065827)
                      ·
                        rfl

theorem cell23_6788921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_6788921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788921 prefixEnd_6788921 := by exact prefixLift 6788921
  have htrace : WordTrace (prefixWord ++ tailWord_6788921) baseStart_6788921 baseEnd_6788921 := by
    simpa [prefixWord, tailWord_6788921, baseEnd_6788921] using wordTrace_append hprefix tailTrace_6788921
  have hstable : (prefixWord ++ tailWord_6788921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788921).length < 2 ^ (prefixWord ++ tailWord_6788921).sum := by decide
  have hdescent : baseEnd_6788921 < baseStart_6788921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788941 : List Nat := [1, 6, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_6788941 : Nat := 118140960795 + 6788941 * 2 ^ 59
def prefixEnd_6788941 : Nat := 4983230072969 + 3 ^ 40 * 6788941 * 2
def baseEnd_6788941 : Nat := 1161996622671809323605245

theorem tailTrace_6788941 : CollatzResearch.WordTrace tailWord_6788941 prefixEnd_6788941 1161996622671809323605245 := by
  unfold tailWord_6788941
  simp only [CollatzResearch.WordTrace]
  refine ⟨247613020497833690658678677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165075346998555793772452451 247613020497833690658678677)
  ·
    refine ⟨11606860335835954249625563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 247613020497833690658678677 11606860335835954249625563)
    ·
      refine ⟨17410290503753931374438345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11606860335835954249625563 17410290503753931374438345)
      ·
        refine ⟨13057717877815448530828759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17410290503753931374438345 13057717877815448530828759)
        ·
          refine ⟨19586576816723172796243139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13057717877815448530828759 19586576816723172796243139)
          ·
            refine ⟨29379865225084759194364709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19586576816723172796243139 29379865225084759194364709)
            ·
              refine ⟨5508724729703392348943383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29379865225084759194364709 5508724729703392348943383)
              ·
                refine ⟨8263087094555088523415075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5508724729703392348943383 8263087094555088523415075)
                ·
                  refine ⟨12394630641832632785122613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8263087094555088523415075 12394630641832632785122613)
                  ·
                    refine ⟨1161996622671809323605245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12394630641832632785122613 1161996622671809323605245)
                    ·
                      rfl

theorem cell23_6788941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_6788941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788941 prefixEnd_6788941 := by exact prefixLift 6788941
  have htrace : WordTrace (prefixWord ++ tailWord_6788941) baseStart_6788941 baseEnd_6788941 := by
    simpa [prefixWord, tailWord_6788941, baseEnd_6788941] using wordTrace_append hprefix tailTrace_6788941
  have hstable : (prefixWord ++ tailWord_6788941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788941).length < 2 ^ (prefixWord ++ tailWord_6788941).sum := by decide
  have hdescent : baseEnd_6788941 < baseStart_6788941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788961 : List Nat := [1, 2, 3, 1, 1, 1, 3, 6, 1, 2, 2]
def baseStart_6788961 : Nat := 118140960795 + 6788961 * 2 ^ 59
def prefixEnd_6788961 : Nat := 4983230072969 + 3 ^ 40 * 6788961 * 2
def baseEnd_6788961 : Nat := 3486000137628517892565643

theorem tailTrace_6788961 : CollatzResearch.WordTrace tailWord_6788961 prefixEnd_6788961 3486000137628517892565643 := by
  unfold tailWord_6788961
  simp only [CollatzResearch.WordTrace]
  refine ⟨247613749957761234074406737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165075833305174156049604491 247613749957761234074406737)
  ·
    refine ⟨185710312468320925555805053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247613749957761234074406737 185710312468320925555805053)
    ·
      refine ⟨69641367175620347083426895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185710312468320925555805053 69641367175620347083426895)
      ·
        refine ⟨104462050763430520625140343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69641367175620347083426895 104462050763430520625140343)
        ·
          refine ⟨156693076145145780937710515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104462050763430520625140343 156693076145145780937710515)
          ·
            refine ⟨235039614217718671406565773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156693076145145780937710515 235039614217718671406565773)
            ·
              refine ⟨88139855331644501777462165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235039614217718671406565773 88139855331644501777462165)
              ·
                refine ⟨4131555718670836020818539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88139855331644501777462165 4131555718670836020818539)
                ·
                  refine ⟨6197333578006254031227809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4131555718670836020818539 6197333578006254031227809)
                  ·
                    refine ⟨4648000183504690523420857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6197333578006254031227809 4648000183504690523420857)
                    ·
                      refine ⟨3486000137628517892565643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4648000183504690523420857 3486000137628517892565643)
                      ·
                        rfl

theorem cell23_6788961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_6788961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788961 prefixEnd_6788961 := by exact prefixLift 6788961
  have htrace : WordTrace (prefixWord ++ tailWord_6788961) baseStart_6788961 baseEnd_6788961 := by
    simpa [prefixWord, tailWord_6788961, baseEnd_6788961] using wordTrace_append hprefix tailTrace_6788961
  have hstable : (prefixWord ++ tailWord_6788961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788961).length < 2 ^ (prefixWord ++ tailWord_6788961).sum := by decide
  have hdescent : baseEnd_6788961 < baseStart_6788961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788974 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_6788974 : Nat := 118140960795 + 6788974 * 2 ^ 59
def prefixEnd_6788974 : Nat := 4983230072969 + 3 ^ 40 * 6788974 * 2
def baseEnd_6788974 : Nat := 3486006812877026341703083

theorem tailTrace_6788974 : CollatzResearch.WordTrace tailWord_6788974 prefixEnd_6788974 3486006812877026341703083 := by
  unfold tailWord_6788974
  simp only [CollatzResearch.WordTrace]
  refine ⟨30951778013339267161828747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165076149404476091529753317 30951778013339267161828747)
  ·
    refine ⟨46427667020008900742743121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30951778013339267161828747 46427667020008900742743121)
    ·
      refine ⟨34820750265006675557057341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46427667020008900742743121 34820750265006675557057341)
      ·
        refine ⟨13057781349377503333896503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34820750265006675557057341 13057781349377503333896503)
        ·
          refine ⟨19586672024066255000844755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13057781349377503333896503 19586672024066255000844755)
          ·
            refine ⟨29380008036099382501267133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19586672024066255000844755 29380008036099382501267133)
            ·
              refine ⟨11017503013537268437975175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29380008036099382501267133 11017503013537268437975175)
              ·
                refine ⟨16526254520305902656962763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11017503013537268437975175 16526254520305902656962763)
                ·
                  refine ⟨24789381780458853985444145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16526254520305902656962763 24789381780458853985444145)
                  ·
                    refine ⟨18592036335344140489083109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24789381780458853985444145 18592036335344140489083109)
                    ·
                      refine ⟨3486006812877026341703083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18592036335344140489083109 3486006812877026341703083)
                      ·
                        rfl

theorem cell23_6788974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_6788974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788974 prefixEnd_6788974 := by exact prefixLift 6788974
  have htrace : WordTrace (prefixWord ++ tailWord_6788974) baseStart_6788974 baseEnd_6788974 := by
    simpa [prefixWord, tailWord_6788974, baseEnd_6788974] using wordTrace_append hprefix tailTrace_6788974
  have hstable : (prefixWord ++ tailWord_6788974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788974).length < 2 ^ (prefixWord ++ tailWord_6788974).sum := by decide
  have hdescent : baseEnd_6788974 < baseStart_6788974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789022 : List Nat := [4, 3, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_6789022 : Nat := 118140960795 + 6789022 * 2 ^ 59
def prefixEnd_6789022 : Nat := 4983230072969 + 3 ^ 40 * 6789022 * 2
def baseEnd_6789022 : Nat := 1162010486649480717967621

theorem tailTrace_6789022 : CollatzResearch.WordTrace tailWord_6789022 prefixEnd_6789022 1162010486649480717967621 := by
  unfold tailWord_6789022
  simp only [CollatzResearch.WordTrace]
  refine ⟨30951996851317530186547165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165077316540360160994918213 30951996851317530186547165)
  ·
    refine ⟨11606998819244073819955187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30951996851317530186547165 11606998819244073819955187)
    ·
      refine ⟨17410498228866110729932781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11606998819244073819955187 17410498228866110729932781)
      ·
        refine ⟨6528936835824791523724793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17410498228866110729932781 6528936835824791523724793)
        ·
          refine ⟨4896702626868593642793595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6528936835824791523724793 4896702626868593642793595)
          ·
            refine ⟨7345053940302890464190393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4896702626868593642793595 7345053940302890464190393)
            ·
              refine ⟨5508790455227167848142795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7345053940302890464190393 5508790455227167848142795)
              ·
                refine ⟨8263185682840751772214193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5508790455227167848142795 8263185682840751772214193)
                ·
                  refine ⟨6197389262130563829160645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8263185682840751772214193 6197389262130563829160645)
                  ·
                    refine ⟨1162010486649480717967621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6197389262130563829160645 1162010486649480717967621)
                    ·
                      rfl

theorem cell23_6789022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_6789022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789022 prefixEnd_6789022 := by exact prefixLift 6789022
  have htrace : WordTrace (prefixWord ++ tailWord_6789022) baseStart_6789022 baseEnd_6789022 := by
    simpa [prefixWord, tailWord_6789022, baseEnd_6789022] using wordTrace_append hprefix tailTrace_6789022
  have hstable : (prefixWord ++ tailWord_6789022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789022).length < 2 ^ (prefixWord ++ tailWord_6789022).sum := by decide
  have hdescent : baseEnd_6789022 < baseStart_6789022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789028 : List Nat := [2, 3, 1, 2, 1, 5, 2, 1, 2, 1, 3]
def baseStart_6789028 : Nat := 118140960795 + 6789028 * 2 ^ 59
def prefixEnd_6789028 : Nat := 4983230072969 + 3 ^ 40 * 6789028 * 2
def baseEnd_6789028 : Nat := 3486034540832369130427835

theorem tailTrace_6789028 : CollatzResearch.WordTrace tailWord_6789028 prefixEnd_6789028 3486034540832369130427835 := by
  unfold tailWord_6789028
  simp only [CollatzResearch.WordTrace]
  refine ⟨123808096824259252258547869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165077462432345669678063825 123808096824259252258547869)
  ·
    refine ⟨46428036309097219596955451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123808096824259252258547869 46428036309097219596955451)
    ·
      refine ⟨69642054463645829395433177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46428036309097219596955451 69642054463645829395433177)
      ·
        refine ⟨52231540847734372046574883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69642054463645829395433177 52231540847734372046574883)
        ·
          refine ⟨78347311271601558069862325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52231540847734372046574883 78347311271601558069862325)
          ·
            refine ⟨7345060431712646069049593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78347311271601558069862325 7345060431712646069049593)
            ·
              refine ⟨5508795323784484551787195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7345060431712646069049593 5508795323784484551787195)
              ·
                refine ⟨8263192985676726827680793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5508795323784484551787195 8263192985676726827680793)
                ·
                  refine ⟨6197394739257545120760595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8263192985676726827680793 6197394739257545120760595)
                  ·
                    refine ⟨9296092108886317681140893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6197394739257545120760595 9296092108886317681140893)
                    ·
                      refine ⟨3486034540832369130427835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9296092108886317681140893 3486034540832369130427835)
                      ·
                        rfl

theorem cell23_6789028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_6789028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789028 prefixEnd_6789028 := by exact prefixLift 6789028
  have htrace : WordTrace (prefixWord ++ tailWord_6789028) baseStart_6789028 baseEnd_6789028 := by
    simpa [prefixWord, tailWord_6789028, baseEnd_6789028] using wordTrace_append hprefix tailTrace_6789028
  have hstable : (prefixWord ++ tailWord_6789028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789028).length < 2 ^ (prefixWord ++ tailWord_6789028).sum := by decide
  have hdescent : baseEnd_6789028 < baseStart_6789028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789050 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7]
def baseStart_6789050 : Nat := 118140960795 + 6789050 * 2 ^ 59
def prefixEnd_6789050 : Nat := 4983230072969 + 3 ^ 40 * 6789050 * 2
def baseEnd_6789050 : Nat := 3486045837406768044352733

theorem tailTrace_6789050 : CollatzResearch.WordTrace tailWord_6789050 prefixEnd_6789050 3486045837406768044352733 := by
  unfold tailWord_6789050
  simp only [CollatzResearch.WordTrace]
  refine ⟨61904249013609700568599151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165077997369625868182931069 61904249013609700568599151)
  ·
    refine ⟨92856373520414550852898727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61904249013609700568599151 92856373520414550852898727)
    ·
      refine ⟨139284560280621826279348091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92856373520414550852898727 139284560280621826279348091)
      ·
        refine ⟨208926840420932739419022137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139284560280621826279348091 208926840420932739419022137)
        ·
          refine ⟨156695130315699554564266603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208926840420932739419022137 156695130315699554564266603)
          ·
            refine ⟨235042695473549331846399905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156695130315699554564266603 235042695473549331846399905)
            ·
              refine ⟨176282021605161998884799929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235042695473549331846399905 176282021605161998884799929)
              ·
                refine ⟨132211516203871499163599947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176282021605161998884799929 132211516203871499163599947)
                ·
                  refine ⟨198317274305807248745399921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132211516203871499163599947 198317274305807248745399921)
                  ·
                    refine ⟨148737955729355436559049941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 198317274305807248745399921 148737955729355436559049941)
                    ·
                      refine ⟨3486045837406768044352733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148737955729355436559049941 3486045837406768044352733)
                      ·
                        rfl

theorem cell23_6789050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_6789050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789050 prefixEnd_6789050 := by exact prefixLift 6789050
  have htrace : WordTrace (prefixWord ++ tailWord_6789050) baseStart_6789050 baseEnd_6789050 := by
    simpa [prefixWord, tailWord_6789050, baseEnd_6789050] using wordTrace_append hprefix tailTrace_6789050
  have hstable : (prefixWord ++ tailWord_6789050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789050).length < 2 ^ (prefixWord ++ tailWord_6789050).sum := by decide
  have hdescent : baseEnd_6789050 < baseStart_6789050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789067 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 3]
def baseStart_6789067 : Nat := 118140960795 + 6789067 * 2 ^ 59
def prefixEnd_6789067 : Nat := 4983230072969 + 3 ^ 40 * 6789067 * 2
def baseEnd_6789067 : Nat := 3486054566577894477840155

theorem tailTrace_6789067 : CollatzResearch.WordTrace tailWord_6789067 prefixEnd_6789067 3486054566577894477840155 := by
  unfold tailWord_6789067
  simp only [CollatzResearch.WordTrace]
  refine ⟨247617616095377214177765455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165078410730251476118510303 247617616095377214177765455)
  ·
    refine ⟨371426424143065821266648183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247617616095377214177765455 371426424143065821266648183)
    ·
      refine ⟨557139636214598731899972275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371426424143065821266648183 557139636214598731899972275)
      ·
        refine ⟨835709454321898097849958413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557139636214598731899972275 835709454321898097849958413)
        ·
          refine ⟨313391045370711786693734405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 835709454321898097849958413 313391045370711786693734405)
          ·
            refine ⟨58760821007008460005075201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313391045370711786693734405 58760821007008460005075201)
            ·
              refine ⟨44070615755256345003806401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58760821007008460005075201 44070615755256345003806401)
              ·
                refine ⟨33052961816442258752854801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44070615755256345003806401 33052961816442258752854801)
                ·
                  refine ⟨24789721362331694064641101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33052961816442258752854801 24789721362331694064641101)
                  ·
                    refine ⟨9296145510874385274240413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24789721362331694064641101 9296145510874385274240413)
                    ·
                      refine ⟨3486054566577894477840155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9296145510874385274240413 3486054566577894477840155)
                      ·
                        rfl

theorem cell23_6789067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 3].length) (baseStart_6789067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789067 prefixEnd_6789067 := by exact prefixLift 6789067
  have htrace : WordTrace (prefixWord ++ tailWord_6789067) baseStart_6789067 baseEnd_6789067 := by
    simpa [prefixWord, tailWord_6789067, baseEnd_6789067] using wordTrace_append hprefix tailTrace_6789067
  have hstable : (prefixWord ++ tailWord_6789067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789067).length < 2 ^ (prefixWord ++ tailWord_6789067).sum := by decide
  have hdescent : baseEnd_6789067 < baseStart_6789067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789068 : List Nat := [2, 2, 1, 4, 1, 3, 2, 2, 2, 2, 2]
def baseStart_6789068 : Nat := 118140960795 + 6789068 * 2 ^ 59
def prefixEnd_6789068 : Nat := 4983230072969 + 3 ^ 40 * 6789068 * 2
def baseEnd_6789068 : Nat := 3486055080058548973927651

theorem tailTrace_6789068 : CollatzResearch.WordTrace tailWord_6789068 prefixEnd_6789068 3486055080058548973927651 := by
  unfold tailWord_6789068
  simp only [CollatzResearch.WordTrace]
  refine ⟨123808826284186795674275929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165078435045582394232367905 123808826284186795674275929)
  ·
    refine ⟨92856619713140096755706947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123808826284186795674275929 92856619713140096755706947)
    ·
      refine ⟨139284929569710145133560421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92856619713140096755706947 139284929569710145133560421)
      ·
        refine ⟨26115924294320652212542579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139284929569710145133560421 26115924294320652212542579)
        ·
          refine ⟨39173886441480978318813869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26115924294320652212542579 39173886441480978318813869)
          ·
            refine ⟨14690207415555366869555201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39173886441480978318813869 14690207415555366869555201)
            ·
              refine ⟨11017655561666525152166401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14690207415555366869555201 11017655561666525152166401)
              ·
                refine ⟨8263241671249893864124801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11017655561666525152166401 8263241671249893864124801)
                ·
                  refine ⟨6197431253437420398093601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8263241671249893864124801 6197431253437420398093601)
                  ·
                    refine ⟨4648073440078065298570201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6197431253437420398093601 4648073440078065298570201)
                    ·
                      refine ⟨3486055080058548973927651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4648073440078065298570201 3486055080058548973927651)
                      ·
                        rfl

theorem cell23_6789068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_6789068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789068 prefixEnd_6789068 := by exact prefixLift 6789068
  have htrace : WordTrace (prefixWord ++ tailWord_6789068) baseStart_6789068 baseEnd_6789068 := by
    simpa [prefixWord, tailWord_6789068, baseEnd_6789068] using wordTrace_append hprefix tailTrace_6789068
  have hstable : (prefixWord ++ tailWord_6789068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789068).length < 2 ^ (prefixWord ++ tailWord_6789068).sum := by decide
  have hdescent : baseEnd_6789068 < baseStart_6789068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789168 : List Nat := [2, 1, 1, 1, 2, 7, 1, 3, 1, 4]
def baseStart_6789168 : Nat := 118140960795 + 6789168 * 2 ^ 59
def prefixEnd_6789168 : Nat := 4983230072969 + 3 ^ 40 * 6789168 * 2
def baseEnd_6789168 : Nat := 1162035476041332860892397

theorem tailTrace_6789168 : CollatzResearch.WordTrace tailWord_6789168 prefixEnd_6789168 1162035476041332860892397 := by
  unfold tailWord_6789168
  simp only [CollatzResearch.WordTrace]
  refine ⟨123810649934005654213596079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165080866578674205618128105 123810649934005654213596079)
  ·
    refine ⟨185715974901008481320394119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123810649934005654213596079 185715974901008481320394119)
    ·
      refine ⟨278573962351512721980591179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185715974901008481320394119 278573962351512721980591179)
      ·
        refine ⟨417860943527269082970886769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278573962351512721980591179 417860943527269082970886769)
        ·
          refine ⟨313395707645451812228165077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417860943527269082970886769 313395707645451812228165077)
          ·
            refine ⟨7345211897940276849097619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 313395707645451812228165077 7345211897940276849097619)
            ·
              refine ⟨11017817846910415273646429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7345211897940276849097619 11017817846910415273646429)
              ·
                refine ⟨4131681692591405727617411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11017817846910415273646429 4131681692591405727617411)
                ·
                  refine ⟨6197522538887108591426117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4131681692591405727617411 6197522538887108591426117)
                  ·
                    refine ⟨1162035476041332860892397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6197522538887108591426117 1162035476041332860892397)
                    ·
                      rfl

theorem cell23_6789168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 1, 4].length) (baseStart_6789168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789168 prefixEnd_6789168 := by exact prefixLift 6789168
  have htrace : WordTrace (prefixWord ++ tailWord_6789168) baseStart_6789168 baseEnd_6789168 := by
    simpa [prefixWord, tailWord_6789168, baseEnd_6789168] using wordTrace_append hprefix tailTrace_6789168
  have hstable : (prefixWord ++ tailWord_6789168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789168).length < 2 ^ (prefixWord ++ tailWord_6789168).sum := by decide
  have hdescent : baseEnd_6789168 < baseStart_6789168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789185 : List Nat := [1, 2, 5, 1, 2, 2, 3, 2, 1, 4]
def baseStart_6789185 : Nat := 118140960795 + 6789185 * 2 ^ 59
def prefixEnd_6789185 : Nat := 4983230072969 + 3 ^ 40 * 6789185 * 2
def baseEnd_6789185 : Nat := 1162038385765041672054871

theorem tailTrace_6789185 : CollatzResearch.WordTrace tailWord_6789185 prefixEnd_6789185 1162038385765041672054871 := by
  unfold tailWord_6789185
  simp only [CollatzResearch.WordTrace]
  refine ⟨247621919908949720330561009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165081279939299813553707339 247621919908949720330561009)
  ·
    refine ⟨185716439931712290247920757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247621919908949720330561009 185716439931712290247920757)
    ·
      refine ⟨17410916243598027210742571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185716439931712290247920757 17410916243598027210742571)
      ·
        refine ⟨26116374365397040816113857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17410916243598027210742571 26116374365397040816113857)
        ·
          refine ⟨19587280774047780612085393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26116374365397040816113857 19587280774047780612085393)
          ·
            refine ⟨14690460580535835459064045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19587280774047780612085393 14690460580535835459064045)
            ·
              refine ⟨5508922717700938297149017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14690460580535835459064045 5508922717700938297149017)
              ·
                refine ⟨4131692038275703722861763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5508922717700938297149017 4131692038275703722861763)
                ·
                  refine ⟨6197538057413555584292645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4131692038275703722861763 6197538057413555584292645)
                  ·
                    refine ⟨1162038385765041672054871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6197538057413555584292645 1162038385765041672054871)
                    ·
                      rfl

theorem cell23_6789185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_6789185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789185 prefixEnd_6789185 := by exact prefixLift 6789185
  have htrace : WordTrace (prefixWord ++ tailWord_6789185) baseStart_6789185 baseEnd_6789185 := by
    simpa [prefixWord, tailWord_6789185, baseEnd_6789185] using wordTrace_append hprefix tailTrace_6789185
  have hstable : (prefixWord ++ tailWord_6789185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789185).length < 2 ^ (prefixWord ++ tailWord_6789185).sum := by decide
  have hdescent : baseEnd_6789185 < baseStart_6789185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789237 : List Nat := [1, 3, 4, 15]
def baseStart_6789237 : Nat := 118140960795 + 6789237 * 2 ^ 59
def prefixEnd_6789237 : Nat := 4983230072969 + 3 ^ 40 * 6789237 * 2
def baseEnd_6789237 : Nat := 1594029199034823416879

theorem tailTrace_6789237 : CollatzResearch.WordTrace tailWord_6789237 prefixEnd_6789237 1594029199034823416879 := by
  unfold tailWord_6789237
  simp only [CollatzResearch.WordTrace]
  refine ⟨247623816504761333211453965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165082544336507555474302643 247623816504761333211453965)
  ·
    refine ⟨92858931189285499954295237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247623816504761333211453965 92858931189285499954295237)
    ·
      refine ⟨17411049597991031241430357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92858931189285499954295237 17411049597991031241430357)
      ·
        refine ⟨1594029199034823416879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 17411049597991031241430357 1594029199034823416879)
        ·
          rfl

theorem cell23_6789237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 15].length) (baseStart_6789237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789237 prefixEnd_6789237 := by exact prefixLift 6789237
  have htrace : WordTrace (prefixWord ++ tailWord_6789237) baseStart_6789237 baseEnd_6789237 := by
    simpa [prefixWord, tailWord_6789237, baseEnd_6789237] using wordTrace_append hprefix tailTrace_6789237
  have hstable : (prefixWord ++ tailWord_6789237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789237).length < 2 ^ (prefixWord ++ tailWord_6789237).sum := by decide
  have hdescent : baseEnd_6789237 < baseStart_6789237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789241 : List Nat := [1, 2, 1, 3, 4, 1, 1, 4, 2, 4]
def baseStart_6789241 : Nat := 118140960795 + 6789241 * 2 ^ 59
def prefixEnd_6789241 : Nat := 4983230072969 + 3 ^ 40 * 6789241 * 2
def baseEnd_6789241 : Nat := 1162047970737258932354785

theorem tailTrace_6789241 : CollatzResearch.WordTrace tailWord_6789241 prefixEnd_6789241 1162047970737258932354785 := by
  unfold tailWord_6789241
  simp only [CollatzResearch.WordTrace]
  refine ⟨247623962396746841894599577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165082641597831227929733051 247623962396746841894599577)
  ·
    refine ⟨185717971797560131420949683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247623962396746841894599577 185717971797560131420949683)
    ·
      refine ⟨278576957696340197131424525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185717971797560131420949683 278576957696340197131424525)
      ·
        refine ⟨104466359136127573924284197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278576957696340197131424525 104466359136127573924284197)
        ·
          refine ⟨19587442338023920110803287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104466359136127573924284197 19587442338023920110803287)
          ·
            refine ⟨29381163507035880166204931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19587442338023920110803287 29381163507035880166204931)
            ·
              refine ⟨44071745260553820249307397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29381163507035880166204931 44071745260553820249307397)
              ·
                refine ⟨8263452236353841296745137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44071745260553820249307397 8263452236353841296745137)
                ·
                  refine ⟨6197589177265380972558853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8263452236353841296745137 6197589177265380972558853)
                  ·
                    refine ⟨1162047970737258932354785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6197589177265380972558853 1162047970737258932354785)
                    ·
                      rfl

theorem cell23_6789241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 4].length) (baseStart_6789241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789241 prefixEnd_6789241 := by exact prefixLift 6789241
  have htrace : WordTrace (prefixWord ++ tailWord_6789241) baseStart_6789241 baseEnd_6789241 := by
    simpa [prefixWord, tailWord_6789241, baseEnd_6789241] using wordTrace_append hprefix tailTrace_6789241
  have hstable : (prefixWord ++ tailWord_6789241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789241).length < 2 ^ (prefixWord ++ tailWord_6789241).sum := by decide
  have hdescent : baseEnd_6789241 < baseStart_6789241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789267 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 4, 7]
def baseStart_6789267 : Nat := 118140960795 + 6789267 * 2 ^ 59
def prefixEnd_6789267 : Nat := 4983230072969 + 3 ^ 40 * 6789267 * 2
def baseEnd_6789267 : Nat := 1162052420902931231779745

theorem tailTrace_6789267 : CollatzResearch.WordTrace tailWord_6789267 prefixEnd_6789267 1162052420902931231779745 := by
  unfold tailWord_6789267
  simp only [CollatzResearch.WordTrace]
  refine ⟨247624910694652648335046055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165083273796435098890030703 247624910694652648335046055)
  ·
    refine ⟨371437366041978972502569083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247624910694652648335046055 371437366041978972502569083)
    ·
      refine ⟨557156049062968458753853625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371437366041978972502569083 557156049062968458753853625)
      ·
        refine ⟨417867036797226344065390219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557156049062968458753853625 417867036797226344065390219)
        ·
          refine ⟨626800555195839516098085329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417867036797226344065390219 626800555195839516098085329)
          ·
            refine ⟨470100416396879637073563997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626800555195839516098085329 470100416396879637073563997)
            ·
              refine ⟨176287656148829863902586499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 470100416396879637073563997 176287656148829863902586499)
              ·
                refine ⟨264431484223244795853879749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176287656148829863902586499 264431484223244795853879749)
                ·
                  refine ⟨49580903291858399222602453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264431484223244795853879749 49580903291858399222602453)
                  ·
                    refine ⟨1162052420902931231779745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49580903291858399222602453 1162052420902931231779745)
                    ·
                      rfl

theorem cell23_6789267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 7].length) (baseStart_6789267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789267 prefixEnd_6789267 := by exact prefixLift 6789267
  have htrace : WordTrace (prefixWord ++ tailWord_6789267) baseStart_6789267 baseEnd_6789267 := by
    simpa [prefixWord, tailWord_6789267, baseEnd_6789267] using wordTrace_append hprefix tailTrace_6789267
  have hstable : (prefixWord ++ tailWord_6789267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789267).length < 2 ^ (prefixWord ++ tailWord_6789267).sum := by decide
  have hdescent : baseEnd_6789267 < baseStart_6789267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789271 : List Nat := [1, 1, 3, 3, 4, 1, 3, 7]
def baseStart_6789271 : Nat := 118140960795 + 6789271 * 2 ^ 59
def prefixEnd_6789271 : Nat := 4983230072969 + 3 ^ 40 * 6789271 * 2
def baseEnd_6789271 : Nat := 129117011727089321469971

theorem tailTrace_6789271 : CollatzResearch.WordTrace tailWord_6789271 prefixEnd_6789271 129117011727089321469971 := by
  unfold tailWord_6789271
  simp only [CollatzResearch.WordTrace]
  refine ⟨247625056586638157018191667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165083371057758771345461111 247625056586638157018191667)
  ·
    refine ⟨371437584879957235527287501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247625056586638157018191667 371437584879957235527287501)
    ·
      refine ⟨139289094329983963322732813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371437584879957235527287501 139289094329983963322732813)
      ·
        refine ⟨52233410373743986246024805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139289094329983963322732813 52233410373743986246024805)
        ·
          refine ⟨9793764445076997421129651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52233410373743986246024805 9793764445076997421129651)
          ·
            refine ⟨14690646667615496131694477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9793764445076997421129651 14690646667615496131694477)
            ·
              refine ⟨5508992500355811049385429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14690646667615496131694477 5508992500355811049385429)
              ·
                refine ⟨129117011727089321469971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5508992500355811049385429 129117011727089321469971)
                ·
                  rfl

theorem cell23_6789271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 7].length) (baseStart_6789271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789271 prefixEnd_6789271 := by exact prefixLift 6789271
  have htrace : WordTrace (prefixWord ++ tailWord_6789271) baseStart_6789271 baseEnd_6789271 := by
    simpa [prefixWord, tailWord_6789271, baseEnd_6789271] using wordTrace_append hprefix tailTrace_6789271
  have hstable : (prefixWord ++ tailWord_6789271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789271).length < 2 ^ (prefixWord ++ tailWord_6789271).sum := by decide
  have hdescent : baseEnd_6789271 < baseStart_6789271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789281 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 1, 3, 3]
def baseStart_6789281 : Nat := 118140960795 + 6789281 * 2 ^ 59
def prefixEnd_6789281 : Nat := 4983230072969 + 3 ^ 40 * 6789281 * 2
def baseEnd_6789281 : Nat := 3486164451437956640564171

theorem tailTrace_6789281 : CollatzResearch.WordTrace tailWord_6789281 prefixEnd_6789281 3486164451437956640564171 := by
  unfold tailWord_6789281
  simp only [CollatzResearch.WordTrace]
  refine ⟨247625421316601928726055697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165083614211067952484037131 247625421316601928726055697)
  ·
    refine ⟨185719065987451446544541773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247625421316601928726055697 185719065987451446544541773)
    ·
      refine ⟨69644649745294292454203165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185719065987451446544541773 69644649745294292454203165)
      ·
        refine ⟨26116743654485359670326187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69644649745294292454203165 26116743654485359670326187)
        ·
          refine ⟨39175115481728039505489281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26116743654485359670326187 39175115481728039505489281)
          ·
            refine ⟨29381336611296029629116961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39175115481728039505489281 29381336611296029629116961)
            ·
              refine ⟨22036002458472022221837721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29381336611296029629116961 22036002458472022221837721)
              ·
                refine ⟨16527001843854016666378291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22036002458472022221837721 16527001843854016666378291)
                ·
                  refine ⟨24790502765781024999567437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16527001843854016666378291 24790502765781024999567437)
                  ·
                    refine ⟨9296438537167884374837789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24790502765781024999567437 9296438537167884374837789)
                    ·
                      refine ⟨3486164451437956640564171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9296438537167884374837789 3486164451437956640564171)
                      ·
                        rfl

theorem cell23_6789281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_6789281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789281 prefixEnd_6789281 := by exact prefixLift 6789281
  have htrace : WordTrace (prefixWord ++ tailWord_6789281) baseStart_6789281 baseEnd_6789281 := by
    simpa [prefixWord, tailWord_6789281, baseEnd_6789281] using wordTrace_append hprefix tailTrace_6789281
  have hstable : (prefixWord ++ tailWord_6789281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789281).length < 2 ^ (prefixWord ++ tailWord_6789281).sum := by decide
  have hdescent : baseEnd_6789281 < baseStart_6789281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789282 : List Nat := [3, 3, 1, 3, 1, 1, 1, 5, 1, 2, 2]
def baseStart_6789282 : Nat := 118140960795 + 6789282 * 2 ^ 59
def prefixEnd_6789282 : Nat := 4983230072969 + 3 ^ 40 * 6789282 * 2
def baseEnd_6789282 : Nat := 3486164964918611136651667

theorem tailTrace_6789282 : CollatzResearch.WordTrace tailWord_6789282 prefixEnd_6789282 3486164964918611136651667 := by
  unfold tailWord_6789282
  simp only [CollatzResearch.WordTrace]
  refine ⟨61906364447399576474210525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165083638526398870597894733 61906364447399576474210525)
  ·
    refine ⟨23214886667774841177828947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61906364447399576474210525 23214886667774841177828947)
    ·
      refine ⟨34822330001662261766743421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23214886667774841177828947 34822330001662261766743421)
      ·
        refine ⟨13058373750623348162528783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34822330001662261766743421 13058373750623348162528783)
        ·
          refine ⟨19587560625935022243793175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13058373750623348162528783 19587560625935022243793175)
          ·
            refine ⟨29381340938902533365689763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19587560625935022243793175 29381340938902533365689763)
            ·
              refine ⟨44072011408353800048534645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29381340938902533365689763 44072011408353800048534645)
              ·
                refine ⟨4131751069533168754550123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44072011408353800048534645 4131751069533168754550123)
                ·
                  refine ⟨6197626604299753131825185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4131751069533168754550123 6197626604299753131825185)
                  ·
                    refine ⟨4648219953224814848868889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6197626604299753131825185 4648219953224814848868889)
                    ·
                      refine ⟨3486164964918611136651667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4648219953224814848868889 3486164964918611136651667)
                      ·
                        rfl

theorem cell23_6789282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_6789282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789282 prefixEnd_6789282 := by exact prefixLift 6789282
  have htrace : WordTrace (prefixWord ++ tailWord_6789282) baseStart_6789282 baseEnd_6789282 := by
    simpa [prefixWord, tailWord_6789282, baseEnd_6789282] using wordTrace_append hprefix tailTrace_6789282
  have hstable : (prefixWord ++ tailWord_6789282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789282).length < 2 ^ (prefixWord ++ tailWord_6789282).sum := by decide
  have hdescent : baseEnd_6789282 < baseStart_6789282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789321 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 1, 4, 2]
def baseStart_6789321 : Nat := 118140960795 + 6789321 * 2 ^ 59
def prefixEnd_6789321 : Nat := 4983230072969 + 3 ^ 40 * 6789321 * 2
def baseEnd_6789321 : Nat := 3486184990664136484063987

theorem tailTrace_6789321 : CollatzResearch.WordTrace tailWord_6789321 prefixEnd_6789321 3486184990664136484063987 := by
  unfold tailWord_6789321
  simp only [CollatzResearch.WordTrace]
  refine ⟨247626880236457015557511817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165084586824304677038341211 247626880236457015557511817)
  ·
    refine ⟨185720160177342761668133863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247626880236457015557511817 185720160177342761668133863)
    ·
      refine ⟨278580240266014142502200795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185720160177342761668133863 278580240266014142502200795)
      ·
        refine ⟨417870360399021213753301193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278580240266014142502200795 417870360399021213753301193)
        ·
          refine ⟨313402770299265910314975895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417870360399021213753301193 313402770299265910314975895)
          ·
            refine ⟨470104155448898865472463843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313402770299265910314975895 470104155448898865472463843)
            ·
              refine ⟨705156233173348298208695765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470104155448898865472463843 705156233173348298208695765)
              ·
                refine ⟨16527099215000350739266307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 705156233173348298208695765 16527099215000350739266307)
                ·
                  refine ⟨24790648822500526108899461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16527099215000350739266307 24790648822500526108899461)
                  ·
                    refine ⟨4648246654218848645418649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24790648822500526108899461 4648246654218848645418649)
                    ·
                      refine ⟨3486184990664136484063987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4648246654218848645418649 3486184990664136484063987)
                      ·
                        rfl

theorem cell23_6789321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 4, 2].length) (baseStart_6789321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789321 prefixEnd_6789321 := by exact prefixLift 6789321
  have htrace : WordTrace (prefixWord ++ tailWord_6789321) baseStart_6789321 baseEnd_6789321 := by
    simpa [prefixWord, tailWord_6789321, baseEnd_6789321] using wordTrace_append hprefix tailTrace_6789321
  have hstable : (prefixWord ++ tailWord_6789321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789321).length < 2 ^ (prefixWord ++ tailWord_6789321).sum := by decide
  have hdescent : baseEnd_6789321 < baseStart_6789321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789338 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2]
def baseStart_6789338 : Nat := 118140960795 + 6789338 * 2 ^ 59
def prefixEnd_6789338 : Nat := 4983230072969 + 3 ^ 40 * 6789338 * 2
def baseEnd_6789338 : Nat := 3486193719835262917551409

theorem tailTrace_6789338 : CollatzResearch.WordTrace tailWord_6789338 prefixEnd_6789338 3486193719835262917551409 := by
  unfold tailWord_6789338
  simp only [CollatzResearch.WordTrace]
  refine ⟨61906875069348856865220167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165085000184930284973920445 61906875069348856865220167)
  ·
    refine ⟨92860312604023285297830251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61906875069348856865220167 92860312604023285297830251)
    ·
      refine ⟨139290468906034927946745377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92860312604023285297830251 139290468906034927946745377)
      ·
        refine ⟨104467851679526195960059033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139290468906034927946745377 104467851679526195960059033)
        ·
          refine ⟨78350888759644646970044275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104467851679526195960059033 78350888759644646970044275)
          ·
            refine ⟨117526333139466970455066413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78350888759644646970044275 117526333139466970455066413)
            ·
              refine ⟨44072374927300113920649905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117526333139466970455066413 44072374927300113920649905)
              ·
                refine ⟨33054281195475085440487429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44072374927300113920649905 33054281195475085440487429)
                ·
                  refine ⟨6197677724151578520091393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33054281195475085440487429 6197677724151578520091393)
                  ·
                    refine ⟨4648258293113683890068545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6197677724151578520091393 4648258293113683890068545)
                    ·
                      refine ⟨3486193719835262917551409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4648258293113683890068545 3486193719835262917551409)
                      ·
                        rfl

theorem cell23_6789338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_6789338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789338 prefixEnd_6789338 := by exact prefixLift 6789338
  have htrace : WordTrace (prefixWord ++ tailWord_6789338) baseStart_6789338 baseEnd_6789338 := by
    simpa [prefixWord, tailWord_6789338, baseEnd_6789338] using wordTrace_append hprefix tailTrace_6789338
  have hstable : (prefixWord ++ tailWord_6789338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789338).length < 2 ^ (prefixWord ++ tailWord_6789338).sum := by decide
  have hdescent : baseEnd_6789338 < baseStart_6789338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789341 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_6789341 : Nat := 118140960795 + 6789341 * 2 ^ 59
def prefixEnd_6789341 : Nat := 4983230072969 + 3 ^ 40 * 6789341 * 2
def baseEnd_6789341 : Nat := 3486195260277226405813895

theorem tailTrace_6789341 : CollatzResearch.WordTrace tailWord_6789341 prefixEnd_6789341 3486195260277226405813895 := by
  unfold tailWord_6789341
  simp only [CollatzResearch.WordTrace]
  refine ⟨247627609696384558973239877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165085073130923039315493251 247627609696384558973239877)
  ·
    refine ⟨46430176818072104807482477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247627609696384558973239877 46430176818072104807482477)
    ·
      refine ⟨17411316306777039302805929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46430176818072104807482477 17411316306777039302805929)
      ·
        refine ⟨13058487230082779477104447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17411316306777039302805929 13058487230082779477104447)
        ·
          refine ⟨19587730845124169215656671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13058487230082779477104447 19587730845124169215656671)
          ·
            refine ⟨29381596267686253823485007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19587730845124169215656671 29381596267686253823485007)
            ·
              refine ⟨44072394401529380735227511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29381596267686253823485007 44072394401529380735227511)
              ·
                refine ⟨66108591602294071102841267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44072394401529380735227511 66108591602294071102841267)
                ·
                  refine ⟨99162887403441106654261901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66108591602294071102841267 99162887403441106654261901)
                  ·
                    refine ⟨37186082776290414995348213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99162887403441106654261901 37186082776290414995348213)
                    ·
                      refine ⟨3486195260277226405813895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37186082776290414995348213 3486195260277226405813895)
                      ·
                        rfl

theorem cell23_6789341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_6789341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789341 prefixEnd_6789341 := by exact prefixLift 6789341
  have htrace : WordTrace (prefixWord ++ tailWord_6789341) baseStart_6789341 baseEnd_6789341 := by
    simpa [prefixWord, tailWord_6789341, baseEnd_6789341] using wordTrace_append hprefix tailTrace_6789341
  have hstable : (prefixWord ++ tailWord_6789341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789341).length < 2 ^ (prefixWord ++ tailWord_6789341).sum := by decide
  have hdescent : baseEnd_6789341 < baseStart_6789341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789354 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_6789354 : Nat := 118140960795 + 6789354 * 2 ^ 59
def prefixEnd_6789354 : Nat := 4983230072969 + 3 ^ 40 * 6789354 * 2
def baseEnd_6789354 : Nat := 3486201935525734854951335

theorem tailTrace_6789354 : CollatzResearch.WordTrace tailWord_6789354 prefixEnd_6789354 3486201935525734854951335 := by
  unfold tailWord_6789354
  simp only [CollatzResearch.WordTrace]
  refine ⟨61907020961334365548365779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165085389230224974795642077 61907020961334365548365779)
  ·
    refine ⟨92860531442001548322548669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61907020961334365548365779 92860531442001548322548669)
    ·
      refine ⟨34822699290750580620955751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92860531442001548322548669 34822699290750580620955751)
      ·
        refine ⟨52234048936125870931433627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34822699290750580620955751 52234048936125870931433627)
        ·
          refine ⟨78351073404188806397150441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52234048936125870931433627 78351073404188806397150441)
          ·
            refine ⟨58763305053141604797862831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78351073404188806397150441 58763305053141604797862831)
            ·
              refine ⟨88144957579712407196794247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58763305053141604797862831 88144957579712407196794247)
              ·
                refine ⟨132217436369568610795191371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88144957579712407196794247 132217436369568610795191371)
                ·
                  refine ⟨198326154554352916192787057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132217436369568610795191371 198326154554352916192787057)
                  ·
                    refine ⟨148744615915764687144590293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 198326154554352916192787057 148744615915764687144590293)
                    ·
                      refine ⟨3486201935525734854951335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148744615915764687144590293 3486201935525734854951335)
                      ·
                        rfl

theorem cell23_6789354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_6789354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789354 prefixEnd_6789354 := by exact prefixLift 6789354
  have htrace : WordTrace (prefixWord ++ tailWord_6789354) baseStart_6789354 baseEnd_6789354 := by
    simpa [prefixWord, tailWord_6789354, baseEnd_6789354] using wordTrace_append hprefix tailTrace_6789354
  have hstable : (prefixWord ++ tailWord_6789354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789354).length < 2 ^ (prefixWord ++ tailWord_6789354).sum := by decide
  have hdescent : baseEnd_6789354 < baseStart_6789354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789361 : List Nat := [1, 2, 2, 2, 2, 1, 2, 6, 5]
def baseStart_6789361 : Nat := 118140960795 + 6789361 * 2 ^ 59
def prefixEnd_6789361 : Nat := 4983230072969 + 3 ^ 40 * 6789361 * 2
def baseEnd_6789361 : Nat := 387356169987812925284867

theorem tailTrace_6789361 : CollatzResearch.WordTrace tailWord_6789361 prefixEnd_6789361 387356169987812925284867 := by
  unfold tailWord_6789361
  simp only [CollatzResearch.WordTrace]
  refine ⟨247628339156312102388967937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165085559437541401592645291 247628339156312102388967937)
  ·
    refine ⟨185721254367234076791725953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247628339156312102388967937 185721254367234076791725953)
    ·
      refine ⟨139290940775425557593794465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185721254367234076791725953 139290940775425557593794465)
      ·
        refine ⟨104468205581569168195345849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139290940775425557593794465 104468205581569168195345849)
        ·
          refine ⟨78351154186176876146509387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104468205581569168195345849 78351154186176876146509387)
          ·
            refine ⟨117526731279265314219764081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78351154186176876146509387 117526731279265314219764081)
            ·
              refine ⟨88145048459448985664823061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117526731279265314219764081 88145048459448985664823061)
              ·
                refine ⟨4131799146536671203038581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88145048459448985664823061 4131799146536671203038581)
                ·
                  refine ⟨387356169987812925284867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4131799146536671203038581 387356169987812925284867)
                  ·
                    rfl

theorem cell23_6789361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 5].length) (baseStart_6789361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789361 prefixEnd_6789361 := by exact prefixLift 6789361
  have htrace : WordTrace (prefixWord ++ tailWord_6789361) baseStart_6789361 baseEnd_6789361 := by
    simpa [prefixWord, tailWord_6789361, baseEnd_6789361] using wordTrace_append hprefix tailTrace_6789361
  have hstable : (prefixWord ++ tailWord_6789361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789361).length < 2 ^ (prefixWord ++ tailWord_6789361).sum := by decide
  have hdescent : baseEnd_6789361 < baseStart_6789361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789372 : List Nat := [2, 2, 2, 1, 4, 1, 4, 1, 2, 2, 2]
def baseStart_6789372 : Nat := 118140960795 + 6789372 * 2 ^ 59
def prefixEnd_6789372 : Nat := 4983230072969 + 3 ^ 40 * 6789372 * 2
def baseEnd_6789372 : Nat := 3486211178177515784526253

theorem tailTrace_6789372 : CollatzResearch.WordTrace tailWord_6789372 prefixEnd_6789372 3486211178177515784526253 := by
  unfold tailWord_6789372
  simp only [CollatzResearch.WordTrace]
  refine ⟨123814370179636125633809185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165085826906181500845078913 123814370179636125633809185)
  ·
    refine ⟨92860777634727094225356889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123814370179636125633809185 92860777634727094225356889)
    ·
      refine ⟨69645583226045320669017667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92860777634727094225356889 69645583226045320669017667)
      ·
        refine ⟨104468374839067981003526501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69645583226045320669017667 104468374839067981003526501)
        ·
          refine ⟨19587820282325246438161219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104468374839067981003526501 19587820282325246438161219)
          ·
            refine ⟨29381730423487869657241829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19587820282325246438161219 29381730423487869657241829)
            ·
              refine ⟨5509074454403975560732843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29381730423487869657241829 5509074454403975560732843)
              ·
                refine ⟨8263611681605963341099265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5509074454403975560732843 8263611681605963341099265)
                ·
                  refine ⟨6197708761204472505824449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8263611681605963341099265 6197708761204472505824449)
                  ·
                    refine ⟨4648281570903354379368337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6197708761204472505824449 4648281570903354379368337)
                    ·
                      refine ⟨3486211178177515784526253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4648281570903354379368337 3486211178177515784526253)
                      ·
                        rfl

theorem cell23_6789372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_6789372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789372 prefixEnd_6789372 := by exact prefixLift 6789372
  have htrace : WordTrace (prefixWord ++ tailWord_6789372) baseStart_6789372 baseEnd_6789372 := by
    simpa [prefixWord, tailWord_6789372, baseEnd_6789372] using wordTrace_append hprefix tailTrace_6789372
  have hstable : (prefixWord ++ tailWord_6789372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789372).length < 2 ^ (prefixWord ++ tailWord_6789372).sum := by decide
  have hdescent : baseEnd_6789372 < baseStart_6789372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789381 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 4, 5, 2]
def baseStart_6789381 : Nat := 118140960795 + 6789381 * 2 ^ 59
def prefixEnd_6789381 : Nat := 4983230072969 + 3 ^ 40 * 6789381 * 2
def baseEnd_6789381 : Nat := 3486215799503406249313711

theorem tailTrace_6789381 : CollatzResearch.WordTrace tailWord_6789381 prefixEnd_6789381 3486215799503406249313711 := by
  unfold tailWord_6789381
  simp only [CollatzResearch.WordTrace]
  refine ⟨247629068616239645804695997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165086045744159763869797331 247629068616239645804695997)
  ·
    refine ⟨92860900731089867176760999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247629068616239645804695997 92860900731089867176760999)
    ·
      refine ⟨139291351096634800765141499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92860900731089867176760999 139291351096634800765141499)
      ·
        refine ⟨208937026644952201147712249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139291351096634800765141499 208937026644952201147712249)
        ·
          refine ⟨156702769983714150860784187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208937026644952201147712249 156702769983714150860784187)
          ·
            refine ⟨235054154975571226291176281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156702769983714150860784187 235054154975571226291176281)
            ·
              refine ⟨176290616231678419718382211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235054154975571226291176281 176290616231678419718382211)
              ·
                refine ⟨264435924347517629577573317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176290616231678419718382211 264435924347517629577573317)
                ·
                  refine ⟨49581735815159555545794997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264435924347517629577573317 49581735815159555545794997)
                  ·
                    refine ⟨4648287732671208332418281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49581735815159555545794997 4648287732671208332418281)
                    ·
                      refine ⟨3486215799503406249313711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4648287732671208332418281 3486215799503406249313711)
                      ·
                        rfl

theorem cell23_6789381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 5, 2].length) (baseStart_6789381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789381 prefixEnd_6789381 := by exact prefixLift 6789381
  have htrace : WordTrace (prefixWord ++ tailWord_6789381) baseStart_6789381 baseEnd_6789381 := by
    simpa [prefixWord, tailWord_6789381, baseEnd_6789381] using wordTrace_append hprefix tailTrace_6789381
  have hstable : (prefixWord ++ tailWord_6789381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789381).length < 2 ^ (prefixWord ++ tailWord_6789381).sum := by decide
  have hdescent : baseEnd_6789381 < baseStart_6789381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789411 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 4]
def baseStart_6789411 : Nat := 118140960795 + 6789411 * 2 ^ 59
def prefixEnd_6789411 : Nat := 4983230072969 + 3 ^ 40 * 6789411 * 2
def baseEnd_6789411 : Nat := 3486231203923041131938573

theorem tailTrace_6789411 : CollatzResearch.WordTrace tailWord_6789411 prefixEnd_6789411 3486231203923041131938573 := by
  unfold tailWord_6789411
  simp only [CollatzResearch.WordTrace]
  refine ⟨247630162806130960928288087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165086775204087307285525391 247630162806130960928288087)
  ·
    refine ⟨371445244209196441392432131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247630162806130960928288087 371445244209196441392432131)
    ·
      refine ⟨557167866313794662088648197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371445244209196441392432131 557167866313794662088648197)
      ·
        refine ⟨104468974933836499141621537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 557167866313794662088648197 104468974933836499141621537)
        ·
          refine ⟨78351731200377374356216153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104468974933836499141621537 78351731200377374356216153)
          ·
            refine ⟨58763798400283030767162115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78351731200377374356216153 58763798400283030767162115)
            ·
              refine ⟨88145697600424546150743173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58763798400283030767162115 88145697600424546150743173)
              ·
                refine ⟨16527318300079602403264345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88145697600424546150743173 16527318300079602403264345)
                ·
                  refine ⟨12395488725059701802448259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16527318300079602403264345 12395488725059701802448259)
                  ·
                    refine ⟨18593233087589552703672389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12395488725059701802448259 18593233087589552703672389)
                    ·
                      refine ⟨3486231203923041131938573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18593233087589552703672389 3486231203923041131938573)
                      ·
                        rfl

theorem cell23_6789411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_6789411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789411 prefixEnd_6789411 := by exact prefixLift 6789411
  have htrace : WordTrace (prefixWord ++ tailWord_6789411) baseStart_6789411 baseEnd_6789411 := by
    simpa [prefixWord, tailWord_6789411, baseEnd_6789411] using wordTrace_append hprefix tailTrace_6789411
  have hstable : (prefixWord ++ tailWord_6789411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789411).length < 2 ^ (prefixWord ++ tailWord_6789411).sum := by decide
  have hdescent : baseEnd_6789411 < baseStart_6789411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789424 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 6]
def baseStart_6789424 : Nat := 118140960795 + 6789424 * 2 ^ 59
def prefixEnd_6789424 : Nat := 4983230072969 + 3 ^ 40 * 6789424 * 2
def baseEnd_6789424 : Nat := 3486237879171549581076013

theorem tailTrace_6789424 : CollatzResearch.WordTrace tailWord_6789424 prefixEnd_6789424 3486237879171549581076013 := by
  unfold tailWord_6789424
  simp only [CollatzResearch.WordTrace]
  refine ⟨123815318477541932074255663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165087091303389242765674217 123815318477541932074255663)
  ·
    refine ⟨185722977716312898111383495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123815318477541932074255663 185722977716312898111383495)
    ·
      refine ⟨278584466574469347167075243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185722977716312898111383495 278584466574469347167075243)
      ·
        refine ⟨417876699861704020750612865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278584466574469347167075243 417876699861704020750612865)
        ·
          refine ⟨313407524896278015562959649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417876699861704020750612865 313407524896278015562959649)
          ·
            refine ⟨235055643672208511672219737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313407524896278015562959649 235055643672208511672219737)
            ·
              refine ⟨176291732754156383754164803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235055643672208511672219737 176291732754156383754164803)
              ·
                refine ⟨264437599131234575631247205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176291732754156383754164803 264437599131234575631247205)
                ·
                  refine ⟨49582049837106482930858851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264437599131234575631247205 49582049837106482930858851)
                  ·
                    refine ⟨74373074755659724396288277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49582049837106482930858851 74373074755659724396288277)
                    ·
                      refine ⟨3486237879171549581076013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74373074755659724396288277 3486237879171549581076013)
                      ·
                        rfl

theorem cell23_6789424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_6789424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789424 prefixEnd_6789424 := by exact prefixLift 6789424
  have htrace : WordTrace (prefixWord ++ tailWord_6789424) baseStart_6789424 baseEnd_6789424 := by
    simpa [prefixWord, tailWord_6789424, baseEnd_6789424] using wordTrace_append hprefix tailTrace_6789424
  have hstable : (prefixWord ++ tailWord_6789424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789424).length < 2 ^ (prefixWord ++ tailWord_6789424).sum := by decide
  have hdescent : baseEnd_6789424 < baseStart_6789424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789431 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 3]
def baseStart_6789431 : Nat := 118140960795 + 6789431 * 2 ^ 59
def prefixEnd_6789431 : Nat := 4983230072969 + 3 ^ 40 * 6789431 * 2
def baseEnd_6789431 : Nat := 3486241473536131053688481

theorem tailTrace_6789431 : CollatzResearch.WordTrace tailWord_6789431 prefixEnd_6789431 3486241473536131053688481 := by
  unfold tailWord_6789431
  simp only [CollatzResearch.WordTrace]
  refine ⟨247630892266058504344016147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165087261510705669562677431 247630892266058504344016147)
  ·
    refine ⟨371446338399087756516024221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247630892266058504344016147 371446338399087756516024221)
    ·
      refine ⟨139292376899657908693509083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371446338399087756516024221 139292376899657908693509083)
      ·
        refine ⟨208938565349486863040263625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139292376899657908693509083 208938565349486863040263625)
        ·
          refine ⟨156703924012115147280197719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208938565349486863040263625 156703924012115147280197719)
          ·
            refine ⟨235055886018172720920296579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156703924012115147280197719 235055886018172720920296579)
            ·
              refine ⟨352583829027259081380444869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235055886018172720920296579 352583829027259081380444869)
              ·
                refine ⟨66109467942611077758833413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352583829027259081380444869 66109467942611077758833413)
                ·
                  refine ⟨12395525239239577079781265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66109467942611077758833413 12395525239239577079781265)
                  ·
                    refine ⟨9296643929429682809835949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12395525239239577079781265 9296643929429682809835949)
                    ·
                      refine ⟨3486241473536131053688481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9296643929429682809835949 3486241473536131053688481)
                      ·
                        rfl

theorem cell23_6789431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_6789431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789431 prefixEnd_6789431 := by exact prefixLift 6789431
  have htrace : WordTrace (prefixWord ++ tailWord_6789431) baseStart_6789431 baseEnd_6789431 := by
    simpa [prefixWord, tailWord_6789431, baseEnd_6789431] using wordTrace_append hprefix tailTrace_6789431
  have hstable : (prefixWord ++ tailWord_6789431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789431).length < 2 ^ (prefixWord ++ tailWord_6789431).sum := by decide
  have hdescent : baseEnd_6789431 < baseStart_6789431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789438 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_6789438 : Nat := 118140960795 + 6789438 * 2 ^ 59
def prefixEnd_6789438 : Nat := 4983230072969 + 3 ^ 40 * 6789438 * 2
def baseEnd_6789438 : Nat := 1162081689300237508766983

theorem tailTrace_6789438 : CollatzResearch.WordTrace tailWord_6789438 prefixEnd_6789438 1162081689300237508766983 := by
  unfold tailWord_6789438
  simp only [CollatzResearch.WordTrace]
  refine ⟨30953893447129143067440121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165087431718022096359680645 30953893447129143067440121)
  ·
    refine ⟨23215420085346857300580091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30953893447129143067440121 23215420085346857300580091)
    ·
      refine ⟨34823130128020285950870137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23215420085346857300580091 34823130128020285950870137)
      ·
        refine ⟨26117347596015214463152603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34823130128020285950870137 26117347596015214463152603)
        ·
          refine ⟨39176021394022821694728905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26117347596015214463152603 39176021394022821694728905)
          ·
            refine ⟨29382016045517116271046679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39176021394022821694728905 29382016045517116271046679)
            ·
              refine ⟨44073024068275674406570019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29382016045517116271046679 44073024068275674406570019)
              ·
                refine ⟨66109536102413511609855029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44073024068275674406570019 66109536102413511609855029)
                ·
                  refine ⟨6197769009601266713423909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66109536102413511609855029 6197769009601266713423909)
                  ·
                    refine ⟨1162081689300237508766983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6197769009601266713423909 1162081689300237508766983)
                    ·
                      rfl

theorem cell23_6789438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_6789438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789438 prefixEnd_6789438 := by exact prefixLift 6789438
  have htrace : WordTrace (prefixWord ++ tailWord_6789438) baseStart_6789438 baseEnd_6789438 := by
    simpa [prefixWord, tailWord_6789438, baseEnd_6789438] using wordTrace_append hprefix tailTrace_6789438
  have hstable : (prefixWord ++ tailWord_6789438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789438).length < 2 ^ (prefixWord ++ tailWord_6789438).sum := by decide
  have hdescent : baseEnd_6789438 < baseStart_6789438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789448 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 2, 2, 3]
def baseStart_6789448 : Nat := 118140960795 + 6789448 * 2 ^ 59
def prefixEnd_6789448 : Nat := 4983230072969 + 3 ^ 40 * 6789448 * 2
def baseEnd_6789448 : Nat := 3486250202707257487175903

theorem tailTrace_6789448 : CollatzResearch.WordTrace tailWord_6789448 prefixEnd_6789448 3486250202707257487175903 := by
  unfold tailWord_6789448
  simp only [CollatzResearch.WordTrace]
  refine ⟨123815756153498458123692499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165087674871331277498256665 123815756153498458123692499)
  ·
    refine ⟨185723634230247687185538749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123815756153498458123692499 185723634230247687185538749)
    ·
      refine ⟨69646362836342882694577031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185723634230247687185538749 69646362836342882694577031)
      ·
        refine ⟨104469544254514324041865547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69646362836342882694577031 104469544254514324041865547)
        ·
          refine ⟨156704316381771486062798321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104469544254514324041865547 156704316381771486062798321)
          ·
            refine ⟨117528237286328614547098741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156704316381771486062798321 117528237286328614547098741)
            ·
              refine ⟨11018272245593307613790507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117528237286328614547098741 11018272245593307613790507)
              ·
                refine ⟨16527408368389961420685761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11018272245593307613790507 16527408368389961420685761)
                ·
                  refine ⟨12395556276292471065514321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16527408368389961420685761 12395556276292471065514321)
                  ·
                    refine ⟨9296667207219353299135741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12395556276292471065514321 9296667207219353299135741)
                    ·
                      refine ⟨3486250202707257487175903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9296667207219353299135741 3486250202707257487175903)
                      ·
                        rfl

theorem cell23_6789448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_6789448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789448 prefixEnd_6789448 := by exact prefixLift 6789448
  have htrace : WordTrace (prefixWord ++ tailWord_6789448) baseStart_6789448 baseEnd_6789448 := by
    simpa [prefixWord, tailWord_6789448, baseEnd_6789448] using wordTrace_append hprefix tailTrace_6789448
  have hstable : (prefixWord ++ tailWord_6789448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789448).length < 2 ^ (prefixWord ++ tailWord_6789448).sum := by decide
  have hdescent : baseEnd_6789448 < baseStart_6789448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789488 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 1, 5, 2]
def baseStart_6789488 : Nat := 118140960795 + 6789488 * 2 ^ 59
def prefixEnd_6789488 : Nat := 4983230072969 + 3 ^ 40 * 6789488 * 2
def baseEnd_6789488 : Nat := 3486270741933437330675719

theorem tailTrace_6789488 : CollatzResearch.WordTrace tailWord_6789488 prefixEnd_6789488 3486270741933437330675719 := by
  unfold tailWord_6789488
  simp only [CollatzResearch.WordTrace]
  refine ⟨123816485613426001539420559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165088647484568002052560745 123816485613426001539420559)
  ·
    refine ⟨185724728420139002309130839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123816485613426001539420559 185724728420139002309130839)
    ·
      refine ⟨278587092630208503463696259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185724728420139002309130839 278587092630208503463696259)
      ·
        refine ⟨417880638945312755195544389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278587092630208503463696259 417880638945312755195544389)
        ·
          refine ⟨78352619802246141599164573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 417880638945312755195544389 78352619802246141599164573)
          ·
            refine ⟨29382232425842303099686715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78352619802246141599164573 29382232425842303099686715)
            ·
              refine ⟨44073348638763454649530073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29382232425842303099686715 44073348638763454649530073)
              ·
                refine ⟨33055011479072590987147555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44073348638763454649530073 33055011479072590987147555)
                ·
                  refine ⟨49582517218608886480721333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33055011479072590987147555 49582517218608886480721333)
                  ·
                    refine ⟨4648360989244583107567625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49582517218608886480721333 4648360989244583107567625)
                    ·
                      refine ⟨3486270741933437330675719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4648360989244583107567625 3486270741933437330675719)
                      ·
                        rfl

theorem cell23_6789488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 1, 5, 2].length) (baseStart_6789488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789488 prefixEnd_6789488 := by exact prefixLift 6789488
  have htrace : WordTrace (prefixWord ++ tailWord_6789488) baseStart_6789488 baseEnd_6789488 := by
    simpa [prefixWord, tailWord_6789488, baseEnd_6789488] using wordTrace_append hprefix tailTrace_6789488
  have hstable : (prefixWord ++ tailWord_6789488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789488).length < 2 ^ (prefixWord ++ tailWord_6789488).sum := by decide
  have hdescent : baseEnd_6789488 < baseStart_6789488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789505 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 1, 5, 2]
def baseStart_6789505 : Nat := 118140960795 + 6789505 * 2 ^ 59
def prefixEnd_6789505 : Nat := 4983230072969 + 3 ^ 40 * 6789505 * 2
def baseEnd_6789505 : Nat := 3486279471104563764163141

theorem tailTrace_6789505 : CollatzResearch.WordTrace tailWord_6789505 prefixEnd_6789505 3486279471104563764163141 := by
  unfold tailWord_6789505
  simp only [CollatzResearch.WordTrace]
  refine ⟨247633591267790414982209969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165089060845193609988139979 247633591267790414982209969)
  ·
    refine ⟨185725193450842811236657477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247633591267790414982209969 185725193450842811236657477)
    ·
      refine ⟨34823473772033027106873277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185725193450842811236657477 34823473772033027106873277)
      ·
        refine ⟨13058802664512385165077479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34823473772033027106873277 13058802664512385165077479)
        ·
          refine ⟨19588203996768577747616219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13058802664512385165077479 19588203996768577747616219)
          ·
            refine ⟨29382305995152866621424329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19588203996768577747616219 29382305995152866621424329)
            ·
              refine ⟨22036729496364649966068247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29382305995152866621424329 22036729496364649966068247)
              ·
                refine ⟨33055094244546974949102371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22036729496364649966068247 33055094244546974949102371)
                ·
                  refine ⟨49582641366820462423653557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33055094244546974949102371 49582641366820462423653557)
                  ·
                    refine ⟨4648372628139418352217521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49582641366820462423653557 4648372628139418352217521)
                    ·
                      refine ⟨3486279471104563764163141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4648372628139418352217521 3486279471104563764163141)
                      ·
                        rfl

theorem cell23_6789505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_6789505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789505 prefixEnd_6789505 := by exact prefixLift 6789505
  have htrace : WordTrace (prefixWord ++ tailWord_6789505) baseStart_6789505 baseEnd_6789505 := by
    simpa [prefixWord, tailWord_6789505, baseEnd_6789505] using wordTrace_append hprefix tailTrace_6789505
  have hstable : (prefixWord ++ tailWord_6789505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789505).length < 2 ^ (prefixWord ++ tailWord_6789505).sum := by decide
  have hdescent : baseEnd_6789505 < baseStart_6789505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789506 : List Nat := [3, 4, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_6789506 : Nat := 118140960795 + 6789506 * 2 ^ 59
def prefixEnd_6789506 : Nat := 4983230072969 + 3 ^ 40 * 6789506 * 2
def baseEnd_6789506 : Nat := 1162093328195072753416879

theorem tailTrace_6789506 : CollatzResearch.WordTrace tailWord_6789506 prefixEnd_6789506 1162093328195072753416879 := by
  unfold tailWord_6789506
  simp only [CollatzResearch.WordTrace]
  refine ⟨61908406935196698038249093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165089085160524528101997581 61908406935196698038249093)
  ·
    refine ⟨11607826300349380882171705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61908406935196698038249093 11607826300349380882171705)
    ·
      refine ⟨8705869725262035661628779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11607826300349380882171705 8705869725262035661628779)
      ·
        refine ⟨13058804587893053492443169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8705869725262035661628779 13058804587893053492443169)
        ·
          refine ⟨9794103440919790119332377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13058804587893053492443169 9794103440919790119332377)
          ·
            refine ⟨7345577580689842589499283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9794103440919790119332377 7345577580689842589499283)
            ·
              refine ⟨11018366371034763884248925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7345577580689842589499283 11018366371034763884248925)
              ·
                refine ⟨4131887389138036456593347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11018366371034763884248925 4131887389138036456593347)
                ·
                  refine ⟨6197831083707054684890021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4131887389138036456593347 6197831083707054684890021)
                  ·
                    refine ⟨1162093328195072753416879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6197831083707054684890021 1162093328195072753416879)
                    ·
                      rfl

theorem cell23_6789506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_6789506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789506 prefixEnd_6789506 := by exact prefixLift 6789506
  have htrace : WordTrace (prefixWord ++ tailWord_6789506) baseStart_6789506 baseEnd_6789506 := by
    simpa [prefixWord, tailWord_6789506, baseEnd_6789506] using wordTrace_append hprefix tailTrace_6789506
  have hstable : (prefixWord ++ tailWord_6789506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789506).length < 2 ^ (prefixWord ++ tailWord_6789506).sum := by decide
  have hdescent : baseEnd_6789506 < baseStart_6789506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789511 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 3, 6]
def baseStart_6789511 : Nat := 118140960795 + 6789511 * 2 ^ 59
def prefixEnd_6789511 : Nat := 4983230072969 + 3 ^ 40 * 6789511 * 2
def baseEnd_6789511 : Nat := 1162094183996163580229371

theorem tailTrace_6789511 : CollatzResearch.WordTrace tailWord_6789511 prefixEnd_6789511 1162094183996163580229371 := by
  unfold tailWord_6789511
  simp only [CollatzResearch.WordTrace]
  refine ⟨247633810105768678006928387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165089206737179118671285591 247633810105768678006928387)
  ·
    refine ⟨371450715158653017010392581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247633810105768678006928387 371450715158653017010392581)
    ·
      refine ⟨69647009092247440689448609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371450715158653017010392581 69647009092247440689448609)
      ·
        refine ⟨52235256819185580517086457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69647009092247440689448609 52235256819185580517086457)
        ·
          refine ⟨39176442614389185387814843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52235256819185580517086457 39176442614389185387814843)
          ·
            refine ⟨58764663921583778081722265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39176442614389185387814843 58764663921583778081722265)
            ·
              refine ⟨44073497941187833561291699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58764663921583778081722265 44073497941187833561291699)
              ·
                refine ⟨66110246911781750341937549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44073497941187833561291699 66110246911781750341937549)
                ·
                  refine ⟨24791342591918156378226581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66110246911781750341937549 24791342591918156378226581)
                  ·
                    refine ⟨1162094183996163580229371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24791342591918156378226581 1162094183996163580229371)
                    ·
                      rfl

theorem cell23_6789511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_6789511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789511 prefixEnd_6789511 := by exact prefixLift 6789511
  have htrace : WordTrace (prefixWord ++ tailWord_6789511) baseStart_6789511 baseEnd_6789511 := by
    simpa [prefixWord, tailWord_6789511, baseEnd_6789511] using wordTrace_append hprefix tailTrace_6789511
  have hstable : (prefixWord ++ tailWord_6789511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789511).length < 2 ^ (prefixWord ++ tailWord_6789511).sum := by decide
  have hdescent : baseEnd_6789511 < baseStart_6789511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789538 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_6789538 : Nat := 118140960795 + 6789538 * 2 ^ 59
def prefixEnd_6789538 : Nat := 4983230072969 + 3 ^ 40 * 6789538 * 2
def baseEnd_6789538 : Nat := 3486296415966162135050489

theorem tailTrace_6789538 : CollatzResearch.WordTrace tailWord_6789538 prefixEnd_6789538 3486296415966162135050489 := by
  unfold tailWord_6789538
  simp only [CollatzResearch.WordTrace]
  refine ⟨61908698719167715404540317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165089863251113907745440845 61908698719167715404540317)
  ·
    refine ⟨23215762019687893276702619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61908698719167715404540317 23215762019687893276702619)
    ·
      refine ⟨34823643029531839915053929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23215762019687893276702619 34823643029531839915053929)
      ·
        refine ⟨26117732272148879936290447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34823643029531839915053929 26117732272148879936290447)
        ·
          refine ⟨39176598408223319904435671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26117732272148879936290447 39176598408223319904435671)
          ·
            refine ⟨58764897612334979856653507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39176598408223319904435671 58764897612334979856653507)
            ·
              refine ⟨88147346418502469784980261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58764897612334979856653507 88147346418502469784980261)
              ·
                refine ⟨16527627453469213084683799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88147346418502469784980261 16527627453469213084683799)
                ·
                  refine ⟨24791441180203819627025699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16527627453469213084683799 24791441180203819627025699)
                  ·
                    refine ⟨37187161770305729440538549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24791441180203819627025699 37187161770305729440538549)
                    ·
                      refine ⟨3486296415966162135050489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37187161770305729440538549 3486296415966162135050489)
                      ·
                        rfl

theorem cell23_6789538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_6789538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789538 prefixEnd_6789538 := by exact prefixLift 6789538
  have htrace : WordTrace (prefixWord ++ tailWord_6789538) baseStart_6789538 baseEnd_6789538 := by
    simpa [prefixWord, tailWord_6789538, baseEnd_6789538] using wordTrace_append hprefix tailTrace_6789538
  have hstable : (prefixWord ++ tailWord_6789538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789538).length < 2 ^ (prefixWord ++ tailWord_6789538).sum := by decide
  have hdescent : baseEnd_6789538 < baseStart_6789538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789541 : List Nat := [1, 3, 1, 2, 1, 1, 6, 8]
def baseStart_6789541 : Nat := 118140960795 + 6789541 * 2 ^ 59
def prefixEnd_6789541 : Nat := 4983230072969 + 3 ^ 40 * 6789541 * 2
def baseEnd_6789541 : Nat := 129122146533634282344925

theorem tailTrace_6789541 : CollatzResearch.WordTrace tailWord_6789541 prefixEnd_6789541 129122146533634282344925 := by
  unfold tailWord_6789541
  simp only [CollatzResearch.WordTrace]
  refine ⟨247634904295659993130520477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165089936197106662087013651 247634904295659993130520477)
  ·
    refine ⟨92863089110872497423945179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247634904295659993130520477 92863089110872497423945179)
    ·
      refine ⟨139294633666308746135917769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92863089110872497423945179 139294633666308746135917769)
      ·
        refine ⟨104470975249731559601938327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139294633666308746135917769 104470975249731559601938327)
        ·
          refine ⟨156706462874597339402907491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104470975249731559601938327 156706462874597339402907491)
          ·
            refine ⟨235059694311896009104361237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156706462874597339402907491 235059694311896009104361237)
            ·
              refine ⟨11018423170870125426766933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 235059694311896009104361237 11018423170870125426766933)
              ·
                refine ⟨129122146533634282344925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11018423170870125426766933 129122146533634282344925)
                ·
                  rfl

theorem cell23_6789541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 8].length) (baseStart_6789541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789541 prefixEnd_6789541 := by exact prefixLift 6789541
  have htrace : WordTrace (prefixWord ++ tailWord_6789541) baseStart_6789541 baseEnd_6789541 := by
    simpa [prefixWord, tailWord_6789541, baseEnd_6789541] using wordTrace_append hprefix tailTrace_6789541
  have hstable : (prefixWord ++ tailWord_6789541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789541).length < 2 ^ (prefixWord ++ tailWord_6789541).sum := by decide
  have hdescent : baseEnd_6789541 < baseStart_6789541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789549 : List Nat := [1, 5, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_6789549 : Nat := 118140960795 + 6789549 * 2 ^ 59
def prefixEnd_6789549 : Nat := 4983230072969 + 3 ^ 40 * 6789549 * 2
def baseEnd_6789549 : Nat := 1162100688084453864004313

theorem tailTrace_6789549 : CollatzResearch.WordTrace tailWord_6789549 prefixEnd_6789549 1162100688084453864004313 := by
  unfold tailWord_6789549
  simp only [CollatzResearch.WordTrace]
  refine ⟨247635196079631010496811701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165090130719754006997874467 247635196079631010496811701)
  ·
    refine ⟨23215799632465407234076097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247635196079631010496811701 23215799632465407234076097)
    ·
      refine ⟨17411849724349055425557073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23215799632465407234076097 17411849724349055425557073)
      ·
        refine ⟨13058887293261791569167805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17411849724349055425557073 13058887293261791569167805)
        ·
          refine ⟨4897082734973171838437927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13058887293261791569167805 4897082734973171838437927)
          ·
            refine ⟨7345624102459757757656891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4897082734973171838437927 7345624102459757757656891)
            ·
              refine ⟨11018436153689636636485337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7345624102459757757656891 11018436153689636636485337)
              ·
                refine ⟨8263827115267227477364003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11018436153689636636485337 8263827115267227477364003)
                ·
                  refine ⟨12395740672900841216046005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8263827115267227477364003 12395740672900841216046005)
                  ·
                    refine ⟨1162100688084453864004313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12395740672900841216046005 1162100688084453864004313)
                    ·
                      rfl

theorem cell23_6789549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_6789549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789549 prefixEnd_6789549 := by exact prefixLift 6789549
  have htrace : WordTrace (prefixWord ++ tailWord_6789549) baseStart_6789549 baseEnd_6789549 := by
    simpa [prefixWord, tailWord_6789549, baseEnd_6789549] using wordTrace_append hprefix tailTrace_6789549
  have hstable : (prefixWord ++ tailWord_6789549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789549).length < 2 ^ (prefixWord ++ tailWord_6789549).sum := by decide
  have hdescent : baseEnd_6789549 < baseStart_6789549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789556 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_6789556 : Nat := 118140960795 + 6789556 * 2 ^ 59
def prefixEnd_6789556 : Nat := 4983230072969 + 3 ^ 40 * 6789556 * 2
def baseEnd_6789556 : Nat := 3486305658617943064625407

theorem tailTrace_6789556 : CollatzResearch.WordTrace tailWord_6789556 prefixEnd_6789556 3486305658617943064625407 := by
  unfold tailWord_6789556
  simp only [CollatzResearch.WordTrace]
  refine ⟨123817725695302825346158261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165090300927070433794877681 123817725695302825346158261)
  ·
    refine ⟨11607911783934639876202337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123817725695302825346158261 11607911783934639876202337)
    ·
      refine ⟨8705933837950979907151753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11607911783934639876202337 8705933837950979907151753)
      ·
        refine ⟨6529450378463234930363815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8705933837950979907151753 6529450378463234930363815)
        ·
          refine ⟨9794175567694852395545723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6529450378463234930363815 9794175567694852395545723)
          ·
            refine ⟨14691263351542278593318585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9794175567694852395545723 14691263351542278593318585)
            ·
              refine ⟨11018447513656708944988939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14691263351542278593318585 11018447513656708944988939)
              ·
                refine ⟨16527671270485063417483409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11018447513656708944988939 16527671270485063417483409)
                ·
                  refine ⟨12395753452863797563112557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16527671270485063417483409 12395753452863797563112557)
                  ·
                    refine ⟨4648407544823924086167209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12395753452863797563112557 4648407544823924086167209)
                    ·
                      refine ⟨3486305658617943064625407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4648407544823924086167209 3486305658617943064625407)
                      ·
                        rfl

theorem cell23_6789556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_6789556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789556 prefixEnd_6789556 := by exact prefixLift 6789556
  have htrace : WordTrace (prefixWord ++ tailWord_6789556) baseStart_6789556 baseEnd_6789556 := by
    simpa [prefixWord, tailWord_6789556, baseEnd_6789556] using wordTrace_append hprefix tailTrace_6789556
  have hstable : (prefixWord ++ tailWord_6789556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789556).length < 2 ^ (prefixWord ++ tailWord_6789556).sum := by decide
  have hdescent : baseEnd_6789556 < baseStart_6789556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789572 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_6789572 : Nat := 118140960795 + 6789572 * 2 ^ 59
def prefixEnd_6789572 : Nat := 4983230072969 + 3 ^ 40 * 6789572 * 2
def baseEnd_6789572 : Nat := 3486313874308415002025333

theorem tailTrace_6789572 : CollatzResearch.WordTrace tailWord_6789572 prefixEnd_6789572 3486313874308415002025333 := by
  unfold tailWord_6789572
  simp only [CollatzResearch.WordTrace]
  refine ⟨123818017479273842712449485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165090689972365123616599313 123818017479273842712449485)
  ·
    refine ⟨46431756554727691017168557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123818017479273842712449485 46431756554727691017168557)
    ·
      refine ⟨17411908708022884131438209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46431756554727691017168557 17411908708022884131438209)
      ·
        refine ⟨13058931531017163098578657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17411908708022884131438209 13058931531017163098578657)
        ·
          refine ⟨9794198648262872323933993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13058931531017163098578657 9794198648262872323933993)
          ·
            refine ⟨7345648986197154242950495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9794198648262872323933993 7345648986197154242950495)
            ·
              refine ⟨11018473479295731364425743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7345648986197154242950495 11018473479295731364425743)
              ·
                refine ⟨16527710218943597046638615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11018473479295731364425743 16527710218943597046638615)
                ·
                  refine ⟨24791565328415395569957923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16527710218943597046638615 24791565328415395569957923)
                  ·
                    refine ⟨37187347992623093354936885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24791565328415395569957923 37187347992623093354936885)
                    ·
                      refine ⟨3486313874308415002025333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37187347992623093354936885 3486313874308415002025333)
                      ·
                        rfl

theorem cell23_6789572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_6789572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789572 prefixEnd_6789572 := by exact prefixLift 6789572
  have htrace : WordTrace (prefixWord ++ tailWord_6789572) baseStart_6789572 baseEnd_6789572 := by
    simpa [prefixWord, tailWord_6789572, baseEnd_6789572] using wordTrace_append hprefix tailTrace_6789572
  have hstable : (prefixWord ++ tailWord_6789572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789572).length < 2 ^ (prefixWord ++ tailWord_6789572).sum := by decide
  have hdescent : baseEnd_6789572 < baseStart_6789572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789588 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_6789588 : Nat := 118140960795 + 6789588 * 2 ^ 59
def prefixEnd_6789588 : Nat := 4983230072969 + 3 ^ 40 * 6789588 * 2
def baseEnd_6789588 : Nat := 1162107363332962313141753

theorem tailTrace_6789588 : CollatzResearch.WordTrace tailWord_6789588 prefixEnd_6789588 1162107363332962313141753 := by
  unfold tailWord_6789588
  simp only [CollatzResearch.WordTrace]
  refine ⟨123818309263244860078740709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165091079017659813438320945 123818309263244860078740709)
  ·
    refine ⟨23215932986858411264763883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123818309263244860078740709 23215932986858411264763883)
    ·
      refine ⟨34823899480287616897145825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23215932986858411264763883 34823899480287616897145825)
      ·
        refine ⟨26117924610215712672859369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34823899480287616897145825 26117924610215712672859369)
        ·
          refine ⟨19588443457661784504644527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26117924610215712672859369 19588443457661784504644527)
          ·
            refine ⟨29382665186492676756966791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19588443457661784504644527 29382665186492676756966791)
            ·
              refine ⟨44073997779739015135450187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29382665186492676756966791 44073997779739015135450187)
              ·
                refine ⟨66110996669608522703175281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44073997779739015135450187 66110996669608522703175281)
                ·
                  refine ⟨49583247502206392027381461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66110996669608522703175281 49583247502206392027381461)
                  ·
                    refine ⟨1162107363332962313141753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49583247502206392027381461 1162107363332962313141753)
                    ·
                      rfl

theorem cell23_6789588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_6789588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789588 prefixEnd_6789588 := by exact prefixLift 6789588
  have htrace : WordTrace (prefixWord ++ tailWord_6789588) baseStart_6789588 baseEnd_6789588 := by
    simpa [prefixWord, tailWord_6789588, baseEnd_6789588] using wordTrace_append hprefix tailTrace_6789588
  have hstable : (prefixWord ++ tailWord_6789588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789588).length < 2 ^ (prefixWord ++ tailWord_6789588).sum := by decide
  have hdescent : baseEnd_6789588 < baseStart_6789588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789625 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 1, 4, 2]
def baseStart_6789625 : Nat := 118140960795 + 6789625 * 2 ^ 59
def prefixEnd_6789625 : Nat := 4983230072969 + 3 ^ 40 * 6789625 * 2
def baseEnd_6789625 : Nat := 3486341088783103294662589

theorem tailTrace_6789625 : CollatzResearch.WordTrace tailWord_6789625 prefixEnd_6789625 3486341088783103294662589 := by
  unfold tailWord_6789625
  simp only [CollatzResearch.WordTrace]
  refine ⟨247637968027355675476578329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165091978684903783651052219 247637968027355675476578329)
  ·
    refine ⟨185728476020516756607433747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247637968027355675476578329 185728476020516756607433747)
    ·
      refine ⟨278592714030775134911150621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185728476020516756607433747 278592714030775134911150621)
      ·
        refine ⟨104472267761540675591681483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278592714030775134911150621 104472267761540675591681483)
        ·
          refine ⟨156708401642311013387522225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104472267761540675591681483 156708401642311013387522225)
          ·
            refine ⟨117531301231733260040641669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156708401642311013387522225 117531301231733260040641669)
            ·
              refine ⟨22037118980949986257620313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117531301231733260040641669 22037118980949986257620313)
              ·
                refine ⟨16527839235712489693215235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22037118980949986257620313 16527839235712489693215235)
                ·
                  refine ⟨24791758853568734539822853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16527839235712489693215235 24791758853568734539822853)
                  ·
                    refine ⟨4648454785044137726216785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24791758853568734539822853 4648454785044137726216785)
                    ·
                      refine ⟨3486341088783103294662589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4648454785044137726216785 3486341088783103294662589)
                      ·
                        rfl

theorem cell23_6789625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_6789625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789625 prefixEnd_6789625 := by exact prefixLift 6789625
  have htrace : WordTrace (prefixWord ++ tailWord_6789625) baseStart_6789625 baseEnd_6789625 := by
    simpa [prefixWord, tailWord_6789625, baseEnd_6789625] using wordTrace_append hprefix tailTrace_6789625
  have hstable : (prefixWord ++ tailWord_6789625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789625).length < 2 ^ (prefixWord ++ tailWord_6789625).sum := by decide
  have hdescent : baseEnd_6789625 < baseStart_6789625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789631 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 9]
def baseStart_6789631 : Nat := 118140960795 + 6789631 * 2 ^ 59
def prefixEnd_6789631 : Nat := 4983230072969 + 3 ^ 40 * 6789631 * 2
def baseEnd_6789631 : Nat := 387371574407447807909729

theorem tailTrace_6789631 : CollatzResearch.WordTrace tailWord_6789631 prefixEnd_6789631 387371574407447807909729 := by
  unfold tailWord_6789631
  simp only [CollatzResearch.WordTrace]
  refine ⟨247638186865333938501296747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165092124576889292334197831 247638186865333938501296747)
  ·
    refine ⟨371457280298000907751945121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247638186865333938501296747 371457280298000907751945121)
    ·
      refine ⟨278592960223500680813958841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371457280298000907751945121 278592960223500680813958841)
      ·
        refine ⟨208944720167625510610469131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278592960223500680813958841 208944720167625510610469131)
        ·
          refine ⟨313417080251438265915703697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208944720167625510610469131 313417080251438265915703697)
          ·
            refine ⟨235062810188578699436777773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313417080251438265915703697 235062810188578699436777773)
            ·
              refine ⟨88148553820717012288791665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235062810188578699436777773 88148553820717012288791665)
              ·
                refine ⟨66111415365537759216593749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88148553820717012288791665 66111415365537759216593749)
                ·
                  refine ⟨387371574407447807909729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66111415365537759216593749 387371574407447807909729)
                  ·
                    rfl

theorem cell23_6789631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 9].length) (baseStart_6789631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789631 prefixEnd_6789631 := by exact prefixLift 6789631
  have htrace : WordTrace (prefixWord ++ tailWord_6789631) baseStart_6789631 baseEnd_6789631 := by
    simpa [prefixWord, tailWord_6789631, baseEnd_6789631] using wordTrace_append hprefix tailTrace_6789631
  have hstable : (prefixWord ++ tailWord_6789631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789631).length < 2 ^ (prefixWord ++ tailWord_6789631).sum := by decide
  have hdescent : baseEnd_6789631 < baseStart_6789631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789641 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 9]
def baseStart_6789641 : Nat := 118140960795 + 6789641 * 2 ^ 59
def prefixEnd_6789641 : Nat := 4983230072969 + 3 ^ 40 * 6789641 * 2
def baseEnd_6789641 : Nat := 3486349304473575232062515

theorem tailTrace_6789641 : CollatzResearch.WordTrace tailWord_6789641 prefixEnd_6789641 3486349304473575232062515 := by
  unfold tailWord_6789641
  simp only [CollatzResearch.WordTrace]
  refine ⟨247638551595297710209160777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165092367730198473472773851 247638551595297710209160777)
  ·
    refine ⟨185728913696473282656870583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247638551595297710209160777 185728913696473282656870583)
    ·
      refine ⟨278593370544709923985305875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185728913696473282656870583 278593370544709923985305875)
      ·
        refine ⟨417890055817064885977958813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278593370544709923985305875 417890055817064885977958813)
        ·
          refine ⟨156708770931399332241734555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 417890055817064885977958813 156708770931399332241734555)
          ·
            refine ⟨235063156397098998362601833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156708770931399332241734555 235063156397098998362601833)
            ·
              refine ⟨176297367297824248771951375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235063156397098998362601833 176297367297824248771951375)
              ·
                refine ⟨264446050946736373157927063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176297367297824248771951375 264446050946736373157927063)
                ·
                  refine ⟨396669076420104559736890595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264446050946736373157927063 396669076420104559736890595)
                  ·
                    refine ⟨595003614630156839605335893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 396669076420104559736890595 595003614630156839605335893)
                    ·
                      refine ⟨3486349304473575232062515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 595003614630156839605335893 3486349304473575232062515)
                      ·
                        rfl

theorem cell23_6789641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_6789641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789641 prefixEnd_6789641 := by exact prefixLift 6789641
  have htrace : WordTrace (prefixWord ++ tailWord_6789641) baseStart_6789641 baseEnd_6789641 := by
    simpa [prefixWord, tailWord_6789641, baseEnd_6789641] using wordTrace_append hprefix tailTrace_6789641
  have hstable : (prefixWord ++ tailWord_6789641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789641).length < 2 ^ (prefixWord ++ tailWord_6789641).sum := by decide
  have hdescent : baseEnd_6789641 < baseStart_6789641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789642 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 4, 2, 2]
def baseStart_6789642 : Nat := 118140960795 + 6789642 * 2 ^ 59
def prefixEnd_6789642 : Nat := 4983230072969 + 3 ^ 40 * 6789642 * 2
def baseEnd_6789642 : Nat := 3486349817954229728150011

theorem tailTrace_6789642 : CollatzResearch.WordTrace tailWord_6789642 prefixEnd_6789642 3486349817954229728150011 := by
  unfold tailWord_6789642
  simp only [CollatzResearch.WordTrace]
  refine ⟨61909647017073521844986795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165092392045529391586631453 61909647017073521844986795)
  ·
    refine ⟨92864470525610282767480193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61909647017073521844986795 92864470525610282767480193)
    ·
      refine ⟨69648352894207712075610145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92864470525610282767480193 69648352894207712075610145)
      ·
        refine ⟨52236264670655784056707609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69648352894207712075610145 52236264670655784056707609)
        ·
          refine ⟨39177198502991838042530707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52236264670655784056707609 39177198502991838042530707)
          ·
            refine ⟨58765797754487757063796061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39177198502991838042530707 58765797754487757063796061)
            ·
              refine ⟨22037174157932908898923523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58765797754487757063796061 22037174157932908898923523)
              ·
                refine ⟨33055761236899363348385285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22037174157932908898923523 33055761236899363348385285)
                ·
                  refine ⟨6197955231918630627822241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33055761236899363348385285 6197955231918630627822241)
                  ·
                    refine ⟨4648466423938972970866681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6197955231918630627822241 4648466423938972970866681)
                    ·
                      refine ⟨3486349817954229728150011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4648466423938972970866681 3486349817954229728150011)
                      ·
                        rfl

theorem cell23_6789642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_6789642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789642 prefixEnd_6789642 := by exact prefixLift 6789642
  have htrace : WordTrace (prefixWord ++ tailWord_6789642) baseStart_6789642 baseEnd_6789642 := by
    simpa [prefixWord, tailWord_6789642, baseEnd_6789642] using wordTrace_append hprefix tailTrace_6789642
  have hstable : (prefixWord ++ tailWord_6789642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789642).length < 2 ^ (prefixWord ++ tailWord_6789642).sum := by decide
  have hdescent : baseEnd_6789642 < baseStart_6789642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789688 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 1, 2, 5]
def baseStart_6789688 : Nat := 118140960795 + 6789688 * 2 ^ 59
def prefixEnd_6789688 : Nat := 4983230072969 + 3 ^ 40 * 6789688 * 2
def baseEnd_6789688 : Nat := 3486373438064336548174799

theorem tailTrace_6789688 : CollatzResearch.WordTrace tailWord_6789688 prefixEnd_6789688 3486373438064336548174799 := by
  unfold tailWord_6789688
  simp only [CollatzResearch.WordTrace]
  refine ⟨123820132913063718618060859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165093510550751624824081145 123820132913063718618060859)
  ·
    refine ⟨185730199369595577927091289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123820132913063718618060859 185730199369595577927091289)
    ·
      refine ⟨139297649527196683445318467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185730199369595577927091289 139297649527196683445318467)
      ·
        refine ⟨208946474290795025167977701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139297649527196683445318467 208946474290795025167977701)
        ·
          refine ⟨39177463929524067218995819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208946474290795025167977701 39177463929524067218995819)
          ·
            refine ⟨58766195894286100828493729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39177463929524067218995819 58766195894286100828493729)
            ·
              refine ⟨44074646920714575621370297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58766195894286100828493729 44074646920714575621370297)
              ·
                refine ⟨33055985190535931716027723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44074646920714575621370297 33055985190535931716027723)
                ·
                  refine ⟨49583977785803897574041585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33055985190535931716027723 49583977785803897574041585)
                  ·
                    refine ⟨37187983339352923180531189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49583977785803897574041585 37187983339352923180531189)
                    ·
                      refine ⟨3486373438064336548174799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37187983339352923180531189 3486373438064336548174799)
                      ·
                        rfl

theorem cell23_6789688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_6789688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789688 prefixEnd_6789688 := by exact prefixLift 6789688
  have htrace : WordTrace (prefixWord ++ tailWord_6789688) baseStart_6789688 baseEnd_6789688 := by
    simpa [prefixWord, tailWord_6789688, baseEnd_6789688] using wordTrace_append hprefix tailTrace_6789688
  have hstable : (prefixWord ++ tailWord_6789688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789688).length < 2 ^ (prefixWord ++ tailWord_6789688).sum := by decide
  have hdescent : baseEnd_6789688 < baseStart_6789688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789728 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 4]
def baseStart_6789728 : Nat := 118140960795 + 6789728 * 2 ^ 59
def prefixEnd_6789728 : Nat := 4983230072969 + 3 ^ 40 * 6789728 * 2
def baseEnd_6789728 : Nat := 3486393977290516391674615

theorem tailTrace_6789728 : CollatzResearch.WordTrace tailWord_6789728 prefixEnd_6789728 3486393977290516391674615 := by
  unfold tailWord_6789728
  simp only [CollatzResearch.WordTrace]
  refine ⟨123820862372991262033788919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165094483163988349378385225 123820862372991262033788919)
  ·
    refine ⟨185731293559486893050683379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123820862372991262033788919 185731293559486893050683379)
    ·
      refine ⟨278596940339230339576025069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185731293559486893050683379 278596940339230339576025069)
      ·
        refine ⟨104473852627211377341009401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278596940339230339576025069 104473852627211377341009401)
        ·
          refine ⟨78355389470408533005757051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104473852627211377341009401 78355389470408533005757051)
          ·
            refine ⟨117533084205612799508635577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78355389470408533005757051 117533084205612799508635577)
            ·
              refine ⟨88149813154209599631476683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117533084205612799508635577 88149813154209599631476683)
              ·
                refine ⟨132224719731314399447215025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88149813154209599631476683 132224719731314399447215025)
                ·
                  refine ⟨99168539798485799585411269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132224719731314399447215025 99168539798485799585411269)
                  ·
                    refine ⟨18594101212216087422264613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99168539798485799585411269 18594101212216087422264613)
                    ·
                      refine ⟨3486393977290516391674615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18594101212216087422264613 3486393977290516391674615)
                      ·
                        rfl

theorem cell23_6789728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_6789728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789728 prefixEnd_6789728 := by exact prefixLift 6789728
  have htrace : WordTrace (prefixWord ++ tailWord_6789728) baseStart_6789728 baseEnd_6789728 := by
    simpa [prefixWord, tailWord_6789728, baseEnd_6789728] using wordTrace_append hprefix tailTrace_6789728
  have hstable : (prefixWord ++ tailWord_6789728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789728).length < 2 ^ (prefixWord ++ tailWord_6789728).sum := by decide
  have hdescent : baseEnd_6789728 < baseStart_6789728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789775 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 3, 5, 2]
def baseStart_6789775 : Nat := 118140960795 + 6789775 * 2 ^ 59
def prefixEnd_6789775 : Nat := 4983230072969 + 3 ^ 40 * 6789775 * 2
def baseEnd_6789775 : Nat := 3486418110881277707786899

theorem tailTrace_6789775 : CollatzResearch.WordTrace tailWord_6789775 prefixEnd_6789775 3486418110881277707786899 := by
  unfold tailWord_6789775
  simp only [CollatzResearch.WordTrace]
  refine ⟨247643438976812251094538779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165095625984541500729692519 247643438976812251094538779)
  ·
    refine ⟨371465158465218376641808169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247643438976812251094538779 371465158465218376641808169)
    ·
      refine ⟨278598868848913782481356127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371465158465218376641808169 278598868848913782481356127)
      ·
        refine ⟨417898303273370673722034191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278598868848913782481356127 417898303273370673722034191)
        ·
          refine ⟨626847454910056010583051287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417898303273370673722034191 626847454910056010583051287)
          ·
            refine ⟨940271182365084015874576931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626847454910056010583051287 940271182365084015874576931)
            ·
              refine ⟨1410406773547626023811865397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940271182365084015874576931 1410406773547626023811865397)
              ·
                refine ⟨132225635020089939732362381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1410406773547626023811865397 132225635020089939732362381)
                ·
                  refine ⟨49584613132533727399635893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132225635020089939732362381 49584613132533727399635893)
                  ·
                    refine ⟨4648557481175036943715865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49584613132533727399635893 4648557481175036943715865)
                    ·
                      refine ⟨3486418110881277707786899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4648557481175036943715865 3486418110881277707786899)
                      ·
                        rfl

theorem cell23_6789775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 5, 2].length) (baseStart_6789775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789775 prefixEnd_6789775 := by exact prefixLift 6789775
  have htrace : WordTrace (prefixWord ++ tailWord_6789775) baseStart_6789775 baseEnd_6789775 := by
    simpa [prefixWord, tailWord_6789775, baseEnd_6789775] using wordTrace_append hprefix tailTrace_6789775
  have hstable : (prefixWord ++ tailWord_6789775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789775).length < 2 ^ (prefixWord ++ tailWord_6789775).sum := by decide
  have hdescent : baseEnd_6789775 < baseStart_6789775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789785 : List Nat := [1, 2, 1, 2, 1, 2, 4, 4, 1, 5]
def baseStart_6789785 : Nat := 118140960795 + 6789785 * 2 ^ 59
def prefixEnd_6789785 : Nat := 4983230072969 + 3 ^ 40 * 6789785 * 2
def baseEnd_6789785 : Nat := 1162141081895940889553951

theorem tailTrace_6789785 : CollatzResearch.WordTrace tailWord_6789785 prefixEnd_6789785 1162141081895940889553951 := by
  unfold tailWord_6789785
  simp only [CollatzResearch.WordTrace]
  refine ⟨247643803706776022802402809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165095869137850681868268539 247643803706776022802402809)
  ·
    refine ⟨185732852780082017101802107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247643803706776022802402809 185732852780082017101802107)
    ·
      refine ⟨278599279170123025652703161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185732852780082017101802107 278599279170123025652703161)
      ·
        refine ⟨208949459377592269239527371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278599279170123025652703161 208949459377592269239527371)
        ·
          refine ⟨313424189066388403859291057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208949459377592269239527371 313424189066388403859291057)
          ·
            refine ⟨235068141799791302894468293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313424189066388403859291057 235068141799791302894468293)
            ·
              refine ⟨44075276587460869292712805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235068141799791302894468293 44075276587460869292712805)
              ·
                refine ⟨8264114360148912992383651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44075276587460869292712805 8264114360148912992383651)
                ·
                  refine ⟨12396171540223369488575477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8264114360148912992383651 12396171540223369488575477)
                  ·
                    refine ⟨1162141081895940889553951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12396171540223369488575477 1162141081895940889553951)
                    ·
                      rfl

theorem cell23_6789785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 5].length) (baseStart_6789785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789785 prefixEnd_6789785 := by exact prefixLift 6789785
  have htrace : WordTrace (prefixWord ++ tailWord_6789785) baseStart_6789785 baseEnd_6789785 := by
    simpa [prefixWord, tailWord_6789785, baseEnd_6789785] using wordTrace_append hprefix tailTrace_6789785
  have hstable : (prefixWord ++ tailWord_6789785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789785).length < 2 ^ (prefixWord ++ tailWord_6789785).sum := by decide
  have hdescent : baseEnd_6789785 < baseStart_6789785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789786 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3]
def baseStart_6789786 : Nat := 118140960795 + 6789786 * 2 ^ 59
def prefixEnd_6789786 : Nat := 4983230072969 + 3 ^ 40 * 6789786 * 2
def baseEnd_6789786 : Nat := 3486423759168477164749349

theorem tailTrace_6789786 : CollatzResearch.WordTrace tailWord_6789786 prefixEnd_6789786 3486423759168477164749349 := by
  unfold tailWord_6789786
  simp only [CollatzResearch.WordTrace]
  refine ⟨61910960044943099993297303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165095893453181599982126141 61910960044943099993297303)
  ·
    refine ⟨92866440067414649989945955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61910960044943099993297303 92866440067414649989945955)
    ·
      refine ⟨139299660101121974984918933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92866440067414649989945955 139299660101121974984918933)
      ·
        refine ⟨6529671567240092577418075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139299660101121974984918933 6529671567240092577418075)
        ·
          refine ⟨9794507350860138866127113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6529671567240092577418075 9794507350860138866127113)
          ·
            refine ⟨7345880513145104149595335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9794507350860138866127113 7345880513145104149595335)
            ·
              refine ⟨11018820769717656224393003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7345880513145104149595335 11018820769717656224393003)
              ·
                refine ⟨16528231154576484336589505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11018820769717656224393003 16528231154576484336589505)
                ·
                  refine ⟨12396173365932363252442129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16528231154576484336589505 12396173365932363252442129)
                  ·
                    refine ⟨9297130024449272439331597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12396173365932363252442129 9297130024449272439331597)
                    ·
                      refine ⟨3486423759168477164749349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9297130024449272439331597 3486423759168477164749349)
                      ·
                        rfl

theorem cell23_6789786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_6789786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789786 prefixEnd_6789786 := by exact prefixLift 6789786
  have htrace : WordTrace (prefixWord ++ tailWord_6789786) baseStart_6789786 baseEnd_6789786 := by
    simpa [prefixWord, tailWord_6789786, baseEnd_6789786] using wordTrace_append hprefix tailTrace_6789786
  have hstable : (prefixWord ++ tailWord_6789786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789786).length < 2 ^ (prefixWord ++ tailWord_6789786).sum := by decide
  have hdescent : baseEnd_6789786 < baseStart_6789786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789832 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 1, 6]
def baseStart_6789832 : Nat := 118140960795 + 6789832 * 2 ^ 59
def prefixEnd_6789832 : Nat := 4983230072969 + 3 ^ 40 * 6789832 * 2
def baseEnd_6789832 : Nat := 1162149126426194661591379

theorem tailTrace_6789832 : CollatzResearch.WordTrace tailWord_6789832 prefixEnd_6789832 1162149126426194661591379 := by
  unfold tailWord_6789832
  simp only [CollatzResearch.WordTrace]
  refine ⟨123822758968802874914681875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165097011958403833219575833 123822758968802874914681875)
  ·
    refine ⟨185734138453204312372022813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123822758968802874914681875 185734138453204312372022813)
    ·
      refine ⟨69650301919951617139508555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185734138453204312372022813 69650301919951617139508555)
      ·
        refine ⟨104475452879927425709262833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69650301919951617139508555 104475452879927425709262833)
        ·
          refine ⟨78356589659945569281947125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104475452879927425709262833 78356589659945569281947125)
          ·
            refine ⟨7345930280619897120182543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78356589659945569281947125 7345930280619897120182543)
            ·
              refine ⟨11018895420929845680273815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7345930280619897120182543 11018895420929845680273815)
              ·
                refine ⟨16528343131394768520410723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11018895420929845680273815 16528343131394768520410723)
                ·
                  refine ⟨24792514697092152780616085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16528343131394768520410723 24792514697092152780616085)
                  ·
                    refine ⟨1162149126426194661591379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24792514697092152780616085 1162149126426194661591379)
                    ·
                      rfl

theorem cell23_6789832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_6789832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789832 prefixEnd_6789832 := by exact prefixLift 6789832
  have htrace : WordTrace (prefixWord ++ tailWord_6789832) baseStart_6789832 baseEnd_6789832 := by
    simpa [prefixWord, tailWord_6789832, baseEnd_6789832] using wordTrace_append hprefix tailTrace_6789832
  have hstable : (prefixWord ++ tailWord_6789832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789832).length < 2 ^ (prefixWord ++ tailWord_6789832).sum := by decide
  have hdescent : baseEnd_6789832 < baseStart_6789832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789859 : List Nat := [1, 1, 1, 7, 1, 1, 2, 3, 1, 2, 3]
def baseStart_6789859 : Nat := 118140960795 + 6789859 * 2 ^ 59
def prefixEnd_6789859 : Nat := 4983230072969 + 3 ^ 40 * 6789859 * 2
def baseEnd_6789859 : Nat := 3486461243256255379136513

theorem tailTrace_6789859 : CollatzResearch.WordTrace tailWord_6789859 prefixEnd_6789859 3486461243256255379136513 := by
  unfold tailWord_6789859
  simp only [CollatzResearch.WordTrace]
  refine ⟨247646502708507933440596631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165097668472338622293731087 247646502708507933440596631)
  ·
    refine ⟨371469754062761900160894947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247646502708507933440596631 371469754062761900160894947)
    ·
      refine ⟨557204631094142850241342421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371469754062761900160894947 557204631094142850241342421)
      ·
        refine ⟨13059483541268973052531463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 557204631094142850241342421 13059483541268973052531463)
        ·
          refine ⟨19589225311903459578797195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13059483541268973052531463 19589225311903459578797195)
          ·
            refine ⟨29383837967855189368195793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19589225311903459578797195 29383837967855189368195793)
            ·
              refine ⟨22037878475891392026146845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29383837967855189368195793 22037878475891392026146845)
              ·
                refine ⟨8264204428459272009805067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22037878475891392026146845 8264204428459272009805067)
                ·
                  refine ⟨12396306642688908014707601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8264204428459272009805067 12396306642688908014707601)
                  ·
                    refine ⟨9297229982016681011030701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12396306642688908014707601 9297229982016681011030701)
                    ·
                      refine ⟨3486461243256255379136513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9297229982016681011030701 3486461243256255379136513)
                      ·
                        rfl

theorem cell23_6789859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_6789859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789859 prefixEnd_6789859 := by exact prefixLift 6789859
  have htrace : WordTrace (prefixWord ++ tailWord_6789859) baseStart_6789859 baseEnd_6789859 := by
    simpa [prefixWord, tailWord_6789859, baseEnd_6789859] using wordTrace_append hprefix tailTrace_6789859
  have hstable : (prefixWord ++ tailWord_6789859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789859).length < 2 ^ (prefixWord ++ tailWord_6789859).sum := by decide
  have hdescent : baseEnd_6789859 < baseStart_6789859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789872 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 4, 1, 3]
def baseStart_6789872 : Nat := 118140960795 + 6789872 * 2 ^ 59
def prefixEnd_6789872 : Nat := 4983230072969 + 3 ^ 40 * 6789872 * 2
def baseEnd_6789872 : Nat := 3486467918504763828273953

theorem tailTrace_6789872 : CollatzResearch.WordTrace tailWord_6789872 prefixEnd_6789872 3486467918504763828273953 := by
  unfold tailWord_6789872
  simp only [CollatzResearch.WordTrace]
  refine ⟨123823488428730418330409935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165097984571640557773879913 123823488428730418330409935)
  ·
    refine ⟨185735232643095627495614903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123823488428730418330409935 185735232643095627495614903)
    ·
      refine ⟨278602848964643441243422355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185735232643095627495614903 278602848964643441243422355)
      ·
        refine ⟨417904273446965161865133533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278602848964643441243422355 417904273446965161865133533)
        ·
          refine ⟨156714102542611935699425075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 417904273446965161865133533 156714102542611935699425075)
          ·
            refine ⟨235071153813917903549137613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156714102542611935699425075 235071153813917903549137613)
            ·
              refine ⟨88151682680219213830926605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235071153813917903549137613 88151682680219213830926605)
              ·
                refine ⟨33056881005082205186597477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88151682680219213830926605 33056881005082205186597477)
                ·
                  refine ⟨6198165188452913472487027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33056881005082205186597477 6198165188452913472487027)
                  ·
                    refine ⟨9297247782679370208730541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6198165188452913472487027 9297247782679370208730541)
                    ·
                      refine ⟨3486467918504763828273953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9297247782679370208730541 3486467918504763828273953)
                      ·
                        rfl

theorem cell23_6789872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 4, 1, 3].length) (baseStart_6789872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789872 prefixEnd_6789872 := by exact prefixLift 6789872
  have htrace : WordTrace (prefixWord ++ tailWord_6789872) baseStart_6789872 baseEnd_6789872 := by
    simpa [prefixWord, tailWord_6789872, baseEnd_6789872] using wordTrace_append hprefix tailTrace_6789872
  have hstable : (prefixWord ++ tailWord_6789872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789872).length < 2 ^ (prefixWord ++ tailWord_6789872).sum := by decide
  have hdescent : baseEnd_6789872 < baseStart_6789872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789873 : List Nat := [1, 2, 2, 2, 2, 2, 5, 2, 1, 2, 2]
def baseStart_6789873 : Nat := 118140960795 + 6789873 * 2 ^ 59
def prefixEnd_6789873 : Nat := 4983230072969 + 3 ^ 40 * 6789873 * 2
def baseEnd_6789873 : Nat := 3486468431985418324361449

theorem tailTrace_6789873 : CollatzResearch.WordTrace tailWord_6789873 prefixEnd_6789873 3486468431985418324361449 := by
  unfold tailWord_6789873
  simp only [CollatzResearch.WordTrace]
  refine ⟨247647013330457213831606273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165098008886971475887737515 247647013330457213831606273)
  ·
    refine ⟨185735259997842910373704705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247647013330457213831606273 185735259997842910373704705)
    ·
      refine ⟨139301444998382182780278529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185735259997842910373704705 139301444998382182780278529)
      ·
        refine ⟨104476083748786637085208897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139301444998382182780278529 104476083748786637085208897)
        ·
          refine ⟨78357062811589977813906673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104476083748786637085208897 78357062811589977813906673)
          ·
            refine ⟨58767797108692483360430005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78357062811589977813906673 58767797108692483360430005)
            ·
              refine ⟨5509480978939920315040313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58767797108692483360430005 5509480978939920315040313)
              ·
                refine ⟨4132110734204940236280235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5509480978939920315040313 4132110734204940236280235)
                ·
                  refine ⟨6198166101307410354420353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4132110734204940236280235 6198166101307410354420353)
                  ·
                    refine ⟨4648624575980557765815265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6198166101307410354420353 4648624575980557765815265)
                    ·
                      refine ⟨3486468431985418324361449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4648624575980557765815265 3486468431985418324361449)
                      ·
                        rfl

theorem cell23_6789873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_6789873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789873 prefixEnd_6789873 := by exact prefixLift 6789873
  have htrace : WordTrace (prefixWord ++ tailWord_6789873) baseStart_6789873 baseEnd_6789873 := by
    simpa [prefixWord, tailWord_6789873, baseEnd_6789873] using wordTrace_append hprefix tailTrace_6789873
  have hstable : (prefixWord ++ tailWord_6789873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789873).length < 2 ^ (prefixWord ++ tailWord_6789873).sum := by decide
  have hdescent : baseEnd_6789873 < baseStart_6789873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789906 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_6789906 : Nat := 118140960795 + 6789906 * 2 ^ 59
def prefixEnd_6789906 : Nat := 4983230072969 + 3 ^ 40 * 6789906 * 2
def baseEnd_6789906 : Nat := 3486485376847016695248797

theorem tailTrace_6789906 : CollatzResearch.WordTrace tailWord_6789906 prefixEnd_6789906 3486485376847016695248797 := by
  unfold tailWord_6789906
  simp only [CollatzResearch.WordTrace]
  refine ⟨61912054234834415116889393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165098811292891773645038381 61912054234834415116889393)
  ·
    refine ⟨46434040676125811337667045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61912054234834415116889393 46434040676125811337667045)
    ·
      refine ⟨8706382626773589625812571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46434040676125811337667045 8706382626773589625812571)
      ·
        refine ⟨13059573940160384438718857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8706382626773589625812571 13059573940160384438718857)
        ·
          refine ⟨9794680455120288329039143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13059573940160384438718857 9794680455120288329039143)
          ·
            refine ⟨14692020682680432493558715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9794680455120288329039143 14692020682680432493558715)
            ·
              refine ⟨22038031024020648740338073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14692020682680432493558715 22038031024020648740338073)
              ·
                refine ⟨16528523268015486555253555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22038031024020648740338073 16528523268015486555253555)
                ·
                  refine ⟨24792784902023229832880333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16528523268015486555253555 24792784902023229832880333)
                  ·
                    refine ⟨9297294338258711187330125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24792784902023229832880333 9297294338258711187330125)
                    ·
                      refine ⟨3486485376847016695248797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9297294338258711187330125 3486485376847016695248797)
                      ·
                        rfl

theorem cell23_6789906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_6789906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789906 prefixEnd_6789906 := by exact prefixLift 6789906
  have htrace : WordTrace (prefixWord ++ tailWord_6789906) baseStart_6789906 baseEnd_6789906 := by
    simpa [prefixWord, tailWord_6789906, baseEnd_6789906] using wordTrace_append hprefix tailTrace_6789906
  have hstable : (prefixWord ++ tailWord_6789906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789906).length < 2 ^ (prefixWord ++ tailWord_6789906).sum := by decide
  have hdescent : baseEnd_6789906 < baseStart_6789906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789915 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 3]
def baseStart_6789915 : Nat := 118140960795 + 6789915 * 2 ^ 59
def prefixEnd_6789915 : Nat := 4983230072969 + 3 ^ 40 * 6789915 * 2
def baseEnd_6789915 : Nat := 3486489998172907160036255

theorem tailTrace_6789915 : CollatzResearch.WordTrace tailWord_6789915 prefixEnd_6789915 3486489998172907160036255 := by
  unfold tailWord_6789915
  simp only [CollatzResearch.WordTrace]
  refine ⟨247648545196305055004635199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165099030130870036669756799 247648545196305055004635199)
  ·
    refine ⟨371472817794457582506952799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247648545196305055004635199 371472817794457582506952799)
    ·
      refine ⟨557209226691686373760429199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371472817794457582506952799 557209226691686373760429199)
      ·
        refine ⟨835813840037529560640643799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557209226691686373760429199 835813840037529560640643799)
        ·
          refine ⟨1253720760056294340960965699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835813840037529560640643799 1253720760056294340960965699)
          ·
            refine ⟨1880581140084441511441448549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253720760056294340960965699 1880581140084441511441448549)
            ·
              refine ⟨352608963765832783395271603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1880581140084441511441448549 352608963765832783395271603)
              ·
                refine ⟨528913445648749175092907405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352608963765832783395271603 528913445648749175092907405)
                ·
                  refine ⟨198342542118280940659840277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 528913445648749175092907405 198342542118280940659840277)
                  ·
                    refine ⟨9297306661794419093430013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 198342542118280940659840277 9297306661794419093430013)
                    ·
                      refine ⟨3486489998172907160036255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9297306661794419093430013 3486489998172907160036255)
                      ·
                        rfl

theorem cell23_6789915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 3].length) (baseStart_6789915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789915 prefixEnd_6789915 := by exact prefixLift 6789915
  have htrace : WordTrace (prefixWord ++ tailWord_6789915) baseStart_6789915 baseEnd_6789915 := by
    simpa [prefixWord, tailWord_6789915, baseEnd_6789915] using wordTrace_append hprefix tailTrace_6789915
  have hstable : (prefixWord ++ tailWord_6789915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789915).length < 2 ^ (prefixWord ++ tailWord_6789915).sum := by decide
  have hdescent : baseEnd_6789915 < baseStart_6789915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789946 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2]
def baseStart_6789946 : Nat := 118140960795 + 6789946 * 2 ^ 59
def prefixEnd_6789946 : Nat := 4983230072969 + 3 ^ 40 * 6789946 * 2
def baseEnd_6789946 : Nat := 3486505916073196538748613

theorem tailTrace_6789946 : CollatzResearch.WordTrace tailWord_6789946 prefixEnd_6789946 3486505916073196538748613 := by
  unfold tailWord_6789946
  simp only [CollatzResearch.WordTrace]
  refine ⟨61912418964798186824753423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165099783906128498199342461 61912418964798186824753423)
  ·
    refine ⟨92868628447197280237130135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61912418964798186824753423 92868628447197280237130135)
    ·
      refine ⟨139302942670795920355695203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92868628447197280237130135 139302942670795920355695203)
      ·
        refine ⟨208954414006193880533542805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139302942670795920355695203 208954414006193880533542805)
        ·
          refine ⟨9794738156540338150009819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 208954414006193880533542805 9794738156540338150009819)
          ·
            refine ⟨14692107234810507225014729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9794738156540338150009819 14692107234810507225014729)
            ·
              refine ⟨11019080426107880418761047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14692107234810507225014729 11019080426107880418761047)
              ·
                refine ⟨16528620639161820628141571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11019080426107880418761047 16528620639161820628141571)
                ·
                  refine ⟨24792930958742730942212357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16528620639161820628141571 24792930958742730942212357)
                  ·
                    refine ⟨4648674554764262051664817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24792930958742730942212357 4648674554764262051664817)
                    ·
                      refine ⟨3486505916073196538748613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4648674554764262051664817 3486505916073196538748613)
                      ·
                        rfl

theorem cell23_6789946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2].length) (baseStart_6789946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789946 prefixEnd_6789946 := by exact prefixLift 6789946
  have htrace : WordTrace (prefixWord ++ tailWord_6789946) baseStart_6789946 baseEnd_6789946 := by
    simpa [prefixWord, tailWord_6789946, baseEnd_6789946] using wordTrace_append hprefix tailTrace_6789946
  have hstable : (prefixWord ++ tailWord_6789946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789946).length < 2 ^ (prefixWord ++ tailWord_6789946).sum := by decide
  have hdescent : baseEnd_6789946 < baseStart_6789946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789980 : List Nat := [2, 2, 4, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_6789980 : Nat := 118140960795 + 6789980 * 2 ^ 59
def prefixEnd_6789980 : Nat := 4983230072969 + 3 ^ 40 * 6789980 * 2
def baseEnd_6789980 : Nat := 3486523374415449405723457

theorem tailTrace_6789980 : CollatzResearch.WordTrace tailWord_6789980 prefixEnd_6789980 3486523374415449405723457 := by
  unfold tailWord_6789980
  simp only [CollatzResearch.WordTrace]
  refine ⟨123825457970534785552875697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165100610627379714070500929 123825457970534785552875697)
  ·
    refine ⟨92869093477901089164656773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123825457970534785552875697 92869093477901089164656773)
    ·
      refine ⟨17412955027106454218373145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92869093477901089164656773 17412955027106454218373145)
      ·
        refine ⟨13059716270329840663779859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17412955027106454218373145 13059716270329840663779859)
        ·
          refine ⟨19589574405494760995669789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13059716270329840663779859 19589574405494760995669789)
          ·
            refine ⟨7346090402060535373376171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19589574405494760995669789 7346090402060535373376171)
            ·
              refine ⟨11019135603090803060064257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7346090402060535373376171 11019135603090803060064257)
              ·
                refine ⟨8264351702318102295048193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11019135603090803060064257 8264351702318102295048193)
                ·
                  refine ⟨6198263776738576721286145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8264351702318102295048193 6198263776738576721286145)
                  ·
                    refine ⟨4648697832553932540964609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6198263776738576721286145 4648697832553932540964609)
                    ·
                      refine ⟨3486523374415449405723457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4648697832553932540964609 3486523374415449405723457)
                      ·
                        rfl

theorem cell23_6789980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_6789980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6789980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6789980 prefixEnd_6789980 := by exact prefixLift 6789980
  have htrace : WordTrace (prefixWord ++ tailWord_6789980) baseStart_6789980 baseEnd_6789980 := by
    simpa [prefixWord, tailWord_6789980, baseEnd_6789980] using wordTrace_append hprefix tailTrace_6789980
  have hstable : (prefixWord ++ tailWord_6789980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789980).length < 2 ^ (prefixWord ++ tailWord_6789980).sum := by decide
  have hdescent : baseEnd_6789980 < baseStart_6789980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790002 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_6790002 : Nat := 118140960795 + 6790002 * 2 ^ 59
def prefixEnd_6790002 : Nat := 4983230072969 + 3 ^ 40 * 6790002 * 2
def baseEnd_6790002 : Nat := 3486534670989848319648355

theorem tailTrace_6790002 : CollatzResearch.WordTrace tailWord_6790002 prefixEnd_6790002 3486534670989848319648355 := by
  unfold tailWord_6790002
  simp only [CollatzResearch.WordTrace]
  refine ⟨61912929586747467215763065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165101145564659912575368173 61912929586747467215763065)
  ·
    refine ⟨46434697190060600411822299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61912929586747467215763065 46434697190060600411822299)
    ·
      refine ⟨69652045785090900617733449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46434697190060600411822299 69652045785090900617733449)
      ·
        refine ⟨52239034338818175463300087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69652045785090900617733449 52239034338818175463300087)
        ·
          refine ⟨78358551508227263194950131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52239034338818175463300087 78358551508227263194950131)
          ·
            refine ⟨117537827262340894792425197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78358551508227263194950131 117537827262340894792425197)
            ·
              refine ⟨44076685223377835547159449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117537827262340894792425197 44076685223377835547159449)
              ·
                refine ⟨33057513917533376660369587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44076685223377835547159449 33057513917533376660369587)
                ·
                  refine ⟨49586270876300064990554381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33057513917533376660369587 49586270876300064990554381)
                  ·
                    refine ⟨18594851578612524371457893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49586270876300064990554381 18594851578612524371457893)
                    ·
                      refine ⟨3486534670989848319648355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18594851578612524371457893 3486534670989848319648355)
                      ·
                        rfl

theorem cell23_6790002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_6790002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790002 prefixEnd_6790002 := by exact prefixLift 6790002
  have htrace : WordTrace (prefixWord ++ tailWord_6790002) baseStart_6790002 baseEnd_6790002 := by
    simpa [prefixWord, tailWord_6790002, baseEnd_6790002] using wordTrace_append hprefix tailTrace_6790002
  have hstable : (prefixWord ++ tailWord_6790002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790002).length < 2 ^ (prefixWord ++ tailWord_6790002).sum := by decide
  have hdescent : baseEnd_6790002 < baseStart_6790002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790039 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 3]
def baseStart_6790039 : Nat := 118140960795 + 6790039 * 2 ^ 59
def prefixEnd_6790039 : Nat := 4983230072969 + 3 ^ 40 * 6790039 * 2
def baseEnd_6790039 : Nat := 3486553669774064674885685

theorem tailTrace_6790039 : CollatzResearch.WordTrace tailWord_6790039 prefixEnd_6790039 3486553669774064674885685 := by
  unfold tailWord_6790039
  simp only [CollatzResearch.WordTrace]
  refine ⟨247653067847855824182149171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165102045231903882788099447 247653067847855824182149171)
  ·
    refine ⟨371479601771783736273223757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247653067847855824182149171 371479601771783736273223757)
    ·
      refine ⟨139304850664418901102458909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371479601771783736273223757 139304850664418901102458909)
      ·
        refine ⟨52239318999157087913422091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139304850664418901102458909 52239318999157087913422091)
        ·
          refine ⟨78358978498735631870133137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52239318999157087913422091 78358978498735631870133137)
          ·
            refine ⟨58769233874051723902599853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78358978498735631870133137 58769233874051723902599853)
            ·
              refine ⟨22038462702769396463474945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58769233874051723902599853 22038462702769396463474945)
              ·
                refine ⟨16528847027077047347606209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22038462702769396463474945 16528847027077047347606209)
                ·
                  refine ⟨12396635270307785510704657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16528847027077047347606209 12396635270307785510704657)
                  ·
                    refine ⟨9297476452730839133028493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12396635270307785510704657 9297476452730839133028493)
                    ·
                      refine ⟨3486553669774064674885685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9297476452730839133028493 3486553669774064674885685)
                      ·
                        rfl

theorem cell23_6790039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_6790039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790039 prefixEnd_6790039 := by exact prefixLift 6790039
  have htrace : WordTrace (prefixWord ++ tailWord_6790039) baseStart_6790039 baseEnd_6790039 := by
    simpa [prefixWord, tailWord_6790039, baseEnd_6790039] using wordTrace_append hprefix tailTrace_6790039
  have hstable : (prefixWord ++ tailWord_6790039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790039).length < 2 ^ (prefixWord ++ tailWord_6790039).sum := by decide
  have hdescent : baseEnd_6790039 < baseStart_6790039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790119 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 1, 6]
def baseStart_6790119 : Nat := 118140960795 + 6790119 * 2 ^ 59
def prefixEnd_6790119 : Nat := 4983230072969 + 3 ^ 40 * 6790119 * 2
def baseEnd_6790119 : Nat := 1162198249408808120628439

theorem tailTrace_6790119 : CollatzResearch.WordTrace tailWord_6790119 prefixEnd_6790119 1162198249408808120628439 := by
  unfold tailWord_6790119
  simp only [CollatzResearch.WordTrace]
  refine ⟨247655985687565997845061411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165103990458377331896707607 247655985687565997845061411)
  ·
    refine ⟨371483978531348996767592117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247655985687565997845061411 371483978531348996767592117)
    ·
      refine ⟨34826622987313968446961761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 371483978531348996767592117 34826622987313968446961761)
      ·
        refine ⟨26119967240485476335221321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34826622987313968446961761 26119967240485476335221321)
        ·
          refine ⟨19589975430364107251415991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26119967240485476335221321 19589975430364107251415991)
          ·
            refine ⟨29384963145546160877123987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19589975430364107251415991 29384963145546160877123987)
            ·
              refine ⟨44077444718319241315685981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29384963145546160877123987 44077444718319241315685981)
              ·
                refine ⟨16529041769369715493382243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44077444718319241315685981 16529041769369715493382243)
                ·
                  refine ⟨24793562654054573240073365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16529041769369715493382243 24793562654054573240073365)
                  ·
                    refine ⟨1162198249408808120628439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24793562654054573240073365 1162198249408808120628439)
                    ·
                      rfl

theorem cell23_6790119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_6790119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790119 prefixEnd_6790119 := by exact prefixLift 6790119
  have htrace : WordTrace (prefixWord ++ tailWord_6790119) baseStart_6790119 baseEnd_6790119 := by
    simpa [prefixWord, tailWord_6790119, baseEnd_6790119] using wordTrace_append hprefix tailTrace_6790119
  have hstable : (prefixWord ++ tailWord_6790119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790119).length < 2 ^ (prefixWord ++ tailWord_6790119).sum := by decide
  have hdescent : baseEnd_6790119 < baseStart_6790119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790173 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_6790173 : Nat := 118140960795 + 6790173 * 2 ^ 59
def prefixEnd_6790173 : Nat := 4983230072969 + 3 ^ 40 * 6790173 * 2
def baseEnd_6790173 : Nat := 3486622476181767150610069

theorem tailTrace_6790173 : CollatzResearch.WordTrace tailWord_6790173 prefixEnd_6790173 3486622476181767150610069 := by
  unfold tailWord_6790173
  simp only [CollatzResearch.WordTrace]
  refine ⟨247657955229370365067527173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165105303486246910045018115 247657955229370365067527173)
  ·
    refine ⟨46435866605506943450161345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247657955229370365067527173 46435866605506943450161345)
    ·
      refine ⟨34826899954130207587621009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46435866605506943450161345 34826899954130207587621009)
      ·
        refine ⟨26120174965597655690715757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34826899954130207587621009 26120174965597655690715757)
        ·
          refine ⟨9795065612099120884018409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26120174965597655690715757 9795065612099120884018409)
          ·
            refine ⟨7346299209074340663013807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9795065612099120884018409 7346299209074340663013807)
            ·
              refine ⟨11019448813611510994520711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7346299209074340663013807 11019448813611510994520711)
              ·
                refine ⟨16529173220417266491781067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11019448813611510994520711 16529173220417266491781067)
                ·
                  refine ⟨24793759830625899737671601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16529173220417266491781067 24793759830625899737671601)
                  ·
                    refine ⟨18595319872969424803253701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24793759830625899737671601 18595319872969424803253701)
                    ·
                      refine ⟨3486622476181767150610069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18595319872969424803253701 3486622476181767150610069)
                      ·
                        rfl

theorem cell23_6790173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_6790173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790173 prefixEnd_6790173 := by exact prefixLift 6790173
  have htrace : WordTrace (prefixWord ++ tailWord_6790173) baseStart_6790173 baseEnd_6790173 := by
    simpa [prefixWord, tailWord_6790173, baseEnd_6790173] using wordTrace_append hprefix tailTrace_6790173
  have hstable : (prefixWord ++ tailWord_6790173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790173).length < 2 ^ (prefixWord ++ tailWord_6790173).sum := by decide
  have hdescent : baseEnd_6790173 < baseStart_6790173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790183 : List Nat := [1, 1, 7, 1, 1, 3, 2, 7]
def baseStart_6790183 : Nat := 118140960795 + 6790183 * 2 ^ 59
def prefixEnd_6790183 : Nat := 4983230072969 + 3 ^ 40 * 6790183 * 2
def baseEnd_6790183 : Nat := 129134355962530078203149

theorem tailTrace_6790183 : CollatzResearch.WordTrace tailWord_6790183 prefixEnd_6790183 129134355962530078203149 := by
  unfold tailWord_6790183
  simp only [CollatzResearch.WordTrace]
  refine ⟨247658319959334136775391203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165105546639556091183594135 247658319959334136775391203)
  ·
    refine ⟨371487479939001205163086805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247658319959334136775391203 371487479939001205163086805)
    ·
      refine ⟨8706737811070340746009847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 371487479939001205163086805 8706737811070340746009847)
      ·
        refine ⟨13060106716605511119014771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8706737811070340746009847 13060106716605511119014771)
        ·
          refine ⟨19590160074908266678522157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13060106716605511119014771 19590160074908266678522157)
          ·
            refine ⟨7346310028090600004445809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19590160074908266678522157 7346310028090600004445809)
            ·
              refine ⟨5509732521067950003334357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7346310028090600004445809 5509732521067950003334357)
              ·
                refine ⟨129134355962530078203149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5509732521067950003334357 129134355962530078203149)
                ·
                  rfl

theorem cell23_6790183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 7].length) (baseStart_6790183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790183 prefixEnd_6790183 := by exact prefixLift 6790183
  have htrace : WordTrace (prefixWord ++ tailWord_6790183) baseStart_6790183 baseEnd_6790183 := by
    simpa [prefixWord, tailWord_6790183, baseEnd_6790183] using wordTrace_append hprefix tailTrace_6790183
  have hstable : (prefixWord ++ tailWord_6790183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790183).length < 2 ^ (prefixWord ++ tailWord_6790183).sum := by decide
  have hdescent : baseEnd_6790183 < baseStart_6790183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790229 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_6790229 : Nat := 118140960795 + 6790229 * 2 ^ 59
def prefixEnd_6790229 : Nat := 4983230072969 + 3 ^ 40 * 6790229 * 2
def baseEnd_6790229 : Nat := 3486651231098418931509811

theorem tailTrace_6790229 : CollatzResearch.WordTrace tailWord_6790229 prefixEnd_6790229 3486651231098418931509811 := by
  unfold tailWord_6790229
  simp only [CollatzResearch.WordTrace]
  refine ⟨247659997717167486631565741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165106665144778324421043827 247659997717167486631565741)
  ·
    refine ⟨92872499143937807486837153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247659997717167486631565741 92872499143937807486837153)
    ·
      refine ⟨69654374357953355615127865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92872499143937807486837153 69654374357953355615127865)
      ·
        refine ⟨52240780768465016711345899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69654374357953355615127865 52240780768465016711345899)
        ·
          refine ⟨78361171152697525067018849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52240780768465016711345899 78361171152697525067018849)
          ·
            refine ⟨58770878364523143800264137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78361171152697525067018849 58770878364523143800264137)
            ·
              refine ⟨44078158773392357850198103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58770878364523143800264137 44078158773392357850198103)
              ·
                refine ⟨66117238160088536775297155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44078158773392357850198103 66117238160088536775297155)
                ·
                  refine ⟨99175857240132805162945733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66117238160088536775297155 99175857240132805162945733)
                  ·
                    refine ⟨18595473232524900968052325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99175857240132805162945733 18595473232524900968052325)
                    ·
                      refine ⟨3486651231098418931509811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18595473232524900968052325 3486651231098418931509811)
                      ·
                        rfl

theorem cell23_6790229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_6790229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790229 prefixEnd_6790229 := by exact prefixLift 6790229
  have htrace : WordTrace (prefixWord ++ tailWord_6790229) baseStart_6790229 baseEnd_6790229 := by
    simpa [prefixWord, tailWord_6790229, baseEnd_6790229] using wordTrace_append hprefix tailTrace_6790229
  have hstable : (prefixWord ++ tailWord_6790229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790229).length < 2 ^ (prefixWord ++ tailWord_6790229).sum := by decide
  have hdescent : baseEnd_6790229 < baseStart_6790229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790256 : List Nat := [2, 1, 1, 1, 5, 1, 2, 5, 5]
def baseStart_6790256 : Nat := 118140960795 + 6790256 * 2 ^ 59
def prefixEnd_6790256 : Nat := 4983230072969 + 3 ^ 40 * 6790256 * 2
def baseEnd_6790256 : Nat := 387407232786232258430243

theorem tailTrace_6790256 : CollatzResearch.WordTrace tailWord_6790256 prefixEnd_6790256 387407232786232258430243 := by
  unfold tailWord_6790256
  simp only [CollatzResearch.WordTrace]
  refine ⟨123830491244034835121399311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165107321658713113495199081 123830491244034835121399311)
  ·
    refine ⟨185745736866052252682098967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123830491244034835121399311 185745736866052252682098967)
    ·
      refine ⟨278618605299078379023148451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185745736866052252682098967 278618605299078379023148451)
      ·
        refine ⟨417927907948617568534722677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278618605299078379023148451 417927907948617568534722677)
        ·
          refine ⟨39180741370182897050130251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 417927907948617568534722677 39180741370182897050130251)
          ·
            refine ⟨58771112055274345575195377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39180741370182897050130251 58771112055274345575195377)
            ·
              refine ⟨44078334041455759181396533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58771112055274345575195377 44078334041455759181396533)
              ·
                refine ⟨4132343816386477423255925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44078334041455759181396533 4132343816386477423255925)
                ·
                  refine ⟨387407232786232258430243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4132343816386477423255925 387407232786232258430243)
                  ·
                    rfl

theorem cell23_6790256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 5].length) (baseStart_6790256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790256 prefixEnd_6790256 := by exact prefixLift 6790256
  have htrace : WordTrace (prefixWord ++ tailWord_6790256) baseStart_6790256 baseEnd_6790256 := by
    simpa [prefixWord, tailWord_6790256, baseEnd_6790256] using wordTrace_append hprefix tailTrace_6790256
  have hstable : (prefixWord ++ tailWord_6790256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790256).length < 2 ^ (prefixWord ++ tailWord_6790256).sum := by decide
  have hdescent : baseEnd_6790256 < baseStart_6790256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790273 : List Nat := [1, 2, 4, 2, 2, 2, 1, 4, 5]
def baseStart_6790273 : Nat := 118140960795 + 6790273 * 2 ^ 59
def prefixEnd_6790273 : Nat := 4983230072969 + 3 ^ 40 * 6790273 * 2
def baseEnd_6790273 : Nat := 387408202694135195484401

theorem tailTrace_6790273 : CollatzResearch.WordTrace tailWord_6790273 prefixEnd_6790273 387408202694135195484401 := by
  unfold tailWord_6790273
  simp only [CollatzResearch.WordTrace]
  refine ⟨247661602529008082146167473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165107735019338721430778315 247661602529008082146167473)
  ·
    refine ⟨185746201896756061609625605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247661602529008082146167473 185746201896756061609625605)
    ·
      refine ⟨34827412855641761551804801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185746201896756061609625605 34827412855641761551804801)
      ·
        refine ⟨26120559641731321163853601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34827412855641761551804801 26120559641731321163853601)
        ·
          refine ⟨19590419731298490872890201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26120559641731321163853601 19590419731298490872890201)
          ·
            refine ⟨14692814798473868154667651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19590419731298490872890201 14692814798473868154667651)
            ·
              refine ⟨22039222197710802232001477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14692814798473868154667651 22039222197710802232001477)
              ·
                refine ⟨4132354162070775418500277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22039222197710802232001477 4132354162070775418500277)
                ·
                  refine ⟨387408202694135195484401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4132354162070775418500277 387408202694135195484401)
                  ·
                    rfl

theorem cell23_6790273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 5].length) (baseStart_6790273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790273 prefixEnd_6790273 := by exact prefixLift 6790273
  have htrace : WordTrace (prefixWord ++ tailWord_6790273) baseStart_6790273 baseEnd_6790273 := by
    simpa [prefixWord, tailWord_6790273, baseEnd_6790273] using wordTrace_append hprefix tailTrace_6790273
  have hstable : (prefixWord ++ tailWord_6790273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790273).length < 2 ^ (prefixWord ++ tailWord_6790273).sum := by decide
  have hdescent : baseEnd_6790273 < baseStart_6790273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790319 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 6]
def baseStart_6790319 : Nat := 118140960795 + 6790319 * 2 ^ 59
def prefixEnd_6790319 : Nat := 4983230072969 + 3 ^ 40 * 6790319 * 2
def baseEnd_6790319 : Nat := 3486697444357323579384397

theorem tailTrace_6790319 : CollatzResearch.WordTrace tailWord_6790319 prefixEnd_6790319 3486697444357323579384397 := by
  unfold tailWord_6790319
  simp only [CollatzResearch.WordTrace]
  refine ⟨247663280286841432002342011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165108853524560954668228007 247663280286841432002342011)
  ·
    refine ⟨371494920430262148003513017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247663280286841432002342011 371494920430262148003513017)
    ·
      refine ⟨278621190322696611002634763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371494920430262148003513017 278621190322696611002634763)
      ·
        refine ⟨417931785484044916503952145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278621190322696611002634763 417931785484044916503952145)
        ·
          refine ⟨313448839113033687377964109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417931785484044916503952145 313448839113033687377964109)
          ·
            refine ⟨117543314667387632766736541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313448839113033687377964109 117543314667387632766736541)
            ·
              refine ⟨44078743000270362287526203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117543314667387632766736541 44078743000270362287526203)
              ·
                refine ⟨66118114500405543431289305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44078743000270362287526203 66118114500405543431289305)
                ·
                  refine ⟨49588585875304157573466979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66118114500405543431289305 49588585875304157573466979)
                  ·
                    refine ⟨74382878812956236360200469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49588585875304157573466979 74382878812956236360200469)
                    ·
                      refine ⟨3486697444357323579384397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74382878812956236360200469 3486697444357323579384397)
                      ·
                        rfl

theorem cell23_6790319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_6790319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790319 prefixEnd_6790319 := by exact prefixLift 6790319
  have htrace : WordTrace (prefixWord ++ tailWord_6790319) baseStart_6790319 baseEnd_6790319 := by
    simpa [prefixWord, tailWord_6790319, baseEnd_6790319] using wordTrace_append hprefix tailTrace_6790319
  have hstable : (prefixWord ++ tailWord_6790319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790319).length < 2 ^ (prefixWord ++ tailWord_6790319).sum := by decide
  have hdescent : baseEnd_6790319 < baseStart_6790319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790440 : List Nat := [2, 1, 5, 1, 2, 1, 1, 4, 2, 4]
def baseStart_6790440 : Nat := 118140960795 + 6790440 * 2 ^ 59
def prefixEnd_6790440 : Nat := 4983230072969 + 3 ^ 40 * 6790440 * 2
def baseEnd_6790440 : Nat := 1162253191838839201990447

theorem tailTrace_6790440 : CollatzResearch.WordTrace tailWord_6790440 prefixEnd_6790440 1162253191838839201990447 := by
  unfold tailWord_6790440
  simp only [CollatzResearch.WordTrace]
  refine ⟨123833846759701534833748387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165111795679602046444997849 123833846759701534833748387)
  ·
    refine ⟨185750770139552302250622581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123833846759701534833748387 185750770139552302250622581)
    ·
      refine ⟨17414134700583028335995867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185750770139552302250622581 17414134700583028335995867)
      ·
        refine ⟨26121202050874542503993801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17414134700583028335995867 26121202050874542503993801)
        ·
          refine ⟨19590901538155906877995351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26121202050874542503993801 19590901538155906877995351)
          ·
            refine ⟨29386352307233860316993027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19590901538155906877995351 29386352307233860316993027)
            ·
              refine ⟨44079528460850790475489541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29386352307233860316993027 44079528460850790475489541)
              ·
                refine ⟨8264911586409523214154289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44079528460850790475489541 8264911586409523214154289)
                ·
                  refine ⟨6198683689807142410615717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8264911586409523214154289 6198683689807142410615717)
                  ·
                    refine ⟨1162253191838839201990447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6198683689807142410615717 1162253191838839201990447)
                    ·
                      rfl

theorem cell23_6790440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_6790440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790440 prefixEnd_6790440 := by exact prefixLift 6790440
  have htrace : WordTrace (prefixWord ++ tailWord_6790440) baseStart_6790440 baseEnd_6790440 := by
    simpa [prefixWord, tailWord_6790440, baseEnd_6790440] using wordTrace_append hprefix tailTrace_6790440
  have hstable : (prefixWord ++ tailWord_6790440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790440).length < 2 ^ (prefixWord ++ tailWord_6790440).sum := by decide
  have hdescent : baseEnd_6790440 < baseStart_6790440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790453 : List Nat := [1, 3, 3, 1, 2, 4, 1, 8]
def baseStart_6790453 : Nat := 118140960795 + 6790453 * 2 ^ 59
def prefixEnd_6790453 : Nat := 4983230072969 + 3 ^ 40 * 6790453 * 2
def baseEnd_6790453 : Nat := 129139490769075039078103

theorem tailTrace_6790453 : CollatzResearch.WordTrace tailWord_6790453 prefixEnd_6790453 129139490769075039078103 := by
  unfold tailWord_6790453
  simp only [CollatzResearch.WordTrace]
  refine ⟨247668167668355972887720013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165112111778903981925146675 247668167668355972887720013)
  ·
    refine ⟨92875562875633489832895005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247668167668355972887720013 92875562875633489832895005)
    ·
      refine ⟨34828336078362558687335627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92875562875633489832895005 34828336078362558687335627)
      ·
        refine ⟨52242504117543838031003441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34828336078362558687335627 52242504117543838031003441)
        ·
          refine ⟨39181878088157878523252581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52242504117543838031003441 39181878088157878523252581)
          ·
            refine ⟨7346602141529602223109859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39181878088157878523252581 7346602141529602223109859)
            ·
              refine ⟨11019903212294403334664789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7346602141529602223109859 11019903212294403334664789)
              ·
                refine ⟨129139490769075039078103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11019903212294403334664789 129139490769075039078103)
                ·
                  rfl

theorem cell23_6790453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 8].length) (baseStart_6790453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790453 prefixEnd_6790453 := by exact prefixLift 6790453
  have htrace : WordTrace (prefixWord ++ tailWord_6790453) baseStart_6790453 baseEnd_6790453 := by
    simpa [prefixWord, tailWord_6790453, baseEnd_6790453] using wordTrace_append hprefix tailTrace_6790453
  have hstable : (prefixWord ++ tailWord_6790453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790453).length < 2 ^ (prefixWord ++ tailWord_6790453).sum := by decide
  have hdescent : baseEnd_6790453 < baseStart_6790453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790463 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 3]
def baseStart_6790463 : Nat := 118140960795 + 6790463 * 2 ^ 59
def prefixEnd_6790463 : Nat := 4983230072969 + 3 ^ 40 * 6790463 * 2
def baseEnd_6790463 : Nat := 3486771385571571015983735

theorem tailTrace_6790463 : CollatzResearch.WordTrace tailWord_6790463 prefixEnd_6790463 3486771385571571015983735 := by
  unfold tailWord_6790463
  simp only [CollatzResearch.WordTrace]
  refine ⟨247668532398319744595584043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165112354932213163063722695 247668532398319744595584043)
  ·
    refine ⟨371502798597479616893376065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247668532398319744595584043 371502798597479616893376065)
    ·
      refine ⟨278627098948109712670032049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371502798597479616893376065 278627098948109712670032049)
      ·
        refine ⟨208970324211082284502524037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278627098948109712670032049 208970324211082284502524037)
        ·
          refine ⟨39181935789577928344223257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208970324211082284502524037 39181935789577928344223257)
          ·
            refine ⟨29386451842183446258167443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39181935789577928344223257 29386451842183446258167443)
            ·
              refine ⟨44079677763275169387251165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29386451842183446258167443 44079677763275169387251165)
              ·
                refine ⟨16529879161228188520219187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44079677763275169387251165 16529879161228188520219187)
                ·
                  refine ⟨24794818741842282780328781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16529879161228188520219187 24794818741842282780328781)
                  ·
                    refine ⟨9298057028190856042623293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24794818741842282780328781 9298057028190856042623293)
                    ·
                      refine ⟨3486771385571571015983735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9298057028190856042623293 3486771385571571015983735)
                      ·
                        rfl

theorem cell23_6790463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_6790463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790463 prefixEnd_6790463 := by exact prefixLift 6790463
  have htrace : WordTrace (prefixWord ++ tailWord_6790463) baseStart_6790463 baseEnd_6790463 := by
    simpa [prefixWord, tailWord_6790463, baseEnd_6790463] using wordTrace_append hprefix tailTrace_6790463
  have hstable : (prefixWord ++ tailWord_6790463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790463).length < 2 ^ (prefixWord ++ tailWord_6790463).sum := by decide
  have hdescent : baseEnd_6790463 < baseStart_6790463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790613 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_6790613 : Nat := 118140960795 + 6790613 * 2 ^ 59
def prefixEnd_6790613 : Nat := 4983230072969 + 3 ^ 40 * 6790613 * 2
def baseEnd_6790613 : Nat := 3486848407669745429108045

theorem tailTrace_6790613 : CollatzResearch.WordTrace tailWord_6790613 prefixEnd_6790613 3486848407669745429108045 := by
  unfold tailWord_6790613
  simp only [CollatzResearch.WordTrace]
  refine ⟨247674003347776320213544493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165116002231850880142362995 247674003347776320213544493)
  ·
    refine ⟨92877751255416120080079185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247674003347776320213544493 92877751255416120080079185)
    ·
      refine ⟨69658313441562090060059389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92877751255416120080079185 69658313441562090060059389)
      ·
        refine ⟨26121867540585783772522271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69658313441562090060059389 26121867540585783772522271)
        ·
          refine ⟨39182801310878675658783407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26121867540585783772522271 39182801310878675658783407)
          ·
            refine ⟨58774201966318013488175111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39182801310878675658783407 58774201966318013488175111)
            ·
              refine ⟨88161302949477020232262667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58774201966318013488175111 88161302949477020232262667)
              ·
                refine ⟨132241954424215530348394001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88161302949477020232262667 132241954424215530348394001)
                ·
                  refine ⟨99181465818161647761295501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132241954424215530348394001 99181465818161647761295501)
                  ·
                    refine ⟨37193049681810617910485813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99181465818161647761295501 37193049681810617910485813)
                    ·
                      refine ⟨3486848407669745429108045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37193049681810617910485813 3486848407669745429108045)
                      ·
                        rfl

theorem cell23_6790613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_6790613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790613 prefixEnd_6790613 := by exact prefixLift 6790613
  have htrace : WordTrace (prefixWord ++ tailWord_6790613) baseStart_6790613 baseEnd_6790613 := by
    simpa [prefixWord, tailWord_6790613, baseEnd_6790613] using wordTrace_append hprefix tailTrace_6790613
  have hstable : (prefixWord ++ tailWord_6790613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790613).length < 2 ^ (prefixWord ++ tailWord_6790613).sum := by decide
  have hdescent : baseEnd_6790613 < baseStart_6790613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790627 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 2, 4, 2]
def baseStart_6790627 : Nat := 118140960795 + 6790627 * 2 ^ 59
def prefixEnd_6790627 : Nat := 4983230072969 + 3 ^ 40 * 6790627 * 2
def baseEnd_6790627 : Nat := 3486855596398908374332981

theorem tailTrace_6790627 : CollatzResearch.WordTrace tailWord_6790627 prefixEnd_6790627 3486855596398908374332981 := by
  unfold tailWord_6790627
  simp only [CollatzResearch.WordTrace]
  refine ⟨247674513969725600604554135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165116342646483733736369423 247674513969725600604554135)
  ·
    refine ⟨371511770954588400906831203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247674513969725600604554135 371511770954588400906831203)
    ·
      refine ⟨557267656431882601360246805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371511770954588400906831203 557267656431882601360246805)
      ·
        refine ⟨26121921395244496938761569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 557267656431882601360246805 26121921395244496938761569)
        ·
          refine ⟨19591441046433372704071177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26121921395244496938761569 19591441046433372704071177)
          ·
            refine ⟨14693580784825029528053383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19591441046433372704071177 14693580784825029528053383)
            ·
              refine ⟨22040371177237544292080075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14693580784825029528053383 22040371177237544292080075)
              ·
                refine ⟨33060556765856316438120113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22040371177237544292080075 33060556765856316438120113)
                ·
                  refine ⟨24795417574392237328590085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33060556765856316438120113 24795417574392237328590085)
                  ·
                    refine ⟨4649140795198544499110641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24795417574392237328590085 4649140795198544499110641)
                    ·
                      refine ⟨3486855596398908374332981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4649140795198544499110641 3486855596398908374332981)
                      ·
                        rfl

theorem cell23_6790627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_6790627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790627 prefixEnd_6790627 := by exact prefixLift 6790627
  have htrace : WordTrace (prefixWord ++ tailWord_6790627) baseStart_6790627 baseEnd_6790627 := by
    simpa [prefixWord, tailWord_6790627, baseEnd_6790627] using wordTrace_append hprefix tailTrace_6790627
  have hstable : (prefixWord ++ tailWord_6790627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790627).length < 2 ^ (prefixWord ++ tailWord_6790627).sum := by decide
  have hdescent : baseEnd_6790627 < baseStart_6790627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790643 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 3]
def baseStart_6790643 : Nat := 118140960795 + 6790643 * 2 ^ 59
def prefixEnd_6790643 : Nat := 4983230072969 + 3 ^ 40 * 6790643 * 2
def baseEnd_6790643 : Nat := 3486863812089380311732907

theorem tailTrace_6790643 : CollatzResearch.WordTrace tailWord_6790643 prefixEnd_6790643 3486863812089380311732907 := by
  unfold tailWord_6790643
  simp only [CollatzResearch.WordTrace]
  refine ⟨247675097537667635337136583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165116731691778423558091055 247675097537667635337136583)
  ·
    refine ⟨371512646306501453005704875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247675097537667635337136583 371512646306501453005704875)
    ·
      refine ⟨557268969459752179508557313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371512646306501453005704875 557268969459752179508557313)
      ·
        refine ⟨417951727094814134631417985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557268969459752179508557313 417951727094814134631417985)
        ·
          refine ⟨313463795321110600973563489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417951727094814134631417985 313463795321110600973563489)
          ·
            refine ⟨235097846490832950730172617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313463795321110600973563489 235097846490832950730172617)
            ·
              refine ⟨176323384868124713047629463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235097846490832950730172617 176323384868124713047629463)
              ·
                refine ⟨264485077302187069571444195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176323384868124713047629463 264485077302187069571444195)
                ·
                  refine ⟨396727615953280604357166293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264485077302187069571444195 396727615953280604357166293)
                  ·
                    refine ⟨9298303498905014164621085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 396727615953280604357166293 9298303498905014164621085)
                    ·
                      refine ⟨3486863812089380311732907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9298303498905014164621085 3486863812089380311732907)
                      ·
                        rfl

theorem cell23_6790643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 3].length) (baseStart_6790643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790643 prefixEnd_6790643 := by exact prefixLift 6790643
  have htrace : WordTrace (prefixWord ++ tailWord_6790643) baseStart_6790643 baseEnd_6790643 := by
    simpa [prefixWord, tailWord_6790643, baseEnd_6790643] using wordTrace_append hprefix tailTrace_6790643
  have hstable : (prefixWord ++ tailWord_6790643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790643).length < 2 ^ (prefixWord ++ tailWord_6790643).sum := by decide
  have hdescent : baseEnd_6790643 < baseStart_6790643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790667 : List Nat := [1, 1, 1, 1, 8, 2, 1, 2, 6]
def baseStart_6790667 : Nat := 118140960795 + 6790667 * 2 ^ 59
def prefixEnd_6790667 : Nat := 4983230072969 + 3 ^ 40 * 6790667 * 2
def baseEnd_6790667 : Nat := 387430681736120913092533

theorem tailTrace_6790667 : CollatzResearch.WordTrace tailWord_6790667 prefixEnd_6790667 387430681736120913092533 := by
  unfold tailWord_6790667
  simp only [CollatzResearch.WordTrace]
  refine ⟨247675972889580687436010255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165117315259720458290673503 247675972889580687436010255)
  ·
    refine ⟨371513959334371031154015383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247675972889580687436010255 371513959334371031154015383)
    ·
      refine ⟨557270939001556546731023075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371513959334371031154015383 557270939001556546731023075)
      ·
        refine ⟨835906408502334820096534613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557270939001556546731023075 835906408502334820096534613)
        ·
          refine ⟨9795778224636736173006265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 835906408502334820096534613 9795778224636736173006265)
          ·
            refine ⟨7346833668477552129754699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9795778224636736173006265 7346833668477552129754699)
            ·
              refine ⟨11020250502716328194632049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7346833668477552129754699 11020250502716328194632049)
              ·
                refine ⟨8265187877037246145974037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11020250502716328194632049 8265187877037246145974037)
                ·
                  refine ⟨387430681736120913092533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8265187877037246145974037 387430681736120913092533)
                  ·
                    rfl

theorem cell23_6790667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 6].length) (baseStart_6790667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790667 prefixEnd_6790667 := by exact prefixLift 6790667
  have htrace : WordTrace (prefixWord ++ tailWord_6790667) baseStart_6790667 baseEnd_6790667 := by
    simpa [prefixWord, tailWord_6790667, baseEnd_6790667] using wordTrace_append hprefix tailTrace_6790667
  have hstable : (prefixWord ++ tailWord_6790667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790667).length < 2 ^ (prefixWord ++ tailWord_6790667).sum := by decide
  have hdescent : baseEnd_6790667 < baseStart_6790667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790677 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 3, 1, 3]
def baseStart_6790677 : Nat := 118140960795 + 6790677 * 2 ^ 59
def prefixEnd_6790677 : Nat := 4983230072969 + 3 ^ 40 * 6790677 * 2
def baseEnd_6790677 : Nat := 3486881270431633178707751

theorem tailTrace_6790677 : CollatzResearch.WordTrace tailWord_6790677 prefixEnd_6790677 3486881270431633178707751 := by
  unfold tailWord_6790677
  simp only [CollatzResearch.WordTrace]
  refine ⟨247676337619544459143874285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165117558413029639429249523 247676337619544459143874285)
  ·
    refine ⟨92878626607329172178952857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247676337619544459143874285 92878626607329172178952857)
    ·
      refine ⟨69658969955496879134214643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92878626607329172178952857 69658969955496879134214643)
      ·
        refine ⟨104488454933245318701321965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69658969955496879134214643 104488454933245318701321965)
        ·
          refine ⟨39183170599966994512995737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104488454933245318701321965 39183170599966994512995737)
          ·
            refine ⟨29387377949975245884746803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39183170599966994512995737 29387377949975245884746803)
            ·
              refine ⟨44081066924962868827120205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29387377949975245884746803 44081066924962868827120205)
              ·
                refine ⟨16530400096861075810170077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44081066924962868827120205 16530400096861075810170077)
                ·
                  refine ⟨6198900036322903428813779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16530400096861075810170077 6198900036322903428813779)
                  ·
                    refine ⟨9298350054484355143220669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6198900036322903428813779 9298350054484355143220669)
                    ·
                      refine ⟨3486881270431633178707751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9298350054484355143220669 3486881270431633178707751)
                      ·
                        rfl

theorem cell23_6790677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_6790677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790677 prefixEnd_6790677 := by exact prefixLift 6790677
  have htrace : WordTrace (prefixWord ++ tailWord_6790677) baseStart_6790677 baseEnd_6790677 := by
    simpa [prefixWord, tailWord_6790677, baseEnd_6790677] using wordTrace_append hprefix tailTrace_6790677
  have hstable : (prefixWord ++ tailWord_6790677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790677).length < 2 ^ (prefixWord ++ tailWord_6790677).sum := by decide
  have hdescent : baseEnd_6790677 < baseStart_6790677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790711 : List Nat := [1, 1, 3, 1, 2, 6, 1, 3, 1, 1, 3]
def baseStart_6790711 : Nat := 118140960795 + 6790711 * 2 ^ 59
def prefixEnd_6790711 : Nat := 4983230072969 + 3 ^ 40 * 6790711 * 2
def baseEnd_6790711 : Nat := 3486898728773886045682595

theorem tailTrace_6790711 : CollatzResearch.WordTrace tailWord_6790711 prefixEnd_6790711 3486898728773886045682595 := by
  unfold tailWord_6790711
  simp only [CollatzResearch.WordTrace]
  refine ⟨247677577701421282950611987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165118385134280855300407991 247677577701421282950611987)
  ·
    refine ⟨371516366552131924425917981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247677577701421282950611987 371516366552131924425917981)
    ·
      refine ⟨139318637457049471659719243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371516366552131924425917981 139318637457049471659719243)
      ·
        refine ⟨208977956185574207489578865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139318637457049471659719243 208977956185574207489578865)
        ·
          refine ⟨156733467139180655617184149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208977956185574207489578865 156733467139180655617184149)
          ·
            refine ⟨7346881272149093232055507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 156733467139180655617184149 7346881272149093232055507)
            ·
              refine ⟨11020321908223639848083261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7346881272149093232055507 11020321908223639848083261)
              ·
                refine ⟨4132620715583864943031223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11020321908223639848083261 4132620715583864943031223)
                ·
                  refine ⟨6198931073375797414546835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4132620715583864943031223 6198931073375797414546835)
                  ·
                    refine ⟨9298396610063696121820253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6198931073375797414546835 9298396610063696121820253)
                    ·
                      refine ⟨3486898728773886045682595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9298396610063696121820253 3486898728773886045682595)
                      ·
                        rfl

theorem cell23_6790711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 1, 1, 3].length) (baseStart_6790711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790711 prefixEnd_6790711 := by exact prefixLift 6790711
  have htrace : WordTrace (prefixWord ++ tailWord_6790711) baseStart_6790711 baseEnd_6790711 := by
    simpa [prefixWord, tailWord_6790711, baseEnd_6790711] using wordTrace_append hprefix tailTrace_6790711
  have hstable : (prefixWord ++ tailWord_6790711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790711).length < 2 ^ (prefixWord ++ tailWord_6790711).sum := by decide
  have hdescent : baseEnd_6790711 < baseStart_6790711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790720 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 3]
def baseStart_6790720 : Nat := 118140960795 + 6790720 * 2 ^ 59
def prefixEnd_6790720 : Nat := 4983230072969 + 3 ^ 40 * 6790720 * 2
def baseEnd_6790720 : Nat := 3486903350099776510470053

theorem tailTrace_6790720 : CollatzResearch.WordTrace tailWord_6790720 prefixEnd_6790720 3486903350099776510470053 := by
  unfold tailWord_6790720
  simp only [CollatzResearch.WordTrace]
  refine ⟨123838952979194338743844807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165118603972259118325126409 123838952979194338743844807)
  ·
    refine ⟨185758429468791508115767211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123838952979194338743844807 185758429468791508115767211)
    ·
      refine ⟨278637644203187262173650817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185758429468791508115767211 278637644203187262173650817)
      ·
        refine ⟨208978233152390446630238113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278637644203187262173650817 208978233152390446630238113)
        ·
          refine ⟨156733674864292834972678585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208978233152390446630238113 156733674864292834972678585)
          ·
            refine ⟨117550256148219626229508939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156733674864292834972678585 117550256148219626229508939)
            ·
              refine ⟨176325384222329439344263409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117550256148219626229508939 176325384222329439344263409)
              ·
                refine ⟨132244038166747079508197557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176325384222329439344263409 132244038166747079508197557)
                ·
                  refine ⟨12397878578132538703893521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132244038166747079508197557 12397878578132538703893521)
                  ·
                    refine ⟨9298408933599404027920141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12397878578132538703893521 9298408933599404027920141)
                    ·
                      refine ⟨3486903350099776510470053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9298408933599404027920141 3486903350099776510470053)
                      ·
                        rfl

theorem cell23_6790720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_6790720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790720 prefixEnd_6790720 := by exact prefixLift 6790720
  have htrace : WordTrace (prefixWord ++ tailWord_6790720) baseStart_6790720 baseEnd_6790720 := by
    simpa [prefixWord, tailWord_6790720, baseEnd_6790720] using wordTrace_append hprefix tailTrace_6790720
  have hstable : (prefixWord ++ tailWord_6790720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790720).length < 2 ^ (prefixWord ++ tailWord_6790720).sum := by decide
  have hdescent : baseEnd_6790720 < baseStart_6790720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790740 : List Nat := [2, 4, 1, 1, 1, 2, 4, 8]
def baseStart_6790740 : Nat := 118140960795 + 6790740 * 2 ^ 59
def prefixEnd_6790740 : Nat := 4983230072969 + 3 ^ 40 * 6790740 * 2
def baseEnd_6790740 : Nat := 129144948878254312304443

theorem tailTrace_6790740 : CollatzResearch.WordTrace tailWord_6790740 prefixEnd_6790740 129144948878254312304443 := by
  unfold tailWord_6790740
  simp only [CollatzResearch.WordTrace]
  refine ⟨123839317709158110451708837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165119090278877480602278449 123839317709158110451708837)
  ·
    refine ⟨23219872070467145709695407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123839317709158110451708837 23219872070467145709695407)
    ·
      refine ⟨34829808105700718564543111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23219872070467145709695407 34829808105700718564543111)
      ·
        refine ⟨52244712158551077846814667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34829808105700718564543111 52244712158551077846814667)
        ·
          refine ⟨78367068237826616770222001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52244712158551077846814667 78367068237826616770222001)
          ·
            refine ⟨58775301178369962577666501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78367068237826616770222001 58775301178369962577666501)
            ·
              refine ⟨11020368970944367983312469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58775301178369962577666501 11020368970944367983312469)
              ·
                refine ⟨129144948878254312304443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11020368970944367983312469 129144948878254312304443)
                ·
                  rfl

theorem cell23_6790740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 8].length) (baseStart_6790740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790740 prefixEnd_6790740 := by exact prefixLift 6790740
  have htrace : WordTrace (prefixWord ++ tailWord_6790740) baseStart_6790740 baseEnd_6790740 := by
    simpa [prefixWord, tailWord_6790740, baseEnd_6790740] using wordTrace_append hprefix tailTrace_6790740
  have hstable : (prefixWord ++ tailWord_6790740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790740).length < 2 ^ (prefixWord ++ tailWord_6790740).sum := by decide
  have hdescent : baseEnd_6790740 < baseStart_6790740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790763 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 7]
def baseStart_6790763 : Nat := 118140960795 + 6790763 * 2 ^ 59
def prefixEnd_6790763 : Nat := 4983230072969 + 3 ^ 40 * 6790763 * 2
def baseEnd_6790763 : Nat := 3486925429767919842232355

theorem tailTrace_6790763 : CollatzResearch.WordTrace tailWord_6790763 prefixEnd_6790763 3486925429767919842232355 := by
  unfold tailWord_6790763
  simp only [CollatzResearch.WordTrace]
  refine ⟨247679474297232895831504943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165119649531488597221003295 247679474297232895831504943)
  ·
    refine ⟨371519211445849343747257415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247679474297232895831504943 371519211445849343747257415)
    ·
      refine ⟨557278817168774015620886123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371519211445849343747257415 557278817168774015620886123)
      ·
        refine ⟨835918225753161023431329185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557278817168774015620886123 835918225753161023431329185)
        ·
          refine ⟨626938669314870767573496889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835918225753161023431329185 626938669314870767573496889)
          ·
            refine ⟨470204001986153075680122667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626938669314870767573496889 470204001986153075680122667)
            ·
              refine ⟨705306002979229613520184001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470204001986153075680122667 705306002979229613520184001)
              ·
                refine ⟨528979502234422210140138001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705306002979229613520184001 528979502234422210140138001)
                ·
                  refine ⟨396734626675816657605103501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528979502234422210140138001 396734626675816657605103501)
                  ·
                    refine ⟨148775485003431246601913813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 396734626675816657605103501 148775485003431246601913813)
                    ·
                      refine ⟨3486925429767919842232355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148775485003431246601913813 3486925429767919842232355)
                      ·
                        rfl

theorem cell23_6790763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 7].length) (baseStart_6790763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790763 prefixEnd_6790763 := by exact prefixLift 6790763
  have htrace : WordTrace (prefixWord ++ tailWord_6790763) baseStart_6790763 baseEnd_6790763 := by
    simpa [prefixWord, tailWord_6790763, baseEnd_6790763] using wordTrace_append hprefix tailTrace_6790763
  have hstable : (prefixWord ++ tailWord_6790763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790763).length < 2 ^ (prefixWord ++ tailWord_6790763).sum := by decide
  have hdescent : baseEnd_6790763 < baseStart_6790763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790784 : List Nat := [2, 1, 1, 2, 1, 4, 4, 2, 2, 1, 3]
def baseStart_6790784 : Nat := 118140960795 + 6790784 * 2 ^ 59
def prefixEnd_6790784 : Nat := 4983230072969 + 3 ^ 40 * 6790784 * 2
def baseEnd_6790784 : Nat := 3486936212861664260069759

theorem tailTrace_6790784 : CollatzResearch.WordTrace tailWord_6790784 prefixEnd_6790784 3486936212861664260069759 := by
  unfold tailWord_6790784
  simp only [CollatzResearch.WordTrace]
  refine ⟨123840120115078408209009703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165120160153437877612012937 123840120115078408209009703)
  ·
    refine ⟨185760180172617612313514555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123840120115078408209009703 185760180172617612313514555)
    ·
      refine ⟨278640270258926418470271833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185760180172617612313514555 278640270258926418470271833)
      ·
        refine ⟨208980202694194813852703875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278640270258926418470271833 208980202694194813852703875)
        ·
          refine ⟨313470304041292220779055813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208980202694194813852703875 313470304041292220779055813)
          ·
            refine ⟨58775682007742291396072965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313470304041292220779055813 58775682007742291396072965)
            ·
              refine ⟨11020440376451679636763681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58775682007742291396072965 11020440376451679636763681)
              ·
                refine ⟨8265330282338759727572761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11020440376451679636763681 8265330282338759727572761)
                ·
                  refine ⟨6198997711754069795679571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8265330282338759727572761 6198997711754069795679571)
                  ·
                    refine ⟨9298496567631104693519357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6198997711754069795679571 9298496567631104693519357)
                    ·
                      refine ⟨3486936212861664260069759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9298496567631104693519357 3486936212861664260069759)
                      ·
                        rfl

theorem cell23_6790784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 2, 1, 3].length) (baseStart_6790784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790784 prefixEnd_6790784 := by exact prefixLift 6790784
  have htrace : WordTrace (prefixWord ++ tailWord_6790784) baseStart_6790784 baseEnd_6790784 := by
    simpa [prefixWord, tailWord_6790784, baseEnd_6790784] using wordTrace_append hprefix tailTrace_6790784
  have hstable : (prefixWord ++ tailWord_6790784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790784).length < 2 ^ (prefixWord ++ tailWord_6790784).sum := by decide
  have hdescent : baseEnd_6790784 < baseStart_6790784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790785 : List Nat := [1, 2, 4, 2, 1, 4, 2, 2, 1, 2, 2]
def baseStart_6790785 : Nat := 118140960795 + 6790785 * 2 ^ 59
def prefixEnd_6790785 : Nat := 4983230072969 + 3 ^ 40 * 6790785 * 2
def baseEnd_6790785 : Nat := 3486936726342318756157255

theorem tailTrace_6790785 : CollatzResearch.WordTrace tailWord_6790785 prefixEnd_6790785 3486936726342318756157255 := by
  unfold tailWord_6790785
  simp only [CollatzResearch.WordTrace]
  refine ⟨247680276703153193588805809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165120184468768795725870539 247680276703153193588805809)
  ·
    refine ⟨185760207527364895191604357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247680276703153193588805809 185760207527364895191604357)
    ·
      refine ⟨34830038911380917848425817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185760207527364895191604357 34830038911380917848425817)
      ·
        refine ⟨26122529183535688386319363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34830038911380917848425817 26122529183535688386319363)
        ·
          refine ⟨39183793775303532579479045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26122529183535688386319363 39183793775303532579479045)
          ·
            refine ⟨7346961332869412358652321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39183793775303532579479045 7346961332869412358652321)
            ·
              refine ⟨5510220999652059268989241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7346961332869412358652321 5510220999652059268989241)
              ·
                refine ⟨4132665749739044451741931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5510220999652059268989241 4132665749739044451741931)
                ·
                  refine ⟨6198998624608566677612897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4132665749739044451741931 6198998624608566677612897)
                  ·
                    refine ⟨4649248968456425008209673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6198998624608566677612897 4649248968456425008209673)
                    ·
                      refine ⟨3486936726342318756157255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4649248968456425008209673 3486936726342318756157255)
                      ·
                        rfl

theorem cell23_6790785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_6790785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790785 prefixEnd_6790785 := by exact prefixLift 6790785
  have htrace : WordTrace (prefixWord ++ tailWord_6790785) baseStart_6790785 baseEnd_6790785 := by
    simpa [prefixWord, tailWord_6790785, baseEnd_6790785] using wordTrace_append hprefix tailTrace_6790785
  have hstable : (prefixWord ++ tailWord_6790785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790785).length < 2 ^ (prefixWord ++ tailWord_6790785).sum := by decide
  have hdescent : baseEnd_6790785 < baseStart_6790785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790794 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 3, 3, 2]
def baseStart_6790794 : Nat := 118140960795 + 6790794 * 2 ^ 59
def prefixEnd_6790794 : Nat := 4983230072969 + 3 ^ 40 * 6790794 * 2
def baseEnd_6790794 : Nat := 3486941347668209220944713

theorem tailTrace_6790794 : CollatzResearch.WordTrace tailWord_6790794 prefixEnd_6790794 3486941347668209220944713 := by
  unfold tailWord_6790794
  simp only [CollatzResearch.WordTrace]
  refine ⟨61920151240030147031470859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165120403306747058750588957 61920151240030147031470859)
  ·
    refine ⟨92880226860045220547206289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61920151240030147031470859 92880226860045220547206289)
    ·
      refine ⟨69660170145033915410404717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92880226860045220547206289 69660170145033915410404717)
      ·
        refine ⟨26122563804387718278901769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69660170145033915410404717 26122563804387718278901769)
        ·
          refine ⟨19591922853290788709176327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26122563804387718278901769 19591922853290788709176327)
          ·
            refine ⟨29387884279936183063764491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19591922853290788709176327 29387884279936183063764491)
            ·
              refine ⟨44081826419904274595646737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29387884279936183063764491 44081826419904274595646737)
              ·
                refine ⟨33061369814928205946735053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44081826419904274595646737 33061369814928205946735053)
                ·
                  refine ⟨12398013680598077230025645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33061369814928205946735053 12398013680598077230025645)
                  ·
                    refine ⟨4649255130224278961259617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12398013680598077230025645 4649255130224278961259617)
                    ·
                      refine ⟨3486941347668209220944713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4649255130224278961259617 3486941347668209220944713)
                      ·
                        rfl

theorem cell23_6790794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_6790794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790794 prefixEnd_6790794 := by exact prefixLift 6790794
  have htrace : WordTrace (prefixWord ++ tailWord_6790794) baseStart_6790794 baseEnd_6790794 := by
    simpa [prefixWord, tailWord_6790794, baseEnd_6790794] using wordTrace_append hprefix tailTrace_6790794
  have hstable : (prefixWord ++ tailWord_6790794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790794).length < 2 ^ (prefixWord ++ tailWord_6790794).sum := by decide
  have hdescent : baseEnd_6790794 < baseStart_6790794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790841 : List Nat := [1, 2, 1, 4, 1, 1, 5, 2, 2, 2, 2]
def baseStart_6790841 : Nat := 118140960795 + 6790841 * 2 ^ 59
def prefixEnd_6790841 : Nat := 4983230072969 + 3 ^ 40 * 6790841 * 2
def baseEnd_6790841 : Nat := 3486965481258970537056997

theorem tailTrace_6790841 : CollatzResearch.WordTrace tailWord_6790841 prefixEnd_6790841 3486965481258970537056997 := by
  unfold tailWord_6790841
  simp only [CollatzResearch.WordTrace]
  refine ⟨247682319190950315152844377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165121546127300210101896251 247682319190950315152844377)
  ·
    refine ⟨185761739393212736364633283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247682319190950315152844377 185761739393212736364633283)
    ·
      refine ⟨278642609089819104546949925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185761739393212736364633283 278642609089819104546949925)
      ·
        refine ⟨52245489204341082102553111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278642609089819104546949925 52245489204341082102553111)
        ·
          refine ⟨78368233806511623153829667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52245489204341082102553111 78368233806511623153829667)
          ·
            refine ⟨117552350709767434730744501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78368233806511623153829667 117552350709767434730744501)
            ·
              refine ⟨11020532879040697006007297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117552350709767434730744501 11020532879040697006007297)
              ·
                refine ⟨8265399659280522754505473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11020532879040697006007297 8265399659280522754505473)
                ·
                  refine ⟨6199049744460392065879105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8265399659280522754505473 6199049744460392065879105)
                  ·
                    refine ⟨4649287308345294049409329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6199049744460392065879105 4649287308345294049409329)
                    ·
                      refine ⟨3486965481258970537056997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4649287308345294049409329 3486965481258970537056997)
                      ·
                        rfl

theorem cell23_6790841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_6790841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790841 prefixEnd_6790841 := by exact prefixLift 6790841
  have htrace : WordTrace (prefixWord ++ tailWord_6790841) baseStart_6790841 baseEnd_6790841 := by
    simpa [prefixWord, tailWord_6790841, baseEnd_6790841] using wordTrace_append hprefix tailTrace_6790841
  have hstable : (prefixWord ++ tailWord_6790841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790841).length < 2 ^ (prefixWord ++ tailWord_6790841).sum := by decide
  have hdescent : baseEnd_6790841 < baseStart_6790841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790847 : List Nat := [1, 1, 2, 2, 2, 3, 1, 6, 5]
def baseStart_6790847 : Nat := 118140960795 + 6790847 * 2 ^ 59
def prefixEnd_6790847 : Nat := 4983230072969 + 3 ^ 40 * 6790847 * 2
def baseEnd_6790847 : Nat := 387440951349210834842441

theorem tailTrace_6790847 : CollatzResearch.WordTrace tailWord_6790847 prefixEnd_6790847 387440951349210834842441 := by
  unfold tailWord_6790847
  simp only [CollatzResearch.WordTrace]
  refine ⟨247682538028928578177562795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165121692019285718785041863 247682538028928578177562795)
  ·
    refine ⟨371523807043392867266344193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247682538028928578177562795 371523807043392867266344193)
    ·
      refine ⟨278642855282544650449758145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371523807043392867266344193 278642855282544650449758145)
      ·
        refine ⟨208982141461908487837318609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278642855282544650449758145 208982141461908487837318609)
        ·
          refine ⟨156736606096431365877988957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208982141461908487837318609 156736606096431365877988957)
          ·
            refine ⟨58776227286161762204245859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156736606096431365877988957 58776227286161762204245859)
            ·
              refine ⟨88164340929242643306368789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58776227286161762204245859 88164340929242643306368789)
              ·
                refine ⟨4132703481058248904986037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88164340929242643306368789 4132703481058248904986037)
                ·
                  refine ⟨387440951349210834842441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4132703481058248904986037 387440951349210834842441)
                  ·
                    rfl

theorem cell23_6790847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 5].length) (baseStart_6790847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790847 prefixEnd_6790847 := by exact prefixLift 6790847
  have htrace : WordTrace (prefixWord ++ tailWord_6790847) baseStart_6790847 baseEnd_6790847 := by
    simpa [prefixWord, tailWord_6790847, baseEnd_6790847] using wordTrace_append hprefix tailTrace_6790847
  have hstable : (prefixWord ++ tailWord_6790847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790847).length < 2 ^ (prefixWord ++ tailWord_6790847).sum := by decide
  have hdescent : baseEnd_6790847 < baseStart_6790847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790858 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 1, 4, 2]
def baseStart_6790858 : Nat := 118140960795 + 6790858 * 2 ^ 59
def prefixEnd_6790858 : Nat := 4983230072969 + 3 ^ 40 * 6790858 * 2
def baseEnd_6790858 : Nat := 3486974210430096970544419

theorem tailTrace_6790858 : CollatzResearch.WordTrace tailWord_6790858 prefixEnd_6790858 3486974210430096970544419 := by
  unfold tailWord_6790858
  simp only [CollatzResearch.WordTrace]
  refine ⟨61920734807972181764053307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165121959487925818037475485 61920734807972181764053307)
  ·
    refine ⟨92881102211958272646079961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61920734807972181764053307 92881102211958272646079961)
    ·
      refine ⟨69660826658968704484559971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92881102211958272646079961 69660826658968704484559971)
      ·
        refine ⟨104491239988453056726839957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69660826658968704484559971 104491239988453056726839957)
        ·
          refine ⟨4898026874458737034070623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104491239988453056726839957 4898026874458737034070623)
          ·
            refine ⟨7347040311688105551105935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4898026874458737034070623 7347040311688105551105935)
            ·
              refine ⟨11020560467532158326658903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7347040311688105551105935 11020560467532158326658903)
              ·
                refine ⟨16530840701298237489988355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11020560467532158326658903 16530840701298237489988355)
                ·
                  refine ⟨24796261051947356234982533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16530840701298237489988355 24796261051947356234982533)
                  ·
                    refine ⟨4649298947240129294059225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24796261051947356234982533 4649298947240129294059225)
                    ·
                      refine ⟨3486974210430096970544419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4649298947240129294059225 3486974210430096970544419)
                      ·
                        rfl

theorem cell23_6790858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_6790858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790858 prefixEnd_6790858 := by exact prefixLift 6790858
  have htrace : WordTrace (prefixWord ++ tailWord_6790858) baseStart_6790858 baseEnd_6790858 := by
    simpa [prefixWord, tailWord_6790858, baseEnd_6790858] using wordTrace_append hprefix tailTrace_6790858
  have hstable : (prefixWord ++ tailWord_6790858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790858).length < 2 ^ (prefixWord ++ tailWord_6790858).sum := by decide
  have hdescent : baseEnd_6790858 < baseStart_6790858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790881 : List Nat := [1, 2, 3, 1, 5, 2, 1, 3, 5]
def baseStart_6790881 : Nat := 118140960795 + 6790881 * 2 ^ 59
def prefixEnd_6790881 : Nat := 4983230072969 + 3 ^ 40 * 6790881 * 2
def baseEnd_6790881 : Nat := 387442891165016708950757

theorem tailTrace_6790881 : CollatzResearch.WordTrace tailWord_6790881 prefixEnd_6790881 387442891165016708950757 := by
  unfold tailWord_6790881
  simp only [CollatzResearch.WordTrace]
  refine ⟨247683778110805401984300497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165122518740536934656200331 247683778110805401984300497)
  ·
    refine ⟨185762833583104051488225373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247683778110805401984300497 185762833583104051488225373)
    ·
      refine ⟨69661062593664019308084515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185762833583104051488225373 69661062593664019308084515)
      ·
        refine ⟨104491593890496028962126773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69661062593664019308084515 104491593890496028962126773)
        ·
          refine ⟨9796086927234002715199385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104491593890496028962126773 9796086927234002715199385)
          ·
            refine ⟨7347065195425502036399539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9796086927234002715199385 7347065195425502036399539)
            ·
              refine ⟨11020597793138253054599309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7347065195425502036399539 11020597793138253054599309)
              ·
                refine ⟨4132724172426844895474741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11020597793138253054599309 4132724172426844895474741)
                ·
                  refine ⟨387442891165016708950757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4132724172426844895474741 387442891165016708950757)
                  ·
                    rfl

theorem cell23_6790881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 5].length) (baseStart_6790881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790881 prefixEnd_6790881 := by exact prefixLift 6790881
  have htrace : WordTrace (prefixWord ++ tailWord_6790881) baseStart_6790881 baseEnd_6790881 := by
    simpa [prefixWord, tailWord_6790881, baseEnd_6790881] using wordTrace_append hprefix tailTrace_6790881
  have hstable : (prefixWord ++ tailWord_6790881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790881).length < 2 ^ (prefixWord ++ tailWord_6790881).sum := by decide
  have hdescent : baseEnd_6790881 < baseStart_6790881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790897 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 4, 1, 4]
def baseStart_6790897 : Nat := 118140960795 + 6790897 * 2 ^ 59
def prefixEnd_6790897 : Nat := 4983230072969 + 3 ^ 40 * 6790897 * 2
def baseEnd_6790897 : Nat := 3486994236175622317956739

theorem tailTrace_6790897 : CollatzResearch.WordTrace tailWord_6790897 prefixEnd_6790897 3486994236175622317956739 := by
  unfold tailWord_6790897
  simp only [CollatzResearch.WordTrace]
  refine ⟨247684361678747436716882945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165122907785831624477921963 247684361678747436716882945)
  ·
    refine ⟨185763271259060577537662209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247684361678747436716882945 185763271259060577537662209)
    ·
      refine ⟨139322453444295433153246657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185763271259060577537662209 139322453444295433153246657)
      ·
        refine ⟨104491840083221574864934993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139322453444295433153246657 104491840083221574864934993)
        ·
          refine ⟨78368880062416181148701245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104491840083221574864934993 78368880062416181148701245)
          ·
            refine ⟨29388330023406067930762967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78368880062416181148701245 29388330023406067930762967)
            ·
              refine ⟨44082495035109101896144451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29388330023406067930762967 44082495035109101896144451)
              ·
                refine ⟨66123742552663652844216677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44082495035109101896144451 66123742552663652844216677)
                ·
                  refine ⟨12398201728624434908290627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66123742552663652844216677 12398201728624434908290627)
                  ·
                    refine ⟨18597302592936652362435941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12398201728624434908290627 18597302592936652362435941)
                    ·
                      refine ⟨3486994236175622317956739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18597302592936652362435941 3486994236175622317956739)
                      ·
                        rfl

theorem cell23_6790897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_6790897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790897 prefixEnd_6790897 := by exact prefixLift 6790897
  have htrace : WordTrace (prefixWord ++ tailWord_6790897) baseStart_6790897 baseEnd_6790897 := by
    simpa [prefixWord, tailWord_6790897, baseEnd_6790897] using wordTrace_append hprefix tailTrace_6790897
  have hstable : (prefixWord ++ tailWord_6790897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790897).length < 2 ^ (prefixWord ++ tailWord_6790897).sum := by decide
  have hdescent : baseEnd_6790897 < baseStart_6790897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790907 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 3, 4]
def baseStart_6790907 : Nat := 118140960795 + 6790907 * 2 ^ 59
def prefixEnd_6790907 : Nat := 4983230072969 + 3 ^ 40 * 6790907 * 2
def baseEnd_6790907 : Nat := 1162333123660722426277231

theorem tailTrace_6790907 : CollatzResearch.WordTrace tailWord_6790907 prefixEnd_6790907 1162333123660722426277231 := by
  unfold tailWord_6790907
  simp only [CollatzResearch.WordTrace]
  refine ⟨247684726408711208424746975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165123150939140805616497983 247684726408711208424746975)
  ·
    refine ⟨371527089613066812637120463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247684726408711208424746975 371527089613066812637120463)
    ·
      refine ⟨557290634419600218955680695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371527089613066812637120463 557290634419600218955680695)
      ·
        refine ⟨835935951629400328433521043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557290634419600218955680695 835935951629400328433521043)
        ·
          refine ⟨1253903927444100492650281565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835935951629400328433521043 1253903927444100492650281565)
          ·
            refine ⟨470213972791537684743855587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1253903927444100492650281565 470213972791537684743855587)
            ·
              refine ⟨705320959187306527115783381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470213972791537684743855587 705320959187306527115783381)
              ·
                refine ⟨16530959980952496729276173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 705320959187306527115783381 16530959980952496729276173)
                ·
                  refine ⟨6199109992857186273478565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16530959980952496729276173 6199109992857186273478565)
                  ·
                    refine ⟨1162333123660722426277231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6199109992857186273478565 1162333123660722426277231)
                    ·
                      rfl

theorem cell23_6790907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 4].length) (baseStart_6790907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790907 prefixEnd_6790907 := by exact prefixLift 6790907
  have htrace : WordTrace (prefixWord ++ tailWord_6790907) baseStart_6790907 baseEnd_6790907 := by
    simpa [prefixWord, tailWord_6790907, baseEnd_6790907] using wordTrace_append hprefix tailTrace_6790907
  have hstable : (prefixWord ++ tailWord_6790907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790907).length < 2 ^ (prefixWord ++ tailWord_6790907).sum := by decide
  have hdescent : baseEnd_6790907 < baseStart_6790907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6790914 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_6790914 : Nat := 118140960795 + 6790914 * 2 ^ 59
def prefixEnd_6790914 : Nat := 4983230072969 + 3 ^ 40 * 6790914 * 2
def baseEnd_6790914 : Nat := 3487002965346748751444161

theorem tailTrace_6790914 : CollatzResearch.WordTrace tailWord_6790914 prefixEnd_6790914 3487002965346748751444161 := by
  unfold tailWord_6790914
  simp only [CollatzResearch.WordTrace]
  refine ⟨61921245429921462155062949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165123321146457232413501197 61921245429921462155062949)
  ·
    refine ⟨11610233518110274154074303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61921245429921462155062949 11610233518110274154074303)
    ·
      refine ⟨17415350277165411231111455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11610233518110274154074303 17415350277165411231111455)
      ·
        refine ⟨26123025415748116846667183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17415350277165411231111455 26123025415748116846667183)
        ·
          refine ⟨39184538123622175270000775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26123025415748116846667183 39184538123622175270000775)
          ·
            refine ⟨58776807185433262905001163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39184538123622175270000775 58776807185433262905001163)
            ·
              refine ⟨88165210778149894357501745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58776807185433262905001163 88165210778149894357501745)
              ·
                refine ⟨66123908083612420768126309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88165210778149894357501745 66123908083612420768126309)
                ·
                  refine ⟨12398232765677328894023683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66123908083612420768126309 12398232765677328894023683)
                  ·
                    refine ⟨18597349148515993341035525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12398232765677328894023683 18597349148515993341035525)
                    ·
                      refine ⟨3487002965346748751444161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18597349148515993341035525 3487002965346748751444161)
                      ·
                        rfl

theorem cell23_6790914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_6790914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6790914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6790914 prefixEnd_6790914 := by exact prefixLift 6790914
  have htrace : WordTrace (prefixWord ++ tailWord_6790914) baseStart_6790914 baseEnd_6790914 := by
    simpa [prefixWord, tailWord_6790914, baseEnd_6790914] using wordTrace_append hprefix tailTrace_6790914
  have hstable : (prefixWord ++ tailWord_6790914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6790914).length < 2 ^ (prefixWord ++ tailWord_6790914).sum := by decide
  have hdescent : baseEnd_6790914 < baseStart_6790914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6790914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791017 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 3, 2, 4]
def baseStart_6791017 : Nat := 118140960795 + 6791017 * 2 ^ 59
def prefixEnd_6791017 : Nat := 4983230072969 + 3 ^ 40 * 6791017 * 2
def baseEnd_6791017 : Nat := 3487055853854161848456187

theorem tailTrace_6791017 : CollatzResearch.WordTrace tailWord_6791017 prefixEnd_6791017 3487055853854161848456187 := by
  unfold tailWord_6791017
  simp only [CollatzResearch.WordTrace]
  refine ⟨247688738438312697211251305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165125825625541798140834203 247688738438312697211251305)
  ·
    refine ⟨185766553828734522908438479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247688738438312697211251305 185766553828734522908438479)
    ·
      refine ⟨278649830743101784362657719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185766553828734522908438479 278649830743101784362657719)
      ·
        refine ⟨417974746114652676543986579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278649830743101784362657719 417974746114652676543986579)
        ·
          refine ⟨626962119171979014815979869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417974746114652676543986579 626962119171979014815979869)
          ·
            refine ⟨235110794689492130555992451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 626962119171979014815979869 235110794689492130555992451)
            ·
              refine ⟨352666192034238195833988677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235110794689492130555992451 352666192034238195833988677)
              ·
                refine ⟨66124911006419661718872877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352666192034238195833988677 66124911006419661718872877)
                ·
                  refine ⟨24796841627407373144577329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66124911006419661718872877 24796841627407373144577329)
                  ·
                    refine ⟨18597631220555529858432997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24796841627407373144577329 18597631220555529858432997)
                    ·
                      refine ⟨3487055853854161848456187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18597631220555529858432997 3487055853854161848456187)
                      ·
                        rfl

theorem cell23_6791017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_6791017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791017 prefixEnd_6791017 := by exact prefixLift 6791017
  have htrace : WordTrace (prefixWord ++ tailWord_6791017) baseStart_6791017 baseEnd_6791017 := by
    simpa [prefixWord, tailWord_6791017, baseEnd_6791017] using wordTrace_append hprefix tailTrace_6791017
  have hstable : (prefixWord ++ tailWord_6791017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791017).length < 2 ^ (prefixWord ++ tailWord_6791017).sum := by decide
  have hdescent : baseEnd_6791017 < baseStart_6791017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791034 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4]
def baseStart_6791034 : Nat := 118140960795 + 6791034 * 2 ^ 59
def prefixEnd_6791034 : Nat := 4983230072969 + 3 ^ 40 * 6791034 * 2
def baseEnd_6791034 : Nat := 3487064583025288281943609

theorem tailTrace_6791034 : CollatzResearch.WordTrace tailWord_6791034 prefixEnd_6791034 3487064583025288281943609 := by
  unfold tailWord_6791034
  simp only [CollatzResearch.WordTrace]
  refine ⟨61922339619812777278655039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165126238986167406076413437 61922339619812777278655039)
  ·
    refine ⟨92883509429719165917982559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61922339619812777278655039 92883509429719165917982559)
    ·
      refine ⟨139325264144578748876973839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92883509429719165917982559 139325264144578748876973839)
      ·
        refine ⟨208987896216868123315460759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139325264144578748876973839 208987896216868123315460759)
        ·
          refine ⟨313481844325302184973191139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208987896216868123315460759 313481844325302184973191139)
          ·
            refine ⟨470222766487953277459786709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313481844325302184973191139 470222766487953277459786709)
            ·
              refine ⟨11020846089561404940463751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 470222766487953277459786709 11020846089561404940463751)
              ·
                refine ⟨16531269134342107410695627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11020846089561404940463751 16531269134342107410695627)
                ·
                  refine ⟨24796903701513161116043441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16531269134342107410695627 24796903701513161116043441)
                  ·
                    refine ⟨18597677776134870837032581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24796903701513161116043441 18597677776134870837032581)
                    ·
                      refine ⟨3487064583025288281943609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18597677776134870837032581 3487064583025288281943609)
                      ·
                        rfl

theorem cell23_6791034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_6791034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791034 prefixEnd_6791034 := by exact prefixLift 6791034
  have htrace : WordTrace (prefixWord ++ tailWord_6791034) baseStart_6791034 baseEnd_6791034 := by
    simpa [prefixWord, tailWord_6791034, baseEnd_6791034] using wordTrace_append hprefix tailTrace_6791034
  have hstable : (prefixWord ++ tailWord_6791034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791034).length < 2 ^ (prefixWord ++ tailWord_6791034).sum := by decide
  have hdescent : baseEnd_6791034 < baseStart_6791034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791038 : List Nat := [4, 2, 3, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_6791038 : Nat := 118140960795 + 6791038 * 2 ^ 59
def prefixEnd_6791038 : Nat := 4983230072969 + 3 ^ 40 * 6791038 * 2
def baseEnd_6791038 : Nat := 3487066636947906266293591

theorem tailTrace_6791038 : CollatzResearch.WordTrace tailWord_6791038 prefixEnd_6791038 3487066636947906266293591 := by
  unfold tailWord_6791038
  simp only [CollatzResearch.WordTrace]
  refine ⟨30961188046404577224720721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165126336247491078531843845 30961188046404577224720721)
  ·
    refine ⟨23220891034803432918540541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30961188046404577224720721 23220891034803432918540541)
    ·
      refine ⟨8707834138051287344452703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23220891034803432918540541 8707834138051287344452703)
      ·
        refine ⟨13061751207076931016679055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8707834138051287344452703 13061751207076931016679055)
        ·
          refine ⟨19592626810615396525018583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13061751207076931016679055 19592626810615396525018583)
          ·
            refine ⟨29388940215923094787527875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19592626810615396525018583 29388940215923094787527875)
            ·
              refine ⟨44083410323884642181291813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29388940215923094787527875 44083410323884642181291813)
              ·
                refine ⟨8265639435728370408992215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44083410323884642181291813 8265639435728370408992215)
                ·
                  refine ⟨12398459153592555613488323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8265639435728370408992215 12398459153592555613488323)
                  ·
                    refine ⟨18597688730388833420232485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12398459153592555613488323 18597688730388833420232485)
                    ·
                      refine ⟨3487066636947906266293591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18597688730388833420232485 3487066636947906266293591)
                      ·
                        rfl

theorem cell23_6791038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_6791038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791038 prefixEnd_6791038 := by exact prefixLift 6791038
  have htrace : WordTrace (prefixWord ++ tailWord_6791038) baseStart_6791038 baseEnd_6791038 := by
    simpa [prefixWord, tailWord_6791038, baseEnd_6791038] using wordTrace_append hprefix tailTrace_6791038
  have hstable : (prefixWord ++ tailWord_6791038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791038).length < 2 ^ (prefixWord ++ tailWord_6791038).sum := by decide
  have hdescent : baseEnd_6791038 < baseStart_6791038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791044 : List Nat := [2, 3, 2, 1, 1, 1, 6, 7]
def baseStart_6791044 : Nat := 118140960795 + 6791044 * 2 ^ 59
def prefixEnd_6791044 : Nat := 4983230072969 + 3 ^ 40 * 6791044 * 2
def baseEnd_6791044 : Nat := 129150730290067897882169

theorem tailTrace_6791044 : CollatzResearch.WordTrace tailWord_6791044 prefixEnd_6791044 129150730290067897882169 := by
  unfold tailWord_6791044
  simp only [CollatzResearch.WordTrace]
  refine ⟨123844861604607440411242093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165126482139476587214989457 123844861604607440411242093)
  ·
    refine ⟨46441823101727790154215785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123844861604607440411242093 46441823101727790154215785)
    ·
      refine ⟨34831367326295842615661839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46441823101727790154215785 34831367326295842615661839)
      ·
        refine ⟨52247050989443763923492759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34831367326295842615661839 52247050989443763923492759)
        ·
          refine ⟨78370576484165645885239139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52247050989443763923492759 78370576484165645885239139)
          ·
            refine ⟨117555864726248468827858709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78370576484165645885239139 117555864726248468827858709)
            ·
              refine ⟨5510431159042896976305877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117555864726248468827858709 5510431159042896976305877)
              ·
                refine ⟨129150730290067897882169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5510431159042896976305877 129150730290067897882169)
                ·
                  rfl

theorem cell23_6791044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 7].length) (baseStart_6791044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791044 prefixEnd_6791044 := by exact prefixLift 6791044
  have htrace : WordTrace (prefixWord ++ tailWord_6791044) baseStart_6791044 baseEnd_6791044 := by
    simpa [prefixWord, tailWord_6791044, baseEnd_6791044] using wordTrace_append hprefix tailTrace_6791044
  have hstable : (prefixWord ++ tailWord_6791044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791044).length < 2 ^ (prefixWord ++ tailWord_6791044).sum := by decide
  have hdescent : baseEnd_6791044 < baseStart_6791044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791058 : List Nat := [3, 2, 3, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_6791058 : Nat := 118140960795 + 6791058 * 2 ^ 59
def prefixEnd_6791058 : Nat := 4983230072969 + 3 ^ 40 * 6791058 * 2
def baseEnd_6791058 : Nat := 3487076906560996188043499

theorem tailTrace_6791058 : CollatzResearch.WordTrace tailWord_6791058 prefixEnd_6791058 3487076906560996188043499 := by
  unfold tailWord_6791058
  simp only [CollatzResearch.WordTrace]
  refine ⟨61922558457791040303373457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165126822554109440808995885 61922558457791040303373457)
  ·
    refine ⟨46441918843343280227530093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61922558457791040303373457 46441918843343280227530093)
    ·
      refine ⟨17415719566253730085323785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46441918843343280227530093 17415719566253730085323785)
      ·
        refine ⟨13061789674690297563992839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17415719566253730085323785 13061789674690297563992839)
        ·
          refine ⟨19592684512035446345989259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13061789674690297563992839 19592684512035446345989259)
          ·
            refine ⟨29389026768053169518983889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19592684512035446345989259 29389026768053169518983889)
            ·
              refine ⟨22041770076039877139237917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29389026768053169518983889 22041770076039877139237917)
              ·
                refine ⟨8265663778514953927214219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22041770076039877139237917 8265663778514953927214219)
                ·
                  refine ⟨12398495667772430890821329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8265663778514953927214219 12398495667772430890821329)
                  ·
                    refine ⟨9298871750829323168115997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12398495667772430890821329 9298871750829323168115997)
                    ·
                      refine ⟨3487076906560996188043499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9298871750829323168115997 3487076906560996188043499)
                      ·
                        rfl

theorem cell23_6791058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_6791058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791058 prefixEnd_6791058 := by exact prefixLift 6791058
  have htrace : WordTrace (prefixWord ++ tailWord_6791058) baseStart_6791058 baseEnd_6791058 := by
    simpa [prefixWord, tailWord_6791058, baseEnd_6791058] using wordTrace_append hprefix tailTrace_6791058
  have hstable : (prefixWord ++ tailWord_6791058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791058).length < 2 ^ (prefixWord ++ tailWord_6791058).sum := by decide
  have hdescent : baseEnd_6791058 < baseStart_6791058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791087 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 1, 8]
def baseStart_6791087 : Nat := 118140960795 + 6791087 * 2 ^ 59
def prefixEnd_6791087 : Nat := 4983230072969 + 3 ^ 40 * 6791087 * 2
def baseEnd_6791087 : Nat := 1162363932499992191526955

theorem tailTrace_6791087 : CollatzResearch.WordTrace tailWord_6791087 prefixEnd_6791087 1162363932499992191526955 := by
  unfold tailWord_6791087
  simp only [CollatzResearch.WordTrace]
  refine ⟨247691291548059099166299515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165127527698706066110866343 247691291548059099166299515)
  ·
    refine ⟨371536937322088648749449273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247691291548059099166299515 371536937322088648749449273)
    ·
      refine ⟨278652702991566486562086955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371536937322088648749449273 278652702991566486562086955)
      ·
        refine ⟨417979054487349729843130433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278652702991566486562086955 417979054487349729843130433)
        ·
          refine ⟨313484290865512297382347825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417979054487349729843130433 313484290865512297382347825)
          ·
            refine ⟨235113218149134223036760869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313484290865512297382347825 235113218149134223036760869)
            ·
              refine ⟨44083728402962666819392663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235113218149134223036760869 44083728402962666819392663)
              ·
                refine ⟨66125592604444000229088995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44083728402962666819392663 66125592604444000229088995)
                ·
                  refine ⟨99188388906666000343633493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66125592604444000229088995 99188388906666000343633493)
                  ·
                    refine ⟨1162363932499992191526955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99188388906666000343633493 1162363932499992191526955)
                    ·
                      rfl

theorem cell23_6791087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 8].length) (baseStart_6791087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791087 prefixEnd_6791087 := by exact prefixLift 6791087
  have htrace : WordTrace (prefixWord ++ tailWord_6791087) baseStart_6791087 baseEnd_6791087 := by
    simpa [prefixWord, tailWord_6791087, baseEnd_6791087] using wordTrace_append hprefix tailTrace_6791087
  have hstable : (prefixWord ++ tailWord_6791087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791087).length < 2 ^ (prefixWord ++ tailWord_6791087).sum := by decide
  have hdescent : baseEnd_6791087 < baseStart_6791087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791092 : List Nat := [2, 5, 2, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_6791092 : Nat := 118140960795 + 6791092 * 2 ^ 59
def prefixEnd_6791092 : Nat := 4983230072969 + 3 ^ 40 * 6791092 * 2
def baseEnd_6791092 : Nat := 3487094364903249055018343

theorem tailTrace_6791092 : CollatzResearch.WordTrace tailWord_6791092 prefixEnd_6791092 3487094364903249055018343 := by
  unfold tailWord_6791092
  simp only [CollatzResearch.WordTrace]
  refine ⟨123845736956520492510115765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165127649275360656680154353 123845736956520492510115765)
  ·
    refine ⟨11610537839673796172823353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123845736956520492510115765 11610537839673796172823353)
    ·
      refine ⟨8707903379755347129617515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11610537839673796172823353 8707903379755347129617515)
      ·
        refine ⟨13061855069633020694426273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8707903379755347129617515 13061855069633020694426273)
        ·
          refine ⟨9796391302224765520819705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13061855069633020694426273 9796391302224765520819705)
          ·
            refine ⟨7347293476668574140614779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9796391302224765520819705 7347293476668574140614779)
            ·
              refine ⟨11020940215002861210922169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7347293476668574140614779 11020940215002861210922169)
              ·
                refine ⟨8265705161252145908191627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11020940215002861210922169 8265705161252145908191627)
                ·
                  refine ⟨12398557741878218862287441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8265705161252145908191627 12398557741878218862287441)
                  ·
                    refine ⟨9298918306408664146715581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12398557741878218862287441 9298918306408664146715581)
                    ·
                      refine ⟨3487094364903249055018343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9298918306408664146715581 3487094364903249055018343)
                      ·
                        rfl

theorem cell23_6791092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_6791092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791092 prefixEnd_6791092 := by exact prefixLift 6791092
  have htrace : WordTrace (prefixWord ++ tailWord_6791092) baseStart_6791092 baseEnd_6791092 := by
    simpa [prefixWord, tailWord_6791092, baseEnd_6791092] using wordTrace_append hprefix tailTrace_6791092
  have hstable : (prefixWord ++ tailWord_6791092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791092).length < 2 ^ (prefixWord ++ tailWord_6791092).sum := by decide
  have hdescent : baseEnd_6791092 < baseStart_6791092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791114 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_6791114 : Nat := 118140960795 + 6791114 * 2 ^ 59
def prefixEnd_6791114 : Nat := 4983230072969 + 3 ^ 40 * 6791114 * 2
def baseEnd_6791114 : Nat := 3487105661477647968943241

theorem tailTrace_6791114 : CollatzResearch.WordTrace tailWord_6791114 prefixEnd_6791114 3487105661477647968943241 := by
  unfold tailWord_6791114
  simp only [CollatzResearch.WordTrace]
  refine ⟨61923069079740320694383099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165128184212640855185021597 61923069079740320694383099)
  ·
    refine ⟨92884603619610481041574649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61923069079740320694383099 92884603619610481041574649)
    ·
      refine ⟨69663452714707860781180987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92884603619610481041574649 69663452714707860781180987)
      ·
        refine ⟨104495179072061791171771481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69663452714707860781180987 104495179072061791171771481)
        ·
          refine ⟨78371384304046343378828611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104495179072061791171771481 78371384304046343378828611)
          ·
            refine ⟨117557076456069515068242917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78371384304046343378828611 117557076456069515068242917)
            ·
              refine ⟨22041951835513034075295547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117557076456069515068242917 22041951835513034075295547)
              ·
                refine ⟨33062927753269551112943321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22041951835513034075295547 33062927753269551112943321)
                ·
                  refine ⟨24797195814952163334707491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33062927753269551112943321 24797195814952163334707491)
                  ·
                    refine ⟨37195793722428245002061237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24797195814952163334707491 37195793722428245002061237)
                    ·
                      refine ⟨3487105661477647968943241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37195793722428245002061237 3487105661477647968943241)
                      ·
                        rfl

theorem cell23_6791114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_6791114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791114 prefixEnd_6791114 := by exact prefixLift 6791114
  have htrace : WordTrace (prefixWord ++ tailWord_6791114) baseStart_6791114 baseEnd_6791114 := by
    simpa [prefixWord, tailWord_6791114, baseEnd_6791114] using wordTrace_append hprefix tailTrace_6791114
  have hstable : (prefixWord ++ tailWord_6791114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791114).length < 2 ^ (prefixWord ++ tailWord_6791114).sum := by decide
  have hdescent : baseEnd_6791114 < baseStart_6791114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791138 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_6791138 : Nat := 118140960795 + 6791138 * 2 ^ 59
def prefixEnd_6791138 : Nat := 4983230072969 + 3 ^ 40 * 6791138 * 2
def baseEnd_6791138 : Nat := 1162372661671118625014377

theorem tailTrace_6791138 : CollatzResearch.WordTrace tailWord_6791138 prefixEnd_6791138 1162372661671118625014377 := by
  unfold tailWord_6791138
  simp only [CollatzResearch.WordTrace]
  refine ⟨61923287917718583719101517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165128767780582889917604045 61923287917718583719101517)
  ·
    refine ⟨23221232969144468894663069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61923287917718583719101517 23221232969144468894663069)
    ·
      refine ⟨8707962363429175835498651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23221232969144468894663069 8707962363429175835498651)
      ·
        refine ⟨13061943545143763753247977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8707962363429175835498651 13061943545143763753247977)
        ·
          refine ⟨9796457658857822814935983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13061943545143763753247977 9796457658857822814935983)
          ·
            refine ⟨14694686488286734222403975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9796457658857822814935983 14694686488286734222403975)
            ·
              refine ⟨22042029732430101333605963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14694686488286734222403975 22042029732430101333605963)
              ·
                refine ⟨33063044598645152000408945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22042029732430101333605963 33063044598645152000408945)
                ·
                  refine ⟨24797283448983864000306709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33063044598645152000408945 24797283448983864000306709)
                  ·
                    refine ⟨1162372661671118625014377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24797283448983864000306709 1162372661671118625014377)
                    ·
                      rfl

theorem cell23_6791138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_6791138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791138 prefixEnd_6791138 := by exact prefixLift 6791138
  have htrace : WordTrace (prefixWord ++ tailWord_6791138) baseStart_6791138 baseEnd_6791138 := by
    simpa [prefixWord, tailWord_6791138, baseEnd_6791138] using wordTrace_append hprefix tailTrace_6791138
  have hstable : (prefixWord ++ tailWord_6791138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791138).length < 2 ^ (prefixWord ++ tailWord_6791138).sum := by decide
  have hdescent : baseEnd_6791138 < baseStart_6791138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791164 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 1, 7]
def baseStart_6791164 : Nat := 118140960795 + 6791164 * 2 ^ 59
def prefixEnd_6791164 : Nat := 4983230072969 + 3 ^ 40 * 6791164 * 2
def baseEnd_6791164 : Nat := 1162377111836790924439337

theorem tailTrace_6791164 : CollatzResearch.WordTrace tailWord_6791164 prefixEnd_6791164 1162377111836790924439337 := by
  unfold tailWord_6791164
  simp only [CollatzResearch.WordTrace]
  refine ⟨123847049984390070658426273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165129399979186760877901697 123847049984390070658426273)
  ·
    refine ⟨92885287488292552993819705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123847049984390070658426273 92885287488292552993819705)
    ·
      refine ⟨69663965616219414745364779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92885287488292552993819705 69663965616219414745364779)
      ·
        refine ⟨104495948424329122118047169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69663965616219414745364779 104495948424329122118047169)
        ·
          refine ⟨78371961318246841588535377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104495948424329122118047169 78371961318246841588535377)
          ·
            refine ⟨58778970988685131191401533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78371961318246841588535377 58778970988685131191401533)
            ·
              refine ⟨22042114120756924196775575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58778970988685131191401533 22042114120756924196775575)
              ·
                refine ⟨33063171181135386295163363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22042114120756924196775575 33063171181135386295163363)
                ·
                  refine ⟨49594756771703079442745045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33063171181135386295163363 49594756771703079442745045)
                  ·
                    refine ⟨1162377111836790924439337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49594756771703079442745045 1162377111836790924439337)
                    ·
                      rfl

theorem cell23_6791164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_6791164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791164 prefixEnd_6791164 := by exact prefixLift 6791164
  have htrace : WordTrace (prefixWord ++ tailWord_6791164) baseStart_6791164 baseEnd_6791164 := by
    simpa [prefixWord, tailWord_6791164, baseEnd_6791164] using wordTrace_append hprefix tailTrace_6791164
  have hstable : (prefixWord ++ tailWord_6791164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791164).length < 2 ^ (prefixWord ++ tailWord_6791164).sum := by decide
  have hdescent : baseEnd_6791164 < baseStart_6791164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791221 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_6791221 : Nat := 118140960795 + 6791221 * 2 ^ 59
def prefixEnd_6791221 : Nat := 4983230072969 + 3 ^ 40 * 6791221 * 2
def baseEnd_6791221 : Nat := 3487160603907679050305249

theorem tailTrace_6791221 : CollatzResearch.WordTrace tailWord_6791221 prefixEnd_6791221 3487160603907679050305249 := by
  unfold tailWord_6791221
  simp only [CollatzResearch.WordTrace]
  refine ⟨247696178929573640051677517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165130785953049093367785011 247696178929573640051677517)
  ·
    refine ⟨92886067098590115019379069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247696178929573640051677517 92886067098590115019379069)
    ·
      refine ⟨34832275161971293132267151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92886067098590115019379069 34832275161971293132267151)
      ·
        refine ⟨52248412742956939698400727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34832275161971293132267151 52248412742956939698400727)
        ·
          refine ⟨78372619114435409547601091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52248412742956939698400727 78372619114435409547601091)
          ·
            refine ⟨117558928671653114321401637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78372619114435409547601091 117558928671653114321401637)
            ·
              refine ⟨22042299125934958935262807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117558928671653114321401637 22042299125934958935262807)
              ·
                refine ⟨33063448688902438402894211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22042299125934958935262807 33063448688902438402894211)
                ·
                  refine ⟨49595173033353657604341317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33063448688902438402894211 49595173033353657604341317)
                  ·
                    refine ⟨9299094943753810800813997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49595173033353657604341317 9299094943753810800813997)
                    ·
                      refine ⟨3487160603907679050305249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9299094943753810800813997 3487160603907679050305249)
                      ·
                        rfl

theorem cell23_6791221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_6791221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791221 prefixEnd_6791221 := by exact prefixLift 6791221
  have htrace : WordTrace (prefixWord ++ tailWord_6791221) baseStart_6791221 baseEnd_6791221 := by
    simpa [prefixWord, tailWord_6791221, baseEnd_6791221] using wordTrace_append hprefix tailTrace_6791221
  have hstable : (prefixWord ++ tailWord_6791221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791221).length < 2 ^ (prefixWord ++ tailWord_6791221).sum := by decide
  have hdescent : baseEnd_6791221 < baseStart_6791221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791244 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 1, 1, 8]
def baseStart_6791244 : Nat := 118140960795 + 6791244 * 2 ^ 59
def prefixEnd_6791244 : Nat := 4983230072969 + 3 ^ 40 * 6791244 * 2
def baseEnd_6791244 : Nat := 3487172413962732460317643

theorem tailTrace_6791244 : CollatzResearch.WordTrace tailWord_6791244 prefixEnd_6791244 3487172413962732460317643 := by
  unfold tailWord_6791244
  simp only [CollatzResearch.WordTrace]
  refine ⟨123848508904245157489882393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165131345205660209986509857 123848508904245157489882393)
  ·
    refine ⟨92886381678183868117411795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123848508904245157489882393 92886381678183868117411795)
    ·
      refine ⟨139329572517275802176117693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92886381678183868117411795 139329572517275802176117693)
      ·
        refine ⟨52248589693978425816044135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139329572517275802176117693 52248589693978425816044135)
        ·
          refine ⟨78372884540967638724066203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52248589693978425816044135 78372884540967638724066203)
          ·
            refine ⟨117559326811451458086099305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78372884540967638724066203 117559326811451458086099305)
            ·
              refine ⟨88169495108588593564574479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117559326811451458086099305 88169495108588593564574479)
              ·
                refine ⟨132254242662882890346861719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88169495108588593564574479 132254242662882890346861719)
                ·
                  refine ⟨198381363994324335520292579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132254242662882890346861719 198381363994324335520292579)
                  ·
                    refine ⟨297572045991486503280438869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198381363994324335520292579 297572045991486503280438869)
                    ·
                      refine ⟨3487172413962732460317643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 297572045991486503280438869 3487172413962732460317643)
                      ·
                        rfl

theorem cell23_6791244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_6791244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791244 prefixEnd_6791244 := by exact prefixLift 6791244
  have htrace : WordTrace (prefixWord ++ tailWord_6791244) baseStart_6791244 baseEnd_6791244 := by
    simpa [prefixWord, tailWord_6791244, baseEnd_6791244] using wordTrace_append hprefix tailTrace_6791244
  have hstable : (prefixWord ++ tailWord_6791244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791244).length < 2 ^ (prefixWord ++ tailWord_6791244).sum := by decide
  have hdescent : baseEnd_6791244 < baseStart_6791244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791268 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 3, 1, 3]
def baseStart_6791268 : Nat := 118140960795 + 6791268 * 2 ^ 59
def prefixEnd_6791268 : Nat := 4983230072969 + 3 ^ 40 * 6791268 * 2
def baseEnd_6791268 : Nat := 3487184737498440366417533

theorem tailTrace_6791268 : CollatzResearch.WordTrace tailWord_6791268 prefixEnd_6791268 3487184737498440366417533 := by
  unfold tailWord_6791268
  simp only [CollatzResearch.WordTrace]
  refine ⟨123848946580201683539319229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165131928773602244719092305 123848946580201683539319229)
  ·
    refine ⟨46443354967575631327244711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123848946580201683539319229 46443354967575631327244711)
    ·
      refine ⟨69665032451363446990867067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46443354967575631327244711 69665032451363446990867067)
      ·
        refine ⟨104497548677045170486300601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69665032451363446990867067 104497548677045170486300601)
        ·
          refine ⟨78373161507783877864725451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104497548677045170486300601 78373161507783877864725451)
          ·
            refine ⟨117559742261675816797088177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78373161507783877864725451 117559742261675816797088177)
            ·
              refine ⟨88169806696256862597816133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117559742261675816797088177 88169806696256862597816133)
              ·
                refine ⟨16531838755548161737090525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88169806696256862597816133 16531838755548161737090525)
                ·
                  refine ⟨6199439533330560651408947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16531838755548161737090525 6199439533330560651408947)
                  ·
                    refine ⟨9299159299995840977113421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6199439533330560651408947 9299159299995840977113421)
                    ·
                      refine ⟨3487184737498440366417533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9299159299995840977113421 3487184737498440366417533)
                      ·
                        rfl

theorem cell23_6791268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_6791268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791268 prefixEnd_6791268 := by exact prefixLift 6791268
  have htrace : WordTrace (prefixWord ++ tailWord_6791268) baseStart_6791268 baseEnd_6791268 := by
    simpa [prefixWord, tailWord_6791268, baseEnd_6791268] using wordTrace_append hprefix tailTrace_6791268
  have hstable : (prefixWord ++ tailWord_6791268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791268).length < 2 ^ (prefixWord ++ tailWord_6791268).sum := by decide
  have hdescent : baseEnd_6791268 < baseStart_6791268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791271 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 3, 5]
def baseStart_6791271 : Nat := 118140960795 + 6791271 * 2 ^ 59
def prefixEnd_6791271 : Nat := 4983230072969 + 3 ^ 40 * 6791271 * 2
def baseEnd_6791271 : Nat := 1162395425980134618226673

theorem tailTrace_6791271 : CollatzResearch.WordTrace tailWord_6791271 prefixEnd_6791271 1162395425980134618226673 := by
  unfold tailWord_6791271
  simp only [CollatzResearch.WordTrace]
  refine ⟨247698002579392498590997667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165132001719594999060665111 247698002579392498590997667)
  ·
    refine ⟨371547003869088747886496501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247698002579392498590997667 371547003869088747886496501)
    ·
      refine ⟨34832531612727070114359047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 371547003869088747886496501 34832531612727070114359047)
      ·
        refine ⟨52248797419090605171538571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34832531612727070114359047 52248797419090605171538571)
        ·
          refine ⟨78373196128635907757307857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52248797419090605171538571 78373196128635907757307857)
          ·
            refine ⟨58779897096476930817980893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78373196128635907757307857 58779897096476930817980893)
            ·
              refine ⟨22042461411178849056742835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58779897096476930817980893 22042461411178849056742835)
              ·
                refine ⟨33063692116768273585114253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22042461411178849056742835 33063692116768273585114253)
                ·
                  refine ⟨12398884543788102594417845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33063692116768273585114253 12398884543788102594417845)
                  ·
                    refine ⟨1162395425980134618226673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12398884543788102594417845 1162395425980134618226673)
                    ·
                      rfl

theorem cell23_6791271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_6791271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791271 prefixEnd_6791271 := by exact prefixLift 6791271
  have htrace : WordTrace (prefixWord ++ tailWord_6791271) baseStart_6791271 baseEnd_6791271 := by
    simpa [prefixWord, tailWord_6791271, baseEnd_6791271] using wordTrace_append hprefix tailTrace_6791271
  have hstable : (prefixWord ++ tailWord_6791271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791271).length < 2 ^ (prefixWord ++ tailWord_6791271).sum := by decide
  have hdescent : baseEnd_6791271 < baseStart_6791271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791325 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 5, 2, 2]
def baseStart_6791325 : Nat := 118140960795 + 6791325 * 2 ^ 59
def prefixEnd_6791325 : Nat := 4983230072969 + 3 ^ 40 * 6791325 * 2
def baseEnd_6791325 : Nat := 3487214005895746643404771

theorem tailTrace_6791325 : CollatzResearch.WordTrace tailWord_6791325 prefixEnd_6791325 3487214005895746643404771 := by
  unfold tailWord_6791325
  simp only [CollatzResearch.WordTrace]
  refine ⟨247699972121196865813463429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165133314747464577208975619 247699972121196865813463429)
  ·
    refine ⟨46443744772724412340024393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247699972121196865813463429 46443744772724412340024393)
    ·
      refine ⟨34832808579543309255018295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46443744772724412340024393 34832808579543309255018295)
      ·
        refine ⟨52249212869314963882527443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34832808579543309255018295 52249212869314963882527443)
        ·
          refine ⟨78373819303972445823791165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52249212869314963882527443 78373819303972445823791165)
          ·
            refine ⟨29390182238989667183921687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78373819303972445823791165 29390182238989667183921687)
            ·
              refine ⟨44085273358484500775882531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29390182238989667183921687 44085273358484500775882531)
              ·
                refine ⟨66127910037726751163823797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44085273358484500775882531 66127910037726751163823797)
                ·
                  refine ⟨6199491566036882921608481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66127910037726751163823797 6199491566036882921608481)
                  ·
                    refine ⟨4649618674527662191206361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6199491566036882921608481 4649618674527662191206361)
                    ·
                      refine ⟨3487214005895746643404771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4649618674527662191206361 3487214005895746643404771)
                      ·
                        rfl

theorem cell23_6791325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_6791325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791325 prefixEnd_6791325 := by exact prefixLift 6791325
  have htrace : WordTrace (prefixWord ++ tailWord_6791325) baseStart_6791325 baseEnd_6791325 := by
    simpa [prefixWord, tailWord_6791325, baseEnd_6791325] using wordTrace_append hprefix tailTrace_6791325
  have hstable : (prefixWord ++ tailWord_6791325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791325).length < 2 ^ (prefixWord ++ tailWord_6791325).sum := by decide
  have hdescent : baseEnd_6791325 < baseStart_6791325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791328 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 3]
def baseStart_6791328 : Nat := 118140960795 + 6791328 * 2 ^ 59
def prefixEnd_6791328 : Nat := 4983230072969 + 3 ^ 40 * 6791328 * 2
def baseEnd_6791328 : Nat := 3487215546337710131667257

theorem tailTrace_6791328 : CollatzResearch.WordTrace tailWord_6791328 prefixEnd_6791328 3487215546337710131667257 := by
  unfold tailWord_6791328
  simp only [CollatzResearch.WordTrace]
  refine ⟨123850040770092998662911319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165133387693457331550548425 123850040770092998662911319)
  ·
    refine ⟨185775061155139497994366979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123850040770092998662911319 185775061155139497994366979)
    ·
      refine ⟨278662591732709246991550469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185775061155139497994366979 278662591732709246991550469)
      ·
        refine ⟨52249235949882983810915713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278662591732709246991550469 52249235949882983810915713)
        ·
          refine ⟨39186926962412237858186785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52249235949882983810915713 39186926962412237858186785)
          ·
            refine ⟨29390195221809178393640089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39186926962412237858186785 29390195221809178393640089)
            ·
              refine ⟨22042646416356883795230067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29390195221809178393640089 22042646416356883795230067)
              ·
                refine ⟨33063969624535325692845101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22042646416356883795230067 33063969624535325692845101)
                ·
                  refine ⟨12398988609200747134816913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33063969624535325692845101 12398988609200747134816913)
                  ·
                    refine ⟨9299241456900560351112685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12398988609200747134816913 9299241456900560351112685)
                    ·
                      refine ⟨3487215546337710131667257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9299241456900560351112685 3487215546337710131667257)
                      ·
                        rfl

theorem cell23_6791328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_6791328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791328 prefixEnd_6791328 := by exact prefixLift 6791328
  have htrace : WordTrace (prefixWord ++ tailWord_6791328) baseStart_6791328 baseEnd_6791328 := by
    simpa [prefixWord, tailWord_6791328, baseEnd_6791328] using wordTrace_append hprefix tailTrace_6791328
  have hstable : (prefixWord ++ tailWord_6791328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791328).length < 2 ^ (prefixWord ++ tailWord_6791328).sum := by decide
  have hdescent : baseEnd_6791328 < baseStart_6791328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791362 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_6791362 : Nat := 118140960795 + 6791362 * 2 ^ 59
def prefixEnd_6791362 : Nat := 4983230072969 + 3 ^ 40 * 6791362 * 2
def baseEnd_6791362 : Nat := 3487233004679962998642101

theorem tailTrace_6791362 : CollatzResearch.WordTrace tailWord_6791362 prefixEnd_6791362 3487233004679962998642101 := by
  unfold tailWord_6791362
  simp only [CollatzResearch.WordTrace]
  refine ⟨61925330405515705283140085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165134214414708547421706893 61925330405515705283140085)
  ·
    refine ⟨5805499725517097370294383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61925330405515705283140085 5805499725517097370294383)
    ·
      refine ⟨8708249588275646055441575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5805499725517097370294383 8708249588275646055441575)
      ·
        refine ⟨13062374382413469083162363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8708249588275646055441575 13062374382413469083162363)
        ·
          refine ⟨19593561573620203624743545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13062374382413469083162363 19593561573620203624743545)
          ·
            refine ⟨14695171180215152718557659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19593561573620203624743545 14695171180215152718557659)
            ·
              refine ⟨22042756770322729077836489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14695171180215152718557659 22042756770322729077836489)
              ·
                refine ⟨16532067577742046808377367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22042756770322729077836489 16532067577742046808377367)
                ·
                  refine ⟨24798101366613070212566051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16532067577742046808377367 24798101366613070212566051)
                  ·
                    refine ⟨37197152049919605318849077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24798101366613070212566051 37197152049919605318849077)
                    ·
                      refine ⟨3487233004679962998642101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37197152049919605318849077 3487233004679962998642101)
                      ·
                        rfl

theorem cell23_6791362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_6791362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791362 prefixEnd_6791362 := by exact prefixLift 6791362
  have htrace : WordTrace (prefixWord ++ tailWord_6791362) baseStart_6791362 baseEnd_6791362 := by
    simpa [prefixWord, tailWord_6791362, baseEnd_6791362] using wordTrace_append hprefix tailTrace_6791362
  have hstable : (prefixWord ++ tailWord_6791362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791362).length < 2 ^ (prefixWord ++ tailWord_6791362).sum := by decide
  have hdescent : baseEnd_6791362 < baseStart_6791362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791372 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 1, 2, 4]
def baseStart_6791372 : Nat := 118140960795 + 6791372 * 2 ^ 59
def prefixEnd_6791372 : Nat := 4983230072969 + 3 ^ 40 * 6791372 * 2
def baseEnd_6791372 : Nat := 3487238139486507959517055

theorem tailTrace_6791372 : CollatzResearch.WordTrace tailWord_6791372 prefixEnd_6791372 3487238139486507959517055 := by
  unfold tailWord_6791372
  simp only [CollatzResearch.WordTrace]
  refine ⟨123850843176013296420212185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165134457568017728560282913 123850843176013296420212185)
  ·
    refine ⟨92888132382009972315159139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123850843176013296420212185 92888132382009972315159139)
    ·
      refine ⟨139332198573014958472738709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92888132382009972315159139 139332198573014958472738709)
      ·
        refine ⟨6531196808110076178409627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139332198573014958472738709 6531196808110076178409627)
        ·
          refine ⟨9796795212165114267614441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6531196808110076178409627 9796795212165114267614441)
          ·
            refine ⟨7347596409123835700710831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9796795212165114267614441 7347596409123835700710831)
            ·
              refine ⟨11021394613685753551066247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7347596409123835700710831 11021394613685753551066247)
              ·
                refine ⟨16532091920528630326599371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11021394613685753551066247 16532091920528630326599371)
                ·
                  refine ⟨24798137880792945489899057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16532091920528630326599371 24798137880792945489899057)
                  ·
                    refine ⟨18598603410594709117424293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24798137880792945489899057 18598603410594709117424293)
                    ·
                      refine ⟨3487238139486507959517055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18598603410594709117424293 3487238139486507959517055)
                      ·
                        rfl

theorem cell23_6791372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_6791372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791372 prefixEnd_6791372 := by exact prefixLift 6791372
  have htrace : WordTrace (prefixWord ++ tailWord_6791372) baseStart_6791372 baseEnd_6791372 := by
    simpa [prefixWord, tailWord_6791372, baseEnd_6791372] using wordTrace_append hprefix tailTrace_6791372
  have hstable : (prefixWord ++ tailWord_6791372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791372).length < 2 ^ (prefixWord ++ tailWord_6791372).sum := by decide
  have hdescent : baseEnd_6791372 < baseStart_6791372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791382 : List Nat := [5, 2, 1, 2, 1, 3, 2, 7]
def baseStart_6791382 : Nat := 118140960795 + 6791382 * 2 ^ 59
def prefixEnd_6791382 : Nat := 4983230072969 + 3 ^ 40 * 6791382 * 2
def baseEnd_6791382 : Nat := 129157158307150108162667

theorem tailTrace_6791382 : CollatzResearch.WordTrace tailWord_6791382 prefixEnd_6791382 129157158307150108162667 := by
  unfold tailWord_6791382
  simp only [CollatzResearch.WordTrace]
  refine ⟨15481378192624397784268025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165134700721326909698858933 15481378192624397784268025)
  ·
    refine ⟨11611033644468298338201019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15481378192624397784268025 11611033644468298338201019)
    ·
      refine ⟨17416550466702447507301529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11611033644468298338201019 17416550466702447507301529)
      ·
        refine ⟨13062412850026835630476147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17416550466702447507301529 13062412850026835630476147)
        ·
          refine ⟨19593619275040253445714221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13062412850026835630476147 19593619275040253445714221)
          ·
            refine ⟨7347607228140095042142833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19593619275040253445714221 7347607228140095042142833)
            ·
              refine ⟨5510705421105071281607125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7347607228140095042142833 5510705421105071281607125)
              ·
                refine ⟨129157158307150108162667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5510705421105071281607125 129157158307150108162667)
                ·
                  rfl

theorem cell23_6791382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_6791382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791382 prefixEnd_6791382 := by exact prefixLift 6791382
  have htrace : WordTrace (prefixWord ++ tailWord_6791382) baseStart_6791382 baseEnd_6791382 := by
    simpa [prefixWord, tailWord_6791382, baseEnd_6791382] using wordTrace_append hprefix tailTrace_6791382
  have hstable : (prefixWord ++ tailWord_6791382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791382).length < 2 ^ (prefixWord ++ tailWord_6791382).sum := by decide
  have hdescent : baseEnd_6791382 < baseStart_6791382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791385 : List Nat := [1, 2, 1, 2, 3, 1, 3, 4, 1, 3, 2]
def baseStart_6791385 : Nat := 118140960795 + 6791385 * 2 ^ 59
def prefixEnd_6791385 : Nat := 4983230072969 + 3 ^ 40 * 6791385 * 2
def baseEnd_6791385 : Nat := 3487244814735016408654495

theorem tailTrace_6791385 : CollatzResearch.WordTrace tailWord_6791385 prefixEnd_6791385 3487244814735016408654495 := by
  unfold tailWord_6791385
  simp only [CollatzResearch.WordTrace]
  refine ⟨247702160500979496060647609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165134773667319664040431739 247702160500979496060647609)
  ·
    refine ⟨185776620375734622045485707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247702160500979496060647609 185776620375734622045485707)
    ·
      refine ⟨278664930563601933068228561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185776620375734622045485707 278664930563601933068228561)
      ·
        refine ⟨208998697922701449801171421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278664930563601933068228561 208998697922701449801171421)
        ·
          refine ⟨78374511721013043675439283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208998697922701449801171421 78374511721013043675439283)
          ·
            refine ⟨117561767581519565513158925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78374511721013043675439283 117561767581519565513158925)
            ·
              refine ⟨44085662843069837067434597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117561767581519565513158925 44085662843069837067434597)
              ·
                refine ⟨8266061783075594450143987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44085662843069837067434597 8266061783075594450143987)
                ·
                  refine ⟨12399092674613391675215981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8266061783075594450143987 12399092674613391675215981)
                  ·
                    refine ⟨4649659752980021878205993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12399092674613391675215981 4649659752980021878205993)
                    ·
                      refine ⟨3487244814735016408654495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4649659752980021878205993 3487244814735016408654495)
                      ·
                        rfl

theorem cell23_6791385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 3, 2].length) (baseStart_6791385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791385 prefixEnd_6791385 := by exact prefixLift 6791385
  have htrace : WordTrace (prefixWord ++ tailWord_6791385) baseStart_6791385 baseEnd_6791385 := by
    simpa [prefixWord, tailWord_6791385, baseEnd_6791385] using wordTrace_append hprefix tailTrace_6791385
  have hstable : (prefixWord ++ tailWord_6791385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791385).length < 2 ^ (prefixWord ++ tailWord_6791385).sum := by decide
  have hdescent : baseEnd_6791385 < baseStart_6791385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791401 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 2, 1, 5]
def baseStart_6791401 : Nat := 118140960795 + 6791401 * 2 ^ 59
def prefixEnd_6791401 : Nat := 4983230072969 + 3 ^ 40 * 6791401 * 2
def baseEnd_6791401 : Nat := 3487253030425488346054421

theorem tailTrace_6791401 : CollatzResearch.WordTrace tailWord_6791401 prefixEnd_6791401 3487253030425488346054421 := by
  unfold tailWord_6791401
  simp only [CollatzResearch.WordTrace]
  refine ⟨247702744068921530793230057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165135162712614353862153371 247702744068921530793230057)
  ·
    refine ⟨185777058051691148094922543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247702744068921530793230057 185777058051691148094922543)
    ·
      refine ⟨278665587077536722142383815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185777058051691148094922543 278665587077536722142383815)
      ·
        refine ⟨417998380616305083213575723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278665587077536722142383815 417998380616305083213575723)
        ·
          refine ⟨626997570924457624820363585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417998380616305083213575723 626997570924457624820363585)
          ·
            refine ⟨470248178193343218615272689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626997570924457624820363585 470248178193343218615272689)
            ·
              refine ⟨352686133645007413961454517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470248178193343218615272689 352686133645007413961454517)
              ·
                refine ⟨33064325029219445058886361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 352686133645007413961454517 33064325029219445058886361)
                ·
                  refine ⟨24798243771914583794164771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33064325029219445058886361 24798243771914583794164771)
                  ·
                    refine ⟨37197365657871875691247157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24798243771914583794164771 37197365657871875691247157)
                    ·
                      refine ⟨3487253030425488346054421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37197365657871875691247157 3487253030425488346054421)
                      ·
                        rfl

theorem cell23_6791401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_6791401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791401 prefixEnd_6791401 := by exact prefixLift 6791401
  have htrace : WordTrace (prefixWord ++ tailWord_6791401) baseStart_6791401 baseEnd_6791401 := by
    simpa [prefixWord, tailWord_6791401, baseEnd_6791401] using wordTrace_append hprefix tailTrace_6791401
  have hstable : (prefixWord ++ tailWord_6791401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791401).length < 2 ^ (prefixWord ++ tailWord_6791401).sum := by decide
  have hdescent : baseEnd_6791401 < baseStart_6791401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791426 : List Nat := [3, 4, 1, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_6791426 : Nat := 118140960795 + 6791426 * 2 ^ 59
def prefixEnd_6791426 : Nat := 4983230072969 + 3 ^ 40 * 6791426 * 2
def baseEnd_6791426 : Nat := 3487265867441850748241807

theorem tailTrace_6791426 : CollatzResearch.WordTrace tailWord_6791426 prefixEnd_6791426 3487265867441850748241807 := by
  unfold tailWord_6791426
  simp only [CollatzResearch.WordTrace]
  refine ⟨61925913973457740015722533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165135770595887306708593421 61925913973457740015722533)
  ·
    refine ⟨11611108870023326252947975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61925913973457740015722533 11611108870023326252947975)
    ·
      refine ⟨17416663305034989379421963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11611108870023326252947975 17416663305034989379421963)
      ·
        refine ⟨26124994957552484069132945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17416663305034989379421963 26124994957552484069132945)
        ·
          refine ⟨19593746218164363051849709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26124994957552484069132945 19593746218164363051849709)
          ·
            refine ⟨7347654831811636144443641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19593746218164363051849709 7347654831811636144443641)
            ·
              refine ⟨5510741123858727108332731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7347654831811636144443641 5510741123858727108332731)
              ·
                refine ⟨8266111685788090662499097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5510741123858727108332731 8266111685788090662499097)
                ·
                  refine ⟨6199583764341067996874323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8266111685788090662499097 6199583764341067996874323)
                  ·
                    refine ⟨9299375646511601995311485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6199583764341067996874323 9299375646511601995311485)
                    ·
                      refine ⟨3487265867441850748241807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9299375646511601995311485 3487265867441850748241807)
                      ·
                        rfl

theorem cell23_6791426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_6791426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791426 prefixEnd_6791426 := by exact prefixLift 6791426
  have htrace : WordTrace (prefixWord ++ tailWord_6791426) baseStart_6791426 baseEnd_6791426 := by
    simpa [prefixWord, tailWord_6791426, baseEnd_6791426] using wordTrace_append hprefix tailTrace_6791426
  have hstable : (prefixWord ++ tailWord_6791426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791426).length < 2 ^ (prefixWord ++ tailWord_6791426).sum := by decide
  have hdescent : baseEnd_6791426 < baseStart_6791426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791451 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 1, 7]
def baseStart_6791451 : Nat := 118140960795 + 6791451 * 2 ^ 59
def prefixEnd_6791451 : Nat := 4983230072969 + 3 ^ 40 * 6791451 * 2
def baseEnd_6791451 : Nat := 1162426234819404383476397

theorem tailTrace_6791451 : CollatzResearch.WordTrace tailWord_6791451 prefixEnd_6791451 1162426234819404383476397 := by
  unfold tailWord_6791451
  simp only [CollatzResearch.WordTrace]
  refine ⟨247704567718740389332550207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165136378479160259555033471 247704567718740389332550207)
  ·
    refine ⟨371556851578110583998825311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247704567718740389332550207 371556851578110583998825311)
    ·
      refine ⟨557335277367165875998237967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371556851578110583998825311 557335277367165875998237967)
      ·
        refine ⟨836002916050748813997356951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557335277367165875998237967 836002916050748813997356951)
        ·
          refine ⟨1254004374076123220996035427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836002916050748813997356951 1254004374076123220996035427)
          ·
            refine ⟨1881006561114184831494053141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254004374076123220996035427 1881006561114184831494053141)
            ·
              refine ⟨88172182552227413976283741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1881006561114184831494053141 88172182552227413976283741)
              ·
                refine ⟨33064568457085280241106403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88172182552227413976283741 33064568457085280241106403)
                ·
                  refine ⟨49596852685627920361659605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33064568457085280241106403 49596852685627920361659605)
                  ·
                    refine ⟨1162426234819404383476397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49596852685627920361659605 1162426234819404383476397)
                    ·
                      rfl

theorem cell23_6791451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 7].length) (baseStart_6791451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791451 prefixEnd_6791451 := by exact prefixLift 6791451
  have htrace : WordTrace (prefixWord ++ tailWord_6791451) baseStart_6791451 baseEnd_6791451 := by
    simpa [prefixWord, tailWord_6791451, baseEnd_6791451] using wordTrace_append hprefix tailTrace_6791451
  have hstable : (prefixWord ++ tailWord_6791451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791451).length < 2 ^ (prefixWord ++ tailWord_6791451).sum := by decide
  have hdescent : baseEnd_6791451 < baseStart_6791451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791466 : List Nat := [3, 1, 4, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_6791466 : Nat := 118140960795 + 6791466 * 2 ^ 59
def prefixEnd_6791466 : Nat := 4983230072969 + 3 ^ 40 * 6791466 * 2
def baseEnd_6791466 : Nat := 3487286406668030591741623

theorem tailTrace_6791466 : CollatzResearch.WordTrace tailWord_6791466 prefixEnd_6791466 3487286406668030591741623 := by
  unfold tailWord_6791466
  simp only [CollatzResearch.WordTrace]
  refine ⟨61926278703421511723586563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165136743209124031262897501 61926278703421511723586563)
  ·
    refine ⟨92889418055132267585379845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61926278703421511723586563 92889418055132267585379845)
    ·
      refine ⟨17416765885337300172258721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92889418055132267585379845 17416765885337300172258721)
      ·
        refine ⟨13062574414002975129194041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17416765885337300172258721 13062574414002975129194041)
        ·
          refine ⟨9796930810502231346895531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13062574414002975129194041 9796930810502231346895531)
          ·
            refine ⟨14695396215753347020343297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9796930810502231346895531 14695396215753347020343297)
            ·
              refine ⟨11021547161815010265257473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14695396215753347020343297 11021547161815010265257473)
              ·
                refine ⟨8266160371361257698943105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11021547161815010265257473 8266160371361257698943105)
                ·
                  refine ⟨6199620278520943274207329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8266160371361257698943105 6199620278520943274207329)
                  ·
                    refine ⟨4649715208890707455655497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6199620278520943274207329 4649715208890707455655497)
                    ·
                      refine ⟨3487286406668030591741623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4649715208890707455655497 3487286406668030591741623)
                      ·
                        rfl

theorem cell23_6791466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_6791466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791466 prefixEnd_6791466 := by exact prefixLift 6791466
  have htrace : WordTrace (prefixWord ++ tailWord_6791466) baseStart_6791466 baseEnd_6791466 := by
    simpa [prefixWord, tailWord_6791466, baseEnd_6791466] using wordTrace_append hprefix tailTrace_6791466
  have hstable : (prefixWord ++ tailWord_6791466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791466).length < 2 ^ (prefixWord ++ tailWord_6791466).sum := by decide
  have hdescent : baseEnd_6791466 < baseStart_6791466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791468 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 2, 5]
def baseStart_6791468 : Nat := 118140960795 + 6791468 * 2 ^ 59
def prefixEnd_6791468 : Nat := 4983230072969 + 3 ^ 40 * 6791468 * 2
def baseEnd_6791468 : Nat := 1162429144543113194638871

theorem tailTrace_6791468 : CollatzResearch.WordTrace tailWord_6791468 prefixEnd_6791468 1162429144543113194638871 := by
  unfold tailWord_6791468
  simp only [CollatzResearch.WordTrace]
  refine ⟨123852593879839400617959529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165136791839785867490612705 123852593879839400617959529)
  ·
    refine ⟨92889445409879550463469647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123852593879839400617959529 92889445409879550463469647)
    ·
      refine ⟨139334168114819325695204471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92889445409879550463469647 139334168114819325695204471)
      ·
        refine ⟨209001252172228988542806707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139334168114819325695204471 209001252172228988542806707)
        ·
          refine ⟨313501878258343482814210061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209001252172228988542806707 313501878258343482814210061)
          ·
            refine ⟨117563204346878806055328773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313501878258343482814210061 117563204346878806055328773)
            ·
              refine ⟨22043100815039776135374145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117563204346878806055328773 22043100815039776135374145)
              ·
                refine ⟨16532325611279832101530609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22043100815039776135374145 16532325611279832101530609)
                ·
                  refine ⟨12399244208459874076147957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16532325611279832101530609 12399244208459874076147957)
                  ·
                    refine ⟨1162429144543113194638871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12399244208459874076147957 1162429144543113194638871)
                    ·
                      rfl

theorem cell23_6791468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_6791468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791468 prefixEnd_6791468 := by exact prefixLift 6791468
  have htrace : WordTrace (prefixWord ++ tailWord_6791468) baseStart_6791468 baseEnd_6791468 := by
    simpa [prefixWord, tailWord_6791468, baseEnd_6791468] using wordTrace_append hprefix tailTrace_6791468
  have hstable : (prefixWord ++ tailWord_6791468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791468).length < 2 ^ (prefixWord ++ tailWord_6791468).sum := by decide
  have hdescent : baseEnd_6791468 < baseStart_6791468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791505 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 2, 1, 4]
def baseStart_6791505 : Nat := 118140960795 + 6791505 * 2 ^ 59
def prefixEnd_6791505 : Nat := 4983230072969 + 3 ^ 40 * 6791505 * 2
def baseEnd_6791505 : Nat := 3487306432413555939153943

theorem tailTrace_6791505 : CollatzResearch.WordTrace tailWord_6791505 prefixEnd_6791505 3487306432413555939153943 := by
  unfold tailWord_6791505
  simp only [CollatzResearch.WordTrace]
  refine ⟨247706537260544756555015969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165137691507029837703343979 247706537260544756555015969)
  ·
    refine ⟨185779902945408567416261977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247706537260544756555015969 185779902945408567416261977)
    ·
      refine ⟨139334927209056425562196483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185779902945408567416261977 139334927209056425562196483)
      ·
        refine ⟨209002390813584638343294725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139334927209056425562196483 209002390813584638343294725)
        ·
          refine ⟨39187948277547119689367761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209002390813584638343294725 39187948277547119689367761)
          ·
            refine ⟨29390961208160339767025821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39187948277547119689367761 29390961208160339767025821)
            ·
              refine ⟨11021610453060127412634683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29390961208160339767025821 11021610453060127412634683)
              ·
                refine ⟨16532415679590191118952025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11021610453060127412634683 16532415679590191118952025)
                ·
                  refine ⟨12399311759692643339214019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16532415679590191118952025 12399311759692643339214019)
                  ·
                    refine ⟨18598967639538965008821029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12399311759692643339214019 18598967639538965008821029)
                    ·
                      refine ⟨3487306432413555939153943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18598967639538965008821029 3487306432413555939153943)
                      ·
                        rfl

theorem cell23_6791505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_6791505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791505 prefixEnd_6791505 := by exact prefixLift 6791505
  have htrace : WordTrace (prefixWord ++ tailWord_6791505) baseStart_6791505 baseEnd_6791505 := by
    simpa [prefixWord, tailWord_6791505, baseEnd_6791505] using wordTrace_append hprefix tailTrace_6791505
  have hstable : (prefixWord ++ tailWord_6791505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791505).length < 2 ^ (prefixWord ++ tailWord_6791505).sum := by decide
  have hdescent : baseEnd_6791505 < baseStart_6791505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791522 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_6791522 : Nat := 118140960795 + 6791522 * 2 ^ 59
def prefixEnd_6791522 : Nat := 4983230072969 + 3 ^ 40 * 6791522 * 2
def baseEnd_6791522 : Nat := 3487315161584682372641365

theorem tailTrace_6791522 : CollatzResearch.WordTrace tailWord_6791522 prefixEnd_6791522 3487315161584682372641365 := by
  unfold tailWord_6791522
  simp only [CollatzResearch.WordTrace]
  refine ⟨61926789325370792114596205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165138104867655445638923213 61926789325370792114596205)
  ·
    refine ⟨23222545997014047042973577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61926789325370792114596205 23222545997014047042973577)
    ·
      refine ⟨17416909497760535282230183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23222545997014047042973577 17416909497760535282230183)
      ·
        refine ⟨26125364246640802923345275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17416909497760535282230183 26125364246640802923345275)
        ·
          refine ⟨39188046369961204385017913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26125364246640802923345275 39188046369961204385017913)
          ·
            refine ⟨29391034777470903288763435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39188046369961204385017913 29391034777470903288763435)
            ·
              refine ⟨44086552166206354933145153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29391034777470903288763435 44086552166206354933145153)
              ·
                refine ⟨33064914124654766199858865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44086552166206354933145153 33064914124654766199858865)
                ·
                  refine ⟨24798685593491074649894149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33064914124654766199858865 24798685593491074649894149)
                  ·
                    refine ⟨4649753548779576496855153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24798685593491074649894149 4649753548779576496855153)
                    ·
                      refine ⟨3487315161584682372641365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4649753548779576496855153 3487315161584682372641365)
                      ·
                        rfl

theorem cell23_6791522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_6791522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791522 prefixEnd_6791522 := by exact prefixLift 6791522
  have htrace : WordTrace (prefixWord ++ tailWord_6791522) baseStart_6791522 baseEnd_6791522 := by
    simpa [prefixWord, tailWord_6791522, baseEnd_6791522] using wordTrace_append hprefix tailTrace_6791522
  have hstable : (prefixWord ++ tailWord_6791522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791522).length < 2 ^ (prefixWord ++ tailWord_6791522).sum := by decide
  have hdescent : baseEnd_6791522 < baseStart_6791522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791532 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 3, 4]
def baseStart_6791532 : Nat := 118140960795 + 6791532 * 2 ^ 59
def prefixEnd_6791532 : Nat := 4983230072969 + 3 ^ 40 * 6791532 * 2
def baseEnd_6791532 : Nat := 1162440098797075777838773

theorem tailTrace_6791532 : CollatzResearch.WordTrace tailWord_6791532 prefixEnd_6791532 1162440098797075777838773 := by
  unfold tailWord_6791532
  simp only [CollatzResearch.WordTrace]
  refine ⟨123853761015723470083124425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165138348020964626777499233 123853761015723470083124425)
  ·
    refine ⟨92890320761792602562343319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123853761015723470083124425 92890320761792602562343319)
    ·
      refine ⟨139335481142688903843514979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92890320761792602562343319 139335481142688903843514979)
      ·
        refine ⟨209003221714033355765272469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139335481142688903843514979 209003221714033355765272469)
        ·
          refine ⟨9797026017845313551497147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 209003221714033355765272469 9797026017845313551497147)
          ·
            refine ⟨14695539026767970327245721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9797026017845313551497147 14695539026767970327245721)
            ·
              refine ⟨11021654270075977745434291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14695539026767970327245721 11021654270075977745434291)
              ·
                refine ⟨16532481405113966618151437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11021654270075977745434291 16532481405113966618151437)
                ·
                  refine ⟨6199680526917737481806789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16532481405113966618151437 6199680526917737481806789)
                  ·
                    refine ⟨1162440098797075777838773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6199680526917737481806789 1162440098797075777838773)
                    ·
                      rfl

theorem cell23_6791532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_6791532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791532 prefixEnd_6791532 := by exact prefixLift 6791532
  have htrace : WordTrace (prefixWord ++ tailWord_6791532) baseStart_6791532 baseEnd_6791532 := by
    simpa [prefixWord, tailWord_6791532, baseEnd_6791532] using wordTrace_append hprefix tailTrace_6791532
  have hstable : (prefixWord ++ tailWord_6791532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791532).length < 2 ^ (prefixWord ++ tailWord_6791532).sum := by decide
  have hdescent : baseEnd_6791532 < baseStart_6791532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791566 : List Nat := [4, 1, 1, 4, 1, 3, 1, 3, 1, 4]
def baseStart_6791566 : Nat := 118140960795 + 6791566 * 2 ^ 59
def prefixEnd_6791566 : Nat := 4983230072969 + 3 ^ 40 * 6791566 * 2
def baseEnd_6791566 : Nat := 1162445918244493400163721

theorem tailTrace_6791566 : CollatzResearch.WordTrace tailWord_6791566 prefixEnd_6791566 1162445918244493400163721 := by
  unfold tailWord_6791566
  simp only [CollatzResearch.WordTrace]
  refine ⟨30963595264165470496623319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165139174742215842648657701 30963595264165470496623319)
  ·
    refine ⟨46445392896248205744934979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30963595264165470496623319 46445392896248205744934979)
    ·
      refine ⟨69668089344372308617402469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46445392896248205744934979 69668089344372308617402469)
      ·
        refine ⟨13062766752069807865762963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69668089344372308617402469 13062766752069807865762963)
        ·
          refine ⟨19594150128104711798644445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13062766752069807865762963 19594150128104711798644445)
          ·
            refine ⟨7347806298039266924491667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19594150128104711798644445 7347806298039266924491667)
            ·
              refine ⟨11021709447058900386737501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7347806298039266924491667 11021709447058900386737501)
              ·
                refine ⟨4133141042647087645026563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11021709447058900386737501 4133141042647087645026563)
                ·
                  refine ⟨6199711563970631467539845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133141042647087645026563 6199711563970631467539845)
                  ·
                    refine ⟨1162445918244493400163721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6199711563970631467539845 1162445918244493400163721)
                    ·
                      rfl

theorem cell23_6791566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_6791566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791566 prefixEnd_6791566 := by exact prefixLift 6791566
  have htrace : WordTrace (prefixWord ++ tailWord_6791566) baseStart_6791566 baseEnd_6791566 := by
    simpa [prefixWord, tailWord_6791566, baseEnd_6791566] using wordTrace_append hprefix tailTrace_6791566
  have hstable : (prefixWord ++ tailWord_6791566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791566).length < 2 ^ (prefixWord ++ tailWord_6791566).sum := by decide
  have hdescent : baseEnd_6791566 < baseStart_6791566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791575 : List Nat := [1, 1, 3, 3, 1, 1, 4, 3, 1, 5]
def baseStart_6791575 : Nat := 118140960795 + 6791575 * 2 ^ 59
def prefixEnd_6791575 : Nat := 4983230072969 + 3 ^ 40 * 6791575 * 2
def baseEnd_6791575 : Nat := 1162447458686456888426207

theorem tailTrace_6791575 : CollatzResearch.WordTrace tailWord_6791575 prefixEnd_6791575 1162447458686456888426207 := by
  unfold tailWord_6791575
  simp only [CollatzResearch.WordTrace]
  refine ⟨247709090370291158510064179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165139393580194105673376119 247709090370291158510064179)
  ·
    refine ⟨371563635555436737765096269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247709090370291158510064179 371563635555436737765096269)
    ·
      refine ⟨139336363333288776661911101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371563635555436737765096269 139336363333288776661911101)
      ·
        refine ⟨52251136249983291248216663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139336363333288776661911101 52251136249983291248216663)
        ·
          refine ⟨78376704374974936872324995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52251136249983291248216663 78376704374974936872324995)
          ·
            refine ⟨117565056562462405308487493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78376704374974936872324995 117565056562462405308487493)
            ·
              refine ⟨22043448105461700995341405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117565056562462405308487493 22043448105461700995341405)
              ·
                refine ⟨8266293039548137873253027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22043448105461700995341405 8266293039548137873253027)
                ·
                  refine ⟨12399439559322206809879541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8266293039548137873253027 12399439559322206809879541)
                  ·
                    refine ⟨1162447458686456888426207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12399439559322206809879541 1162447458686456888426207)
                    ·
                      rfl

theorem cell23_6791575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_6791575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791575 prefixEnd_6791575 := by exact prefixLift 6791575
  have htrace : WordTrace (prefixWord ++ tailWord_6791575) baseStart_6791575 baseEnd_6791575 := by
    simpa [prefixWord, tailWord_6791575, baseEnd_6791575] using wordTrace_append hprefix tailTrace_6791575
  have hstable : (prefixWord ++ tailWord_6791575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791575).length < 2 ^ (prefixWord ++ tailWord_6791575).sum := by decide
  have hdescent : baseEnd_6791575 < baseStart_6791575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791612 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_6791612 : Nat := 118140960795 + 6791612 * 2 ^ 59
def prefixEnd_6791612 : Nat := 4983230072969 + 3 ^ 40 * 6791612 * 2
def baseEnd_6791612 : Nat := 3487361374843587020515951

theorem tailTrace_6791612 : CollatzResearch.WordTrace tailWord_6791612 prefixEnd_6791612 3487361374843587020515951 := by
  unfold tailWord_6791612
  simp only [CollatzResearch.WordTrace]
  refine ⟨123855219935578556914580545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165140293247438075886107393 123855219935578556914580545)
  ·
    refine ⟨92891414951683917685935409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123855219935578556914580545 92891414951683917685935409)
    ·
      refine ⟨69668561213762938264451557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92891414951683917685935409 69668561213762938264451557)
      ·
        refine ⟨13062855227580550924584667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69668561213762938264451557 13062855227580550924584667)
        ·
          refine ⟨19594282841370826386877001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13062855227580550924584667 19594282841370826386877001)
          ·
            refine ⟨14695712131028119790157751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19594282841370826386877001 14695712131028119790157751)
            ·
              refine ⟨22043568196542179685236627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14695712131028119790157751 22043568196542179685236627)
              ·
                refine ⟨33065352294813269527854941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22043568196542179685236627 33065352294813269527854941)
                ·
                  refine ⟨12399507110554976072945603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33065352294813269527854941 12399507110554976072945603)
                  ·
                    refine ⟨18599260665832464109418405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12399507110554976072945603 18599260665832464109418405)
                    ·
                      refine ⟨3487361374843587020515951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18599260665832464109418405 3487361374843587020515951)
                      ·
                        rfl

theorem cell23_6791612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_6791612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791612 prefixEnd_6791612 := by exact prefixLift 6791612
  have htrace : WordTrace (prefixWord ++ tailWord_6791612) baseStart_6791612 baseEnd_6791612 := by
    simpa [prefixWord, tailWord_6791612, baseEnd_6791612] using wordTrace_append hprefix tailTrace_6791612
  have hstable : (prefixWord ++ tailWord_6791612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791612).length < 2 ^ (prefixWord ++ tailWord_6791612).sum := by decide
  have hdescent : baseEnd_6791612 < baseStart_6791612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791648 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 1, 9]
def baseStart_6791648 : Nat := 118140960795 + 6791648 * 2 ^ 59
def prefixEnd_6791648 : Nat := 4983230072969 + 3 ^ 40 * 6791648 * 2
def baseEnd_6791648 : Nat := 1162459953382382959888595

theorem tailTrace_6791648 : CollatzResearch.WordTrace tailWord_6791648 prefixEnd_6791648 1162459953382382959888595 := by
  unfold tailWord_6791648
  simp only [CollatzResearch.WordTrace]
  refine ⟨123855876449513345988735799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165141168599351127984981065 123855876449513345988735799)
  ·
    refine ⟨185783814674270018983103699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123855876449513345988735799 185783814674270018983103699)
    ·
      refine ⟨278675722011405028474655549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185783814674270018983103699 278675722011405028474655549)
      ·
        refine ⟨104503395754276885677995831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278675722011405028474655549 104503395754276885677995831)
        ·
          refine ⟨156755093631415328516993747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104503395754276885677995831 156755093631415328516993747)
          ·
            refine ⟨235132640447122992775490621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156755093631415328516993747 235132640447122992775490621)
            ·
              refine ⟨88174740167671122290808983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235132640447122992775490621 88174740167671122290808983)
              ·
                refine ⟨132262110251506683436213475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88174740167671122290808983 132262110251506683436213475)
                ·
                  refine ⟨198393165377260025154320213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132262110251506683436213475 198393165377260025154320213)
                  ·
                    refine ⟨1162459953382382959888595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 198393165377260025154320213 1162459953382382959888595)
                    ·
                      rfl

theorem cell23_6791648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 9].length) (baseStart_6791648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791648 prefixEnd_6791648 := by exact prefixLift 6791648
  have htrace : WordTrace (prefixWord ++ tailWord_6791648) baseStart_6791648 baseEnd_6791648 := by
    simpa [prefixWord, tailWord_6791648, baseEnd_6791648] using wordTrace_append hprefix tailTrace_6791648
  have hstable : (prefixWord ++ tailWord_6791648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791648).length < 2 ^ (prefixWord ++ tailWord_6791648).sum := by decide
  have hdescent : baseEnd_6791648 < baseStart_6791648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791662 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_6791662 : Nat := 118140960795 + 6791662 * 2 ^ 59
def prefixEnd_6791662 : Nat := 4983230072969 + 3 ^ 40 * 6791662 * 2
def baseEnd_6791662 : Nat := 3487387048876311824890721

theorem tailTrace_6791662 : CollatzResearch.WordTrace tailWord_6791662 prefixEnd_6791662 3487387048876311824890721 := by
  unfold tailWord_6791662
  simp only [CollatzResearch.WordTrace]
  refine ⟨30964032940121996546060155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165141509013983981578987493 30964032940121996546060155)
  ·
    refine ⟨46446049410182994819090233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30964032940121996546060155 46446049410182994819090233)
    ·
      refine ⟨34834537057637246114317675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46446049410182994819090233 34834537057637246114317675)
      ·
        refine ⟨52251805586455869171476513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34834537057637246114317675 52251805586455869171476513)
        ·
          refine ⟨39188854189841901878607385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52251805586455869171476513 39188854189841901878607385)
          ·
            refine ⟨29391640642381426408955539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39188854189841901878607385 29391640642381426408955539)
            ·
              refine ⟨44087460963572139613433309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29391640642381426408955539 44087460963572139613433309)
              ·
                refine ⟨16532797861339552355037491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44087460963572139613433309 16532797861339552355037491)
                ·
                  refine ⟨24799196792009328532556237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16532797861339552355037491 24799196792009328532556237)
                  ·
                    refine ⟨9299698797003498199708589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24799196792009328532556237 9299698797003498199708589)
                    ·
                      refine ⟨3487387048876311824890721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9299698797003498199708589 3487387048876311824890721)
                      ·
                        rfl

theorem cell23_6791662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_6791662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791662 prefixEnd_6791662 := by exact prefixLift 6791662
  have htrace : WordTrace (prefixWord ++ tailWord_6791662) baseStart_6791662 baseEnd_6791662 := by
    simpa [prefixWord, tailWord_6791662, baseEnd_6791662] using wordTrace_append hprefix tailTrace_6791662
  have hstable : (prefixWord ++ tailWord_6791662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791662).length < 2 ^ (prefixWord ++ tailWord_6791662).sum := by decide
  have hdescent : baseEnd_6791662 < baseStart_6791662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791669 : List Nat := [1, 3, 5, 1, 2, 1, 3, 7]
def baseStart_6791669 : Nat := 118140960795 + 6791669 * 2 ^ 59
def prefixEnd_6791669 : Nat := 4983230072969 + 3 ^ 40 * 6791669 * 2
def baseEnd_6791669 : Nat := 129162616416329381389007

theorem tailTrace_6791669 : CollatzResearch.WordTrace tailWord_6791669 prefixEnd_6791669 129162616416329381389007 := by
  unfold tailWord_6791669
  simp only [CollatzResearch.WordTrace]
  refine ⟨247712518831950612563986061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165141679221300408375990707 247712518831950612563986061)
  ·
    refine ⟨92892194561981479711494773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247712518831950612563986061 92892194561981479711494773)
    ·
      refine ⟨8708643240185763722952635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92892194561981479711494773 8708643240185763722952635)
      ·
        refine ⟨13062964860278645584428953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8708643240185763722952635 13062964860278645584428953)
        ·
          refine ⟨9797223645208984188321715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13062964860278645584428953 9797223645208984188321715)
          ·
            refine ⟨14695835467813476282482573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9797223645208984188321715 14695835467813476282482573)
            ·
              refine ⟨5510938300430053605930965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14695835467813476282482573 5510938300430053605930965)
              ·
                refine ⟨129162616416329381389007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5510938300430053605930965 129162616416329381389007)
                ·
                  rfl

theorem cell23_6791669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 7].length) (baseStart_6791669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791669 prefixEnd_6791669 := by exact prefixLift 6791669
  have htrace : WordTrace (prefixWord ++ tailWord_6791669) baseStart_6791669 baseEnd_6791669 := by
    simpa [prefixWord, tailWord_6791669, baseEnd_6791669] using wordTrace_append hprefix tailTrace_6791669
  have hstable : (prefixWord ++ tailWord_6791669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791669).length < 2 ^ (prefixWord ++ tailWord_6791669).sum := by decide
  have hdescent : baseEnd_6791669 < baseStart_6791669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791672 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 3, 3, 2]
def baseStart_6791672 : Nat := 118140960795 + 6791672 * 2 ^ 59
def prefixEnd_6791672 : Nat := 4983230072969 + 3 ^ 40 * 6791672 * 2
def baseEnd_6791672 : Nat := 3487392183682856785765675

theorem tailTrace_6791672 : CollatzResearch.WordTrace tailWord_6791672 prefixEnd_6791672 3487392183682856785765675 := by
  unfold tailWord_6791672
  simp only [CollatzResearch.WordTrace]
  refine ⟨123856314125469872038172635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165141752167293162717563513 123856314125469872038172635)
  ·
    refine ⟨185784471188204808057258953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123856314125469872038172635 185784471188204808057258953)
    ·
      refine ⟨139338353391153606042944215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185784471188204808057258953 139338353391153606042944215)
      ·
        refine ⟨209007530086730409064416323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139338353391153606042944215 209007530086730409064416323)
        ·
          refine ⟨313511295130095613596624485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209007530086730409064416323 313511295130095613596624485)
          ·
            refine ⟨58783367836892927549367091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313511295130095613596624485 58783367836892927549367091)
            ·
              refine ⟨88175051755339391324050637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58783367836892927549367091 88175051755339391324050637)
              ·
                refine ⟨33065644408252271746518989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88175051755339391324050637 33065644408252271746518989)
                ·
                  refine ⟨12399616653094601904944621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33065644408252271746518989 12399616653094601904944621)
                  ·
                    refine ⟨4649856244910475714354233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12399616653094601904944621 4649856244910475714354233)
                    ·
                      refine ⟨3487392183682856785765675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4649856244910475714354233 3487392183682856785765675)
                      ·
                        rfl

theorem cell23_6791672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 3, 3, 2].length) (baseStart_6791672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791672 prefixEnd_6791672 := by exact prefixLift 6791672
  have htrace : WordTrace (prefixWord ++ tailWord_6791672) baseStart_6791672 baseEnd_6791672 := by
    simpa [prefixWord, tailWord_6791672, baseEnd_6791672] using wordTrace_append hprefix tailTrace_6791672
  have hstable : (prefixWord ++ tailWord_6791672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791672).length < 2 ^ (prefixWord ++ tailWord_6791672).sum := by decide
  have hdescent : baseEnd_6791672 < baseStart_6791672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791755 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 4, 5]
def baseStart_6791755 : Nat := 118140960795 + 6791755 * 2 ^ 59
def prefixEnd_6791755 : Nat := 4983230072969 + 3 ^ 40 * 6791755 * 2
def baseEnd_6791755 : Nat := 1162478267525726653675931

theorem tailTrace_6791755 : CollatzResearch.WordTrace tailWord_6791755 prefixEnd_6791755 1162478267525726653675931 := by
  unfold tailWord_6791755
  simp only [CollatzResearch.WordTrace]
  refine ⟨247715655509639049251616719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165143770339759366167744479 247715655509639049251616719)
  ·
    refine ⟨371573483264458573877425079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247715655509639049251616719 371573483264458573877425079)
    ·
      refine ⟨557360224896687860816137619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371573483264458573877425079 557360224896687860816137619)
      ·
        refine ⟨836040337345031791224206429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557360224896687860816137619 836040337345031791224206429)
        ·
          refine ⟨313515126504386921709077411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 836040337345031791224206429 313515126504386921709077411)
          ·
            refine ⟨470272689756580382563616117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313515126504386921709077411 470272689756580382563616117)
            ·
              refine ⟨44088064664679410865339011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 470272689756580382563616117 44088064664679410865339011)
              ·
                refine ⟨66132096997019116298008517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44088064664679410865339011 66132096997019116298008517)
                ·
                  refine ⟨12399768186941084305876597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66132096997019116298008517 12399768186941084305876597)
                  ·
                    refine ⟨1162478267525726653675931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12399768186941084305876597 1162478267525726653675931)
                    ·
                      rfl

theorem cell23_6791755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 5].length) (baseStart_6791755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791755 prefixEnd_6791755 := by exact prefixLift 6791755
  have htrace : WordTrace (prefixWord ++ tailWord_6791755) baseStart_6791755 baseEnd_6791755 := by
    simpa [prefixWord, tailWord_6791755, baseEnd_6791755] using wordTrace_append hprefix tailTrace_6791755
  have hstable : (prefixWord ++ tailWord_6791755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791755).length < 2 ^ (prefixWord ++ tailWord_6791755).sum := by decide
  have hdescent : baseEnd_6791755 < baseStart_6791755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791765 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_6791765 : Nat := 118140960795 + 6791765 * 2 ^ 59
def prefixEnd_6791765 : Nat := 4983230072969 + 3 ^ 40 * 6791765 * 2
def baseEnd_6791765 : Nat := 3487439937383724921902747

theorem tailTrace_6791765 : CollatzResearch.WordTrace tailWord_6791765 prefixEnd_6791765 3487439937383724921902747 := by
  unfold tailWord_6791765
  simp only [CollatzResearch.WordTrace]
  refine ⟨247716020239602820959480749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165144013493068547306320499 247716020239602820959480749)
  ·
    refine ⟨92893507589851057859805281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247716020239602820959480749 92893507589851057859805281)
    ·
      refine ⟨69670130692388293394853961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92893507589851057859805281 69670130692388293394853961)
      ·
        refine ⟨52252598019291220046140471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69670130692388293394853961 52252598019291220046140471)
        ·
          refine ⟨78378897028936830069210707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52252598019291220046140471 78378897028936830069210707)
          ·
            refine ⟨117568345543405245103816061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78378897028936830069210707 117568345543405245103816061)
            ·
              refine ⟨44088129578776966913931023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117568345543405245103816061 44088129578776966913931023)
              ·
                refine ⟨66132194368165450370896535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44088129578776966913931023 66132194368165450370896535)
                ·
                  refine ⟨99198291552248175556344803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66132194368165450370896535 99198291552248175556344803)
                  ·
                    refine ⟨148797437328372263334517205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99198291552248175556344803 148797437328372263334517205)
                    ·
                      refine ⟨3487439937383724921902747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148797437328372263334517205 3487439937383724921902747)
                      ·
                        rfl

theorem cell23_6791765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_6791765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791765 prefixEnd_6791765 := by exact prefixLift 6791765
  have htrace : WordTrace (prefixWord ++ tailWord_6791765) baseStart_6791765 baseEnd_6791765 := by
    simpa [prefixWord, tailWord_6791765, baseEnd_6791765] using wordTrace_append hprefix tailTrace_6791765
  have hstable : (prefixWord ++ tailWord_6791765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791765).length < 2 ^ (prefixWord ++ tailWord_6791765).sum := by decide
  have hdescent : baseEnd_6791765 < baseStart_6791765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791774 : List Nat := [4, 4, 1, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_6791774 : Nat := 118140960795 + 6791774 * 2 ^ 59
def prefixEnd_6791774 : Nat := 4983230072969 + 3 ^ 40 * 6791774 * 2
def baseEnd_6791774 : Nat := 3487444558709615386690207

theorem tailTrace_6791774 : CollatzResearch.WordTrace tailWord_6791774 prefixEnd_6791774 3487444558709615386690207 := by
  unfold tailWord_6791774
  simp only [CollatzResearch.WordTrace]
  refine ⟨30964543562071276937069797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165144232331046810331038917 30964543562071276937069797)
  ·
    refine ⟨5805851917888364425700587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30964543562071276937069797 5805851917888364425700587)
    ·
      refine ⟨8708777876832546638550881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5805851917888364425700587 8708777876832546638550881)
      ·
        refine ⟨6531583407624409978913161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8708777876832546638550881 6531583407624409978913161)
        ·
          refine ⟨4898687555718307484184871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6531583407624409978913161 4898687555718307484184871)
          ·
            refine ⟨7348031333577461226277307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4898687555718307484184871 7348031333577461226277307)
            ·
              refine ⟨11022047000366191839415961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7348031333577461226277307 11022047000366191839415961)
              ·
                refine ⟨8266535250274643879561971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11022047000366191839415961 8266535250274643879561971)
                ·
                  refine ⟨12399802875411965819342957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8266535250274643879561971 12399802875411965819342957)
                  ·
                    refine ⟨4649926078279487182253609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12399802875411965819342957 4649926078279487182253609)
                    ·
                      refine ⟨3487444558709615386690207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4649926078279487182253609 3487444558709615386690207)
                      ·
                        rfl

theorem cell23_6791774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_6791774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791774 prefixEnd_6791774 := by exact prefixLift 6791774
  have htrace : WordTrace (prefixWord ++ tailWord_6791774) baseStart_6791774 baseEnd_6791774 := by
    simpa [prefixWord, tailWord_6791774, baseEnd_6791774] using wordTrace_append hprefix tailTrace_6791774
  have hstable : (prefixWord ++ tailWord_6791774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791774).length < 2 ^ (prefixWord ++ tailWord_6791774).sum := by decide
  have hdescent : baseEnd_6791774 < baseStart_6791774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791775 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 4]
def baseStart_6791775 : Nat := 118140960795 + 6791775 * 2 ^ 59
def prefixEnd_6791775 : Nat := 4983230072969 + 3 ^ 40 * 6791775 * 2
def baseEnd_6791775 : Nat := 3487445072190269882777701

theorem tailTrace_6791775 : CollatzResearch.WordTrace tailWord_6791775 prefixEnd_6791775 3487445072190269882777701 := by
  unfold tailWord_6791775
  simp only [CollatzResearch.WordTrace]
  refine ⟨247716384969566592667344779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165144256646377728444896519 247716384969566592667344779)
  ·
    refine ⟨371574577454349889001017169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247716384969566592667344779 371574577454349889001017169)
    ·
      refine ⟨278680933090762416750762877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371574577454349889001017169 278680933090762416750762877)
      ·
        refine ⟨104505349909035906281536079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278680933090762416750762877 104505349909035906281536079)
        ·
          refine ⟨156758024863553859422304119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104505349909035906281536079 156758024863553859422304119)
          ·
            refine ⟨235137037295330789133456179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156758024863553859422304119 235137037295330789133456179)
            ·
              refine ⟨352705555942996183700184269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235137037295330789133456179 352705555942996183700184269)
              ·
                refine ⟨132264583478623568887569101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352705555942996183700184269 132264583478623568887569101)
                ·
                  refine ⟨49599218804483838332838413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132264583478623568887569101 49599218804483838332838413)
                  ·
                    refine ⟨18599707051681439374814405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49599218804483838332838413 18599707051681439374814405)
                    ·
                      refine ⟨3487445072190269882777701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18599707051681439374814405 3487445072190269882777701)
                      ·
                        rfl

theorem cell23_6791775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_6791775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791775 prefixEnd_6791775 := by exact prefixLift 6791775
  have htrace : WordTrace (prefixWord ++ tailWord_6791775) baseStart_6791775 baseEnd_6791775 := by
    simpa [prefixWord, tailWord_6791775, baseEnd_6791775] using wordTrace_append hprefix tailTrace_6791775
  have hstable : (prefixWord ++ tailWord_6791775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791775).length < 2 ^ (prefixWord ++ tailWord_6791775).sum := by decide
  have hdescent : baseEnd_6791775 < baseStart_6791775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791789 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_6791789 : Nat := 118140960795 + 6791789 * 2 ^ 59
def prefixEnd_6791789 : Nat := 4983230072969 + 3 ^ 40 * 6791789 * 2
def baseEnd_6791789 : Nat := 1162484086973144276000879

theorem tailTrace_6791789 : CollatzResearch.WordTrace tailWord_6791789 prefixEnd_6791789 1162484086973144276000879 := by
  unfold tailWord_6791789
  simp only [CollatzResearch.WordTrace]
  refine ⟨247716895591515873058354421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165144597061010582038902947 247716895591515873058354421)
  ·
    refine ⟨23223458961704613099220727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247716895591515873058354421 23223458961704613099220727)
    ·
      refine ⟨34835188442556919648831091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23223458961704613099220727 34835188442556919648831091)
      ·
        refine ⟨52252782663835379473246637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34835188442556919648831091 52252782663835379473246637)
        ·
          refine ⟨19594793498938267302467489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52252782663835379473246637 19594793498938267302467489)
          ·
            refine ⟨14696095124203700476850617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19594793498938267302467489 14696095124203700476850617)
            ·
              refine ⟨11022071343152775357637963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14696095124203700476850617 11022071343152775357637963)
              ·
                refine ⟨16533107014729163036456945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11022071343152775357637963 16533107014729163036456945)
                ·
                  refine ⟨12399830261046872277342709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16533107014729163036456945 12399830261046872277342709)
                  ·
                    refine ⟨1162484086973144276000879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12399830261046872277342709 1162484086973144276000879)
                    ·
                      rfl

theorem cell23_6791789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_6791789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791789 prefixEnd_6791789 := by exact prefixLift 6791789
  have htrace : WordTrace (prefixWord ++ tailWord_6791789) baseStart_6791789 baseEnd_6791789 := by
    simpa [prefixWord, tailWord_6791789, baseEnd_6791789] using wordTrace_append hprefix tailTrace_6791789
  have hstable : (prefixWord ++ tailWord_6791789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791789).length < 2 ^ (prefixWord ++ tailWord_6791789).sum := by decide
  have hdescent : baseEnd_6791789 < baseStart_6791789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791809 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 2, 4, 2]
def baseStart_6791809 : Nat := 118140960795 + 6791809 * 2 ^ 59
def prefixEnd_6791809 : Nat := 4983230072969 + 3 ^ 40 * 6791809 * 2
def baseEnd_6791809 : Nat := 3487462530532522749752545

theorem tailTrace_6791809 : CollatzResearch.WordTrace tailWord_6791809 prefixEnd_6791809 3487462530532522749752545 := by
  unfold tailWord_6791809
  simp only [CollatzResearch.WordTrace]
  refine ⟨247717625051443416474082481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165145083367628944316054987 247717625051443416474082481)
  ·
    refine ⟨185788218788582562355561861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247717625051443416474082481 185788218788582562355561861)
    ·
      refine ⟨34835291022859230441667849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185788218788582562355561861 34835291022859230441667849)
      ·
        refine ⟨26126468267144422831250887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34835291022859230441667849 26126468267144422831250887)
        ·
          refine ⟨39189702400716634246876331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26126468267144422831250887 39189702400716634246876331)
          ·
            refine ⟨58784553601074951370314497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39189702400716634246876331 58784553601074951370314497)
            ·
              refine ⟨44088415200806213527735873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58784553601074951370314497 44088415200806213527735873)
              ·
                refine ⟨33066311400604660145801905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44088415200806213527735873 33066311400604660145801905)
                ·
                  refine ⟨24799733550453495109351429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33066311400604660145801905 24799733550453495109351429)
                  ·
                    refine ⟨4649950040710030333003393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24799733550453495109351429 4649950040710030333003393)
                    ·
                      refine ⟨3487462530532522749752545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4649950040710030333003393 3487462530532522749752545)
                      ·
                        rfl

theorem cell23_6791809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_6791809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791809 prefixEnd_6791809 := by exact prefixLift 6791809
  have htrace : WordTrace (prefixWord ++ tailWord_6791809) baseStart_6791809 baseEnd_6791809 := by
    simpa [prefixWord, tailWord_6791809, baseEnd_6791809] using wordTrace_append hprefix tailTrace_6791809
  have hstable : (prefixWord ++ tailWord_6791809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791809).length < 2 ^ (prefixWord ++ tailWord_6791809).sum := by decide
  have hdescent : baseEnd_6791809 < baseStart_6791809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791810 : List Nat := [3, 4, 3, 1, 1, 1, 1, 4, 5]
def baseStart_6791810 : Nat := 118140960795 + 6791810 * 2 ^ 59
def prefixEnd_6791810 : Nat := 4983230072969 + 3 ^ 40 * 6791810 * 2
def baseEnd_6791810 : Nat := 387495893779241916204449

theorem tailTrace_6791810 : CollatzResearch.WordTrace tailWord_6791810 prefixEnd_6791810 387495893779241916204449 := by
  unfold tailWord_6791810
  simp only [CollatzResearch.WordTrace]
  refine ⟨61929415381109948411217221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165145107682959862429912589 61929415381109948411217221)
  ·
    refine ⟨11611765383958115327103229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61929415381109948411217221 11611765383958115327103229)
    ·
      refine ⟨4354412018984293247663711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11611765383958115327103229 4354412018984293247663711)
      ·
        refine ⟨6531618028476439871495567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4354412018984293247663711 6531618028476439871495567)
        ·
          refine ⟨9797427042714659807243351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6531618028476439871495567 9797427042714659807243351)
          ·
            refine ⟨14696140564071989710865027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9797427042714659807243351 14696140564071989710865027)
            ·
              refine ⟨22044210846107984566297541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14696140564071989710865027 22044210846107984566297541)
              ·
                refine ⟨4133289533645247106180789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22044210846107984566297541 4133289533645247106180789)
                ·
                  refine ⟨387495893779241916204449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4133289533645247106180789 387495893779241916204449)
                  ·
                    rfl

theorem cell23_6791810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_6791810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791810 prefixEnd_6791810 := by exact prefixLift 6791810
  have htrace : WordTrace (prefixWord ++ tailWord_6791810) baseStart_6791810 baseEnd_6791810 := by
    simpa [prefixWord, tailWord_6791810, baseEnd_6791810] using wordTrace_append hprefix tailTrace_6791810
  have hstable : (prefixWord ++ tailWord_6791810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791810).length < 2 ^ (prefixWord ++ tailWord_6791810).sum := by decide
  have hdescent : baseEnd_6791810 < baseStart_6791810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791826 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_6791826 : Nat := 118140960795 + 6791826 * 2 ^ 59
def prefixEnd_6791826 : Nat := 4983230072969 + 3 ^ 40 * 6791826 * 2
def baseEnd_6791826 : Nat := 3487471259703649183239967

theorem tailTrace_6791826 : CollatzResearch.WordTrace tailWord_6791826 prefixEnd_6791826 3487471259703649183239967 := by
  unfold tailWord_6791826
  simp only [CollatzResearch.WordTrace]
  refine ⟨61929561273095457094362833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165145496728254552251634221 61929561273095457094362833)
  ·
    refine ⟨46447170954821592820772125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61929561273095457094362833 46447170954821592820772125)
    ·
      refine ⟨17417689108058097307789547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46447170954821592820772125 17417689108058097307789547)
      ·
        refine ⟨26126533662087145961684321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17417689108058097307789547 26126533662087145961684321)
        ·
          refine ⟨19594900246565359471263241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26126533662087145961684321 19594900246565359471263241)
          ·
            refine ⟨14696175184924019603447431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19594900246565359471263241 14696175184924019603447431)
            ·
              refine ⟨22044262777386029405171147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14696175184924019603447431 22044262777386029405171147)
              ·
                refine ⟨33066394166079044107756721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22044262777386029405171147 33066394166079044107756721)
                ·
                  refine ⟨24799795624559283080817541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33066394166079044107756721 24799795624559283080817541)
                  ·
                    refine ⟨4649961679604865577653289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24799795624559283080817541 4649961679604865577653289)
                    ·
                      refine ⟨3487471259703649183239967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4649961679604865577653289 3487471259703649183239967)
                      ·
                        rfl

theorem cell23_6791826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_6791826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791826 prefixEnd_6791826 := by exact prefixLift 6791826
  have htrace : WordTrace (prefixWord ++ tailWord_6791826) baseStart_6791826 baseEnd_6791826 := by
    simpa [prefixWord, tailWord_6791826, baseEnd_6791826] using wordTrace_append hprefix tailTrace_6791826
  have hstable : (prefixWord ++ tailWord_6791826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791826).length < 2 ^ (prefixWord ++ tailWord_6791826).sum := by decide
  have hdescent : baseEnd_6791826 < baseStart_6791826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791832 : List Nat := [2, 1, 2, 4, 1, 1, 1, 5, 6]
def baseStart_6791832 : Nat := 118140960795 + 6791832 * 2 ^ 59
def prefixEnd_6791832 : Nat := 4983230072969 + 3 ^ 40 * 6791832 * 2
def baseEnd_6791832 : Nat := 387497148954175128862771

theorem tailTrace_6791832 : CollatzResearch.WordTrace tailWord_6791832 prefixEnd_6791832 387497148954175128862771 := by
  unfold tailWord_6791832
  simp only [CollatzResearch.WordTrace]
  refine ⟨123859231965180045701084875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165145642620240060934779833 123859231965180045701084875)
  ·
    refine ⟨185788847947770068551627313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123859231965180045701084875 185788847947770068551627313)
    ·
      refine ⟨139341635960827551413720485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185788847947770068551627313 139341635960827551413720485)
      ·
        refine ⟨26126556742655165890072591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139341635960827551413720485 26126556742655165890072591)
        ·
          refine ⟨39189835113982748835108887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26126556742655165890072591 39189835113982748835108887)
          ·
            refine ⟨58784752670974123252663331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39189835113982748835108887 58784752670974123252663331)
            ·
              refine ⟨88177129006461184878994997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58784752670974123252663331 88177129006461184878994997)
              ·
                refine ⟨8266605844355736082405781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88177129006461184878994997 8266605844355736082405781)
                ·
                  refine ⟨387497148954175128862771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8266605844355736082405781 387497148954175128862771)
                  ·
                    rfl

theorem cell23_6791832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 6].length) (baseStart_6791832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791832 prefixEnd_6791832 := by exact prefixLift 6791832
  have htrace : WordTrace (prefixWord ++ tailWord_6791832) baseStart_6791832 baseEnd_6791832 := by
    simpa [prefixWord, tailWord_6791832, baseEnd_6791832] using wordTrace_append hprefix tailTrace_6791832
  have hstable : (prefixWord ++ tailWord_6791832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791832).length < 2 ^ (prefixWord ++ tailWord_6791832).sum := by decide
  have hdescent : baseEnd_6791832 < baseStart_6791832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791853 : List Nat := [1, 5, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_6791853 : Nat := 118140960795 + 6791853 * 2 ^ 59
def prefixEnd_6791853 : Nat := 4983230072969 + 3 ^ 40 * 6791853 * 2
def baseEnd_6791853 : Nat := 1162495041227106859200781

theorem tailTrace_6791853 : CollatzResearch.WordTrace tailWord_6791853 prefixEnd_6791853 1162495041227106859200781 := by
  unfold tailWord_6791853
  simp only [CollatzResearch.WordTrace]
  refine ⟨247719229863284011988684213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165146153242189341325789475 247719229863284011988684213)
  ·
    refine ⟨23223677799682876123939145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247719229863284011988684213 23223677799682876123939145)
    ·
      refine ⟨17417758349762157092954359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23223677799682876123939145 17417758349762157092954359)
      ·
        refine ⟨26126637524643235639431539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17417758349762157092954359 26126637524643235639431539)
        ·
          refine ⟨39189956286964853459147309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26126637524643235639431539 39189956286964853459147309)
          ·
            refine ⟨14696233607611820047180241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39189956286964853459147309 14696233607611820047180241)
            ·
              refine ⟨11022175205708865035385181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14696233607611820047180241 11022175205708865035385181)
              ·
                refine ⟨4133315702140824388269443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11022175205708865035385181 4133315702140824388269443)
                ·
                  refine ⟨6199973553211236582404165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133315702140824388269443 6199973553211236582404165)
                  ·
                    refine ⟨1162495041227106859200781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6199973553211236582404165 1162495041227106859200781)
                    ·
                      rfl

theorem cell23_6791853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_6791853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791853 prefixEnd_6791853 := by exact prefixLift 6791853
  have htrace : WordTrace (prefixWord ++ tailWord_6791853) baseStart_6791853 baseEnd_6791853 := by
    simpa [prefixWord, tailWord_6791853, baseEnd_6791853] using wordTrace_append hprefix tailTrace_6791853
  have hstable : (prefixWord ++ tailWord_6791853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791853).length < 2 ^ (prefixWord ++ tailWord_6791853).sum := by decide
  have hdescent : baseEnd_6791853 < baseStart_6791853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791875 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 1, 12]
def baseStart_6791875 : Nat := 118140960795 + 6791875 * 2 ^ 59
def prefixEnd_6791875 : Nat := 4983230072969 + 3 ^ 40 * 6791875 * 2
def baseEnd_6791875 : Nat := 1162498806751906497175747

theorem tailTrace_6791875 : CollatzResearch.WordTrace tailWord_6791875 prefixEnd_6791875 1162498806751906497175747 := by
  unfold tailWord_6791875
  simp only [CollatzResearch.WordTrace]
  refine ⟨247720032269204309745985079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165146688179469539830656719 247720032269204309745985079)
  ·
    refine ⟨371580048403806464618977619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247720032269204309745985079 371580048403806464618977619)
    ·
      refine ⟨557370072605709696928466429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371580048403806464618977619 557370072605709696928466429)
      ·
        refine ⟨209013777227141136348174911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 557370072605709696928466429 209013777227141136348174911)
        ·
          refine ⟨313520665840711704522262367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209013777227141136348174911 313520665840711704522262367)
          ·
            refine ⟨470280998761067556783393551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313520665840711704522262367 470280998761067556783393551)
            ·
              refine ⟨705421498141601335175090327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470280998761067556783393551 705421498141601335175090327)
              ·
                refine ⟨1058132247212402002762635491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705421498141601335175090327 1058132247212402002762635491)
                ·
                  refine ⟨1587198370818603004143953237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1058132247212402002762635491 1587198370818603004143953237)
                  ·
                    refine ⟨1162498806751906497175747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1587198370818603004143953237 1162498806751906497175747)
                    ·
                      rfl

theorem cell23_6791875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 12].length) (baseStart_6791875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791875 prefixEnd_6791875 := by exact prefixLift 6791875
  have htrace : WordTrace (prefixWord ++ tailWord_6791875) baseStart_6791875 baseEnd_6791875 := by
    simpa [prefixWord, tailWord_6791875, baseEnd_6791875] using wordTrace_append hprefix tailTrace_6791875
  have hstable : (prefixWord ++ tailWord_6791875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791875).length < 2 ^ (prefixWord ++ tailWord_6791875).sum := by decide
  have hdescent : baseEnd_6791875 < baseStart_6791875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791876 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_6791876 : Nat := 118140960795 + 6791876 * 2 ^ 59
def prefixEnd_6791876 : Nat := 4983230072969 + 3 ^ 40 * 6791876 * 2
def baseEnd_6791876 : Nat := 3487496933736373987614737

theorem tailTrace_6791876 : CollatzResearch.WordTrace tailWord_6791876 prefixEnd_6791876 3487496933736373987614737 := by
  unfold tailWord_6791876
  simp only [CollatzResearch.WordTrace]
  refine ⟨123860034371100343458385741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165146712494800457944514321 123860034371100343458385741)
  ·
    refine ⟨46447512889162628796894653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123860034371100343458385741 46447512889162628796894653)
    ·
      refine ⟨17417817333435985798835495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46447512889162628796894653 17417817333435985798835495)
      ·
        refine ⟨26126726000153978698253243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17417817333435985798835495 26126726000153978698253243)
        ·
          refine ⟨39190089000230968047379865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26126726000153978698253243 39190089000230968047379865)
          ·
            refine ⟨29392566750173226035534899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39190089000230968047379865 29392566750173226035534899)
            ·
              refine ⟨44088850125259839053302349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29392566750173226035534899 44088850125259839053302349)
              ·
                refine ⟨16533318796972439644988381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44088850125259839053302349 16533318796972439644988381)
                ·
                  refine ⟨6199994548864664866870643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16533318796972439644988381 6199994548864664866870643)
                  ·
                    refine ⟨9299991823296997300305965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6199994548864664866870643 9299991823296997300305965)
                    ·
                      refine ⟨3487496933736373987614737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9299991823296997300305965 3487496933736373987614737)
                      ·
                        rfl

theorem cell23_6791876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_6791876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791876 prefixEnd_6791876 := by exact prefixLift 6791876
  have htrace : WordTrace (prefixWord ++ tailWord_6791876) baseStart_6791876 baseEnd_6791876 := by
    simpa [prefixWord, tailWord_6791876, baseEnd_6791876] using wordTrace_append hprefix tailTrace_6791876
  have hstable : (prefixWord ++ tailWord_6791876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791876).length < 2 ^ (prefixWord ++ tailWord_6791876).sum := by decide
  have hdescent : baseEnd_6791876 < baseStart_6791876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791909 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 4, 4]
def baseStart_6791909 : Nat := 118140960795 + 6791909 * 2 ^ 59
def prefixEnd_6791909 : Nat := 4983230072969 + 3 ^ 40 * 6791909 * 2
def baseEnd_6791909 : Nat := 1162504626199324119500695

theorem tailTrace_6791909 : CollatzResearch.WordTrace tailWord_6791909 prefixEnd_6791909 1162504626199324119500695 := by
  unfold tailWord_6791909
  simp only [CollatzResearch.WordTrace]
  refine ⟨247721272351081133552722781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165147514900720755701815187 247721272351081133552722781)
  ·
    refine ⟨92895477131655425082271043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247721272351081133552722781 92895477131655425082271043)
    ·
      refine ⟨139343215697483137623406565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92895477131655425082271043 139343215697483137623406565)
      ·
        refine ⟨26126852943278088304388731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139343215697483137623406565 26126852943278088304388731)
        ·
          refine ⟨39190279414917132456583097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26126852943278088304388731 39190279414917132456583097)
          ·
            refine ⟨29392709561187849342437323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39190279414917132456583097 29392709561187849342437323)
            ·
              refine ⟨44089064341781774013655985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29392709561187849342437323 44089064341781774013655985)
              ·
                refine ⟨33066798256336330510241989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44089064341781774013655985 33066798256336330510241989)
                ·
                  refine ⟨6200024673063061970670373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33066798256336330510241989 6200024673063061970670373)
                  ·
                    refine ⟨1162504626199324119500695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6200024673063061970670373 1162504626199324119500695)
                    ·
                      rfl

theorem cell23_6791909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_6791909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791909 prefixEnd_6791909 := by exact prefixLift 6791909
  have htrace : WordTrace (prefixWord ++ tailWord_6791909) baseStart_6791909 baseEnd_6791909 := by
    simpa [prefixWord, tailWord_6791909, baseEnd_6791909] using wordTrace_append hprefix tailTrace_6791909
  have hstable : (prefixWord ++ tailWord_6791909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791909).length < 2 ^ (prefixWord ++ tailWord_6791909).sum := by decide
  have hdescent : baseEnd_6791909 < baseStart_6791909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791919 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 5]
def baseStart_6791919 : Nat := 118140960795 + 6791919 * 2 ^ 59
def prefixEnd_6791919 : Nat := 4983230072969 + 3 ^ 40 * 6791919 * 2
def baseEnd_6791919 : Nat := 3487519013404517319377039

theorem tailTrace_6791919 : CollatzResearch.WordTrace tailWord_6791919 prefixEnd_6791919 3487519013404517319377039 := by
  unfold tailWord_6791919
  simp only [CollatzResearch.WordTrace]
  refine ⟨247721637081044905260586811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165147758054029936840391207 247721637081044905260586811)
  ·
    refine ⟨371582455621567357890880217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247721637081044905260586811 371582455621567357890880217)
    ·
      refine ⟨278686841716175518418160163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371582455621567357890880217 278686841716175518418160163)
      ·
        refine ⟨418030262574263277627240245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278686841716175518418160163 418030262574263277627240245)
        ·
          refine ⟨39190337116337182277553773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 418030262574263277627240245 39190337116337182277553773)
          ·
            refine ⟨14696376418626443354082665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39190337116337182277553773 14696376418626443354082665)
            ·
              refine ⟨11022282313969832515561999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14696376418626443354082665 11022282313969832515561999)
              ·
                refine ⟨16533423470954748773342999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11022282313969832515561999 16533423470954748773342999)
                ·
                  refine ⟨24800135206432123160014499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16533423470954748773342999 24800135206432123160014499)
                  ·
                    refine ⟨37200202809648184740021749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24800135206432123160014499 37200202809648184740021749)
                    ·
                      refine ⟨3487519013404517319377039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37200202809648184740021749 3487519013404517319377039)
                      ·
                        rfl

theorem cell23_6791919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 5].length) (baseStart_6791919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791919 prefixEnd_6791919 := by exact prefixLift 6791919
  have htrace : WordTrace (prefixWord ++ tailWord_6791919) baseStart_6791919 baseEnd_6791919 := by
    simpa [prefixWord, tailWord_6791919, baseEnd_6791919] using wordTrace_append hprefix tailTrace_6791919
  have hstable : (prefixWord ++ tailWord_6791919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791919).length < 2 ^ (prefixWord ++ tailWord_6791919).sum := by decide
  have hdescent : baseEnd_6791919 < baseStart_6791919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791922 : List Nat := [3, 2, 1, 3, 1, 2, 11]
def baseStart_6791922 : Nat := 118140960795 + 6791922 * 2 ^ 59
def prefixEnd_6791922 : Nat := 4983230072969 + 3 ^ 40 * 6791922 * 2
def baseEnd_6791922 : Nat := 43055809306746676637525

theorem tailTrace_6791922 : CollatzResearch.WordTrace tailWord_6791922 prefixEnd_6791922 43055809306746676637525 := by
  unfold tailWord_6791922
  simp only [CollatzResearch.WordTrace]
  refine ⟨61930436625008509193236505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165147831000022691181964013 61930436625008509193236505)
  ·
    refine ⟨46447827468756381894927379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61930436625008509193236505 46447827468756381894927379)
    ·
      refine ⟨69671741203134572842391069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46447827468756381894927379 69671741203134572842391069)
      ·
        refine ⟨26126902951175464815896651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69671741203134572842391069 26126902951175464815896651)
        ·
          refine ⟨39190354426763197223844977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26126902951175464815896651 39190354426763197223844977)
          ·
            refine ⟨29392765820072397917883733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39190354426763197223844977 29392765820072397917883733)
            ·
              refine ⟨43055809306746676637525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29392765820072397917883733 43055809306746676637525)
              ·
                rfl

theorem cell23_6791922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 11].length) (baseStart_6791922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791922 prefixEnd_6791922 := by exact prefixLift 6791922
  have htrace : WordTrace (prefixWord ++ tailWord_6791922) baseStart_6791922 baseEnd_6791922 := by
    simpa [prefixWord, tailWord_6791922, baseEnd_6791922] using wordTrace_append hprefix tailTrace_6791922
  have hstable : (prefixWord ++ tailWord_6791922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791922).length < 2 ^ (prefixWord ++ tailWord_6791922).sum := by decide
  have hdescent : baseEnd_6791922 < baseStart_6791922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791926 : List Nat := [5, 1, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_6791926 : Nat := 118140960795 + 6791926 * 2 ^ 59
def prefixEnd_6791926 : Nat := 4983230072969 + 3 ^ 40 * 6791926 * 2
def baseEnd_6791926 : Nat := 1162507535923032930663169

theorem tailTrace_6791926 : CollatzResearch.WordTrace tailWord_6791926 prefixEnd_6791926 1162507535923032930663169 := by
  unfold tailWord_6791926
  simp only [CollatzResearch.WordTrace]
  refine ⟨15482618274501221591005727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165147928261346363637394421 15482618274501221591005727)
  ·
    refine ⟨23223927411751832386508591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15482618274501221591005727 23223927411751832386508591)
    ·
      refine ⟨34835891117627748579762887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23223927411751832386508591 34835891117627748579762887)
      ·
        refine ⟨52253836676441622869644331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34835891117627748579762887 52253836676441622869644331)
        ·
          refine ⟨78380755014662434304466497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52253836676441622869644331 78380755014662434304466497)
          ·
            refine ⟨58785566260996825728349873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78380755014662434304466497 58785566260996825728349873)
            ·
              refine ⟨44089174695747619296262405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58785566260996825728349873 44089174695747619296262405)
              ·
                refine ⟨8266720255452678618049201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44089174695747619296262405 8266720255452678618049201)
                ·
                  refine ⟨6200040191589508963536901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8266720255452678618049201 6200040191589508963536901)
                  ·
                    refine ⟨1162507535923032930663169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6200040191589508963536901 1162507535923032930663169)
                    ·
                      rfl

theorem cell23_6791926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_6791926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791926 prefixEnd_6791926 := by exact prefixLift 6791926
  have htrace : WordTrace (prefixWord ++ tailWord_6791926) baseStart_6791926 baseEnd_6791926 := by
    simpa [prefixWord, tailWord_6791926, baseEnd_6791926] using wordTrace_append hprefix tailTrace_6791926
  have hstable : (prefixWord ++ tailWord_6791926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791926).length < 2 ^ (prefixWord ++ tailWord_6791926).sum := by decide
  have hdescent : baseEnd_6791926 < baseStart_6791926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791943 : List Nat := [1, 1, 4, 4, 1, 1, 4, 1, 2, 4]
def baseStart_6791943 : Nat := 118140960795 + 6791943 * 2 ^ 59
def prefixEnd_6791943 : Nat := 4983230072969 + 3 ^ 40 * 6791943 * 2
def baseEnd_6791943 : Nat := 1162510445646741741825643

theorem tailTrace_6791943 : CollatzResearch.WordTrace tailWord_6791943 prefixEnd_6791943 1162510445646741741825643 := by
  unfold tailWord_6791943
  simp only [CollatzResearch.WordTrace]
  refine ⟨247722512432957957359460483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165148341621971971572973655 247722512432957957359460483)
  ·
    refine ⟨371583768649436936039190725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247722512432957957359460483 371583768649436936039190725)
    ·
      refine ⟨69671956621769425507348261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371583768649436936039190725 69671956621769425507348261)
      ·
        refine ⟨13063491866581767282627799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69671956621769425507348261 13063491866581767282627799)
        ·
          refine ⟨19595237799872650923941699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13063491866581767282627799 19595237799872650923941699)
          ·
            refine ⟨29392856699808976385912549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19595237799872650923941699 29392856699808976385912549)
            ·
              refine ⟨5511160631214183072358603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29392856699808976385912549 5511160631214183072358603)
              ·
                refine ⟨8266740946821274608537905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5511160631214183072358603 8266740946821274608537905)
                ·
                  refine ⟨6200055710115955956403429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8266740946821274608537905 6200055710115955956403429)
                  ·
                    refine ⟨1162510445646741741825643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6200055710115955956403429 1162510445646741741825643)
                    ·
                      rfl

theorem cell23_6791943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_6791943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791943 prefixEnd_6791943 := by exact prefixLift 6791943
  have htrace : WordTrace (prefixWord ++ tailWord_6791943) baseStart_6791943 baseEnd_6791943 := by
    simpa [prefixWord, tailWord_6791943, baseEnd_6791943] using wordTrace_append hprefix tailTrace_6791943
  have hstable : (prefixWord ++ tailWord_6791943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791943).length < 2 ^ (prefixWord ++ tailWord_6791943).sum := by decide
  have hdescent : baseEnd_6791943 < baseStart_6791943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791989 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_6791989 : Nat := 118140960795 + 6791989 * 2 ^ 59
def prefixEnd_6791989 : Nat := 4983230072969 + 3 ^ 40 * 6791989 * 2
def baseEnd_6791989 : Nat := 3487554957050332045501717

theorem tailTrace_6791989 : CollatzResearch.WordTrace tailWord_6791989 prefixEnd_6791989 3487554957050332045501717 := by
  unfold tailWord_6791989
  simp only [CollatzResearch.WordTrace]
  refine ⟨247724190190791307215635021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165149460127194204810423347 247724190190791307215635021)
  ·
    refine ⟨92896571321546740205863133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247724190190791307215635021 92896571321546740205863133)
    ·
      refine ⟨34836214245580027577198675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92896571321546740205863133 34836214245580027577198675)
      ·
        refine ⟨52254321368370041365798013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34836214245580027577198675 52254321368370041365798013)
        ·
          refine ⟨19595370513138765512174255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52254321368370041365798013 19595370513138765512174255)
          ·
            refine ⟨29393055769708148268261383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19595370513138765512174255 29393055769708148268261383)
            ·
              refine ⟨44089583654562222402392075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29393055769708148268261383 44089583654562222402392075)
              ·
                refine ⟨66134375481843333603588113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44089583654562222402392075 66134375481843333603588113)
                ·
                  refine ⟨49600781611382500202691085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66134375481843333603588113 49600781611382500202691085)
                  ·
                    refine ⟨18600293104268437576009157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49600781611382500202691085 18600293104268437576009157)
                    ·
                      refine ⟨3487554957050332045501717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18600293104268437576009157 3487554957050332045501717)
                      ·
                        rfl

theorem cell23_6791989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_6791989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791989 prefixEnd_6791989 := by exact prefixLift 6791989
  have htrace : WordTrace (prefixWord ++ tailWord_6791989) baseStart_6791989 baseEnd_6791989 := by
    simpa [prefixWord, tailWord_6791989, baseEnd_6791989] using wordTrace_append hprefix tailTrace_6791989
  have hstable : (prefixWord ++ tailWord_6791989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791989).length < 2 ^ (prefixWord ++ tailWord_6791989).sum := by decide
  have hdescent : baseEnd_6791989 < baseStart_6791989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6791999 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 2, 6]
def baseStart_6791999 : Nat := 118140960795 + 6791999 * 2 ^ 59
def prefixEnd_6791999 : Nat := 4983230072969 + 3 ^ 40 * 6791999 * 2
def baseEnd_6791999 : Nat := 1162520030618959002125557

theorem tailTrace_6791999 : CollatzResearch.WordTrace tailWord_6791999 prefixEnd_6791999 1162520030618959002125557 := by
  unfold tailWord_6791999
  simp only [CollatzResearch.WordTrace]
  refine ⟨247724554920755078923499051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165149703280503385948999367 247724554920755078923499051)
  ·
    refine ⟨371586832381132618385248577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247724554920755078923499051 371586832381132618385248577)
    ·
      refine ⟨278690124285849463788936433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371586832381132618385248577 278690124285849463788936433)
      ·
        refine ⟨209017593214387097841702325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278690124285849463788936433 209017593214387097841702325)
        ·
          refine ⟨19595399363848790422659593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 209017593214387097841702325 19595399363848790422659593)
          ·
            refine ⟨14696549522886592816994695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19595399363848790422659593 14696549522886592816994695)
            ·
              refine ⟨22044824284329889225492043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14696549522886592816994695 22044824284329889225492043)
              ·
                refine ⟨33067236426494833838238065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22044824284329889225492043 33067236426494833838238065)
                ·
                  refine ⟨24800427319871125378678549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33067236426494833838238065 24800427319871125378678549)
                  ·
                    refine ⟨1162520030618959002125557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24800427319871125378678549 1162520030618959002125557)
                    ·
                      rfl

theorem cell23_6791999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 6].length) (baseStart_6791999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6791999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6791999 prefixEnd_6791999 := by exact prefixLift 6791999
  have htrace : WordTrace (prefixWord ++ tailWord_6791999) baseStart_6791999 baseEnd_6791999 := by
    simpa [prefixWord, tailWord_6791999, baseEnd_6791999] using wordTrace_append hprefix tailTrace_6791999
  have hstable : (prefixWord ++ tailWord_6791999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6791999).length < 2 ^ (prefixWord ++ tailWord_6791999).sum := by decide
  have hdescent : baseEnd_6791999 < baseStart_6791999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6791999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792040 : List Nat := [2, 1, 4, 2, 1, 2, 3, 2, 2, 2, 2]
def baseStart_6792040 : Nat := 118140960795 + 6792040 * 2 ^ 59
def prefixEnd_6792040 : Nat := 4983230072969 + 3 ^ 40 * 6792040 * 2
def baseEnd_6792040 : Nat := 3487581144563711345963983

theorem tailTrace_6792040 : CollatzResearch.WordTrace tailWord_6792040 prefixEnd_6792040 3487581144563711345963983 := by
  unfold tailWord_6792040
  simp only [CollatzResearch.WordTrace]
  refine ⟨123863025156803271462870787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165150700209071028617161049 123863025156803271462870787)
  ·
    refine ⟨185794537735204907194306181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123863025156803271462870787 185794537735204907194306181)
    ·
      refine ⟨34836475825350920098932409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185794537735204907194306181 34836475825350920098932409)
      ·
        refine ⟨26127356869013190074199307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34836475825350920098932409 26127356869013190074199307)
        ·
          refine ⟨39191035303519785111298961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26127356869013190074199307 39191035303519785111298961)
          ·
            refine ⟨29393276477639838833474221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39191035303519785111298961 29393276477639838833474221)
            ·
              refine ⟨11022478679114939562552833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29393276477639838833474221 11022478679114939562552833)
              ·
                refine ⟨8266859009336204671914625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11022478679114939562552833 8266859009336204671914625)
                ·
                  refine ⟨6200144257002153503935969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8266859009336204671914625 6200144257002153503935969)
                  ·
                    refine ⟨4650108192751615127951977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6200144257002153503935969 4650108192751615127951977)
                    ·
                      refine ⟨3487581144563711345963983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4650108192751615127951977 3487581144563711345963983)
                      ·
                        rfl

theorem cell23_6792040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_6792040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792040 prefixEnd_6792040 := by exact prefixLift 6792040
  have htrace : WordTrace (prefixWord ++ tailWord_6792040) baseStart_6792040 baseEnd_6792040 := by
    simpa [prefixWord, tailWord_6792040, baseEnd_6792040] using wordTrace_append hprefix tailTrace_6792040
  have hstable : (prefixWord ++ tailWord_6792040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792040).length < 2 ^ (prefixWord ++ tailWord_6792040).sum := by decide
  have hdescent : baseEnd_6792040 < baseStart_6792040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792096 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 4, 4, 2]
def baseStart_6792096 : Nat := 118140960795 + 6792096 * 2 ^ 59
def prefixEnd_6792096 : Nat := 4983230072969 + 3 ^ 40 * 6792096 * 2
def baseEnd_6792096 : Nat := 3487609899480363126863725

theorem tailTrace_6792096 : CollatzResearch.WordTrace tailWord_6792096 prefixEnd_6792096 3487609899480363126863725 := by
  unfold tailWord_6792096
  simp only [CollatzResearch.WordTrace]
  refine ⟨123864046400701832244890071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165152061867602442993186761 123864046400701832244890071)
  ·
    refine ⟨185796069601052748367335107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123864046400701832244890071 185796069601052748367335107)
    ·
      refine ⟨278694104401579122551002661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185796069601052748367335107 278694104401579122551002661)
      ·
        refine ⟨52255144575296085478312999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278694104401579122551002661 52255144575296085478312999)
        ·
          refine ⟨78382716862944128217469499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52255144575296085478312999 78382716862944128217469499)
          ·
            refine ⟨117574075294416192326204249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78382716862944128217469499 117574075294416192326204249)
            ·
              refine ⟨88180556470812144244653187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117574075294416192326204249 88180556470812144244653187)
              ·
                refine ⟨132270834706218216366979781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88180556470812144244653187 132270834706218216366979781)
                ·
                  refine ⟨24800781507415915568808709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132270834706218216366979781 24800781507415915568808709)
                  ·
                    refine ⟨4650146532640484169151633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24800781507415915568808709 4650146532640484169151633)
                    ·
                      refine ⟨3487609899480363126863725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4650146532640484169151633 3487609899480363126863725)
                      ·
                        rfl

theorem cell23_6792096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_6792096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792096 prefixEnd_6792096 := by exact prefixLift 6792096
  have htrace : WordTrace (prefixWord ++ tailWord_6792096) baseStart_6792096 baseEnd_6792096 := by
    simpa [prefixWord, tailWord_6792096, baseEnd_6792096] using wordTrace_append hprefix tailTrace_6792096
  have hstable : (prefixWord ++ tailWord_6792096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792096).length < 2 ^ (prefixWord ++ tailWord_6792096).sum := by decide
  have hdescent : baseEnd_6792096 < baseStart_6792096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792150 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_6792150 : Nat := 118140960795 + 6792150 * 2 ^ 59
def prefixEnd_6792150 : Nat := 4983230072969 + 3 ^ 40 * 6792150 * 2
def baseEnd_6792150 : Nat := 3487637627435705915588477

theorem tailTrace_6792150 : CollatzResearch.WordTrace tailWord_6792150 prefixEnd_6792150 3487637627435705915588477 := by
  unfold tailWord_6792150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15483128896450501982015369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165153374895472021141497269 15483128896450501982015369)
  ·
    refine ⟨11612346672337876486511527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15483128896450501982015369 11612346672337876486511527)
    ·
      refine ⟨17418520008506814729767291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11612346672337876486511527 17418520008506814729767291)
      ·
        refine ⟨26127780012760222094650937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17418520008506814729767291 26127780012760222094650937)
        ·
          refine ⟨19595835009570166570988203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26127780012760222094650937 19595835009570166570988203)
          ·
            refine ⟨29393752514355249856482305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19595835009570166570988203 29393752514355249856482305)
            ·
              refine ⟨22045314385766437392361729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29393752514355249856482305 22045314385766437392361729)
              ·
                refine ⟨16533985789324828044271297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22045314385766437392361729 16533985789324828044271297)
                ·
                  refine ⟨12400489341993621033203473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16533985789324828044271297 12400489341993621033203473)
                  ·
                    refine ⟨9300367006495215774902605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12400489341993621033203473 9300367006495215774902605)
                    ·
                      refine ⟨3487637627435705915588477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9300367006495215774902605 3487637627435705915588477)
                      ·
                        rfl

theorem cell23_6792150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_6792150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792150 prefixEnd_6792150 := by exact prefixLift 6792150
  have htrace : WordTrace (prefixWord ++ tailWord_6792150) baseStart_6792150 baseEnd_6792150 := by
    simpa [prefixWord, tailWord_6792150, baseEnd_6792150] using wordTrace_append hprefix tailTrace_6792150
  have hstable : (prefixWord ++ tailWord_6792150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792150).length < 2 ^ (prefixWord ++ tailWord_6792150).sum := by decide
  have hdescent : baseEnd_6792150 < baseStart_6792150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792157 : List Nat := [1, 4, 3, 1, 2, 1, 4, 2, 1, 4]
def baseStart_6792157 : Nat := 118140960795 + 6792157 * 2 ^ 59
def prefixEnd_6792157 : Nat := 4983230072969 + 3 ^ 40 * 6792157 * 2
def baseEnd_6792157 : Nat := 1162547073933429129400315

theorem tailTrace_6792157 : CollatzResearch.WordTrace tailWord_6792157 prefixEnd_6792157 1162547073933429129400315 := by
  unfold tailWord_6792157
  simp only [CollatzResearch.WordTrace]
  refine ⟨247730317654182671907750725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165153545102788447938500483 247730317654182671907750725)
  ·
    refine ⟨46449434560159250982703261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247730317654182671907750725 46449434560159250982703261)
    ·
      refine ⟨17418537960059719118513723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46449434560159250982703261 17418537960059719118513723)
      ·
        refine ⟨26127806940089578677770585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17418537960059719118513723 26127806940089578677770585)
        ·
          refine ⟨19595855205067184008327939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26127806940089578677770585 19595855205067184008327939)
          ·
            refine ⟨29393782807600776012491909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19595855205067184008327939 29393782807600776012491909)
            ·
              refine ⟨5511334276425145502342233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29393782807600776012491909 5511334276425145502342233)
              ·
                refine ⟨4133500707318859126756675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5511334276425145502342233 4133500707318859126756675)
                ·
                  refine ⟨6200251060978288690135013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133500707318859126756675 6200251060978288690135013)
                  ·
                    refine ⟨1162547073933429129400315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6200251060978288690135013 1162547073933429129400315)
                    ·
                      rfl

theorem cell23_6792157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_6792157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792157 prefixEnd_6792157 := by exact prefixLift 6792157
  have htrace : WordTrace (prefixWord ++ tailWord_6792157) baseStart_6792157 baseEnd_6792157 := by
    simpa [prefixWord, tailWord_6792157, baseEnd_6792157] using wordTrace_append hprefix tailTrace_6792157
  have hstable : (prefixWord ++ tailWord_6792157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792157).length < 2 ^ (prefixWord ++ tailWord_6792157).sum := by decide
  have hdescent : baseEnd_6792157 < baseStart_6792157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792163 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 3, 1, 3]
def baseStart_6792163 : Nat := 118140960795 + 6792163 * 2 ^ 59
def prefixEnd_6792163 : Nat := 4983230072969 + 3 ^ 40 * 6792163 * 2
def baseEnd_6792163 : Nat := 3487644302684214364725917

theorem tailTrace_6792163 : CollatzResearch.WordTrace tailWord_6792163 prefixEnd_6792163 3487644302684214364725917 := by
  unfold tailWord_6792163
  simp only [CollatzResearch.WordTrace]
  refine ⟨247730536492160934932469143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165153690994773956621646095 247730536492160934932469143)
  ·
    refine ⟨371595804738241402398703715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247730536492160934932469143 371595804738241402398703715)
    ·
      refine ⟨557393707107362103598055573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371595804738241402398703715 557393707107362103598055573)
      ·
        refine ⟨26127830020657598606158855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 557393707107362103598055573 26127830020657598606158855)
        ·
          refine ⟨39191745030986397909238283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26127830020657598606158855 39191745030986397909238283)
          ·
            refine ⟨58787617546479596863857425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39191745030986397909238283 58787617546479596863857425)
            ·
              refine ⟨44090713159859697647893069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58787617546479596863857425 44090713159859697647893069)
              ·
                refine ⟨16534017434947386617959901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44090713159859697647893069 16534017434947386617959901)
                ·
                  refine ⟨6200256538105269981734963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16534017434947386617959901 6200256538105269981734963)
                  ·
                    refine ⟨9300384807157904972602445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6200256538105269981734963 9300384807157904972602445)
                    ·
                      refine ⟨3487644302684214364725917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9300384807157904972602445 3487644302684214364725917)
                      ·
                        rfl

theorem cell23_6792163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_6792163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792163 prefixEnd_6792163 := by exact prefixLift 6792163
  have htrace : WordTrace (prefixWord ++ tailWord_6792163) baseStart_6792163 baseEnd_6792163 := by
    simpa [prefixWord, tailWord_6792163, baseEnd_6792163] using wordTrace_append hprefix tailTrace_6792163
  have hstable : (prefixWord ++ tailWord_6792163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792163).length < 2 ^ (prefixWord ++ tailWord_6792163).sum := by decide
  have hdescent : baseEnd_6792163 < baseStart_6792163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792200 : List Nat := [2, 1, 3, 2, 1, 5, 2, 1, 1, 5]
def baseStart_6792200 : Nat := 118140960795 + 6792200 * 2 ^ 59
def prefixEnd_6792200 : Nat := 4983230072969 + 3 ^ 40 * 6792200 * 2
def baseEnd_6792200 : Nat := 1162554433822810239987749

theorem tailTrace_6792200 : CollatzResearch.WordTrace tailWord_6792200 prefixEnd_6792200 1162554433822810239987749 := by
  unfold tailWord_6792200
  simp only [CollatzResearch.WordTrace]
  refine ⟨123865942996513445125783027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165154590662017926834377369 123865942996513445125783027)
  ·
    refine ⟨185798914494770167688674541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123865942996513445125783027 185798914494770167688674541)
    ·
      refine ⟨69674592935538812883252953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185798914494770167688674541 69674592935538812883252953)
      ·
        refine ⟨52255944701654109662439715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69674592935538812883252953 52255944701654109662439715)
        ·
          refine ⟨78383917052481164493659573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52255944701654109662439715 78383917052481164493659573)
          ·
            refine ⟨7348492223670109171280585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78383917052481164493659573 7348492223670109171280585)
            ·
              refine ⟨5511369167752581878460439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7348492223670109171280585 5511369167752581878460439)
              ·
                refine ⟨8267053751628872817690659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5511369167752581878460439 8267053751628872817690659)
                ·
                  refine ⟨12400580627443309226535989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8267053751628872817690659 12400580627443309226535989)
                  ·
                    refine ⟨1162554433822810239987749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12400580627443309226535989 1162554433822810239987749)
                    ·
                      rfl

theorem cell23_6792200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_6792200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792200 prefixEnd_6792200 := by exact prefixLift 6792200
  have htrace : WordTrace (prefixWord ++ tailWord_6792200) baseStart_6792200 baseEnd_6792200 := by
    simpa [prefixWord, tailWord_6792200, baseEnd_6792200] using wordTrace_append hprefix tailTrace_6792200
  have hstable : (prefixWord ++ tailWord_6792200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792200).length < 2 ^ (prefixWord ++ tailWord_6792200).sum := by decide
  have hdescent : baseEnd_6792200 < baseStart_6792200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792203 : List Nat := [1, 1, 1, 1, 6, 3, 1, 3, 1, 1, 4]
def baseStart_6792203 : Nat := 118140960795 + 6792203 * 2 ^ 59
def prefixEnd_6792203 : Nat := 4983230072969 + 3 ^ 40 * 6792203 * 2
def baseEnd_6792203 : Nat := 3487664841910394208225733

theorem tailTrace_6792203 : CollatzResearch.WordTrace tailWord_6792203 prefixEnd_6792203 3487664841910394208225733 := by
  unfold tailWord_6792203
  simp only [CollatzResearch.WordTrace]
  refine ⟨247731995412016021763925263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165154663608010681175950175 247731995412016021763925263)
  ·
    refine ⟨371597993118024032645887895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247731995412016021763925263 371597993118024032645887895)
    ·
      refine ⟨557396989677036048968831843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371597993118024032645887895 557396989677036048968831843)
      ·
        refine ⟨836095484515554073453247765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557396989677036048968831843 836095484515554073453247765)
        ·
          refine ⟨39191975836666597193120989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 836095484515554073453247765 39191975836666597193120989)
          ·
            refine ⟨14696990938749973947420371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39191975836666597193120989 14696990938749973947420371)
            ·
              refine ⟨22045486408124960921130557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14696990938749973947420371 22045486408124960921130557)
              ·
                refine ⟨8267057403046860345423959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22045486408124960921130557 8267057403046860345423959)
                ·
                  refine ⟨12400586104570290518135939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8267057403046860345423959 12400586104570290518135939)
                  ·
                    refine ⟨18600879156855435777203909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12400586104570290518135939 18600879156855435777203909)
                    ·
                      refine ⟨3487664841910394208225733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18600879156855435777203909 3487664841910394208225733)
                      ·
                        rfl

theorem cell23_6792203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 1, 4].length) (baseStart_6792203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792203 prefixEnd_6792203 := by exact prefixLift 6792203
  have htrace : WordTrace (prefixWord ++ tailWord_6792203) baseStart_6792203 baseEnd_6792203 := by
    simpa [prefixWord, tailWord_6792203, baseEnd_6792203] using wordTrace_append hprefix tailTrace_6792203
  have hstable : (prefixWord ++ tailWord_6792203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792203).length < 2 ^ (prefixWord ++ tailWord_6792203).sum := by decide
  have hdescent : baseEnd_6792203 < baseStart_6792203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792213 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 4, 4]
def baseStart_6792213 : Nat := 118140960795 + 6792213 * 2 ^ 59
def prefixEnd_6792213 : Nat := 4983230072969 + 3 ^ 40 * 6792213 * 2
def baseEnd_6792213 : Nat := 1162556658905646389700229

theorem tailTrace_6792213 : CollatzResearch.WordTrace tailWord_6792213 prefixEnd_6792213 1162556658905646389700229 := by
  unfold tailWord_6792213
  simp only [CollatzResearch.WordTrace]
  refine ⟨247732360141979793471789293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165154906761319862314526195 247732360141979793471789293)
  ·
    refine ⟨92899635053242422551920985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247732360141979793471789293 92899635053242422551920985)
    ·
      refine ⟨69674726289931816913940739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92899635053242422551920985 69674726289931816913940739)
      ·
        refine ⟨104512089434897725370911109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69674726289931816913940739 104512089434897725370911109)
        ·
          refine ⟨19596016769043323507045833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104512089434897725370911109 19596016769043323507045833)
          ·
            refine ⟨14697012576782492630284375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19596016769043323507045833 14697012576782492630284375)
            ·
              refine ⟨22045518865173738945426563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14697012576782492630284375 22045518865173738945426563)
              ·
                refine ⟨33068278297760608418139845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22045518865173738945426563 33068278297760608418139845)
                ·
                  refine ⟨6200302180830114078401221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33068278297760608418139845 6200302180830114078401221)
                  ·
                    refine ⟨1162556658905646389700229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6200302180830114078401221 1162556658905646389700229)
                    ·
                      rfl

theorem cell23_6792213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_6792213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792213 prefixEnd_6792213 := by exact prefixLift 6792213
  have htrace : WordTrace (prefixWord ++ tailWord_6792213) baseStart_6792213 baseEnd_6792213 := by
    simpa [prefixWord, tailWord_6792213, baseEnd_6792213] using wordTrace_append hprefix tailTrace_6792213
  have hstable : (prefixWord ++ tailWord_6792213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792213).length < 2 ^ (prefixWord ++ tailWord_6792213).sum := by decide
  have hdescent : baseEnd_6792213 < baseStart_6792213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792239 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 3, 9]
def baseStart_6792239 : Nat := 118140960795 + 6792239 * 2 ^ 59
def prefixEnd_6792239 : Nat := 4983230072969 + 3 ^ 40 * 6792239 * 2
def baseEnd_6792239 : Nat := 1162561109071318689125189

theorem tailTrace_6792239 : CollatzResearch.WordTrace tailWord_6792239 prefixEnd_6792239 1162561109071318689125189 := by
  unfold tailWord_6792239
  simp only [CollatzResearch.WordTrace]
  refine ⟨247733308439885599912235771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165155538959923733274823847 247733308439885599912235771)
  ·
    refine ⟨371599962659828399868353657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247733308439885599912235771 371599962659828399868353657)
    ·
      refine ⟨278699971994871299901265243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371599962659828399868353657 278699971994871299901265243)
      ·
        refine ⟨418049957992306949851897865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278699971994871299901265243 418049957992306949851897865)
        ·
          refine ⟨313537468494230212388923399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418049957992306949851897865 313537468494230212388923399)
          ·
            refine ⟨470306202741345318583385099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313537468494230212388923399 470306202741345318583385099)
            ·
              refine ⟨705459304112017977875077649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470306202741345318583385099 705459304112017977875077649)
              ·
                refine ⟨529094478084013483406308237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705459304112017977875077649 529094478084013483406308237)
                ·
                  refine ⟨198410429281505056277365589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 529094478084013483406308237 198410429281505056277365589)
                  ·
                    refine ⟨1162561109071318689125189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 198410429281505056277365589 1162561109071318689125189)
                    ·
                      rfl

theorem cell23_6792239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 9].length) (baseStart_6792239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792239 prefixEnd_6792239 := by exact prefixLift 6792239
  have htrace : WordTrace (prefixWord ++ tailWord_6792239) baseStart_6792239 baseEnd_6792239 := by
    simpa [prefixWord, tailWord_6792239, baseEnd_6792239] using wordTrace_append hprefix tailTrace_6792239
  have hstable : (prefixWord ++ tailWord_6792239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792239).length < 2 ^ (prefixWord ++ tailWord_6792239).sum := by decide
  have hdescent : baseEnd_6792239 < baseStart_6792239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792270 : List Nat := [4, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3]
def baseStart_6792270 : Nat := 118140960795 + 6792270 * 2 ^ 59
def prefixEnd_6792270 : Nat := 4983230072969 + 3 ^ 40 * 6792270 * 2
def baseEnd_6792270 : Nat := 3487699245114245446087925

theorem tailTrace_6792270 : CollatzResearch.WordTrace tailWord_6792270 prefixEnd_6792270 3487699245114245446087925 := by
  unfold tailWord_6792270
  simp only [CollatzResearch.WordTrace]
  refine ⟨30966804887846661525826783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165156292735182194804409509 30966804887846661525826783)
  ·
    refine ⟨46450207331769992288740175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30966804887846661525826783 46450207331769992288740175)
    ·
      refine ⟨69675310997654988433110263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46450207331769992288740175 69675310997654988433110263)
      ·
        refine ⟨104512966496482482649665395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69675310997654988433110263 104512966496482482649665395)
        ·
          refine ⟨156769449744723723974498093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104512966496482482649665395 156769449744723723974498093)
          ·
            refine ⟨58788543654271396490436785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156769449744723723974498093 58788543654271396490436785)
            ·
              refine ⟨44091407740703547367827589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58788543654271396490436785 44091407740703547367827589)
              ·
                refine ⟨8267138951381915131467673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44091407740703547367827589 8267138951381915131467673)
                ·
                  refine ⟨6200354213536436348600755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8267138951381915131467673 6200354213536436348600755)
                  ·
                    refine ⟨9300531320304654522901133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6200354213536436348600755 9300531320304654522901133)
                    ·
                      refine ⟨3487699245114245446087925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9300531320304654522901133 3487699245114245446087925)
                      ·
                        rfl

theorem cell23_6792270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_6792270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792270 prefixEnd_6792270 := by exact prefixLift 6792270
  have htrace : WordTrace (prefixWord ++ tailWord_6792270) baseStart_6792270 baseEnd_6792270 := by
    simpa [prefixWord, tailWord_6792270, baseEnd_6792270] using wordTrace_append hprefix tailTrace_6792270
  have hstable : (prefixWord ++ tailWord_6792270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792270).length < 2 ^ (prefixWord ++ tailWord_6792270).sum := by decide
  have hdescent : baseEnd_6792270 < baseStart_6792270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792297 : List Nat := [1, 2, 1, 1, 1, 8, 1, 2, 1, 3, 2]
def baseStart_6792297 : Nat := 118140960795 + 6792297 * 2 ^ 59
def prefixEnd_6792297 : Nat := 4983230072969 + 3 ^ 40 * 6792297 * 2
def baseEnd_6792297 : Nat := 3487713109091916840450301

theorem tailTrace_6792297 : CollatzResearch.WordTrace tailWord_6792297 prefixEnd_6792297 3487713109091916840450301 := by
  unfold tailWord_6792297
  simp only [CollatzResearch.WordTrace]
  refine ⟨247735423873675475817847145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165156949249116983878564763 247735423873675475817847145)
  ·
    refine ⟨185801567905256606863385359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247735423873675475817847145 185801567905256606863385359)
    ·
      refine ⟨278702351857884910295078039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185801567905256606863385359 278702351857884910295078039)
      ·
        refine ⟨418053527786827365442617059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278702351857884910295078039 418053527786827365442617059)
        ·
          refine ⟨627080291680241048163925589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418053527786827365442617059 627080291680241048163925589)
          ·
            refine ⟨7348597168127824783171003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 627080291680241048163925589 7348597168127824783171003)
            ·
              refine ⟨11022895752191737174756505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7348597168127824783171003 11022895752191737174756505)
              ·
                refine ⟨8267171814143802881067379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11022895752191737174756505 8267171814143802881067379)
                ·
                  refine ⟨12400757721215704321601069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8267171814143802881067379 12400757721215704321601069)
                  ·
                    refine ⟨4650284145455889120600401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12400757721215704321601069 4650284145455889120600401)
                    ·
                      refine ⟨3487713109091916840450301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4650284145455889120600401 3487713109091916840450301)
                      ·
                        rfl

theorem cell23_6792297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 3, 2].length) (baseStart_6792297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792297 prefixEnd_6792297 := by exact prefixLift 6792297
  have htrace : WordTrace (prefixWord ++ tailWord_6792297) baseStart_6792297 baseEnd_6792297 := by
    simpa [prefixWord, tailWord_6792297, baseEnd_6792297] using wordTrace_append hprefix tailTrace_6792297
  have hstable : (prefixWord ++ tailWord_6792297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792297).length < 2 ^ (prefixWord ++ tailWord_6792297).sum := by decide
  have hdescent : baseEnd_6792297 < baseStart_6792297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792343 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 3]
def baseStart_6792343 : Nat := 118140960795 + 6792343 * 2 ^ 59
def prefixEnd_6792343 : Nat := 4983230072969 + 3 ^ 40 * 6792343 * 2
def baseEnd_6792343 : Nat := 3487736729202023660475089

theorem tailTrace_6792343 : CollatzResearch.WordTrace tailWord_6792343 prefixEnd_6792343 3487736729202023660475089 := by
  unfold tailWord_6792343
  simp only [CollatzResearch.WordTrace]
  refine ⟨247737101631508825674021683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165158067754339217116014455 247737101631508825674021683)
  ·
    refine ⟨371605652447263238511032525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247737101631508825674021683 371605652447263238511032525)
    ·
      refine ⟨139352119667723714441637197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371605652447263238511032525 139352119667723714441637197)
      ·
        refine ⟨52257044875396392915613949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139352119667723714441637197 52257044875396392915613949)
        ·
          refine ⟨19596391828273647343355231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52257044875396392915613949 19596391828273647343355231)
          ·
            refine ⟨29394587742410471015032847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19596391828273647343355231 29394587742410471015032847)
            ·
              refine ⟨44091881613615706522549271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29394587742410471015032847 44091881613615706522549271)
              ·
                refine ⟨66137822420423559783823907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44091881613615706522549271 66137822420423559783823907)
                ·
                  refine ⟨99206733630635339675735861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66137822420423559783823907 99206733630635339675735861)
                  ·
                    refine ⟨9300631277872063094600237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99206733630635339675735861 9300631277872063094600237)
                    ·
                      refine ⟨3487736729202023660475089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9300631277872063094600237 3487736729202023660475089)
                      ·
                        rfl

theorem cell23_6792343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_6792343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792343 prefixEnd_6792343 := by exact prefixLift 6792343
  have htrace : WordTrace (prefixWord ++ tailWord_6792343) baseStart_6792343 baseEnd_6792343 := by
    simpa [prefixWord, tailWord_6792343, baseEnd_6792343] using wordTrace_append hprefix tailTrace_6792343
  have hstable : (prefixWord ++ tailWord_6792343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792343).length < 2 ^ (prefixWord ++ tailWord_6792343).sum := by decide
  have hdescent : baseEnd_6792343 < baseStart_6792343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792350 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 7]
def baseStart_6792350 : Nat := 118140960795 + 6792350 * 2 ^ 59
def prefixEnd_6792350 : Nat := 4983230072969 + 3 ^ 40 * 6792350 * 2
def baseEnd_6792350 : Nat := 387526702618511681454173

theorem tailTrace_6792350 : CollatzResearch.WordTrace tailWord_6792350 prefixEnd_6792350 387526702618511681454173 := by
  unfold tailWord_6792350
  simp only [CollatzResearch.WordTrace]
  refine ⟨30967169617810433233690813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165158237961655643913017669 30967169617810433233690813)
  ·
    refine ⟨11612688606678912462634055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30967169617810433233690813 11612688606678912462634055)
    ·
      refine ⟨17419032910018368693951083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11612688606678912462634055 17419032910018368693951083)
      ·
        refine ⟨26128549365027553040926625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17419032910018368693951083 26128549365027553040926625)
        ·
          refine ⟨19596412023770664780694969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26128549365027553040926625 19596412023770664780694969)
          ·
            refine ⟨14697309017827998585521227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19596412023770664780694969 14697309017827998585521227)
            ·
              refine ⟨22045963526741997878281841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14697309017827998585521227 22045963526741997878281841)
              ·
                refine ⟨16534472645056498408711381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22045963526741997878281841 16534472645056498408711381)
                ·
                  refine ⟨387526702618511681454173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16534472645056498408711381 387526702618511681454173)
                  ·
                    rfl

theorem cell23_6792350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_6792350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792350 prefixEnd_6792350 := by exact prefixLift 6792350
  have htrace : WordTrace (prefixWord ++ tailWord_6792350) baseStart_6792350 baseEnd_6792350 := by
    simpa [prefixWord, tailWord_6792350, baseEnd_6792350] using wordTrace_append hprefix tailTrace_6792350
  have hstable : (prefixWord ++ tailWord_6792350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792350).length < 2 ^ (prefixWord ++ tailWord_6792350).sum := by decide
  have hdescent : baseEnd_6792350 < baseStart_6792350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792383 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 4]
def baseStart_6792383 : Nat := 118140960795 + 6792383 * 2 ^ 59
def prefixEnd_6792383 : Nat := 4983230072969 + 3 ^ 40 * 6792383 * 2
def baseEnd_6792383 : Nat := 3487757268428203503974905

theorem tailTrace_6792383 : CollatzResearch.WordTrace tailWord_6792383 prefixEnd_6792383 3487757268428203503974905 := by
  unfold tailWord_6792383
  simp only [CollatzResearch.WordTrace]
  refine ⟨247738560551363912505477803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165159040367575941670318535 247738560551363912505477803)
  ·
    refine ⟨371607840827045868758216705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247738560551363912505477803 371607840827045868758216705)
    ·
      refine ⟨278705880620284401568662529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371607840827045868758216705 278705880620284401568662529)
      ·
        refine ⟨209029410465213301176496897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278705880620284401568662529 209029410465213301176496897)
        ·
          refine ⟨156772057848909975882372673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209029410465213301176496897 156772057848909975882372673)
          ·
            refine ⟨117579043386682481911779505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156772057848909975882372673 117579043386682481911779505)
            ·
              refine ⟨88184282540011861433834629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117579043386682481911779505 88184282540011861433834629)
              ·
                refine ⟨16534552976252224018843993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88184282540011861433834629 16534552976252224018843993)
                ·
                  refine ⟨12400914732189168014132995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16534552976252224018843993 12400914732189168014132995)
                  ·
                    refine ⟨18601372098283752021199493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12400914732189168014132995 18601372098283752021199493)
                    ·
                      refine ⟨3487757268428203503974905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18601372098283752021199493 3487757268428203503974905)
                      ·
                        rfl

theorem cell23_6792383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_6792383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792383 prefixEnd_6792383 := by exact prefixLift 6792383
  have htrace : WordTrace (prefixWord ++ tailWord_6792383) baseStart_6792383 baseEnd_6792383 := by
    simpa [prefixWord, tailWord_6792383, baseEnd_6792383] using wordTrace_append hprefix tailTrace_6792383
  have hstable : (prefixWord ++ tailWord_6792383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792383).length < 2 ^ (prefixWord ++ tailWord_6792383).sum := by decide
  have hdescent : baseEnd_6792383 < baseStart_6792383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792403 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 3]
def baseStart_6792403 : Nat := 118140960795 + 6792403 * 2 ^ 59
def prefixEnd_6792403 : Nat := 4983230072969 + 3 ^ 40 * 6792403 * 2
def baseEnd_6792403 : Nat := 3487767538041293425724813

theorem tailTrace_6792403 : CollatzResearch.WordTrace tailWord_6792403 prefixEnd_6792403 3487767538041293425724813 := by
  unfold tailWord_6792403
  simp only [CollatzResearch.WordTrace]
  refine ⟨247739290011291455921205863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165159526674194303947470575 247739290011291455921205863)
  ·
    refine ⟨371608935016937183881808795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247739290011291455921205863 371608935016937183881808795)
    ·
      refine ⟨557413402525405775822713193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371608935016937183881808795 557413402525405775822713193)
      ·
        refine ⟨418060051894054331867034895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557413402525405775822713193 418060051894054331867034895)
        ·
          refine ⟨627090077841081497800552343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418060051894054331867034895 627090077841081497800552343)
          ·
            refine ⟨940635116761622246700828515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627090077841081497800552343 940635116761622246700828515)
            ·
              refine ⟨1410952675142433370051242773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940635116761622246700828515 1410952675142433370051242773)
              ·
                refine ⟨66138406647301564221152005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1410952675142433370051242773 66138406647301564221152005)
                ·
                  refine ⟨12400951246369043291466001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66138406647301564221152005 12400951246369043291466001)
                  ·
                    refine ⟨9300713434776782468599501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12400951246369043291466001 9300713434776782468599501)
                    ·
                      refine ⟨3487767538041293425724813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9300713434776782468599501 3487767538041293425724813)
                      ·
                        rfl

theorem cell23_6792403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 3].length) (baseStart_6792403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792403 prefixEnd_6792403 := by exact prefixLift 6792403
  have htrace : WordTrace (prefixWord ++ tailWord_6792403) baseStart_6792403 baseEnd_6792403 := by
    simpa [prefixWord, tailWord_6792403, baseEnd_6792403] using wordTrace_append hprefix tailTrace_6792403
  have hstable : (prefixWord ++ tailWord_6792403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792403).length < 2 ^ (prefixWord ++ tailWord_6792403).sum := by decide
  have hdescent : baseEnd_6792403 < baseStart_6792403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792427 : List Nat := [1, 1, 1, 1, 2, 6, 3, 3, 1, 4]
def baseStart_6792427 : Nat := 118140960795 + 6792427 * 2 ^ 59
def prefixEnd_6792427 : Nat := 4983230072969 + 3 ^ 40 * 6792427 * 2
def baseEnd_6792427 : Nat := 1162593287192333777274901

theorem tailTrace_6792427 : CollatzResearch.WordTrace tailWord_6792427 prefixEnd_6792427 1162593287192333777274901 := by
  unfold tailWord_6792427
  simp only [CollatzResearch.WordTrace]
  refine ⟨247740165363204508020079535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165160110242136338680053023 247740165363204508020079535)
  ·
    refine ⟨371610248044806762030119303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247740165363204508020079535 371610248044806762030119303)
    ·
      refine ⟨557415372067210143045178955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371610248044806762030119303 557415372067210143045178955)
      ·
        refine ⟨836123058100815214567768433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557415372067210143045178955 836123058100815214567768433)
        ·
          refine ⟨627092293575611410925826325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 836123058100815214567768433 627092293575611410925826325)
          ·
            refine ⟨29394951261356784887148109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 627092293575611410925826325 29394951261356784887148109)
            ·
              refine ⟨11023106723008794332680541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29394951261356784887148109 11023106723008794332680541)
              ·
                refine ⟨4133665021128297874755203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11023106723008794332680541 4133665021128297874755203)
                ·
                  refine ⟨6200497531692446812132805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133665021128297874755203 6200497531692446812132805)
                  ·
                    refine ⟨1162593287192333777274901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6200497531692446812132805 1162593287192333777274901)
                    ·
                      rfl

theorem cell23_6792427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 1, 4].length) (baseStart_6792427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792427 prefixEnd_6792427 := by exact prefixLift 6792427
  have htrace : WordTrace (prefixWord ++ tailWord_6792427) baseStart_6792427 baseEnd_6792427 := by
    simpa [prefixWord, tailWord_6792427, baseEnd_6792427] using wordTrace_append hprefix tailTrace_6792427
  have hstable : (prefixWord ++ tailWord_6792427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792427).length < 2 ^ (prefixWord ++ tailWord_6792427).sum := by decide
  have hdescent : baseEnd_6792427 < baseStart_6792427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792444 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 3, 4]
def baseStart_6792444 : Nat := 118140960795 + 6792444 * 2 ^ 59
def prefixEnd_6792444 : Nat := 4983230072969 + 3 ^ 40 * 6792444 * 2
def baseEnd_6792444 : Nat := 1162596196916042588437375

theorem tailTrace_6792444 : CollatzResearch.WordTrace tailWord_6792444 prefixEnd_6792444 1162596196916042588437375 := by
  unfold tailWord_6792444
  simp only [CollatzResearch.WordTrace]
  refine ⟨123870392702071459961724193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165160523602761946615632257 123870392702071459961724193)
  ·
    refine ⟨92902794526553594971293145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123870392702071459961724193 92902794526553594971293145)
    ·
      refine ⟨69677095894915196228469859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92902794526553594971293145 69677095894915196228469859)
      ·
        refine ⟨104515643842372794342704789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69677095894915196228469859 104515643842372794342704789)
        ·
          refine ⟨4899170805111224734814287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104515643842372794342704789 4899170805111224734814287)
          ·
            refine ⟨7348756207666837102221431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4899170805111224734814287 7348756207666837102221431)
            ·
              refine ⟨11023134311500255653332147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7348756207666837102221431 11023134311500255653332147)
              ·
                refine ⟨16534701467250383479998221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11023134311500255653332147 16534701467250383479998221)
                ·
                  refine ⟨6200513050218893804999333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16534701467250383479998221 6200513050218893804999333)
                  ·
                    refine ⟨1162596196916042588437375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6200513050218893804999333 1162596196916042588437375)
                    ·
                      rfl

theorem cell23_6792444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_6792444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792444 prefixEnd_6792444 := by exact prefixLift 6792444
  have htrace : WordTrace (prefixWord ++ tailWord_6792444) baseStart_6792444 baseEnd_6792444 := by
    simpa [prefixWord, tailWord_6792444, baseEnd_6792444] using wordTrace_append hprefix tailTrace_6792444
  have hstable : (prefixWord ++ tailWord_6792444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792444).length < 2 ^ (prefixWord ++ tailWord_6792444).sum := by decide
  have hdescent : baseEnd_6792444 < baseStart_6792444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792453 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 3, 5]
def baseStart_6792453 : Nat := 118140960795 + 6792453 * 2 ^ 59
def prefixEnd_6792453 : Nat := 4983230072969 + 3 ^ 40 * 6792453 * 2
def baseEnd_6792453 : Nat := 1162597737358006076699861

theorem tailTrace_6792453 : CollatzResearch.WordTrace tailWord_6792453 prefixEnd_6792453 1162597737358006076699861 := by
  unfold tailWord_6792453
  simp only [CollatzResearch.WordTrace]
  refine ⟨247741113661110314460526013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165160742440740209640350675 247741113661110314460526013)
  ·
    refine ⟨92902917622916367922697255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247741113661110314460526013 92902917622916367922697255)
    ·
      refine ⟨139354376434374551884045883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92902917622916367922697255 139354376434374551884045883)
      ·
        refine ⟨209031564651561827826068825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139354376434374551884045883 209031564651561827826068825)
        ·
          refine ⟨156773673488671370869551619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209031564651561827826068825 156773673488671370869551619)
          ·
            refine ⟨235160510233007056304327429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156773673488671370869551619 235160510233007056304327429)
            ·
              refine ⟨44092595668688823057061393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235160510233007056304327429 44092595668688823057061393)
              ·
                refine ⟨33069446751516617292796045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44092595668688823057061393 33069446751516617292796045)
                ·
                  refine ⟨12401042531818731484798517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33069446751516617292796045 12401042531818731484798517)
                  ·
                    refine ⟨1162597737358006076699861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12401042531818731484798517 1162597737358006076699861)
                    ·
                      rfl

theorem cell23_6792453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_6792453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792453 prefixEnd_6792453 := by exact prefixLift 6792453
  have htrace : WordTrace (prefixWord ++ tailWord_6792453) baseStart_6792453 baseEnd_6792453 := by
    simpa [prefixWord, tailWord_6792453, baseEnd_6792453] using wordTrace_append hprefix tailTrace_6792453
  have hstable : (prefixWord ++ tailWord_6792453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792453).length < 2 ^ (prefixWord ++ tailWord_6792453).sum := by decide
  have hdescent : baseEnd_6792453 < baseStart_6792453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792483 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 3, 6]
def baseStart_6792483 : Nat := 118140960795 + 6792483 * 2 ^ 59
def prefixEnd_6792483 : Nat := 4983230072969 + 3 ^ 40 * 6792483 * 2
def baseEnd_6792483 : Nat := 1162602872164551037574815

theorem tailTrace_6792483 : CollatzResearch.WordTrace tailWord_6792483 prefixEnd_6792483 1162602872164551037574815 := by
  unfold tailWord_6792483
  simp only [CollatzResearch.WordTrace]
  refine ⟨247742207851001629584118103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165161471900667753056078735 247742207851001629584118103)
  ·
    refine ⟨371613311776502444376177155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247742207851001629584118103 371613311776502444376177155)
    ·
      refine ⟨557419967664753666564265733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371613311776502444376177155 557419967664753666564265733)
      ·
        refine ⟨104516243937141312480799825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 557419967664753666564265733 104516243937141312480799825)
        ·
          refine ⟨78387182952855984360599869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104516243937141312480799825 78387182952855984360599869)
          ·
            refine ⟨29395193607320994135224951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78387182952855984360599869 29395193607320994135224951)
            ·
              refine ⟨44092790410981491202837427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29395193607320994135224951 44092790410981491202837427)
              ·
                refine ⟨66139185616472236804256141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44092790410981491202837427 66139185616472236804256141)
                ·
                  refine ⟨24802194606177088801596053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66139185616472236804256141 24802194606177088801596053)
                  ·
                    refine ⟨1162602872164551037574815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24802194606177088801596053 1162602872164551037574815)
                    ·
                      rfl

theorem cell23_6792483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 6].length) (baseStart_6792483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792483 prefixEnd_6792483 := by exact prefixLift 6792483
  have htrace : WordTrace (prefixWord ++ tailWord_6792483) baseStart_6792483 baseEnd_6792483 := by
    simpa [prefixWord, tailWord_6792483, baseEnd_6792483] using wordTrace_append hprefix tailTrace_6792483
  have hstable : (prefixWord ++ tailWord_6792483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792483).length < 2 ^ (prefixWord ++ tailWord_6792483).sum := by decide
  have hdescent : baseEnd_6792483 < baseStart_6792483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792484 : List Nat := [2, 3, 1, 3, 1, 1, 2, 5, 1, 1, 3]
def baseStart_6792484 : Nat := 118140960795 + 6792484 * 2 ^ 59
def prefixEnd_6792484 : Nat := 4983230072969 + 3 ^ 40 * 6792484 * 2
def baseEnd_6792484 : Nat := 3487809129974307608811941

theorem tailTrace_6792484 : CollatzResearch.WordTrace tailWord_6792484 prefixEnd_6792484 3487809129974307608811941 := by
  unfold tailWord_6792484
  simp only [CollatzResearch.WordTrace]
  refine ⟨123871122161999003377452253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165161496215998671169936337 123871122161999003377452253)
  ·
    refine ⟨46451670810749626266544595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123871122161999003377452253 46451670810749626266544595)
    ·
      refine ⟨69677506216124439399816893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46451670810749626266544595 69677506216124439399816893)
      ·
        refine ⟨26129064831046664774931335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69677506216124439399816893 26129064831046664774931335)
        ·
          refine ⟨39193597246569997162397003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26129064831046664774931335 39193597246569997162397003)
          ·
            refine ⟨58790395869854995743595505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39193597246569997162397003 58790395869854995743595505)
            ·
              refine ⟨44092796902391246807696629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58790395869854995743595505 44092796902391246807696629)
              ·
                refine ⟨4133699709599179388221559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44092796902391246807696629 4133699709599179388221559)
                ·
                  refine ⟨6200549564398769082332339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133699709599179388221559 6200549564398769082332339)
                  ·
                    refine ⟨9300824346598153623498509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6200549564398769082332339 9300824346598153623498509)
                    ·
                      refine ⟨3487809129974307608811941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9300824346598153623498509 3487809129974307608811941)
                      ·
                        rfl

theorem cell23_6792484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_6792484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792484 prefixEnd_6792484 := by exact prefixLift 6792484
  have htrace : WordTrace (prefixWord ++ tailWord_6792484) baseStart_6792484 baseEnd_6792484 := by
    simpa [prefixWord, tailWord_6792484, baseEnd_6792484] using wordTrace_append hprefix tailTrace_6792484
  have hstable : (prefixWord ++ tailWord_6792484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792484).length < 2 ^ (prefixWord ++ tailWord_6792484).sum := by decide
  have hdescent : baseEnd_6792484 < baseStart_6792484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792500 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_6792500 : Nat := 118140960795 + 6792500 * 2 ^ 59
def prefixEnd_6792500 : Nat := 4983230072969 + 3 ^ 40 * 6792500 * 2
def baseEnd_6792500 : Nat := 1162605781888259848737289

theorem tailTrace_6792500 : CollatzResearch.WordTrace tailWord_6792500 prefixEnd_6792500 1162605781888259848737289 := by
  unfold tailWord_6792500
  simp only [CollatzResearch.WordTrace]
  refine ⟨123871413945970020743743477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165161885261293360991657969 123871413945970020743743477)
  ·
    refine ⟨11612945057434689444725951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123871413945970020743743477 11612945057434689444725951)
    ·
      refine ⟨17419417586152034167088927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11612945057434689444725951 17419417586152034167088927)
      ·
        refine ⟨26129126379228051250633391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17419417586152034167088927 26129126379228051250633391)
        ·
          refine ⟨39193689568842076875950087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26129126379228051250633391 39193689568842076875950087)
          ·
            refine ⟨58790534353263115313925131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39193689568842076875950087 58790534353263115313925131)
            ·
              refine ⟨88185801529894672970887697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58790534353263115313925131 88185801529894672970887697)
              ·
                refine ⟨66139351147421004728165773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88185801529894672970887697 66139351147421004728165773)
                ·
                  refine ⟨24802256680282876773062165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66139351147421004728165773 24802256680282876773062165)
                  ·
                    refine ⟨1162605781888259848737289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24802256680282876773062165 1162605781888259848737289)
                    ·
                      rfl

theorem cell23_6792500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_6792500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792500 prefixEnd_6792500 := by exact prefixLift 6792500
  have htrace : WordTrace (prefixWord ++ tailWord_6792500) baseStart_6792500 baseEnd_6792500 := by
    simpa [prefixWord, tailWord_6792500, baseEnd_6792500] using wordTrace_append hprefix tailTrace_6792500
  have hstable : (prefixWord ++ tailWord_6792500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792500).length < 2 ^ (prefixWord ++ tailWord_6792500).sum := by decide
  have hdescent : baseEnd_6792500 < baseStart_6792500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792501 : List Nat := [1, 3, 3, 1, 2, 2, 4, 2, 1, 1, 3]
def baseStart_6792501 : Nat := 118140960795 + 6792501 * 2 ^ 59
def prefixEnd_6792501 : Nat := 4983230072969 + 3 ^ 40 * 6792501 * 2
def baseEnd_6792501 : Nat := 3487817859145434042299363

theorem tailTrace_6792501 : CollatzResearch.WordTrace tailWord_6792501 prefixEnd_6792501 3487817859145434042299363 := by
  unfold tailWord_6792501
  simp only [CollatzResearch.WordTrace]
  refine ⟨247742864364936418658273357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165161909576624279105515571 247742864364936418658273357)
  ·
    refine ⟨92903574136851156996852509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247742864364936418658273357 92903574136851156996852509)
    ·
      refine ⟨34838840301319183873819691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92903574136851156996852509 34838840301319183873819691)
      ·
        refine ⟨52258260451978775810729537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34838840301319183873819691 52258260451978775810729537)
        ·
          refine ⟨39193695338984081858047153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52258260451978775810729537 39193695338984081858047153)
          ·
            refine ⟨29395271504238061393535365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39193695338984081858047153 29395271504238061393535365)
            ·
              refine ⟨5511613407044636511287881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29395271504238061393535365 5511613407044636511287881)
              ·
                refine ⟨4133710055283477383465911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5511613407044636511287881 4133710055283477383465911)
                ·
                  refine ⟨6200565082925216075198867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133710055283477383465911 6200565082925216075198867)
                  ·
                    refine ⟨9300847624387824112798301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6200565082925216075198867 9300847624387824112798301)
                    ·
                      refine ⟨3487817859145434042299363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9300847624387824112798301 3487817859145434042299363)
                      ·
                        rfl

theorem cell23_6792501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_6792501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792501 prefixEnd_6792501 := by exact prefixLift 6792501
  have htrace : WordTrace (prefixWord ++ tailWord_6792501) baseStart_6792501 baseEnd_6792501 := by
    simpa [prefixWord, tailWord_6792501, baseEnd_6792501] using wordTrace_append hprefix tailTrace_6792501
  have hstable : (prefixWord ++ tailWord_6792501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792501).length < 2 ^ (prefixWord ++ tailWord_6792501).sum := by decide
  have hdescent : baseEnd_6792501 < baseStart_6792501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792510 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_6792510 : Nat := 118140960795 + 6792510 * 2 ^ 59
def prefixEnd_6792510 : Nat := 4983230072969 + 3 ^ 40 * 6792510 * 2
def baseEnd_6792510 : Nat := 3487822480471324507086821

theorem tailTrace_6792510 : CollatzResearch.WordTrace tailWord_6792510 prefixEnd_6792510 3487822480471324507086821 := by
  unfold tailWord_6792510
  simp only [CollatzResearch.WordTrace]
  refine ⟨30967899077737976649418873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165162128414602542130233989 30967899077737976649418873)
  ·
    refine ⟨23225924308303482487064155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30967899077737976649418873 23225924308303482487064155)
    ·
      refine ⟨34838886462455223730596233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23225924308303482487064155 34838886462455223730596233)
      ·
        refine ⟨26129164846841417797947175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34838886462455223730596233 26129164846841417797947175)
        ·
          refine ⟨39193747270262126696920763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26129164846841417797947175 39193747270262126696920763)
          ·
            refine ⟨58790620905393190045381145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39193747270262126696920763 58790620905393190045381145)
            ·
              refine ⟨44092965679044892534035859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58790620905393190045381145 44092965679044892534035859)
              ·
                refine ⟨66139448518567338801053789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44092965679044892534035859 66139448518567338801053789)
                ·
                  refine ⟨24802293194462752050395171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66139448518567338801053789 24802293194462752050395171)
                  ·
                    refine ⟨37203439791694128075592757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24802293194462752050395171 37203439791694128075592757)
                    ·
                      refine ⟨3487822480471324507086821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37203439791694128075592757 3487822480471324507086821)
                      ·
                        rfl

theorem cell23_6792510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_6792510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792510 prefixEnd_6792510 := by exact prefixLift 6792510
  have htrace : WordTrace (prefixWord ++ tailWord_6792510) baseStart_6792510 baseEnd_6792510 := by
    simpa [prefixWord, tailWord_6792510, baseEnd_6792510] using wordTrace_append hprefix tailTrace_6792510
  have hstable : (prefixWord ++ tailWord_6792510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792510).length < 2 ^ (prefixWord ++ tailWord_6792510).sum := by decide
  have hdescent : baseEnd_6792510 < baseStart_6792510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792518 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_6792518 : Nat := 118140960795 + 6792518 * 2 ^ 59
def prefixEnd_6792518 : Nat := 4983230072969 + 3 ^ 40 * 6792518 * 2
def baseEnd_6792518 : Nat := 3487826588316560475786785

theorem tailTrace_6792518 : CollatzResearch.WordTrace tailWord_6792518 prefixEnd_6792518 3487826588316560475786785 := by
  unfold tailWord_6792518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7741983887683588455051319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 165162322937249887041094805 7741983887683588455051319)
  ·
    refine ⟨11612975831525382682576979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7741983887683588455051319 11612975831525382682576979)
    ·
      refine ⟨17419463747288074023865469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11612975831525382682576979 17419463747288074023865469)
      ·
        refine ⟨6532298905233027758949551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17419463747288074023865469 6532298905233027758949551)
        ·
          refine ⟨9798448357849541638424327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6532298905233027758949551 9798448357849541638424327)
          ·
            refine ⟨14697672536774312457636491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9798448357849541638424327 14697672536774312457636491)
            ·
              refine ⟨22046508805161468686454737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14697672536774312457636491 22046508805161468686454737)
              ·
                refine ⟨16534881603871101514841053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22046508805161468686454737 16534881603871101514841053)
                ·
                  refine ⟨6200580601451663068065395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16534881603871101514841053 6200580601451663068065395)
                  ·
                    refine ⟨9300870902177494602098093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6200580601451663068065395 9300870902177494602098093)
                    ·
                      refine ⟨3487826588316560475786785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9300870902177494602098093 3487826588316560475786785)
                      ·
                        rfl

theorem cell23_6792518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_6792518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792518 prefixEnd_6792518 := by exact prefixLift 6792518
  have htrace : WordTrace (prefixWord ++ tailWord_6792518) baseStart_6792518 baseEnd_6792518 := by
    simpa [prefixWord, tailWord_6792518, baseEnd_6792518] using wordTrace_append hprefix tailTrace_6792518
  have hstable : (prefixWord ++ tailWord_6792518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792518).length < 2 ^ (prefixWord ++ tailWord_6792518).sum := by decide
  have hdescent : baseEnd_6792518 < baseStart_6792518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792524 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 3, 2, 2]
def baseStart_6792524 : Nat := 118140960795 + 6792524 * 2 ^ 59
def prefixEnd_6792524 : Nat := 4983230072969 + 3 ^ 40 * 6792524 * 2
def baseEnd_6792524 : Nat := 3487829669200487452311757

theorem tailTrace_6792524 : CollatzResearch.WordTrace tailWord_6792524 prefixEnd_6792524 3487829669200487452311757 := by
  unfold tailWord_6792524
  simp only [CollatzResearch.WordTrace]
  refine ⟨123871851621926546793180313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165162468829235395724240417 123871851621926546793180313)
  ·
    refine ⟨92903888716444910094885235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123871851621926546793180313 92903888716444910094885235)
    ·
      refine ⟨139355833074667365142327853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92903888716444910094885235 139355833074667365142327853)
      ·
        refine ⟨52258437403000261928372945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139355833074667365142327853 52258437403000261928372945)
        ·
          refine ⟨39193828052250196446279709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52258437403000261928372945 39193828052250196446279709)
          ·
            refine ⟨14697685519593823667354891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39193828052250196446279709 14697685519593823667354891)
            ·
              refine ⟨22046528279390735501032337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14697685519593823667354891 22046528279390735501032337)
              ·
                refine ⟨16534896209543051625774253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22046528279390735501032337 16534896209543051625774253)
                ·
                  refine ⟨6200586078578644359665345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16534896209543051625774253 6200586078578644359665345)
                  ·
                    refine ⟨4650439558933983269749009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6200586078578644359665345 4650439558933983269749009)
                    ·
                      refine ⟨3487829669200487452311757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4650439558933983269749009 3487829669200487452311757)
                      ·
                        rfl

theorem cell23_6792524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_6792524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792524 prefixEnd_6792524 := by exact prefixLift 6792524
  have htrace : WordTrace (prefixWord ++ tailWord_6792524) baseStart_6792524 baseEnd_6792524 := by
    simpa [prefixWord, tailWord_6792524, baseEnd_6792524] using wordTrace_append hprefix tailTrace_6792524
  have hstable : (prefixWord ++ tailWord_6792524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792524).length < 2 ^ (prefixWord ++ tailWord_6792524).sum := by decide
  have hdescent : baseEnd_6792524 < baseStart_6792524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792544 : List Nat := [2, 1, 1, 3, 4, 1, 4, 1, 1, 2, 3]
def baseStart_6792544 : Nat := 118140960795 + 6792544 * 2 ^ 59
def prefixEnd_6792544 : Nat := 4983230072969 + 3 ^ 40 * 6792544 * 2
def baseEnd_6792544 : Nat := 3487839938813577374061665

theorem tailTrace_6792544 : CollatzResearch.WordTrace tailWord_6792544 prefixEnd_6792544 3487839938813577374061665 := by
  unfold tailWord_6792544
  simp only [CollatzResearch.WordTrace]
  refine ⟨123872216351890318501044343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165162955135853758001392457 123872216351890318501044343)
  ·
    refine ⟨185808324527835477751566515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123872216351890318501044343 185808324527835477751566515)
    ·
      refine ⟨278712486791753216627349773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185808324527835477751566515 278712486791753216627349773)
      ·
        refine ⟨104517182546907456235256165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278712486791753216627349773 104517182546907456235256165)
        ·
          refine ⟨19596971727545148044110531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104517182546907456235256165 19596971727545148044110531)
          ·
            refine ⟨29395457591317722066165797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19596971727545148044110531 29395457591317722066165797)
            ·
              refine ⟨5511648298372072887406087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29395457591317722066165797 5511648298372072887406087)
              ·
                refine ⟨8267472447558109331109131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5511648298372072887406087 8267472447558109331109131)
                ·
                  refine ⟨12401208671337163996663697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8267472447558109331109131 12401208671337163996663697)
                  ·
                    refine ⟨9300906503502872997497773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12401208671337163996663697 9300906503502872997497773)
                    ·
                      refine ⟨3487839938813577374061665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9300906503502872997497773 3487839938813577374061665)
                      ·
                        rfl

theorem cell23_6792544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_6792544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792544 prefixEnd_6792544 := by exact prefixLift 6792544
  have htrace : WordTrace (prefixWord ++ tailWord_6792544) baseStart_6792544 baseEnd_6792544 := by
    simpa [prefixWord, tailWord_6792544, baseEnd_6792544] using wordTrace_append hprefix tailTrace_6792544
  have hstable : (prefixWord ++ tailWord_6792544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792544).length < 2 ^ (prefixWord ++ tailWord_6792544).sum := by decide
  have hdescent : baseEnd_6792544 < baseStart_6792544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792551 : List Nat := [1, 1, 5, 1, 5, 1, 1, 2, 2, 4]
def baseStart_6792551 : Nat := 118140960795 + 6792551 * 2 ^ 59
def prefixEnd_6792551 : Nat := 4983230072969 + 3 ^ 40 * 6792551 * 2
def baseEnd_6792551 : Nat := 1162614511059386282224711

theorem tailTrace_6792551 : CollatzResearch.WordTrace tailWord_6792551 prefixEnd_6792551 1162614511059386282224711 := by
  unfold tailWord_6792551
  simp only [CollatzResearch.WordTrace]
  refine ⟨247744688014755277197593507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165163125343170184798395671 247744688014755277197593507)
  ·
    refine ⟨371617032022132915796390261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247744688014755277197593507 371617032022132915796390261)
    ·
      refine ⟨34839096752074960855911587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 371617032022132915796390261 34839096752074960855911587)
      ·
        refine ⟨52258645128112441283867381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34839096752074960855911587 52258645128112441283867381)
        ·
          refine ⟨4899247980760541370362567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52258645128112441283867381 4899247980760541370362567)
          ·
            refine ⟨7348871971140812055543851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4899247980760541370362567 7348871971140812055543851)
            ·
              refine ⟨11023307956711218083315777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7348871971140812055543851 11023307956711218083315777)
              ·
                refine ⟨8267480967533413562486833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11023307956711218083315777 8267480967533413562486833)
                ·
                  refine ⟨6200610725650060171865125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8267480967533413562486833 6200610725650060171865125)
                  ·
                    refine ⟨1162614511059386282224711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6200610725650060171865125 1162614511059386282224711)
                    ·
                      rfl

theorem cell23_6792551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_6792551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792551 prefixEnd_6792551 := by exact prefixLift 6792551
  have htrace : WordTrace (prefixWord ++ tailWord_6792551) baseStart_6792551 baseEnd_6792551 := by
    simpa [prefixWord, tailWord_6792551, baseEnd_6792551] using wordTrace_append hprefix tailTrace_6792551
  have hstable : (prefixWord ++ tailWord_6792551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792551).length < 2 ^ (prefixWord ++ tailWord_6792551).sum := by decide
  have hdescent : baseEnd_6792551 < baseStart_6792551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792553 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 4, 2, 5]
def baseStart_6792553 : Nat := 118140960795 + 6792553 * 2 ^ 59
def prefixEnd_6792553 : Nat := 4983230072969 + 3 ^ 40 * 6792553 * 2
def baseEnd_6792553 : Nat := 3487844560139467838849123

theorem tailTrace_6792553 : CollatzResearch.WordTrace tailWord_6792553 prefixEnd_6792553 3487844560139467838849123 := by
  unfold tailWord_6792553
  simp only [CollatzResearch.WordTrace]
  refine ⟨247744760960748031539166313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165163173973832021026110875 247744760960748031539166313)
  ·
    refine ⟨185808570720561023654374735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247744760960748031539166313 185808570720561023654374735)
    ·
      refine ⟨278712856080841535481562103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185808570720561023654374735 278712856080841535481562103)
      ·
        refine ⟨418069284121262303222343155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278712856080841535481562103 418069284121262303222343155)
        ·
          refine ⟨627103926181893454833514733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418069284121262303222343155 627103926181893454833514733)
          ·
            refine ⟨235163972318210045562568025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 627103926181893454833514733 235163972318210045562568025)
            ·
              refine ⟨176372979238657534171926019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235163972318210045562568025 176372979238657534171926019)
              ·
                refine ⟨264559468857986301257889029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176372979238657534171926019 264559468857986301257889029)
                ·
                  refine ⟨49604900410872431485854193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264559468857986301257889029 49604900410872431485854193)
                  ·
                    refine ⟨37203675308154323614390645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49604900410872431485854193 37203675308154323614390645)
                    ·
                      refine ⟨3487844560139467838849123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37203675308154323614390645 3487844560139467838849123)
                      ·
                        rfl

theorem cell23_6792553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_6792553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792553 prefixEnd_6792553 := by exact prefixLift 6792553
  have htrace : WordTrace (prefixWord ++ tailWord_6792553) baseStart_6792553 baseEnd_6792553 := by
    simpa [prefixWord, tailWord_6792553, baseEnd_6792553] using wordTrace_append hprefix tailTrace_6792553
  have hstable : (prefixWord ++ tailWord_6792553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792553).length < 2 ^ (prefixWord ++ tailWord_6792553).sum := by decide
  have hdescent : baseEnd_6792553 < baseStart_6792553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792558 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 3, 2, 2]
def baseStart_6792558 : Nat := 118140960795 + 6792558 * 2 ^ 59
def prefixEnd_6792558 : Nat := 4983230072969 + 3 ^ 40 * 6792558 * 2
def baseEnd_6792558 : Nat := 3487847127542740319286601

theorem tailTrace_6792558 : CollatzResearch.WordTrace tailWord_6792558 prefixEnd_6792558 3487847127542740319286601 := by
  unfold tailWord_6792558
  simp only [CollatzResearch.WordTrace]
  refine ⟨30968117915716239674137291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165163295550486611595398885 30968117915716239674137291)
  ·
    refine ⟨46452176873574359511205937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30968117915716239674137291 46452176873574359511205937)
    ·
      refine ⟨34839132655180769633404453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46452176873574359511205937 34839132655180769633404453)
      ·
        refine ⟨6532337372846394306263335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34839132655180769633404453 6532337372846394306263335)
        ·
          refine ⟨9798506059269591459395003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6532337372846394306263335 9798506059269591459395003)
          ·
            refine ⟨14697759088904387189092505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9798506059269591459395003 14697759088904387189092505)
            ·
              refine ⟨11023319316678290391819379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14697759088904387189092505 11023319316678290391819379)
              ·
                refine ⟨16534978975017435587729069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11023319316678290391819379 16534978975017435587729069)
                ·
                  refine ⟨6200617115631538345398401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16534978975017435587729069 6200617115631538345398401)
                  ·
                    refine ⟨4650462836723653759048801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6200617115631538345398401 4650462836723653759048801)
                    ·
                      refine ⟨3487847127542740319286601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4650462836723653759048801 3487847127542740319286601)
                      ·
                        rfl

theorem cell23_6792558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_6792558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792558 prefixEnd_6792558 := by exact prefixLift 6792558
  have htrace : WordTrace (prefixWord ++ tailWord_6792558) baseStart_6792558 baseEnd_6792558 := by
    simpa [prefixWord, tailWord_6792558, baseEnd_6792558] using wordTrace_append hprefix tailTrace_6792558
  have hstable : (prefixWord ++ tailWord_6792558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792558).length < 2 ^ (prefixWord ++ tailWord_6792558).sum := by decide
  have hdescent : baseEnd_6792558 < baseStart_6792558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792584 : List Nat := [2, 1, 3, 3, 1, 2, 1, 4, 1, 3, 2]
def baseStart_6792584 : Nat := 118140960795 + 6792584 * 2 ^ 59
def prefixEnd_6792584 : Nat := 4983230072969 + 3 ^ 40 * 6792584 * 2
def baseEnd_6792584 : Nat := 3487860478039757217561481

theorem tailTrace_6792584 : CollatzResearch.WordTrace tailWord_6792584 prefixEnd_6792584 3487860478039757217561481 := by
  unfold tailWord_6792584
  simp only [CollatzResearch.WordTrace]
  refine ⟨123872945811817861916772403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165163927749090482555696537 123872945811817861916772403)
  ·
    refine ⟨185809418717726792875158605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123872945811817861916772403 185809418717726792875158605)
    ·
      refine ⟨69678532019147547328184477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185809418717726792875158605 69678532019147547328184477)
      ·
        refine ⟨26129449507180330248069179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69678532019147547328184477 26129449507180330248069179)
        ·
          refine ⟨39194174260770495372103769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26129449507180330248069179 39194174260770495372103769)
          ·
            refine ⟨29395630695577871529077827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39194174260770495372103769 29395630695577871529077827)
            ·
              refine ⟨44093446043366807293616741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29395630695577871529077827 44093446043366807293616741)
              ·
                refine ⟨8267521133131276367553139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44093446043366807293616741 8267521133131276367553139)
                ·
                  refine ⟨12401281699696914551329709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8267521133131276367553139 12401281699696914551329709)
                  ·
                    refine ⟨4650480637386342956748641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12401281699696914551329709 4650480637386342956748641)
                    ·
                      refine ⟨3487860478039757217561481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4650480637386342956748641 3487860478039757217561481)
                      ·
                        rfl

theorem cell23_6792584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_6792584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792584 prefixEnd_6792584 := by exact prefixLift 6792584
  have htrace : WordTrace (prefixWord ++ tailWord_6792584) baseStart_6792584 baseEnd_6792584 := by
    simpa [prefixWord, tailWord_6792584, baseEnd_6792584] using wordTrace_append hprefix tailTrace_6792584
  have hstable : (prefixWord ++ tailWord_6792584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792584).length < 2 ^ (prefixWord ++ tailWord_6792584).sum := by decide
  have hdescent : baseEnd_6792584 < baseStart_6792584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792597 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 1, 4, 2]
def baseStart_6792597 : Nat := 118140960795 + 6792597 * 2 ^ 59
def prefixEnd_6792597 : Nat := 4983230072969 + 3 ^ 40 * 6792597 * 2
def baseEnd_6792597 : Nat := 3487867153288265666698921

theorem tailTrace_6792597 : CollatzResearch.WordTrace tailWord_6792597 prefixEnd_6792597 3487867153288265666698921 := by
  unfold tailWord_6792597
  simp only [CollatzResearch.WordTrace]
  refine ⟨247746365772588627053768045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165164243848392418035845363 247746365772588627053768045)
  ·
    refine ⟨92904887164720735145163017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247746365772588627053768045 92904887164720735145163017)
    ·
      refine ⟨69678665373540551358872263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92904887164720735145163017 69678665373540551358872263)
      ·
        refine ⟨104517998060310827038308395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69678665373540551358872263 104517998060310827038308395)
        ·
          refine ⟨156776997090466240557462593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104517998060310827038308395 156776997090466240557462593)
          ·
            refine ⟨117582747817849680418096945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156776997090466240557462593 117582747817849680418096945)
            ·
              refine ⟨88187060863387260313572709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117582747817849680418096945 88187060863387260313572709)
              ·
                refine ⟨16535073911885111308794883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88187060863387260313572709 16535073911885111308794883)
                ·
                  refine ⟨24802610867827666963192325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16535073911885111308794883 24802610867827666963192325)
                  ·
                    refine ⟨4650489537717687555598561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24802610867827666963192325 4650489537717687555598561)
                    ·
                      refine ⟨3487867153288265666698921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4650489537717687555598561 3487867153288265666698921)
                      ·
                        rfl

theorem cell23_6792597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_6792597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792597 prefixEnd_6792597 := by exact prefixLift 6792597
  have htrace : WordTrace (prefixWord ++ tailWord_6792597) baseStart_6792597 baseEnd_6792597 := by
    simpa [prefixWord, tailWord_6792597, baseEnd_6792597] using wordTrace_append hprefix tailTrace_6792597
  have hstable : (prefixWord ++ tailWord_6792597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792597).length < 2 ^ (prefixWord ++ tailWord_6792597).sum := by decide
  have hdescent : baseEnd_6792597 < baseStart_6792597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792620 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 7]
def baseStart_6792620 : Nat := 118140960795 + 6792620 * 2 ^ 59
def prefixEnd_6792620 : Nat := 4983230072969 + 3 ^ 40 * 6792620 * 2
def baseEnd_6792620 : Nat := 387542107038146564079035

theorem tailTrace_6792620 : CollatzResearch.WordTrace tailWord_6792620 prefixEnd_6792620 387542107038146564079035 := by
  unfold tailWord_6792620
  simp only [CollatzResearch.WordTrace]
  refine ⟨123873602325752650990927657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165164803101003534654570209 123873602325752650990927657)
  ·
    refine ⟨92905201744314488243195743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123873602325752650990927657 92905201744314488243195743)
    ·
      refine ⟨139357802616471732364793615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92905201744314488243195743 139357802616471732364793615)
      ·
        refine ⟨209036703924707598547190423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139357802616471732364793615 209036703924707598547190423)
        ·
          refine ⟨313555055887061397820785635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209036703924707598547190423 313555055887061397820785635)
          ·
            refine ⟨470332583830592096731178453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313555055887061397820785635 470332583830592096731178453)
            ·
              refine ⟨11023419933529502267136995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 470332583830592096731178453 11023419933529502267136995)
              ·
                refine ⟨16535129900294253400705493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11023419933529502267136995 16535129900294253400705493)
                ·
                  refine ⟨387542107038146564079035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16535129900294253400705493 387542107038146564079035)
                  ·
                    rfl

theorem cell23_6792620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 7].length) (baseStart_6792620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792620 prefixEnd_6792620 := by exact prefixLift 6792620
  have htrace : WordTrace (prefixWord ++ tailWord_6792620) baseStart_6792620 baseEnd_6792620 := by
    simpa [prefixWord, tailWord_6792620, baseEnd_6792620] using wordTrace_append hprefix tailTrace_6792620
  have hstable : (prefixWord ++ tailWord_6792620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792620).length < 2 ^ (prefixWord ++ tailWord_6792620).sum := by decide
  have hdescent : baseEnd_6792620 < baseStart_6792620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792677 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 1, 2, 5]
def baseStart_6792677 : Nat := 118140960795 + 6792677 * 2 ^ 59
def prefixEnd_6792677 : Nat := 4983230072969 + 3 ^ 40 * 6792677 * 2
def baseEnd_6792677 : Nat := 3487908231740625353698553

theorem tailTrace_6792677 : CollatzResearch.WordTrace tailWord_6792677 prefixEnd_6792677 3487908231740625353698553 := by
  unfold tailWord_6792677
  simp only [CollatzResearch.WordTrace]
  refine ⟨247749283612298800716680285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165166189074865867144453523 247749283612298800716680285)
  ·
    refine ⟨92905981354612050268755107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247749283612298800716680285 92905981354612050268755107)
    ·
      refine ⟨139358972031918075403132661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92905981354612050268755107 139358972031918075403132661)
      ·
        refine ⟨13064903627992319569043687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139358972031918075403132661 13064903627992319569043687)
        ·
          refine ⟨19597355441988479353565531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13064903627992319569043687 19597355441988479353565531)
          ·
            refine ⟨29396033162982719030348297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19597355441988479353565531 29396033162982719030348297)
            ·
              refine ⟨22047024872237039272761223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29396033162982719030348297 22047024872237039272761223)
              ·
                refine ⟨33070537308355558909141835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22047024872237039272761223 33070537308355558909141835)
                ·
                  refine ⟨49605805962533338363712753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33070537308355558909141835 49605805962533338363712753)
                  ·
                    refine ⟨37204354471900003772784565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49605805962533338363712753 37204354471900003772784565)
                    ·
                      refine ⟨3487908231740625353698553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37204354471900003772784565 3487908231740625353698553)
                      ·
                        rfl

theorem cell23_6792677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_6792677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792677 prefixEnd_6792677 := by exact prefixLift 6792677
  have htrace : WordTrace (prefixWord ++ tailWord_6792677) baseStart_6792677 baseEnd_6792677 := by
    simpa [prefixWord, tailWord_6792677, baseEnd_6792677] using wordTrace_append hprefix tailTrace_6792677
  have hstable : (prefixWord ++ tailWord_6792677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792677).length < 2 ^ (prefixWord ++ tailWord_6792677).sum := by decide
  have hdescent : baseEnd_6792677 < baseStart_6792677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792687 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 1, 6, 2]
def baseStart_6792687 : Nat := 118140960795 + 6792687 * 2 ^ 59
def prefixEnd_6792687 : Nat := 4983230072969 + 3 ^ 40 * 6792687 * 2
def baseEnd_6792687 : Nat := 3487913366547170314573507

theorem tailTrace_6792687 : CollatzResearch.WordTrace tailWord_6792687 prefixEnd_6792687 3487913366547170314573507 := by
  unfold tailWord_6792687
  simp only [CollatzResearch.WordTrace]
  refine ⟨247749648342262572424544315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165166432228175048283029543 247749648342262572424544315)
  ·
    refine ⟨371624472513393858636816473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247749648342262572424544315 371624472513393858636816473)
    ·
      refine ⟨278718354385045393977612355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371624472513393858636816473 278718354385045393977612355)
      ·
        refine ⟨418077531577568090966418533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278718354385045393977612355 418077531577568090966418533)
        ·
          refine ⟨78389537170794017056203475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 418077531577568090966418533 78389537170794017056203475)
          ·
            refine ⟨117584305756191025584305213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78389537170794017056203475 117584305756191025584305213)
            ·
              refine ⟨44094114658571634594114455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117584305756191025584305213 44094114658571634594114455)
              ·
                refine ⟨66141171987857451891171683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44094114658571634594114455 66141171987857451891171683)
                ·
                  refine ⟨99211757981786177836757525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66141171987857451891171683 99211757981786177836757525)
                  ·
                    refine ⟨4650551155396227086098009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99211757981786177836757525 4650551155396227086098009)
                    ·
                      refine ⟨3487913366547170314573507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4650551155396227086098009 3487913366547170314573507)
                      ·
                        rfl

theorem cell23_6792687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 6, 2].length) (baseStart_6792687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792687 prefixEnd_6792687 := by exact prefixLift 6792687
  have htrace : WordTrace (prefixWord ++ tailWord_6792687) baseStart_6792687 baseEnd_6792687 := by
    simpa [prefixWord, tailWord_6792687, baseEnd_6792687] using wordTrace_append hprefix tailTrace_6792687
  have hstable : (prefixWord ++ tailWord_6792687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792687).length < 2 ^ (prefixWord ++ tailWord_6792687).sum := by decide
  have hdescent : baseEnd_6792687 < baseStart_6792687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792707 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 3]
def baseStart_6792707 : Nat := 118140960795 + 6792707 * 2 ^ 59
def prefixEnd_6792707 : Nat := 4983230072969 + 3 ^ 40 * 6792707 * 2
def baseEnd_6792707 : Nat := 3487923636160260236323415

theorem tailTrace_6792707 : CollatzResearch.WordTrace tailWord_6792707 prefixEnd_6792707 3487923636160260236323415 := by
  unfold tailWord_6792707
  simp only [CollatzResearch.WordTrace]
  refine ⟨247750377802190115840272375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165166918534793410560181583 247750377802190115840272375)
  ·
    refine ⟨371625566703285173760408563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247750377802190115840272375 371625566703285173760408563)
    ·
      refine ⟨557438350054927760640612845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371625566703285173760408563 557438350054927760640612845)
      ·
        refine ⟨209039381270597910240229817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 557438350054927760640612845 209039381270597910240229817)
        ·
          refine ⟨156779535952948432680172363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209039381270597910240229817 156779535952948432680172363)
          ·
            refine ⟨235169303929422649020258545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156779535952948432680172363 235169303929422649020258545)
            ·
              refine ⟨176376977947066986765193909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235169303929422649020258545 176376977947066986765193909)
              ·
                refine ⟨16535341682537530009236929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176376977947066986765193909 16535341682537530009236929)
                ·
                  refine ⟨12401506261903147506927697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16535341682537530009236929 12401506261903147506927697)
                  ·
                    refine ⟨9301129696427360630195773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12401506261903147506927697 9301129696427360630195773)
                    ·
                      refine ⟨3487923636160260236323415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9301129696427360630195773 3487923636160260236323415)
                      ·
                        rfl

theorem cell23_6792707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_6792707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792707 prefixEnd_6792707 := by exact prefixLift 6792707
  have htrace : WordTrace (prefixWord ++ tailWord_6792707) baseStart_6792707 baseEnd_6792707 := by
    simpa [prefixWord, tailWord_6792707, baseEnd_6792707] using wordTrace_append hprefix tailTrace_6792707
  have hstable : (prefixWord ++ tailWord_6792707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792707).length < 2 ^ (prefixWord ++ tailWord_6792707).sum := by decide
  have hdescent : baseEnd_6792707 < baseStart_6792707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792765 : List Nat := [1, 4, 1, 3, 4, 1, 1, 3, 1, 4]
def baseStart_6792765 : Nat := 118140960795 + 6792765 * 2 ^ 59
def prefixEnd_6792765 : Nat := 4983230072969 + 3 ^ 40 * 6792765 * 2
def baseEnd_6792765 : Nat := 1162651139346073669799383

theorem tailTrace_6792765 : CollatzResearch.WordTrace tailWord_6792765 prefixEnd_6792765 1162651139346073669799383 := by
  unfold tailWord_6792765
  simp only [CollatzResearch.WordTrace]
  refine ⟨247752493235979991745883749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165168328823986661163922499 247752493235979991745883749)
  ·
    refine ⟨46453592481746248452353203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247752493235979991745883749 46453592481746248452353203)
    ·
      refine ⟨69680388722619372678529805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46453592481746248452353203 69680388722619372678529805)
      ·
        refine ⟨26130145770982264754448677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69680388722619372678529805 26130145770982264754448677)
        ·
          refine ⟨4899402332059174641459127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26130145770982264754448677 4899402332059174641459127)
          ·
            refine ⟨7349103498088761962188691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4899402332059174641459127 7349103498088761962188691)
            ·
              refine ⟨11023655247133142943283037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7349103498088761962188691 11023655247133142943283037)
              ·
                refine ⟨4133870717674928603731139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11023655247133142943283037 4133870717674928603731139)
                ·
                  refine ⟨6200806076512392905596709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133870717674928603731139 6200806076512392905596709)
                  ·
                    refine ⟨1162651139346073669799383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6200806076512392905596709 1162651139346073669799383)
                    ·
                      rfl

theorem cell23_6792765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_6792765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792765 prefixEnd_6792765 := by exact prefixLift 6792765
  have htrace : WordTrace (prefixWord ++ tailWord_6792765) baseStart_6792765 baseEnd_6792765 := by
    simpa [prefixWord, tailWord_6792765, baseEnd_6792765] using wordTrace_append hprefix tailTrace_6792765
  have hstable : (prefixWord ++ tailWord_6792765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792765).length < 2 ^ (prefixWord ++ tailWord_6792765).sum := by decide
  have hdescent : baseEnd_6792765 < baseStart_6792765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792807 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_6792807 : Nat := 118140960795 + 6792807 * 2 ^ 59
def prefixEnd_6792807 : Nat := 4983230072969 + 3 ^ 40 * 6792807 * 2
def baseEnd_6792807 : Nat := 3487974984225709845072955

theorem tailTrace_6792807 : CollatzResearch.WordTrace tailWord_6792807 prefixEnd_6792807 3487974984225709845072955 := by
  unfold tailWord_6792807
  simp only [CollatzResearch.WordTrace]
  refine ⟨247754025101827832918912675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165169350067885221945941783 247754025101827832918912675)
  ·
    refine ⟨371631037652741749378369013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247754025101827832918912675 371631037652741749378369013)
    ·
      refine ⟨34840409779944539004222095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 371631037652741749378369013 34840409779944539004222095)
      ·
        refine ⟨52260614669916808506333143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34840409779944539004222095 52260614669916808506333143)
        ·
          refine ⟨78390922004875212759499715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52260614669916808506333143 78390922004875212759499715)
          ·
            refine ⟨117586383007312819139249573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78390922004875212759499715 117586383007312819139249573)
            ·
              refine ⟨22047446813871153588609295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117586383007312819139249573 22047446813871153588609295)
              ·
                refine ⟨33071170220806730382913943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22047446813871153588609295 33071170220806730382913943)
                ·
                  refine ⟨49606755331210095574370915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33071170220806730382913943 49606755331210095574370915)
                  ·
                    refine ⟨74410132996815143361556373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49606755331210095574370915 74410132996815143361556373)
                    ·
                      refine ⟨3487974984225709845072955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74410132996815143361556373 3487974984225709845072955)
                      ·
                        rfl

theorem cell23_6792807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_6792807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792807 prefixEnd_6792807 := by exact prefixLift 6792807
  have htrace : WordTrace (prefixWord ++ tailWord_6792807) baseStart_6792807 baseEnd_6792807 := by
    simpa [prefixWord, tailWord_6792807, baseEnd_6792807] using wordTrace_append hprefix tailTrace_6792807
  have hstable : (prefixWord ++ tailWord_6792807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792807).length < 2 ^ (prefixWord ++ tailWord_6792807).sum := by decide
  have hdescent : baseEnd_6792807 < baseStart_6792807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792828 : List Nat := [2, 2, 2, 1, 1, 2, 1, 7, 1, 2, 2]
def baseStart_6792828 : Nat := 118140960795 + 6792828 * 2 ^ 59
def prefixEnd_6792828 : Nat := 4983230072969 + 3 ^ 40 * 6792828 * 2
def baseEnd_6792828 : Nat := 3487985767319454262910359

theorem tailTrace_6792828 : CollatzResearch.WordTrace tailWord_6792828 prefixEnd_6792828 3487985767319454262910359 := by
  unfold tailWord_6792828
  simp only [CollatzResearch.WordTrace]
  refine ⟨123877395517375876752713569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165169860689834502336951425 123877395517375876752713569)
  ·
    refine ⟨92908046638031907564535177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123877395517375876752713569 92908046638031907564535177)
    ·
      refine ⟨69681034978523930673401383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92908046638031907564535177 69681034978523930673401383)
      ·
        refine ⟨104521552467785896010102075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69681034978523930673401383 104521552467785896010102075)
        ·
          refine ⟨156782328701678844015153113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104521552467785896010102075 156782328701678844015153113)
          ·
            refine ⟨117586746526259133011364835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156782328701678844015153113 117586746526259133011364835)
            ·
              refine ⟨176380119789388699517047253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117586746526259133011364835 176380119789388699517047253)
              ·
                refine ⟨4133909057563797644930795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 176380119789388699517047253 4133909057563797644930795)
                ·
                  refine ⟨6200863586345696467396193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133909057563797644930795 6200863586345696467396193)
                  ·
                    refine ⟨4650647689759272350547145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6200863586345696467396193 4650647689759272350547145)
                    ·
                      refine ⟨3487985767319454262910359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4650647689759272350547145 3487985767319454262910359)
                      ·
                        rfl

theorem cell23_6792828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_6792828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792828 prefixEnd_6792828 := by exact prefixLift 6792828
  have htrace : WordTrace (prefixWord ++ tailWord_6792828) baseStart_6792828 baseEnd_6792828 := by
    simpa [prefixWord, tailWord_6792828, baseEnd_6792828] using wordTrace_append hprefix tailTrace_6792828
  have hstable : (prefixWord ++ tailWord_6792828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792828).length < 2 ^ (prefixWord ++ tailWord_6792828).sum := by decide
  have hdescent : baseEnd_6792828 < baseStart_6792828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792834 : List Nat := [3, 4, 3, 13]
def baseStart_6792834 : Nat := 118140960795 + 6792834 * 2 ^ 59
def prefixEnd_6792834 : Nat := 4983230072969 + 3 ^ 40 * 6792834 * 2
def baseEnd_6792834 : Nat := 1594873730317046748713

theorem tailTrace_6792834 : CollatzResearch.WordTrace tailWord_6792834 prefixEnd_6792834 1594873730317046748713 := by
  unfold tailWord_6792834
  simp only [CollatzResearch.WordTrace]
  refine ⟨61938752468182504132536389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165170006581820011020097037 61938752468182504132536389)
  ·
    refine ⟨11613516087784219524850573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61938752468182504132536389 11613516087784219524850573)
    ·
      refine ⟨4355068532919082321818965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11613516087784219524850573 4355068532919082321818965)
      ·
        refine ⟨1594873730317046748713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 4355068532919082321818965 1594873730317046748713)
        ·
          rfl

theorem cell23_6792834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 13].length) (baseStart_6792834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792834 prefixEnd_6792834 := by exact prefixLift 6792834
  have htrace : WordTrace (prefixWord ++ tailWord_6792834) baseStart_6792834 baseEnd_6792834 := by
    simpa [prefixWord, tailWord_6792834, baseEnd_6792834] using wordTrace_append hprefix tailTrace_6792834
  have hstable : (prefixWord ++ tailWord_6792834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792834).length < 2 ^ (prefixWord ++ tailWord_6792834).sum := by decide
  have hdescent : baseEnd_6792834 < baseStart_6792834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792867 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 4]
def baseStart_6792867 : Nat := 118140960795 + 6792867 * 2 ^ 59
def prefixEnd_6792867 : Nat := 4983230072969 + 3 ^ 40 * 6792867 * 2
def baseEnd_6792867 : Nat := 3488005793064979610322679

theorem tailTrace_6792867 : CollatzResearch.WordTrace tailWord_6792867 prefixEnd_6792867 3488005793064979610322679 := by
  unfold tailWord_6792867
  simp only [CollatzResearch.WordTrace]
  refine ⟨247756213481610463166096855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165170808987740308777397903 247756213481610463166096855)
  ·
    refine ⟨371634320222415694749145283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247756213481610463166096855 371634320222415694749145283)
    ·
      refine ⟨557451480333623542123717925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371634320222415694749145283 557451480333623542123717925)
      ·
        refine ⟨104522152562554414148197111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 557451480333623542123717925 104522152562554414148197111)
        ·
          refine ⟨156783228843831621222295667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104522152562554414148197111 156783228843831621222295667)
          ·
            refine ⟨235174843265747431833443501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156783228843831621222295667 235174843265747431833443501)
            ·
              refine ⟨88190566224655286937541313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235174843265747431833443501 88190566224655286937541313)
              ·
                refine ⟨66142924668491465203155985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88190566224655286937541313 66142924668491465203155985)
                ·
                  refine ⟨49607193501368598902366989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66142924668491465203155985 49607193501368598902366989)
                  ·
                    refine ⟨18602697563013224588387621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49607193501368598902366989 18602697563013224588387621)
                    ·
                      refine ⟨3488005793064979610322679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18602697563013224588387621 3488005793064979610322679)
                      ·
                        rfl

theorem cell23_6792867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_6792867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792867 prefixEnd_6792867 := by exact prefixLift 6792867
  have htrace : WordTrace (prefixWord ++ tailWord_6792867) baseStart_6792867 baseEnd_6792867 := by
    simpa [prefixWord, tailWord_6792867, baseEnd_6792867] using wordTrace_append hprefix tailTrace_6792867
  have hstable : (prefixWord ++ tailWord_6792867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792867).length < 2 ^ (prefixWord ++ tailWord_6792867).sum := by decide
  have hdescent : baseEnd_6792867 < baseStart_6792867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792894 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_6792894 : Nat := 118140960795 + 6792894 * 2 ^ 59
def prefixEnd_6792894 : Nat := 4983230072969 + 3 ^ 40 * 6792894 * 2
def baseEnd_6792894 : Nat := 1162673219014217001561685

theorem tailTrace_6792894 : CollatzResearch.WordTrace tailWord_6792894 prefixEnd_6792894 1162673219014217001561685 := by
  unfold tailWord_6792894
  simp only [CollatzResearch.WordTrace]
  refine ⟨30969649781564080847166217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165171465501675097851553157 30969649781564080847166217)
  ·
    refine ⟨23227237336173060635374663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30969649781564080847166217 23227237336173060635374663)
    ·
      refine ⟨34840856004259590953061995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23227237336173060635374663 34840856004259590953061995)
      ·
        refine ⟨52261284006389386429592993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34840856004259590953061995 52261284006389386429592993)
        ·
          refine ⟨39195963004792039822194745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52261284006389386429592993 39195963004792039822194745)
          ·
            refine ⟨29396972253594029866646059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39195963004792039822194745 29396972253594029866646059)
            ·
              refine ⟨44095458380391044799969089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29396972253594029866646059 44095458380391044799969089)
              ·
                refine ⟨33071593785293283599976817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44095458380391044799969089 33071593785293283599976817)
                ·
                  refine ⟨24803695338969962699982613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33071593785293283599976817 24803695338969962699982613)
                  ·
                    refine ⟨1162673219014217001561685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24803695338969962699982613 1162673219014217001561685)
                    ·
                      rfl

theorem cell23_6792894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_6792894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792894 prefixEnd_6792894 := by exact prefixLift 6792894
  have htrace : WordTrace (prefixWord ++ tailWord_6792894) baseStart_6792894 baseEnd_6792894 := by
    simpa [prefixWord, tailWord_6792894, baseEnd_6792894] using wordTrace_append hprefix tailTrace_6792894
  have hstable : (prefixWord ++ tailWord_6792894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792894).length < 2 ^ (prefixWord ++ tailWord_6792894).sum := by decide
  have hdescent : baseEnd_6792894 < baseStart_6792894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792901 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 4, 2, 2]
def baseStart_6792901 : Nat := 118140960795 + 6792901 * 2 ^ 59
def prefixEnd_6792901 : Nat := 4983230072969 + 3 ^ 40 * 6792901 * 2
def baseEnd_6792901 : Nat := 3488023251407232477297523

theorem tailTrace_6792901 : CollatzResearch.WordTrace tailWord_6792901 prefixEnd_6792901 3488023251407232477297523 := by
  unfold tailWord_6792901
  simp only [CollatzResearch.WordTrace]
  refine ⟨247757453563487286972834557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165171635708991524648556371 247757453563487286972834557)
  ·
    refine ⟨92909045086307732614812959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247757453563487286972834557 92909045086307732614812959)
    ·
      refine ⟨139363567629461598922219439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92909045086307732614812959 139363567629461598922219439)
      ·
        refine ⟨209045351444192398383329159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139363567629461598922219439 209045351444192398383329159)
        ·
          refine ⟨313568027166288597574993739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209045351444192398383329159 313568027166288597574993739)
          ·
            refine ⟨470352040749432896362490609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313568027166288597574993739 470352040749432896362490609)
            ·
              refine ⟨352764030562074672271867957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470352040749432896362490609 352764030562074672271867957)
              ·
                refine ⟨33071627865194500525487621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 352764030562074672271867957 33071627865194500525487621)
                ·
                  refine ⟨6200930224723968848528929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33071627865194500525487621 6200930224723968848528929)
                  ·
                    refine ⟨4650697668542976636396697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6200930224723968848528929 4650697668542976636396697)
                    ·
                      refine ⟨3488023251407232477297523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4650697668542976636396697 3488023251407232477297523)
                      ·
                        rfl

theorem cell23_6792901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 2, 2].length) (baseStart_6792901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792901 prefixEnd_6792901 := by exact prefixLift 6792901
  have htrace : WordTrace (prefixWord ++ tailWord_6792901) baseStart_6792901 baseEnd_6792901 := by
    simpa [prefixWord, tailWord_6792901, baseEnd_6792901] using wordTrace_append hprefix tailTrace_6792901
  have hstable : (prefixWord ++ tailWord_6792901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792901).length < 2 ^ (prefixWord ++ tailWord_6792901).sum := by decide
  have hdescent : baseEnd_6792901 < baseStart_6792901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792958 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 7]
def baseStart_6792958 : Nat := 118140960795 + 6792958 * 2 ^ 59
def prefixEnd_6792958 : Nat := 4983230072969 + 3 ^ 40 * 6792958 * 2
def baseEnd_6792958 : Nat := 387561391089393194920529

theorem tailTrace_6792958 : CollatzResearch.WordTrace tailWord_6792958 prefixEnd_6792958 387561391089393194920529 := by
  unfold tailWord_6792958
  simp only [CollatzResearch.WordTrace]
  refine ⟨30969941565535098213457441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165173021682853857138439685 30969941565535098213457441)
  ·
    refine ⟨23227456174151323660093081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30969941565535098213457441 23227456174151323660093081)
    ·
      refine ⟨17420592130613492745069811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23227456174151323660093081 17420592130613492745069811)
      ·
        refine ⟨26130888195920239117604717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17420592130613492745069811 26130888195920239117604717)
        ·
          refine ⟨9799083073470089669101769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26130888195920239117604717 9799083073470089669101769)
          ·
            refine ⟨7349312305102567251826327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9799083073470089669101769 7349312305102567251826327)
            ·
              refine ⟨11023968457653850877739491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7349312305102567251826327 11023968457653850877739491)
              ·
                refine ⟨16535952686480776316609237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11023968457653850877739491 16535952686480776316609237)
                ·
                  refine ⟨387561391089393194920529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16535952686480776316609237 387561391089393194920529)
                  ·
                    rfl

theorem cell23_6792958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_6792958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792958 prefixEnd_6792958 := by exact prefixLift 6792958
  have htrace : WordTrace (prefixWord ++ tailWord_6792958) baseStart_6792958 baseEnd_6792958 := by
    simpa [prefixWord, tailWord_6792958, baseEnd_6792958] using wordTrace_append hprefix tailTrace_6792958
  have hstable : (prefixWord ++ tailWord_6792958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792958).length < 2 ^ (prefixWord ++ tailWord_6792958).sum := by decide
  have hdescent : baseEnd_6792958 < baseStart_6792958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792964 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_6792964 : Nat := 118140960795 + 6792964 * 2 ^ 59
def prefixEnd_6792964 : Nat := 4983230072969 + 3 ^ 40 * 6792964 * 2
def baseEnd_6792964 : Nat := 3488055600688465730809733

theorem tailTrace_6792964 : CollatzResearch.WordTrace tailWord_6792964 prefixEnd_6792964 3488055600688465730809733 := by
  unfold tailWord_6792964
  simp only [CollatzResearch.WordTrace]
  refine ⟨123879875681129524366188973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165173167574839365821585297 123879875681129524366188973)
  ·
    refine ⟨46454953380423571637320865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123879875681129524366188973 46454953380423571637320865)
    ·
      refine ⟨34841215035317678727990649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46454953380423571637320865 34841215035317678727990649)
      ·
        refine ⟨26130911276488259045992987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34841215035317678727990649 26130911276488259045992987)
        ·
          refine ⟨39196366914732388568989481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26130911276488259045992987 39196366914732388568989481)
          ·
            refine ⟨29397275186049291426742111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39196366914732388568989481 29397275186049291426742111)
            ·
              refine ⟨44095912779073937140113167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29397275186049291426742111 44095912779073937140113167)
              ·
                refine ⟨66143869168610905710169751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44095912779073937140113167 66143869168610905710169751)
                ·
                  refine ⟨99215803752916358565254627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66143869168610905710169751 99215803752916358565254627)
                  ·
                    refine ⟨148823705629374537847881941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99215803752916358565254627 148823705629374537847881941)
                    ·
                      refine ⟨3488055600688465730809733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148823705629374537847881941 3488055600688465730809733)
                      ·
                        rfl

theorem cell23_6792964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_6792964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792964 prefixEnd_6792964 := by exact prefixLift 6792964
  have htrace : WordTrace (prefixWord ++ tailWord_6792964) baseStart_6792964 baseEnd_6792964 := by
    simpa [prefixWord, tailWord_6792964, baseEnd_6792964] using wordTrace_append hprefix tailTrace_6792964
  have hstable : (prefixWord ++ tailWord_6792964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792964).length < 2 ^ (prefixWord ++ tailWord_6792964).sum := by decide
  have hdescent : baseEnd_6792964 < baseStart_6792964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792973 : List Nat := [1, 7, 2, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_6792973 : Nat := 118140960795 + 6792973 * 2 ^ 59
def prefixEnd_6792973 : Nat := 4983230072969 + 3 ^ 40 * 6792973 * 2
def baseEnd_6792973 : Nat := 3488060222014356195597193

theorem tailTrace_6792973 : CollatzResearch.WordTrace tailWord_6792973 prefixEnd_6792973 3488060222014356195597193 := by
  unfold tailWord_6792973
  simp only [CollatzResearch.WordTrace]
  refine ⟨247760079619226443269455573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165173386412817628846303715 247760079619226443269455573)
  ·
    refine ⟨5806876866075619764127865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 247760079619226443269455573 5806876866075619764127865)
    ·
      refine ⟨4355157649556714823095899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5806876866075619764127865 4355157649556714823095899)
      ·
        refine ⟨6532736474335072234643849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4355157649556714823095899 6532736474335072234643849)
        ·
          refine ⟨4899552355751304175982887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6532736474335072234643849 4899552355751304175982887)
          ·
            refine ⟨7349328533626956263974331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4899552355751304175982887 7349328533626956263974331)
            ·
              refine ⟨11023992800440434395961497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7349328533626956263974331 11023992800440434395961497)
              ·
                refine ⟨8267994600330325796971123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11023992800440434395961497 8267994600330325796971123)
                ·
                  refine ⟨12401991900495488695456685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8267994600330325796971123 12401991900495488695456685)
                  ·
                    refine ⟨4650746962685808260796257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12401991900495488695456685 4650746962685808260796257)
                    ·
                      refine ⟨3488060222014356195597193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4650746962685808260796257 3488060222014356195597193)
                      ·
                        rfl

theorem cell23_6792973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_6792973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792973 prefixEnd_6792973 := by exact prefixLift 6792973
  have htrace : WordTrace (prefixWord ++ tailWord_6792973) baseStart_6792973 baseEnd_6792973 := by
    simpa [prefixWord, tailWord_6792973, baseEnd_6792973] using wordTrace_append hprefix tailTrace_6792973
  have hstable : (prefixWord ++ tailWord_6792973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792973).length < 2 ^ (prefixWord ++ tailWord_6792973).sum := by decide
  have hdescent : baseEnd_6792973 < baseStart_6792973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792974 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_6792974 : Nat := 118140960795 + 6792974 * 2 ^ 59
def prefixEnd_6792974 : Nat := 4983230072969 + 3 ^ 40 * 6792974 * 2
def baseEnd_6792974 : Nat := 3488060735495010691684687

theorem tailTrace_6792974 : CollatzResearch.WordTrace tailWord_6792974 prefixEnd_6792974 3488060735495010691684687 := by
  unfold tailWord_6792974
  simp only [CollatzResearch.WordTrace]
  refine ⟨30970014511527852555030247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165173410728148546960161317 30970014511527852555030247)
  ·
    refine ⟨46455021767291778832545371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30970014511527852555030247 46455021767291778832545371)
    ·
      refine ⟨69682532650937668248818057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46455021767291778832545371 69682532650937668248818057)
      ·
        refine ⟨52261899488203251186613543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69682532650937668248818057 52261899488203251186613543)
        ·
          refine ⟨78392849232304876779920315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52261899488203251186613543 78392849232304876779920315)
          ·
            refine ⟨117589273848457315169880473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78392849232304876779920315 117589273848457315169880473)
            ·
              refine ⟨88191955386342986377410355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117589273848457315169880473 88191955386342986377410355)
              ·
                refine ⟨132287933079514479566115533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88191955386342986377410355 132287933079514479566115533)
                ·
                  refine ⟨49607974904817929837293325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132287933079514479566115533 49607974904817929837293325)
                  ·
                    refine ⟨18602990589306723688984997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49607974904817929837293325 18602990589306723688984997)
                    ·
                      refine ⟨3488060735495010691684687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18602990589306723688984997 3488060735495010691684687)
                      ·
                        rfl

theorem cell23_6792974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_6792974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792974 prefixEnd_6792974 := by exact prefixLift 6792974
  have htrace : WordTrace (prefixWord ++ tailWord_6792974) baseStart_6792974 baseEnd_6792974 := by
    simpa [prefixWord, tailWord_6792974, baseEnd_6792974] using wordTrace_append hprefix tailTrace_6792974
  have hstable : (prefixWord ++ tailWord_6792974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792974).length < 2 ^ (prefixWord ++ tailWord_6792974).sum := by decide
  have hdescent : baseEnd_6792974 < baseStart_6792974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6792991 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 4]
def baseStart_6792991 : Nat := 118140960795 + 6792991 * 2 ^ 59
def prefixEnd_6792991 : Nat := 4983230072969 + 3 ^ 40 * 6792991 * 2
def baseEnd_6792991 : Nat := 3488069464666137125172109

theorem tailTrace_6792991 : CollatzResearch.WordTrace tailWord_6792991 prefixEnd_6792991 3488069464666137125172109 := by
  unfold tailWord_6792991
  simp only [CollatzResearch.WordTrace]
  refine ⟨247760736133161232343610827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165173824088774154895740551 247760736133161232343610827)
  ·
    refine ⟨371641104199741848515416241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247760736133161232343610827 371641104199741848515416241)
    ·
      refine ⟨278730828149806386386562181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371641104199741848515416241 278730828149806386386562181)
      ·
        refine ⟨52262030278088697447480409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278730828149806386386562181 52262030278088697447480409)
        ·
          refine ⟨39196522708566523085610307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52262030278088697447480409 39196522708566523085610307)
          ·
            refine ⟨58794784062849784628415461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39196522708566523085610307 58794784062849784628415461)
            ·
              refine ⟨11024022011784334617827899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58794784062849784628415461 11024022011784334617827899)
              ·
                refine ⟨16536033017676501926741849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11024022011784334617827899 16536033017676501926741849)
                ·
                  refine ⟨12402024763257376445056387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16536033017676501926741849 12402024763257376445056387)
                  ·
                    refine ⟨18603037144886064667584581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12402024763257376445056387 18603037144886064667584581)
                    ·
                      refine ⟨3488069464666137125172109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18603037144886064667584581 3488069464666137125172109)
                      ·
                        rfl

theorem cell23_6792991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_6792991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6792991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6792991 prefixEnd_6792991 := by exact prefixLift 6792991
  have htrace : WordTrace (prefixWord ++ tailWord_6792991) baseStart_6792991 baseEnd_6792991 := by
    simpa [prefixWord, tailWord_6792991, baseEnd_6792991] using wordTrace_append hprefix tailTrace_6792991
  have hstable : (prefixWord ++ tailWord_6792991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6792991).length < 2 ^ (prefixWord ++ tailWord_6792991).sum := by decide
  have hdescent : baseEnd_6792991 < baseStart_6792991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6792991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793024 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 3]
def baseStart_6793024 : Nat := 118140960795 + 6793024 * 2 ^ 59
def prefixEnd_6793024 : Nat := 4983230072969 + 3 ^ 40 * 6793024 * 2
def baseEnd_6793024 : Nat := 3488086409527735496059457

theorem tailTrace_6793024 : CollatzResearch.WordTrace tailWord_6793024 prefixEnd_6793024 3488086409527735496059457 := by
  unfold tailWord_6793024
  simp only [CollatzResearch.WordTrace]
  refine ⟨123880969871020839489781063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165174626494694452653041417 123880969871020839489781063)
  ·
    refine ⟨185821454806531259234671595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123880969871020839489781063 185821454806531259234671595)
    ·
      refine ⟨278732182209796888852007393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185821454806531259234671595 278732182209796888852007393)
      ·
        refine ⟨209049136657347666639005545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278732182209796888852007393 209049136657347666639005545)
        ·
          refine ⟨156786852493010749979254159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209049136657347666639005545 156786852493010749979254159)
          ·
            refine ⟨235180278739516124968881239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156786852493010749979254159 235180278739516124968881239)
            ·
              refine ⟨352770418109274187453321859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235180278739516124968881239 352770418109274187453321859)
              ·
                refine ⟨529155627163911281179982789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352770418109274187453321859 529155627163911281179982789)
                ·
                  refine ⟨99216680093233365221246773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 529155627163911281179982789 99216680093233365221246773)
                  ·
                    refine ⟨9301563758740627989491885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99216680093233365221246773 9301563758740627989491885)
                    ·
                      refine ⟨3488086409527735496059457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9301563758740627989491885 3488086409527735496059457)
                      ·
                        rfl

theorem cell23_6793024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_6793024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793024 prefixEnd_6793024 := by exact prefixLift 6793024
  have htrace : WordTrace (prefixWord ++ tailWord_6793024) baseStart_6793024 baseEnd_6793024 := by
    simpa [prefixWord, tailWord_6793024, baseEnd_6793024] using wordTrace_append hprefix tailTrace_6793024
  have hstable : (prefixWord ++ tailWord_6793024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793024).length < 2 ^ (prefixWord ++ tailWord_6793024).sum := by decide
  have hdescent : baseEnd_6793024 < baseStart_6793024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793052 : List Nat := [2, 2, 4, 2, 2, 1, 2, 3, 1, 4]
def baseStart_6793052 : Nat := 118140960795 + 6793052 * 2 ^ 59
def prefixEnd_6793052 : Nat := 4983230072969 + 3 ^ 40 * 6793052 * 2
def baseEnd_6793052 : Nat := 1162700262328687128836443

theorem tailTrace_6793052 : CollatzResearch.WordTrace tailWord_6793052 prefixEnd_6793052 1162700262328687128836443 := by
  unfold tailWord_6793052
  simp only [CollatzResearch.WordTrace]
  refine ⟨123881480492970119880790705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165175307323960159841054273 123881480492970119880790705)
  ·
    refine ⟨92911110369727589910593029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123881480492970119880790705 92911110369727589910593029)
    ·
      refine ⟨17420833194323923108236193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92911110369727589910593029 17420833194323923108236193)
      ·
        refine ⟨13065624895742942331177145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17420833194323923108236193 13065624895742942331177145)
        ·
          refine ⟨9799218671807206748382859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13065624895742942331177145 9799218671807206748382859)
          ·
            refine ⟨14698828007710810122574289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9799218671807206748382859 14698828007710810122574289)
            ·
              refine ⟨11024121005783107591930717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14698828007710810122574289 11024121005783107591930717)
              ·
                refine ⟨4134045377168665346974019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11024121005783107591930717 4134045377168665346974019)
                ·
                  refine ⟨6201068065752998020461029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4134045377168665346974019 6201068065752998020461029)
                  ·
                    refine ⟨1162700262328687128836443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6201068065752998020461029 1162700262328687128836443)
                    ·
                      rfl

theorem cell23_6793052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_6793052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793052 prefixEnd_6793052 := by exact prefixLift 6793052
  have htrace : WordTrace (prefixWord ++ tailWord_6793052) baseStart_6793052 baseEnd_6793052 := by
    simpa [prefixWord, tailWord_6793052, baseEnd_6793052] using wordTrace_append hprefix tailTrace_6793052
  have hstable : (prefixWord ++ tailWord_6793052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793052).length < 2 ^ (prefixWord ++ tailWord_6793052).sum := by decide
  have hdescent : baseEnd_6793052 < baseStart_6793052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793091 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 1, 6]
def baseStart_6793091 : Nat := 118140960795 + 6793091 * 2 ^ 59
def prefixEnd_6793091 : Nat := 4983230072969 + 3 ^ 40 * 6793091 * 2
def baseEnd_6793091 : Nat := 1162706937577195577973883

theorem tailTrace_6793091 : CollatzResearch.WordTrace tailWord_6793091 prefixEnd_6793091 1162706937577195577973883 := by
  unfold tailWord_6793091
  simp only [CollatzResearch.WordTrace]
  refine ⟨247764383432798949422251127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165176255621865966281500751 247764383432798949422251127)
  ·
    refine ⟨371646575149198424133376691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247764383432798949422251127 371646575149198424133376691)
    ·
      refine ⟨557469862723797636200065037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371646575149198424133376691 557469862723797636200065037)
      ·
        refine ⟨209051198521424113575024389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 557469862723797636200065037 209051198521424113575024389)
        ·
          refine ⟨39197099722767021295317073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209051198521424113575024389 39197099722767021295317073)
          ·
            refine ⟨29397824792075265971487805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39197099722767021295317073 29397824792075265971487805)
            ·
              refine ⟨11024184297028224739307927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29397824792075265971487805 11024184297028224739307927)
              ·
                refine ⟨16536276445542337108961891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11024184297028224739307927 16536276445542337108961891)
                ·
                  refine ⟨24804414668313505663442837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16536276445542337108961891 24804414668313505663442837)
                  ·
                    refine ⟨1162706937577195577973883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24804414668313505663442837 1162706937577195577973883)
                    ·
                      rfl

theorem cell23_6793091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 6].length) (baseStart_6793091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793091 prefixEnd_6793091 := by exact prefixLift 6793091
  have htrace : WordTrace (prefixWord ++ tailWord_6793091) baseStart_6793091 baseEnd_6793091 := by
    simpa [prefixWord, tailWord_6793091, baseEnd_6793091] using wordTrace_append hprefix tailTrace_6793091
  have hstable : (prefixWord ++ tailWord_6793091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793091).length < 2 ^ (prefixWord ++ tailWord_6793091).sum := by decide
  have hdescent : baseEnd_6793091 < baseStart_6793091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793108 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_6793108 : Nat := 118140960795 + 6793108 * 2 ^ 59
def prefixEnd_6793108 : Nat := 4983230072969 + 3 ^ 40 * 6793108 * 2
def baseEnd_6793108 : Nat := 1162709847300904389136357

theorem tailTrace_6793108 : CollatzResearch.WordTrace tailWord_6793108 prefixEnd_6793108 1162709847300904389136357 := by
  unfold tailWord_6793108
  simp only [CollatzResearch.WordTrace]
  refine ⟨123882501736868680662809989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165176668982491574217079985 123882501736868680662809989)
  ·
    refine ⟨23227969075662877624276873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123882501736868680662809989 23227969075662877624276873)
    ·
      refine ⟨17420976806747158218207655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23227969075662877624276873 17420976806747158218207655)
      ·
        refine ⟨26131465210120737327311483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17420976806747158218207655 26131465210120737327311483)
        ·
          refine ⟨39197197815181105990967225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26131465210120737327311483 39197197815181105990967225)
          ·
            refine ⟨29397898361385829493225419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39197197815181105990967225 29397898361385829493225419)
            ·
              refine ⟨44096847542078744239838129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29397898361385829493225419 44096847542078744239838129)
              ·
                refine ⟨33072635656559058179878597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44096847542078744239838129 33072635656559058179878597)
                ·
                  refine ⟨6201119185604823408727237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33072635656559058179878597 6201119185604823408727237)
                  ·
                    refine ⟨1162709847300904389136357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6201119185604823408727237 1162709847300904389136357)
                    ·
                      rfl

theorem cell23_6793108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_6793108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793108 prefixEnd_6793108 := by exact prefixLift 6793108
  have htrace : WordTrace (prefixWord ++ tailWord_6793108) baseStart_6793108 baseEnd_6793108 := by
    simpa [prefixWord, tailWord_6793108, baseEnd_6793108] using wordTrace_append hprefix tailTrace_6793108
  have hstable : (prefixWord ++ tailWord_6793108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793108).length < 2 ^ (prefixWord ++ tailWord_6793108).sum := by decide
  have hdescent : baseEnd_6793108 < baseStart_6793108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793188 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 3, 4, 2]
def baseStart_6793188 : Nat := 118140960795 + 6793188 * 2 ^ 59
def prefixEnd_6793188 : Nat := 4983230072969 + 3 ^ 40 * 6793188 * 2
def baseEnd_6793188 : Nat := 3488170620355072854408703

theorem tailTrace_6793188 : CollatzResearch.WordTrace tailWord_6793188 prefixEnd_6793188 3488170620355072854408703 := by
  unfold tailWord_6793188
  simp only [CollatzResearch.WordTrace]
  refine ⟨123883960656723767494266109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165178614208965023325688145 123883960656723767494266109)
  ·
    refine ⟨46456485246271412810349791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123883960656723767494266109 46456485246271412810349791)
    ·
      refine ⟨69684727869407119215524687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46456485246271412810349791 69684727869407119215524687)
      ·
        refine ⟨104527091804110678823287031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69684727869407119215524687 104527091804110678823287031)
        ·
          refine ⟨156790637706166018234930547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104527091804110678823287031 156790637706166018234930547)
          ·
            refine ⟨235185956559249027352395821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156790637706166018234930547 235185956559249027352395821)
            ·
              refine ⟨88194733709718385257148433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235185956559249027352395821 88194733709718385257148433)
              ·
                refine ⟨66146050282288788942861325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88194733709718385257148433 66146050282288788942861325)
                ·
                  refine ⟨24804768855858295853572997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66146050282288788942861325 24804768855858295853572997)
                  ·
                    refine ⟨4650894160473430472544937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24804768855858295853572997 4650894160473430472544937)
                    ·
                      refine ⟨3488170620355072854408703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4650894160473430472544937 3488170620355072854408703)
                      ·
                        rfl

theorem cell23_6793188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_6793188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793188 prefixEnd_6793188 := by exact prefixLift 6793188
  have htrace : WordTrace (prefixWord ++ tailWord_6793188) baseStart_6793188 baseEnd_6793188 := by
    simpa [prefixWord, tailWord_6793188, baseEnd_6793188] using wordTrace_append hprefix tailTrace_6793188
  have hstable : (prefixWord ++ tailWord_6793188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793188).length < 2 ^ (prefixWord ++ tailWord_6793188).sum := by decide
  have hdescent : baseEnd_6793188 < baseStart_6793188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793198 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 2, 6]
def baseStart_6793198 : Nat := 118140960795 + 6793198 * 2 ^ 59
def prefixEnd_6793198 : Nat := 4983230072969 + 3 ^ 40 * 6793198 * 2
def baseEnd_6793198 : Nat := 1162725251720539271761219

theorem tailTrace_6793198 : CollatzResearch.WordTrace tailWord_6793198 prefixEnd_6793198 1162725251720539271761219 := by
  unfold tailWord_6793198
  simp only [CollatzResearch.WordTrace]
  refine ⟨30971035755426413337049531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165178857362274204464264165 30971035755426413337049531)
  ·
    refine ⟨46456553633139620005574297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30971035755426413337049531 46456553633139620005574297)
    ·
      refine ⟨34842415224854715004180723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46456553633139620005574297 34842415224854715004180723)
      ·
        refine ⟨52263622837282072506271085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34842415224854715004180723 52263622837282072506271085)
        ·
          refine ⟨19598858563980777189851657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52263622837282072506271085 19598858563980777189851657)
          ·
            refine ⟨14699143922985582892388743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19598858563980777189851657 14699143922985582892388743)
            ·
              refine ⟨22048715884478374338583115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14699143922985582892388743 22048715884478374338583115)
              ·
                refine ⟨33073073826717561507874673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22048715884478374338583115 33073073826717561507874673)
                ·
                  refine ⟨24804805370038171130906005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33073073826717561507874673 24804805370038171130906005)
                  ·
                    refine ⟨1162725251720539271761219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24804805370038171130906005 1162725251720539271761219)
                    ·
                      rfl

theorem cell23_6793198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_6793198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793198 prefixEnd_6793198 := by exact prefixLift 6793198
  have htrace : WordTrace (prefixWord ++ tailWord_6793198) baseStart_6793198 baseEnd_6793198 := by
    simpa [prefixWord, tailWord_6793198, baseEnd_6793198] using wordTrace_append hprefix tailTrace_6793198
  have hstable : (prefixWord ++ tailWord_6793198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793198).length < 2 ^ (prefixWord ++ tailWord_6793198).sum := by decide
  have hdescent : baseEnd_6793198 < baseStart_6793198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793226 : List Nat := [3, 1, 2, 2, 5, 1, 2, 1, 1, 3, 2]
def baseStart_6793226 : Nat := 118140960795 + 6793226 * 2 ^ 59
def prefixEnd_6793226 : Nat := 4983230072969 + 3 ^ 40 * 6793226 * 2
def baseEnd_6793226 : Nat := 3488190132619943705733529

theorem tailTrace_6793226 : CollatzResearch.WordTrace tailWord_6793226 prefixEnd_6793226 3488190132619943705733529 := by
  unfold tailWord_6793226
  simp only [CollatzResearch.WordTrace]
  refine ⟨61942326821827466869603883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165179538191539911652277021 61942326821827466869603883)
  ·
    refine ⟨92913490232741200304405825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61942326821827466869603883 92913490232741200304405825)
    ·
      refine ⟨69685117674555900228304369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92913490232741200304405825 69685117674555900228304369)
      ·
        refine ⟨52263838255916925171228277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69685117674555900228304369 52263838255916925171228277)
        ·
          refine ⟨4899734836492211734802651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52263838255916925171228277 4899734836492211734802651)
          ·
            refine ⟨7349602254738317602203977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4899734836492211734802651 7349602254738317602203977)
            ·
              refine ⟨5512201691053738201652983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7349602254738317602203977 5512201691053738201652983)
              ·
                refine ⟨8268302536580607302479475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5512201691053738201652983 8268302536580607302479475)
                ·
                  refine ⟨12402453804870910953719213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8268302536580607302479475 12402453804870910953719213)
                  ·
                    refine ⟨4650920176826591607644705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12402453804870910953719213 4650920176826591607644705)
                    ·
                      refine ⟨3488190132619943705733529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4650920176826591607644705 3488190132619943705733529)
                      ·
                        rfl

theorem cell23_6793226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_6793226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793226 prefixEnd_6793226 := by exact prefixLift 6793226
  have htrace : WordTrace (prefixWord ++ tailWord_6793226) baseStart_6793226 baseEnd_6793226 := by
    simpa [prefixWord, tailWord_6793226, baseEnd_6793226] using wordTrace_append hprefix tailTrace_6793226
  have hstable : (prefixWord ++ tailWord_6793226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793226).length < 2 ^ (prefixWord ++ tailWord_6793226).sum := by decide
  have hdescent : baseEnd_6793226 < baseStart_6793226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793241 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 4, 5]
def baseStart_6793241 : Nat := 118140960795 + 6793241 * 2 ^ 59
def prefixEnd_6793241 : Nat := 4983230072969 + 3 ^ 40 * 6793241 * 2
def baseEnd_6793241 : Nat := 1162732611609920382348653

theorem tailTrace_6793241 : CollatzResearch.WordTrace tailWord_6793241 prefixEnd_6793241 1162732611609920382348653 := by
  unfold tailWord_6793241
  simp only [CollatzResearch.WordTrace]
  refine ⟨247769854382255525040211577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165179902921503683360141051 247769854382255525040211577)
  ·
    refine ⟨185827390786691643780158683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247769854382255525040211577 185827390786691643780158683)
    ·
      refine ⟨278741086180037465670238025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185827390786691643780158683 278741086180037465670238025)
      ·
        refine ⟨209055814635028099252678519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278741086180037465670238025 209055814635028099252678519)
        ·
          refine ⟨313583721952542148879017779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209055814635028099252678519 313583721952542148879017779)
          ·
            refine ⟨470375582928813223318526669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313583721952542148879017779 470375582928813223318526669)
            ·
              refine ⟨176390843598304958744447501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 470375582928813223318526669 176390843598304958744447501)
              ·
                refine ⟨66146566349364359529167813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176390843598304958744447501 66146566349364359529167813)
                ·
                  refine ⟨12402481190505817411718965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66146566349364359529167813 12402481190505817411718965)
                  ·
                    refine ⟨1162732611609920382348653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12402481190505817411718965 1162732611609920382348653)
                    ·
                      rfl

theorem cell23_6793241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 5].length) (baseStart_6793241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793241 prefixEnd_6793241 := by exact prefixLift 6793241
  have htrace : WordTrace (prefixWord ++ tailWord_6793241) baseStart_6793241 baseEnd_6793241 := by
    simpa [prefixWord, tailWord_6793241, baseEnd_6793241] using wordTrace_append hprefix tailTrace_6793241
  have hstable : (prefixWord ++ tailWord_6793241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793241).length < 2 ^ (prefixWord ++ tailWord_6793241).sum := by decide
  have hdescent : baseEnd_6793241 < baseStart_6793241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793245 : List Nat := [1, 4, 2, 2, 2, 1, 2, 4, 5]
def baseStart_6793245 : Nat := 118140960795 + 6793245 * 2 ^ 59
def prefixEnd_6793245 : Nat := 4983230072969 + 3 ^ 40 * 6793245 * 2
def baseEnd_6793245 : Nat := 387577765416931014599549

theorem tailTrace_6793245 : CollatzResearch.WordTrace tailWord_6793245 prefixEnd_6793245 387577765416931014599549 := by
  unfold tailWord_6793245
  simp only [CollatzResearch.WordTrace]
  refine ⟨247770000274241033723357189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165180000182827355815571459 247770000274241033723357189)
  ·
    refine ⟨46456875051420193823129473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247770000274241033723357189 46456875051420193823129473)
    ·
      refine ⟨34842656288565145367347105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46456875051420193823129473 34842656288565145367347105)
      ·
        refine ⟨26131992216423859025510329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34842656288565145367347105 26131992216423859025510329)
        ·
          refine ⟨19598994162317894269132747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26131992216423859025510329 19598994162317894269132747)
          ·
            refine ⟨29398491243476841403699121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19598994162317894269132747 29398491243476841403699121)
            ·
              refine ⟨22048868432607631052774341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29398491243476841403699121 22048868432607631052774341)
              ·
                refine ⟨4134162831113930822395189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22048868432607631052774341 4134162831113930822395189)
                ·
                  refine ⟨387577765416931014599549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4134162831113930822395189 387577765416931014599549)
                  ·
                    rfl

theorem cell23_6793245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_6793245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793245 prefixEnd_6793245 := by exact prefixLift 6793245
  have htrace : WordTrace (prefixWord ++ tailWord_6793245) baseStart_6793245 baseEnd_6793245 := by
    simpa [prefixWord, tailWord_6793245, baseEnd_6793245] using wordTrace_append hprefix tailTrace_6793245
  have hstable : (prefixWord ++ tailWord_6793245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793245).length < 2 ^ (prefixWord ++ tailWord_6793245).sum := by decide
  have hdescent : baseEnd_6793245 < baseStart_6793245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793251 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 7]
def baseStart_6793251 : Nat := 118140960795 + 6793251 * 2 ^ 59
def prefixEnd_6793251 : Nat := 4983230072969 + 3 ^ 40 * 6793251 * 2
def baseEnd_6793251 : Nat := 3488202969636306107920913

theorem tailTrace_6793251 : CollatzResearch.WordTrace tailWord_6793251 prefixEnd_6793251 3488202969636306107920913 := by
  unfold tailWord_6793251
  simp only [CollatzResearch.WordTrace]
  refine ⟨247770219112219296748075607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165180146074812864498717071 247770219112219296748075607)
  ·
    refine ⟨371655328668328945122113411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247770219112219296748075607 371655328668328945122113411)
    ·
      refine ⟨557482993002493417683170117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371655328668328945122113411 557482993002493417683170117)
      ·
        refine ⟨104528061187967515815594397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 557482993002493417683170117 104528061187967515815594397)
        ·
          refine ⟨39198022945487818430847899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104528061187967515815594397 39198022945487818430847899)
          ·
            refine ⟨58797034418231727646271849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39198022945487818430847899 58797034418231727646271849)
            ·
              refine ⟨44097775813673795734703887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58797034418231727646271849 44097775813673795734703887)
              ·
                refine ⟨66146663720510693602055831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44097775813673795734703887 66146663720510693602055831)
                ·
                  refine ⟨99219995580766040403083747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66146663720510693602055831 99219995580766040403083747)
                  ·
                    refine ⟨148829993371149060604625621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99219995580766040403083747 148829993371149060604625621)
                    ·
                      refine ⟨3488202969636306107920913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148829993371149060604625621 3488202969636306107920913)
                      ·
                        rfl

theorem cell23_6793251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_6793251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793251 prefixEnd_6793251 := by exact prefixLift 6793251
  have htrace : WordTrace (prefixWord ++ tailWord_6793251) baseStart_6793251 baseEnd_6793251 := by
    simpa [prefixWord, tailWord_6793251, baseEnd_6793251] using wordTrace_append hprefix tailTrace_6793251
  have hstable : (prefixWord ++ tailWord_6793251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793251).length < 2 ^ (prefixWord ++ tailWord_6793251).sum := by decide
  have hdescent : baseEnd_6793251 < baseStart_6793251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793256 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_6793256 : Nat := 118140960795 + 6793256 * 2 ^ 59
def prefixEnd_6793256 : Nat := 4983230072969 + 3 ^ 40 * 6793256 * 2
def baseEnd_6793256 : Nat := 3488205537039578588358391

theorem tailTrace_6793256 : CollatzResearch.WordTrace tailWord_6793256 prefixEnd_6793256 3488205537039578588358391 := by
  unfold tailWord_6793256
  simp only [CollatzResearch.WordTrace]
  refine ⟨123885200738600591301003811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165180267651467455068005081 123885200738600591301003811)
  ·
    refine ⟨185827801107900886951505717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123885200738600591301003811 185827801107900886951505717)
    ·
      refine ⟨17421356353865708151703661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185827801107900886951505717 17421356353865708151703661)
      ·
        refine ⟨6533008632699640556888873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17421356353865708151703661 6533008632699640556888873)
        ·
          refine ⟨4899756474524730417666655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6533008632699640556888873 4899756474524730417666655)
          ·
            refine ⟨7349634711787095626499983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4899756474524730417666655 7349634711787095626499983)
            ·
              refine ⟨11024452067680643439749975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7349634711787095626499983 11024452067680643439749975)
              ·
                refine ⟨16536678101520965159624963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11024452067680643439749975 16536678101520965159624963)
                ·
                  refine ⟨24805017152281447739437445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16536678101520965159624963 24805017152281447739437445)
                  ·
                    refine ⟨4650940716052771451144521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24805017152281447739437445 4650940716052771451144521)
                    ·
                      refine ⟨3488205537039578588358391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4650940716052771451144521 3488205537039578588358391)
                      ·
                        rfl

theorem cell23_6793256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_6793256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793256 prefixEnd_6793256 := by exact prefixLift 6793256
  have htrace : WordTrace (prefixWord ++ tailWord_6793256) baseStart_6793256 baseEnd_6793256 := by
    simpa [prefixWord, tailWord_6793256, baseEnd_6793256] using wordTrace_append hprefix tailTrace_6793256
  have hstable : (prefixWord ++ tailWord_6793256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793256).length < 2 ^ (prefixWord ++ tailWord_6793256).sum := by decide
  have hdescent : baseEnd_6793256 < baseStart_6793256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793258 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 1, 7]
def baseStart_6793258 : Nat := 118140960795 + 6793258 * 2 ^ 59
def prefixEnd_6793258 : Nat := 4983230072969 + 3 ^ 40 * 6793258 * 2
def baseEnd_6793258 : Nat := 1162735521333629193511127

theorem tailTrace_6793258 : CollatzResearch.WordTrace tailWord_6793258 prefixEnd_6793258 1162735521333629193511127 := by
  unfold tailWord_6793258
  simp only [CollatzResearch.WordTrace]
  refine ⟨61942618605798484235895107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165180316282129291295720285 61942618605798484235895107)
  ·
    refine ⟨92913927908697726353842661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61942618605798484235895107 92913927908697726353842661)
    ·
      refine ⟨17421361482880823691345499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92913927908697726353842661 17421361482880823691345499)
      ·
        refine ⟨26132042224321235537018249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17421361482880823691345499 26132042224321235537018249)
        ·
          refine ⟨19599031668240926652763687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26132042224321235537018249 19599031668240926652763687)
          ·
            refine ⟨29398547502361389979145531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19599031668240926652763687 29398547502361389979145531)
            ·
              refine ⟨44097821253542084968718297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29398547502361389979145531 44097821253542084968718297)
              ·
                refine ⟨33073365940156563726538723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44097821253542084968718297 33073365940156563726538723)
                ·
                  refine ⟨49610048910234845589808085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33073365940156563726538723 49610048910234845589808085)
                  ·
                    refine ⟨1162735521333629193511127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49610048910234845589808085 1162735521333629193511127)
                    ·
                      rfl

theorem cell23_6793258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_6793258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793258 prefixEnd_6793258 := by exact prefixLift 6793258
  have htrace : WordTrace (prefixWord ++ tailWord_6793258) baseStart_6793258 baseEnd_6793258 := by
    simpa [prefixWord, tailWord_6793258, baseEnd_6793258] using wordTrace_append hprefix tailTrace_6793258
  have hstable : (prefixWord ++ tailWord_6793258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793258).length < 2 ^ (prefixWord ++ tailWord_6793258).sum := by decide
  have hdescent : baseEnd_6793258 < baseStart_6793258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793291 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 4]
def baseStart_6793291 : Nat := 118140960795 + 6793291 * 2 ^ 59
def prefixEnd_6793291 : Nat := 4983230072969 + 3 ^ 40 * 6793291 * 2
def baseEnd_6793291 : Nat := 3488223508862485951420729

theorem tailTrace_6793291 : CollatzResearch.WordTrace tailWord_6793291 prefixEnd_6793291 3488223508862485951420729 := by
  unfold tailWord_6793291
  simp only [CollatzResearch.WordTrace]
  refine ⟨247771678032074383579531727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165181118688049589053021151 247771678032074383579531727)
  ·
    refine ⟨371657517048111575369297591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247771678032074383579531727 371657517048111575369297591)
    ·
      refine ⟨557486275572167363053946387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371657517048111575369297591 557486275572167363053946387)
      ·
        refine ⟨836229413358251044580919581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557486275572167363053946387 836229413358251044580919581)
        ·
          refine ⟨313586030009344141717844843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 836229413358251044580919581 313586030009344141717844843)
          ·
            refine ⟨470379045014016212576767265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313586030009344141717844843 470379045014016212576767265)
            ·
              refine ⟨352784283760512159432575449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470379045014016212576767265 352784283760512159432575449)
              ·
                refine ⟨264588212820384119574431587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352784283760512159432575449 264588212820384119574431587)
                ·
                  refine ⟨396882319230576179361647381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264588212820384119574431587 396882319230576179361647381)
                  ·
                    refine ⟨18603858713933258407577221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 396882319230576179361647381 18603858713933258407577221)
                    ·
                      refine ⟨3488223508862485951420729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18603858713933258407577221 3488223508862485951420729)
                      ·
                        rfl

theorem cell23_6793291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 4].length) (baseStart_6793291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793291 prefixEnd_6793291 := by exact prefixLift 6793291
  have htrace : WordTrace (prefixWord ++ tailWord_6793291) baseStart_6793291 baseEnd_6793291 := by
    simpa [prefixWord, tailWord_6793291, baseEnd_6793291] using wordTrace_append hprefix tailTrace_6793291
  have hstable : (prefixWord ++ tailWord_6793291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793291).length < 2 ^ (prefixWord ++ tailWord_6793291).sum := by decide
  have hdescent : baseEnd_6793291 < baseStart_6793291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793302 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_6793302 : Nat := 118140960795 + 6793302 * 2 ^ 59
def prefixEnd_6793302 : Nat := 4983230072969 + 3 ^ 40 * 6793302 * 2
def baseEnd_6793302 : Nat := 3488229157149685408383179

theorem tailTrace_6793302 : CollatzResearch.WordTrace tailWord_6793302 prefixEnd_6793302 3488229157149685408383179 := by
  unfold tailWord_6793302
  simp only [CollatzResearch.WordTrace]
  refine ⟨15485754952189658278636385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165181386156689688305454773 15485754952189658278636385)
  ·
    refine ⟨11614316214142243708977289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15485754952189658278636385 11614316214142243708977289)
    ·
      refine ⟨8710737160606682781732967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11614316214142243708977289 8710737160606682781732967)
      ·
        refine ⟨13066105740910024172599451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8710737160606682781732967 13066105740910024172599451)
        ·
          refine ⟨19599158611365036258899177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13066105740910024172599451 19599158611365036258899177)
          ·
            refine ⟨14699368958523777194174383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19599158611365036258899177 14699368958523777194174383)
            ·
              refine ⟨22049053437785665791261575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14699368958523777194174383 22049053437785665791261575)
              ·
                refine ⟨33073580156678498686892363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22049053437785665791261575 33073580156678498686892363)
                ·
                  refine ⟨49610370235017748030338545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33073580156678498686892363 49610370235017748030338545)
                  ·
                    refine ⟨37207777676263311022753909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49610370235017748030338545 37207777676263311022753909)
                    ·
                      refine ⟨3488229157149685408383179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37207777676263311022753909 3488229157149685408383179)
                      ·
                        rfl

theorem cell23_6793302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_6793302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793302 prefixEnd_6793302 := by exact prefixLift 6793302
  have htrace : WordTrace (prefixWord ++ tailWord_6793302) baseStart_6793302 baseEnd_6793302 := by
    simpa [prefixWord, tailWord_6793302, baseEnd_6793302] using wordTrace_append hprefix tailTrace_6793302
  have hstable : (prefixWord ++ tailWord_6793302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793302).length < 2 ^ (prefixWord ++ tailWord_6793302).sum := by decide
  have hdescent : baseEnd_6793302 < baseStart_6793302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793362 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_6793362 : Nat := 118140960795 + 6793362 * 2 ^ 59
def prefixEnd_6793362 : Nat := 4983230072969 + 3 ^ 40 * 6793362 * 2
def baseEnd_6793362 : Nat := 3488259965988955173632903

theorem tailTrace_6793362 : CollatzResearch.WordTrace tailWord_6793362 prefixEnd_6793362 3488259965988955173632903 := by
  unfold tailWord_6793362
  simp only [CollatzResearch.WordTrace]
  refine ⟨61943566903704290676341585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165182845076544775136910893 61943566903704290676341585)
  ·
    refine ⟨46457675177778218007256189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61943566903704290676341585 46457675177778218007256189)
    ·
      refine ⟨17421628191666831752721071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46457675177778218007256189 17421628191666831752721071)
      ·
        refine ⟨26132442287500247629081607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17421628191666831752721071 26132442287500247629081607)
        ·
          refine ⟨39198663431250371443622411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26132442287500247629081607 39198663431250371443622411)
          ·
            refine ⟨58797995146875557165433617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39198663431250371443622411 58797995146875557165433617)
            ·
              refine ⟨44098496360156667874075213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58797995146875557165433617 44098496360156667874075213)
              ·
                refine ⟨16536936135058750452778205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44098496360156667874075213 16536936135058750452778205)
                ·
                  refine ⟨6201351050647031419791827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16536936135058750452778205 6201351050647031419791827)
                  ·
                    refine ⟨9302026575970547129687741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6201351050647031419791827 9302026575970547129687741)
                    ·
                      refine ⟨3488259965988955173632903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9302026575970547129687741 3488259965988955173632903)
                      ·
                        rfl

theorem cell23_6793362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_6793362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793362 prefixEnd_6793362 := by exact prefixLift 6793362
  have htrace : WordTrace (prefixWord ++ tailWord_6793362) baseStart_6793362 baseEnd_6793362 := by
    simpa [prefixWord, tailWord_6793362, baseEnd_6793362] using wordTrace_append hprefix tailTrace_6793362
  have hstable : (prefixWord ++ tailWord_6793362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793362).length < 2 ^ (prefixWord ++ tailWord_6793362).sum := by decide
  have hdescent : baseEnd_6793362 < baseStart_6793362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793389 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_6793389 : Nat := 118140960795 + 6793389 * 2 ^ 59
def prefixEnd_6793389 : Nat := 4983230072969 + 3 ^ 40 * 6793389 * 2
def baseEnd_6793389 : Nat := 3488273829966626567995279

theorem tailTrace_6793389 : CollatzResearch.WordTrace tailWord_6793389 prefixEnd_6793389 3488273829966626567995279 := by
  unfold tailWord_6793389
  simp only [CollatzResearch.WordTrace]
  refine ⟨247775252385719346316599221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165183501590479564211066147 247775252385719346316599221)
  ·
    refine ⟨23228929911161188717181177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247775252385719346316599221 23228929911161188717181177)
    ·
      refine ⟨17421697433370891537885883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23228929911161188717181177 17421697433370891537885883)
      ·
        refine ⟨26132546150056337306828825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17421697433370891537885883 26132546150056337306828825)
        ·
          refine ⟨19599409612542252980121619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26132546150056337306828825 19599409612542252980121619)
          ·
            refine ⟨29399114418813379470182429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19599409612542252980121619 29399114418813379470182429)
            ·
              refine ⟨11024667907055017301318411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29399114418813379470182429 11024667907055017301318411)
              ·
                refine ⟨16537001860582525951977617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11024667907055017301318411 16537001860582525951977617)
                ·
                  refine ⟨12402751395436894463983213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16537001860582525951977617 12402751395436894463983213)
                  ·
                    refine ⟨4651031773288835423993705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12402751395436894463983213 4651031773288835423993705)
                    ·
                      refine ⟨3488273829966626567995279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4651031773288835423993705 3488273829966626567995279)
                      ·
                        rfl

theorem cell23_6793389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_6793389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793389 prefixEnd_6793389 := by exact prefixLift 6793389
  have htrace : WordTrace (prefixWord ++ tailWord_6793389) baseStart_6793389 baseEnd_6793389 := by
    simpa [prefixWord, tailWord_6793389, baseEnd_6793389] using wordTrace_append hprefix tailTrace_6793389
  have hstable : (prefixWord ++ tailWord_6793389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793389).length < 2 ^ (prefixWord ++ tailWord_6793389).sum := by decide
  have hdescent : baseEnd_6793389 < baseStart_6793389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793402 : List Nat := [3, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4]
def baseStart_6793402 : Nat := 118140960795 + 6793402 * 2 ^ 59
def prefixEnd_6793402 : Nat := 4983230072969 + 3 ^ 40 * 6793402 * 2
def baseEnd_6793402 : Nat := 3488280505215135017132719

theorem tailTrace_6793402 : CollatzResearch.WordTrace tailWord_6793402 prefixEnd_6793402 3488280505215135017132719 := by
  unfold tailWord_6793402
  simp only [CollatzResearch.WordTrace]
  refine ⟨61943931633668062384205615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165183817689781499691214973 61943931633668062384205615)
  ·
    refine ⟨92915897450502093576308423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61943931633668062384205615 92915897450502093576308423)
    ·
      refine ⟨139373846175753140364462635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92915897450502093576308423 139373846175753140364462635)
      ·
        refine ⟨209060769263629710546693953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139373846175753140364462635 209060769263629710546693953)
        ·
          refine ⟨156795576947722282910020465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209060769263629710546693953 156795576947722282910020465)
          ·
            refine ⟨117596682710791712182515349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156795576947722282910020465 117596682710791712182515349)
            ·
              refine ⟨5512344502068361508555407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117596682710791712182515349 5512344502068361508555407)
              ·
                refine ⟨8268516753102542262833111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5512344502068361508555407 8268516753102542262833111)
                ·
                  refine ⟨12402775129653813394249667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8268516753102542262833111 12402775129653813394249667)
                  ·
                    refine ⟨18604162694480720091374501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12402775129653813394249667 18604162694480720091374501)
                    ·
                      refine ⟨3488280505215135017132719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18604162694480720091374501 3488280505215135017132719)
                      ·
                        rfl

theorem cell23_6793402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4].length) (baseStart_6793402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793402 prefixEnd_6793402 := by exact prefixLift 6793402
  have htrace : WordTrace (prefixWord ++ tailWord_6793402) baseStart_6793402 baseEnd_6793402 := by
    simpa [prefixWord, tailWord_6793402, baseEnd_6793402] using wordTrace_append hprefix tailTrace_6793402
  have hstable : (prefixWord ++ tailWord_6793402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793402).length < 2 ^ (prefixWord ++ tailWord_6793402).sum := by decide
  have hdescent : baseEnd_6793402 < baseStart_6793402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793408 : List Nat := [2, 1, 1, 2, 5, 2, 10]
def baseStart_6793408 : Nat := 118140960795 + 6793408 * 2 ^ 59
def prefixEnd_6793408 : Nat := 4983230072969 + 3 ^ 40 * 6793408 * 2
def baseEnd_6793408 : Nat := 43065229458013111032811

theorem tailTrace_6793408 : CollatzResearch.WordTrace tailWord_6793408 prefixEnd_6793408 43065229458013111032811 := by
  unfold tailWord_6793408
  simp only [CollatzResearch.WordTrace]
  refine ⟨123887972686325256280770439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165183963581767008374360585 123887972686325256280770439)
  ·
    refine ⟨185831959029487884421155659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123887972686325256280770439 185831959029487884421155659)
    ·
      refine ⟨278747938544231826631733489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185831959029487884421155659 278747938544231826631733489)
      ·
        refine ⟨209060953908173869973800117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278747938544231826631733489 209060953908173869973800117)
        ·
          refine ⟨19599464428891300310043761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 209060953908173869973800117 19599464428891300310043761)
          ·
            refine ⟨14699598321668475232532821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19599464428891300310043761 14699598321668475232532821)
            ·
              refine ⟨43065229458013111032811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14699598321668475232532821 43065229458013111032811)
              ·
                rfl

theorem cell23_6793408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 10].length) (baseStart_6793408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793408 prefixEnd_6793408 := by exact prefixLift 6793408
  have htrace : WordTrace (prefixWord ++ tailWord_6793408) baseStart_6793408 baseEnd_6793408 := by
    simpa [prefixWord, tailWord_6793408, baseEnd_6793408] using wordTrace_append hprefix tailTrace_6793408
  have hstable : (prefixWord ++ tailWord_6793408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793408).length < 2 ^ (prefixWord ++ tailWord_6793408).sum := by decide
  have hdescent : baseEnd_6793408 < baseStart_6793408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793412 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 4, 4]
def baseStart_6793412 : Nat := 118140960795 + 6793412 * 2 ^ 59
def prefixEnd_6793412 : Nat := 4983230072969 + 3 ^ 40 * 6793412 * 2
def baseEnd_6793412 : Nat := 1162761880007226659335891

theorem tailTrace_6793412 : CollatzResearch.WordTrace tailWord_6793412 prefixEnd_6793412 1162761880007226659335891 := by
  unfold tailWord_6793412
  simp only [CollatzResearch.WordTrace]
  refine ⟨123888045632318010622343245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165184060843090680829790993 123888045632318010622343245)
  ·
    refine ⟨46458017112119253983378717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123888045632318010622343245 46458017112119253983378717)
    ·
      refine ⟨17421756417044720243767019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46458017112119253983378717 17421756417044720243767019)
      ·
        refine ⟨26132634625567080365650529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17421756417044720243767019 26132634625567080365650529)
        ·
          refine ⟨19599475969175310274237897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26132634625567080365650529 19599475969175310274237897)
          ·
            refine ⟨14699606976881482705678423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19599475969175310274237897 14699606976881482705678423)
            ·
              refine ⟨22049410465322224058517635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14699606976881482705678423 22049410465322224058517635)
              ·
                refine ⟨33074115697983336087776453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22049410465322224058517635 33074115697983336087776453)
                ·
                  refine ⟨6201396693371875516458085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33074115697983336087776453 6201396693371875516458085)
                  ·
                    refine ⟨1162761880007226659335891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6201396693371875516458085 1162761880007226659335891)
                    ·
                      rfl

theorem cell23_6793412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_6793412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793412 prefixEnd_6793412 := by exact prefixLift 6793412
  have htrace : WordTrace (prefixWord ++ tailWord_6793412) baseStart_6793412 baseEnd_6793412 := by
    simpa [prefixWord, tailWord_6793412, baseEnd_6793412] using wordTrace_append hprefix tailTrace_6793412
  have hstable : (prefixWord ++ tailWord_6793412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793412).length < 2 ^ (prefixWord ++ tailWord_6793412).sum := by decide
  have hdescent : baseEnd_6793412 < baseStart_6793412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793419 : List Nat := [1, 1, 1, 1, 3, 2, 3, 6, 1, 2, 2]
def baseStart_6793419 : Nat := 118140960795 + 6793419 * 2 ^ 59
def prefixEnd_6793419 : Nat := 4983230072969 + 3 ^ 40 * 6793419 * 2
def baseEnd_6793419 : Nat := 3488289234386261450620141

theorem tailTrace_6793419 : CollatzResearch.WordTrace tailWord_6793419 prefixEnd_6793419 3488289234386261450620141 := by
  unfold tailWord_6793419
  simp only [CollatzResearch.WordTrace]
  refine ⟨247776346575610661440191311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165184231050407107626794207 247776346575610661440191311)
  ·
    refine ⟨371664519863415992160286967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247776346575610661440191311 371664519863415992160286967)
    ·
      refine ⟨557496779795123988240430451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371664519863415992160286967 557496779795123988240430451)
      ·
        refine ⟨836245169692685982360645677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557496779795123988240430451 836245169692685982360645677)
        ·
          refine ⟨313591938634757243385242129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 836245169692685982360645677 313591938634757243385242129)
          ·
            refine ⟨235193953976067932538931597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313591938634757243385242129 235193953976067932538931597)
            ·
              refine ⟨88197732741025474702099349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235193953976067932538931597 88197732741025474702099349)
              ·
                refine ⟨4134268722235569126660907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88197732741025474702099349 4134268722235569126660907)
                ·
                  refine ⟨6201403083353353689991361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4134268722235569126660907 6201403083353353689991361)
                  ·
                    refine ⟨4651052312515015267493521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6201403083353353689991361 4651052312515015267493521)
                    ·
                      refine ⟨3488289234386261450620141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4651052312515015267493521 3488289234386261450620141)
                      ·
                        rfl

theorem cell23_6793419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 1, 2, 2].length) (baseStart_6793419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793419 prefixEnd_6793419 := by exact prefixLift 6793419
  have htrace : WordTrace (prefixWord ++ tailWord_6793419) baseStart_6793419 baseEnd_6793419 := by
    simpa [prefixWord, tailWord_6793419, baseEnd_6793419] using wordTrace_append hprefix tailTrace_6793419
  have hstable : (prefixWord ++ tailWord_6793419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793419).length < 2 ^ (prefixWord ++ tailWord_6793419).sum := by decide
  have hdescent : baseEnd_6793419 < baseStart_6793419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793429 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 1, 6]
def baseStart_6793429 : Nat := 118140960795 + 6793429 * 2 ^ 59
def prefixEnd_6793429 : Nat := 4983230072969 + 3 ^ 40 * 6793429 * 2
def baseEnd_6793429 : Nat := 1162764789730935470498365

theorem tailTrace_6793429 : CollatzResearch.WordTrace tailWord_6793429 prefixEnd_6793429 1162764789730935470498365 := by
  unfold tailWord_6793429
  simp only [CollatzResearch.WordTrace]
  refine ⟨247776711305574433148055341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165184474203716288765370227 247776711305574433148055341)
  ·
    refine ⟨92916266739590412430520753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247776711305574433148055341 92916266739590412430520753)
    ·
      refine ⟨69687200054692809322890565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92916266739590412430520753 69687200054692809322890565)
      ·
        refine ⟨13066350010254901748041981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69687200054692809322890565 13066350010254901748041981)
        ·
          refine ⟨4899881253845588155515743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13066350010254901748041981 4899881253845588155515743)
          ·
            refine ⟨7349821880768382233273615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4899881253845588155515743 7349821880768382233273615)
            ·
              refine ⟨11024732821152573349910423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7349821880768382233273615 11024732821152573349910423)
              ·
                refine ⟨16537099231728860024865635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11024732821152573349910423 16537099231728860024865635)
                ·
                  refine ⟨24805648847593290037298453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16537099231728860024865635 24805648847593290037298453)
                  ·
                    refine ⟨1162764789730935470498365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24805648847593290037298453 1162764789730935470498365)
                    ·
                      rfl

theorem cell23_6793429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_6793429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793429 prefixEnd_6793429 := by exact prefixLift 6793429
  have htrace : WordTrace (prefixWord ++ tailWord_6793429) baseStart_6793429 baseEnd_6793429 := by
    simpa [prefixWord, tailWord_6793429, baseEnd_6793429] using wordTrace_append hprefix tailTrace_6793429
  have hstable : (prefixWord ++ tailWord_6793429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793429).length < 2 ^ (prefixWord ++ tailWord_6793429).sum := by decide
  have hdescent : baseEnd_6793429 < baseStart_6793429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793432 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 1, 2, 4]
def baseStart_6793432 : Nat := 118140960795 + 6793432 * 2 ^ 59
def prefixEnd_6793432 : Nat := 4983230072969 + 3 ^ 40 * 6793432 * 2
def baseEnd_6793432 : Nat := 3488295909634769899757581

theorem tailTrace_6793432 : CollatzResearch.WordTrace tailWord_6793432 prefixEnd_6793432 3488295909634769899757581 := by
  unfold tailWord_6793432
  simp only [CollatzResearch.WordTrace]
  refine ⟨123888410362281782330207275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165184547149709043106943033 123888410362281782330207275)
  ·
    refine ⟨185832615543422673495310913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123888410362281782330207275 185832615543422673495310913)
    ·
      refine ⟨139374461657567005121483185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185832615543422673495310913 139374461657567005121483185)
      ·
        refine ⟨104530846243175253841112389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139374461657567005121483185 104530846243175253841112389)
        ·
          refine ⟨19599533670595360095208573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104530846243175253841112389 19599533670595360095208573)
          ·
            refine ⟨7349825126473260035703215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19599533670595360095208573 7349825126473260035703215)
            ·
              refine ⟨11024737689709890053554823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7349825126473260035703215 11024737689709890053554823)
              ·
                refine ⟨16537106534564835080332235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11024737689709890053554823 16537106534564835080332235)
                ·
                  refine ⟨24805659801847252620498353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16537106534564835080332235 24805659801847252620498353)
                  ·
                    refine ⟨18604244851385439465373765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24805659801847252620498353 18604244851385439465373765)
                    ·
                      refine ⟨3488295909634769899757581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18604244851385439465373765 3488295909634769899757581)
                      ·
                        rfl

theorem cell23_6793432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_6793432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793432 prefixEnd_6793432 := by exact prefixLift 6793432
  have htrace : WordTrace (prefixWord ++ tailWord_6793432) baseStart_6793432 baseEnd_6793432 := by
    simpa [prefixWord, tailWord_6793432, baseEnd_6793432] using wordTrace_append hprefix tailTrace_6793432
  have hstable : (prefixWord ++ tailWord_6793432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793432).length < 2 ^ (prefixWord ++ tailWord_6793432).sum := by decide
  have hdescent : baseEnd_6793432 < baseStart_6793432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793435 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 6, 1, 3]
def baseStart_6793435 : Nat := 118140960795 + 6793435 * 2 ^ 59
def prefixEnd_6793435 : Nat := 4983230072969 + 3 ^ 40 * 6793435 * 2
def baseEnd_6793435 : Nat := 3488297450076733388020067

theorem tailTrace_6793435 : CollatzResearch.WordTrace tailWord_6793435 prefixEnd_6793435 3488297450076733388020067 := by
  unfold tailWord_6793435
  simp only [CollatzResearch.WordTrace]
  refine ⟨247776930143552696172773759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165184620095701797448515839 247776930143552696172773759)
  ·
    refine ⟨371665395215329044259160639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247776930143552696172773759 371665395215329044259160639)
    ·
      refine ⟨557498092822993566388740959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371665395215329044259160639 557498092822993566388740959)
      ·
        refine ⟨836247139234490349583111439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557498092822993566388740959 836247139234490349583111439)
        ·
          refine ⟨1254370708851735524374667159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836247139234490349583111439 1254370708851735524374667159)
          ·
            refine ⟨1881556063277603286562000739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254370708851735524374667159 1881556063277603286562000739)
            ·
              refine ⟨2822334094916404929843001109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881556063277603286562000739 2822334094916404929843001109)
              ·
                refine ⟨132296910699206481086390677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2822334094916404929843001109 132296910699206481086390677)
                ·
                  refine ⟨6201417689025303800924563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132296910699206481086390677 6201417689025303800924563)
                  ·
                    refine ⟨9302126533537955701386845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6201417689025303800924563 9302126533537955701386845)
                    ·
                      refine ⟨3488297450076733388020067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9302126533537955701386845 3488297450076733388020067)
                      ·
                        rfl

theorem cell23_6793435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 1, 3].length) (baseStart_6793435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793435 prefixEnd_6793435 := by exact prefixLift 6793435
  have htrace : WordTrace (prefixWord ++ tailWord_6793435) baseStart_6793435 baseEnd_6793435 := by
    simpa [prefixWord, tailWord_6793435, baseEnd_6793435] using wordTrace_append hprefix tailTrace_6793435
  have hstable : (prefixWord ++ tailWord_6793435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793435).length < 2 ^ (prefixWord ++ tailWord_6793435).sum := by decide
  have hdescent : baseEnd_6793435 < baseStart_6793435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793436 : List Nat := [2, 2, 5, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_6793436 : Nat := 118140960795 + 6793436 * 2 ^ 59
def prefixEnd_6793436 : Nat := 4983230072969 + 3 ^ 40 * 6793436 * 2
def baseEnd_6793436 : Nat := 3488297963557387884107563

theorem tailTrace_6793436 : CollatzResearch.WordTrace tailWord_6793436 prefixEnd_6793436 3488297963557387884107563 := by
  unfold tailWord_6793436
  simp only [CollatzResearch.WordTrace]
  refine ⟨123888483308274536671780081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165184644411032715562373441 123888483308274536671780081)
  ·
    refine ⟨92916362481205902503835061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123888483308274536671780081 92916362481205902503835061)
    ·
      refine ⟨8710908982613053359734537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92916362481205902503835061 8710908982613053359734537)
      ·
        refine ⟨6533181736959790019800903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8710908982613053359734537 6533181736959790019800903)
        ·
          refine ⟨9799772605439685029701355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6533181736959790019800903 9799772605439685029701355)
          ·
            refine ⟨14699658908159527544552033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9799772605439685029701355 14699658908159527544552033)
            ·
              refine ⟨11024744181119645658414025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14699658908159527544552033 11024744181119645658414025)
              ·
                refine ⟨8268558135839734243810519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11024744181119645658414025 8268558135839734243810519)
                ·
                  refine ⟨12402837203759601365715779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8268558135839734243810519 12402837203759601365715779)
                  ·
                    refine ⟨18604255805639402048573669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12402837203759601365715779 18604255805639402048573669)
                    ·
                      refine ⟨3488297963557387884107563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18604255805639402048573669 3488297963557387884107563)
                      ·
                        rfl

theorem cell23_6793436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_6793436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793436 prefixEnd_6793436 := by exact prefixLift 6793436
  have htrace : WordTrace (prefixWord ++ tailWord_6793436) baseStart_6793436 baseEnd_6793436 := by
    simpa [prefixWord, tailWord_6793436, baseEnd_6793436] using wordTrace_append hprefix tailTrace_6793436
  have hstable : (prefixWord ++ tailWord_6793436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793436).length < 2 ^ (prefixWord ++ tailWord_6793436).sum := by decide
  have hdescent : baseEnd_6793436 < baseStart_6793436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793495 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 5]
def baseStart_6793495 : Nat := 118140960795 + 6793495 * 2 ^ 59
def prefixEnd_6793495 : Nat := 4983230072969 + 3 ^ 40 * 6793495 * 2
def baseEnd_6793495 : Nat := 3488328258916003153269791

theorem tailTrace_6793495 : CollatzResearch.WordTrace tailWord_6793495 prefixEnd_6793495 3488328258916003153269791 := by
  unfold tailWord_6793495
  simp only [CollatzResearch.WordTrace]
  refine ⟨247779118523335326419957939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165186079015556884279971959 247779118523335326419957939)
  ·
    refine ⟨371668677785002989629936909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247779118523335326419957939 371668677785002989629936909)
    ·
      refine ⟨139375754169376121111226341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371668677785002989629936909 139375754169376121111226341)
      ·
        refine ⟨26132953906758022708354939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139375754169376121111226341 26132953906758022708354939)
        ·
          refine ⟨39199430860137034062532409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26132953906758022708354939 39199430860137034062532409)
          ·
            refine ⟨29399573145102775546899307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39199430860137034062532409 29399573145102775546899307)
            ·
              refine ⟨44099359717654163320348961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29399573145102775546899307 44099359717654163320348961)
              ·
                refine ⟨33074519788240622490261721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44099359717654163320348961 33074519788240622490261721)
                ·
                  refine ⟨24805889841180466867696291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33074519788240622490261721 24805889841180466867696291)
                  ·
                    refine ⟨37208834761770700301544437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24805889841180466867696291 37208834761770700301544437)
                    ·
                      refine ⟨3488328258916003153269791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37208834761770700301544437 3488328258916003153269791)
                      ·
                        rfl

theorem cell23_6793495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_6793495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793495 prefixEnd_6793495 := by exact prefixLift 6793495
  have htrace : WordTrace (prefixWord ++ tailWord_6793495) baseStart_6793495 baseEnd_6793495 := by
    simpa [prefixWord, tailWord_6793495, baseEnd_6793495] using wordTrace_append hprefix tailTrace_6793495
  have hstable : (prefixWord ++ tailWord_6793495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793495).length < 2 ^ (prefixWord ++ tailWord_6793495).sum := by decide
  have hdescent : baseEnd_6793495 < baseStart_6793495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793509 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 1, 4, 2]
def baseStart_6793509 : Nat := 118140960795 + 6793509 * 2 ^ 59
def prefixEnd_6793509 : Nat := 4983230072969 + 3 ^ 40 * 6793509 * 2
def baseEnd_6793509 : Nat := 3488335447645166098494727

theorem tailTrace_6793509 : CollatzResearch.WordTrace tailWord_6793509 prefixEnd_6793509 3488335447645166098494727 := by
  unfold tailWord_6793509
  simp only [CollatzResearch.WordTrace]
  refine ⟨247779629145284606810967581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165186419430189737873978387 247779629145284606810967581)
  ·
    refine ⟨92917360929481727554112843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247779629145284606810967581 92917360929481727554112843)
    ·
      refine ⟨139376041394222591331169265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92917360929481727554112843 139376041394222591331169265)
      ·
        refine ⟨104532031045666943498376949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139376041394222591331169265 104532031045666943498376949)
        ·
          refine ⟨9799877910531275952972839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104532031045666943498376949 9799877910531275952972839)
          ·
            refine ⟨14699816865796913929459259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9799877910531275952972839 14699816865796913929459259)
            ·
              refine ⟨22049725298695370894188889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14699816865796913929459259 22049725298695370894188889)
              ·
                refine ⟨16537293974021528170641667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22049725298695370894188889 16537293974021528170641667)
                ·
                  refine ⟨24805940961032292255962501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16537293974021528170641667 24805940961032292255962501)
                  ·
                    refine ⟨4651113930193554797992969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24805940961032292255962501 4651113930193554797992969)
                    ·
                      refine ⟨3488335447645166098494727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4651113930193554797992969 3488335447645166098494727)
                      ·
                        rfl

theorem cell23_6793509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_6793509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793509 prefixEnd_6793509 := by exact prefixLift 6793509
  have htrace : WordTrace (prefixWord ++ tailWord_6793509) baseStart_6793509 baseEnd_6793509 := by
    simpa [prefixWord, tailWord_6793509, baseEnd_6793509] using wordTrace_append hprefix tailTrace_6793509
  have hstable : (prefixWord ++ tailWord_6793509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793509).length < 2 ^ (prefixWord ++ tailWord_6793509).sum := by decide
  have hdescent : baseEnd_6793509 < baseStart_6793509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793532 : List Nat := [2, 2, 2, 2, 1, 2, 3, 4, 5]
def baseStart_6793532 : Nat := 118140960795 + 6793532 * 2 ^ 59
def prefixEnd_6793532 : Nat := 4983230072969 + 3 ^ 40 * 6793532 * 2
def baseEnd_6793532 : Nat := 387594139744468834278569

theorem tailTrace_6793532 : CollatzResearch.WordTrace tailWord_6793532 prefixEnd_6793532 387594139744468834278569 := by
  unfold tailWord_6793532
  simp only [CollatzResearch.WordTrace]
  refine ⟨123890234012100640869527425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165186978682800854492703233 123890234012100640869527425)
  ·
    refine ⟨92917675509075480652145569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123890234012100640869527425 92917675509075480652145569)
    ·
      refine ⟨69688256631806610489109177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92917675509075480652145569 69688256631806610489109177)
      ·
        refine ⟨52266192473854957866831883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69688256631806610489109177 52266192473854957866831883)
        ·
          refine ⟨78399288710782436800247825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52266192473854957866831883 78399288710782436800247825)
          ·
            refine ⟨58799466533086827600185869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78399288710782436800247825 58799466533086827600185869)
            ·
              refine ⟨22049799949907560350069701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58799466533086827600185869 22049799949907560350069701)
              ·
                refine ⟨4134337490607667565638069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22049799949907560350069701 4134337490607667565638069)
                ·
                  refine ⟨387594139744468834278569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4134337490607667565638069 387594139744468834278569)
                  ·
                    rfl

theorem cell23_6793532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 5].length) (baseStart_6793532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793532 prefixEnd_6793532 := by exact prefixLift 6793532
  have htrace : WordTrace (prefixWord ++ tailWord_6793532) baseStart_6793532 baseEnd_6793532 := by
    simpa [prefixWord, tailWord_6793532, baseEnd_6793532] using wordTrace_append hprefix tailTrace_6793532
  have hstable : (prefixWord ++ tailWord_6793532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793532).length < 2 ^ (prefixWord ++ tailWord_6793532).sum := by decide
  have hdescent : baseEnd_6793532 < baseStart_6793532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793626 : List Nat := [3, 1, 1, 4, 1, 2, 3, 3, 1, 4]
def baseStart_6793626 : Nat := 118140960795 + 6793626 * 2 ^ 59
def prefixEnd_6793626 : Nat := 4983230072969 + 3 ^ 40 * 6793626 * 2
def baseEnd_6793626 : Nat := 1162798508293914046910563

theorem tailTrace_6793626 : CollatzResearch.WordTrace tailWord_6793626 prefixEnd_6793626 1162798508293914046910563 := by
  unfold tailWord_6793626
  simp only [CollatzResearch.WordTrace]
  refine ⟨61945974121465183948244183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165189264323907157195317821 61945974121465183948244183)
  ·
    refine ⟨92918961182197775922366275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61945974121465183948244183 92918961182197775922366275)
    ·
      refine ⟨139378441773296663883549413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92918961182197775922366275 139378441773296663883549413)
      ·
        refine ⟨26133457832493124478165515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139378441773296663883549413 26133457832493124478165515)
        ·
          refine ⟨39200186748739686717248273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26133457832493124478165515 39200186748739686717248273)
          ·
            refine ⟨29400140061554765037936205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39200186748739686717248273 29400140061554765037936205)
            ·
              refine ⟨11025052523083036889226077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29400140061554765037936205 11025052523083036889226077)
              ·
                refine ⟨4134394696156138833459779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11025052523083036889226077 4134394696156138833459779)
                ·
                  refine ⟨6201592044234208250189669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4134394696156138833459779 6201592044234208250189669)
                  ·
                    refine ⟨1162798508293914046910563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6201592044234208250189669 1162798508293914046910563)
                    ·
                      rfl

theorem cell23_6793626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 1, 4].length) (baseStart_6793626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793626 prefixEnd_6793626 := by exact prefixLift 6793626
  have htrace : WordTrace (prefixWord ++ tailWord_6793626) baseStart_6793626 baseEnd_6793626 := by
    simpa [prefixWord, tailWord_6793626, baseEnd_6793626] using wordTrace_append hprefix tailTrace_6793626
  have hstable : (prefixWord ++ tailWord_6793626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793626).length < 2 ^ (prefixWord ++ tailWord_6793626).sum := by decide
  have hdescent : baseEnd_6793626 < baseStart_6793626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793695 : List Nat := [1, 1, 2, 3, 3, 13]
def baseStart_6793695 : Nat := 118140960795 + 6793695 * 2 ^ 59
def prefixEnd_6793695 : Nat := 4983230072969 + 3 ^ 40 * 6793695 * 2
def baseEnd_6793695 : Nat := 14355682942579845147197

theorem tailTrace_6793695 : CollatzResearch.WordTrace tailWord_6793695 prefixEnd_6793695 14355682942579845147197 := by
  unfold tailWord_6793695
  simp only [CollatzResearch.WordTrace]
  refine ⟨247786413122610760577238539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165190942081740507051492359 247786413122610760577238539)
  ·
    refine ⟨371679619683916140865857809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247786413122610760577238539 371679619683916140865857809)
    ·
      refine ⟨278759714762937105649393357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371679619683916140865857809 278759714762937105649393357)
      ·
        refine ⟨104534893036101414618522509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278759714762937105649393357 104534893036101414618522509)
        ·
          refine ⟨39200584888538030481945941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104534893036101414618522509 39200584888538030481945941)
          ·
            refine ⟨14355682942579845147197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 39200584888538030481945941 14355682942579845147197)
            ·
              rfl

theorem cell23_6793695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 13].length) (baseStart_6793695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793695 prefixEnd_6793695 := by exact prefixLift 6793695
  have htrace : WordTrace (prefixWord ++ tailWord_6793695) baseStart_6793695 baseEnd_6793695 := by
    simpa [prefixWord, tailWord_6793695, baseEnd_6793695] using wordTrace_append hprefix tailTrace_6793695
  have hstable : (prefixWord ++ tailWord_6793695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793695).length < 2 ^ (prefixWord ++ tailWord_6793695).sum := by decide
  have hdescent : baseEnd_6793695 < baseStart_6793695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793705 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 7]
def baseStart_6793705 : Nat := 118140960795 + 6793705 * 2 ^ 59
def prefixEnd_6793705 : Nat := 4983230072969 + 3 ^ 40 * 6793705 * 2
def baseEnd_6793705 : Nat := 3488436089853447331643825

theorem tailTrace_6793705 : CollatzResearch.WordTrace tailWord_6793705 prefixEnd_6793705 3488436089853447331643825 := by
  unfold tailWord_6793705
  simp only [CollatzResearch.WordTrace]
  refine ⟨247786777852574532285102569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165191185235049688190068379 247786777852574532285102569)
  ·
    refine ⟨185840083389430899213826927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247786777852574532285102569 185840083389430899213826927)
    ·
      refine ⟨278760125084146348820740391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185840083389430899213826927 278760125084146348820740391)
      ·
        refine ⟨418140187626219523231110587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278760125084146348820740391 418140187626219523231110587)
        ·
          refine ⟨627210281439329284846665881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418140187626219523231110587 627210281439329284846665881)
          ·
            refine ⟨470407711079496963634999411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 627210281439329284846665881 470407711079496963634999411)
            ·
              refine ⟨705611566619245445452499117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470407711079496963634999411 705611566619245445452499117)
              ·
                refine ⟨264604337482217042044687169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 705611566619245445452499117 264604337482217042044687169)
                ·
                  refine ⟨198453253111662781533515377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264604337482217042044687169 198453253111662781533515377)
                  ·
                    refine ⟨148839939833747086150136533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 198453253111662781533515377 148839939833747086150136533)
                    ·
                      refine ⟨3488436089853447331643825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148839939833747086150136533 3488436089853447331643825)
                      ·
                        rfl

theorem cell23_6793705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_6793705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793705 prefixEnd_6793705 := by exact prefixLift 6793705
  have htrace : WordTrace (prefixWord ++ tailWord_6793705) baseStart_6793705 baseEnd_6793705 := by
    simpa [prefixWord, tailWord_6793705, baseEnd_6793705] using wordTrace_append hprefix tailTrace_6793705
  have hstable : (prefixWord ++ tailWord_6793705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793705).length < 2 ^ (prefixWord ++ tailWord_6793705).sum := by decide
  have hdescent : baseEnd_6793705 < baseStart_6793705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793729 : List Nat := [1, 2, 4, 1, 3, 2, 3, 7]
def baseStart_6793729 : Nat := 118140960795 + 6793729 * 2 ^ 59
def prefixEnd_6793729 : Nat := 4983230072969 + 3 ^ 40 * 6793729 * 2
def baseEnd_6793729 : Nat := 129201793088487231027545

theorem tailTrace_6793729 : CollatzResearch.WordTrace tailWord_6793729 prefixEnd_6793729 129201793088487231027545 := by
  unfold tailWord_6793729
  simp only [CollatzResearch.WordTrace]
  refine ⟨247787653204487584383976241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165191768802991722922650827 247787653204487584383976241)
  ·
    refine ⟨185840739903365688287982181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247787653204487584383976241 185840739903365688287982181)
    ·
      refine ⟨34845138731881066553996659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185840739903365688287982181 34845138731881066553996659)
      ·
        refine ⟨52267708097821599830994989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34845138731881066553996659 52267708097821599830994989)
        ·
          refine ⟨19600390536683099936623121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52267708097821599830994989 19600390536683099936623121)
          ·
            refine ⟨14700292902512324952467341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19600390536683099936623121 14700292902512324952467341)
            ·
              refine ⟨5512609838442121857175253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14700292902512324952467341 5512609838442121857175253)
              ·
                refine ⟨129201793088487231027545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5512609838442121857175253 129201793088487231027545)
                ·
                  rfl

theorem cell23_6793729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 7].length) (baseStart_6793729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793729 prefixEnd_6793729 := by exact prefixLift 6793729
  have htrace : WordTrace (prefixWord ++ tailWord_6793729) baseStart_6793729 baseEnd_6793729 := by
    simpa [prefixWord, tailWord_6793729, baseEnd_6793729] using wordTrace_append hprefix tailTrace_6793729
  have hstable : (prefixWord ++ tailWord_6793729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793729).length < 2 ^ (prefixWord ++ tailWord_6793729).sum := by decide
  have hdescent : baseEnd_6793729 < baseStart_6793729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793734 : List Nat := [6, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_6793734 : Nat := 118140960795 + 6793734 * 2 ^ 59
def prefixEnd_6793734 : Nat := 4983230072969 + 3 ^ 40 * 6793734 * 2
def baseEnd_6793734 : Nat := 3488450980792427718181193

theorem tailTrace_6793734 : CollatzResearch.WordTrace tailWord_6793734 prefixEnd_6793734 3488450980792427718181193 := by
  unfold tailWord_6793734
  simp only [CollatzResearch.WordTrace]
  refine ⟨7743369861545920944934633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 165191890379646313491938837 7743369861545920944934633)
  ·
    refine ⟨5807527396159440708700975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7743369861545920944934633 5807527396159440708700975)
    ·
      refine ⟨8711291094239161063051463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5807527396159440708700975 8711291094239161063051463)
      ·
        refine ⟨13066936641358741594577195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8711291094239161063051463 13066936641358741594577195)
        ·
          refine ⟨19600404962038112391865793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13066936641358741594577195 19600404962038112391865793)
          ·
            refine ⟨14700303721528584293899345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19600404962038112391865793 14700303721528584293899345)
            ·
              refine ⟨11025227791146438220424509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14700303721528584293899345 11025227791146438220424509)
              ·
                refine ⟨4134460421679914332659191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11025227791146438220424509 4134460421679914332659191)
                ·
                  refine ⟨6201690632519871498988787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4134460421679914332659191 6201690632519871498988787)
                  ·
                    refine ⟨9302535948779807248483181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6201690632519871498988787 9302535948779807248483181)
                    ·
                      refine ⟨3488450980792427718181193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9302535948779807248483181 3488450980792427718181193)
                      ·
                        rfl

theorem cell23_6793734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_6793734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793734 prefixEnd_6793734 := by exact prefixLift 6793734
  have htrace : WordTrace (prefixWord ++ tailWord_6793734) baseStart_6793734 baseEnd_6793734 := by
    simpa [prefixWord, tailWord_6793734, baseEnd_6793734] using wordTrace_append hprefix tailTrace_6793734
  have hstable : (prefixWord ++ tailWord_6793734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793734).length < 2 ^ (prefixWord ++ tailWord_6793734).sum := by decide
  have hdescent : baseEnd_6793734 < baseStart_6793734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793739 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 3]
def baseStart_6793739 : Nat := 118140960795 + 6793739 * 2 ^ 59
def prefixEnd_6793739 : Nat := 4983230072969 + 3 ^ 40 * 6793739 * 2
def baseEnd_6793739 : Nat := 3488453548195700198618669

theorem tailTrace_6793739 : CollatzResearch.WordTrace tailWord_6793739 prefixEnd_6793739 3488453548195700198618669 := by
  unfold tailWord_6793739
  simp only [CollatzResearch.WordTrace]
  refine ⟨247788017934451356091840271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165192011956300904061226847 247788017934451356091840271)
  ·
    refine ⟨371682026901677034137760407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247788017934451356091840271 371682026901677034137760407)
    ·
      refine ⟨557523040352515551206640611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371682026901677034137760407 557523040352515551206640611)
      ·
        refine ⟨836284560528773326809960917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557523040352515551206640611 836284560528773326809960917)
        ·
          refine ⟨19600419387393124847108459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 836284560528773326809960917 19600419387393124847108459)
          ·
            refine ⟨29400629081089687270662689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19600419387393124847108459 29400629081089687270662689)
            ·
              refine ⟨22050471810817265452997017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29400629081089687270662689 22050471810817265452997017)
              ·
                refine ⟨16537853858112949089747763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22050471810817265452997017 16537853858112949089747763)
                ·
                  refine ⟨24806780787169423634621645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16537853858112949089747763 24806780787169423634621645)
                  ·
                    refine ⟨9302542795188533862983117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24806780787169423634621645 9302542795188533862983117)
                    ·
                      refine ⟨3488453548195700198618669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9302542795188533862983117 3488453548195700198618669)
                      ·
                        rfl

theorem cell23_6793739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 3].length) (baseStart_6793739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793739 prefixEnd_6793739 := by exact prefixLift 6793739
  have htrace : WordTrace (prefixWord ++ tailWord_6793739) baseStart_6793739 baseEnd_6793739 := by
    simpa [prefixWord, tailWord_6793739, baseEnd_6793739] using wordTrace_append hprefix tailTrace_6793739
  have hstable : (prefixWord ++ tailWord_6793739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793739).length < 2 ^ (prefixWord ++ tailWord_6793739).sum := by decide
  have hdescent : baseEnd_6793739 < baseStart_6793739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793740 : List Nat := [2, 2, 1, 2, 4, 2, 2, 3, 1, 2, 2]
def baseStart_6793740 : Nat := 118140960795 + 6793740 * 2 ^ 59
def prefixEnd_6793740 : Nat := 4983230072969 + 3 ^ 40 * 6793740 * 2
def baseEnd_6793740 : Nat := 3488454061676354694706165

theorem tailTrace_6793740 : CollatzResearch.WordTrace tailWord_6793740 prefixEnd_6793740 3488454061676354694706165 := by
  unfold tailWord_6793740
  simp only [CollatzResearch.WordTrace]
  refine ⟨123894027203723866631313337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165192036271631822175084449 123894027203723866631313337)
  ·
    refine ⟨92920520402792899973485003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123894027203723866631313337 92920520402792899973485003)
    ·
      refine ⟨139380780604189349960227505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92920520402792899973485003 139380780604189349960227505)
      ·
        refine ⟨104535585453142012470170629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139380780604189349960227505 104535585453142012470170629)
        ·
          refine ⟨19600422272464127338156993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104535585453142012470170629 19600422272464127338156993)
          ·
            refine ⟨14700316704348095503617745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19600422272464127338156993 14700316704348095503617745)
            ·
              refine ⟨11025237528261071627713309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14700316704348095503617745 11025237528261071627713309)
              ·
                refine ⟨4134464073097901860392491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11025237528261071627713309 4134464073097901860392491)
                ·
                  refine ⟨6201696109646852790588737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4134464073097901860392491 6201696109646852790588737)
                  ·
                    refine ⟨4651272082235139592941553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6201696109646852790588737 4651272082235139592941553)
                    ·
                      refine ⟨3488454061676354694706165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4651272082235139592941553 3488454061676354694706165)
                      ·
                        rfl

theorem cell23_6793740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_6793740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793740 prefixEnd_6793740 := by exact prefixLift 6793740
  have htrace : WordTrace (prefixWord ++ tailWord_6793740) baseStart_6793740 baseEnd_6793740 := by
    simpa [prefixWord, tailWord_6793740, baseEnd_6793740] using wordTrace_append hprefix tailTrace_6793740
  have hstable : (prefixWord ++ tailWord_6793740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793740).length < 2 ^ (prefixWord ++ tailWord_6793740).sum := by decide
  have hdescent : baseEnd_6793740 < baseStart_6793740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793756 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_6793756 : Nat := 118140960795 + 6793756 * 2 ^ 59
def prefixEnd_6793756 : Nat := 4983230072969 + 3 ^ 40 * 6793756 * 2
def baseEnd_6793756 : Nat := 3488462277366826632106091

theorem tailTrace_6793756 : CollatzResearch.WordTrace tailWord_6793756 prefixEnd_6793756 3488462277366826632106091 := by
  unfold tailWord_6793756
  simp only [CollatzResearch.WordTrace]
  refine ⟨123894318987694883997604561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165192425316926511996806081 123894318987694883997604561)
  ·
    refine ⟨92920739240771162998203421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123894318987694883997604561 92920739240771162998203421)
    ·
      refine ⟨34845277215289186124326283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92920739240771162998203421 34845277215289186124326283)
      ·
        refine ⟨52267915822933779186489425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34845277215289186124326283 52267915822933779186489425)
        ·
          refine ⟨39200936867200334389867069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52267915822933779186489425 39200936867200334389867069)
          ·
            refine ⟨14700351325200125396200151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39200936867200334389867069 14700351325200125396200151)
            ·
              refine ⟨22050526987800188094300227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14700351325200125396200151 22050526987800188094300227)
              ·
                refine ⟨33075790481700282141450341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22050526987800188094300227 33075790481700282141450341)
                ·
                  refine ⟨6201710715318802901521939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33075790481700282141450341 6201710715318802901521939)
                  ·
                    refine ⟨9302566072978204352282909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6201710715318802901521939 9302566072978204352282909)
                    ·
                      refine ⟨3488462277366826632106091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9302566072978204352282909 3488462277366826632106091)
                      ·
                        rfl

theorem cell23_6793756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_6793756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793756 prefixEnd_6793756 := by exact prefixLift 6793756
  have htrace : WordTrace (prefixWord ++ tailWord_6793756) baseStart_6793756 baseEnd_6793756 := by
    simpa [prefixWord, tailWord_6793756, baseEnd_6793756] using wordTrace_append hprefix tailTrace_6793756
  have hstable : (prefixWord ++ tailWord_6793756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793756).length < 2 ^ (prefixWord ++ tailWord_6793756).sum := by decide
  have hdescent : baseEnd_6793756 < baseStart_6793756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793780 : List Nat := [2, 5, 1, 3, 2, 1, 2, 7]
def baseStart_6793780 : Nat := 118140960795 + 6793780 * 2 ^ 59
def prefixEnd_6793780 : Nat := 4983230072969 + 3 ^ 40 * 6793780 * 2
def baseEnd_6793780 : Nat := 129202762996390168081703

theorem tailTrace_6793780 : CollatzResearch.WordTrace tailWord_6793780 prefixEnd_6793780 129202762996390168081703 := by
  unfold tailWord_6793780
  simp only [CollatzResearch.WordTrace]
  refine ⟨123894756663651410047041397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165193008884868546729388529 123894756663651410047041397)
  ·
    refine ⟨11615133437217319691910131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123894756663651410047041397 11615133437217319691910131)
    ·
      refine ⟨17422700155825979537865197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11615133437217319691910131 17422700155825979537865197)
      ·
        refine ⟨6533512558434742326699449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17422700155825979537865197 6533512558434742326699449)
        ·
          refine ⟨4900134418826056745024587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6533512558434742326699449 4900134418826056745024587)
          ·
            refine ⟨7350201628239085117536881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4900134418826056745024587 7350201628239085117536881)
            ·
              refine ⟨5512651221179313838152661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7350201628239085117536881 5512651221179313838152661)
              ·
                refine ⟨129202762996390168081703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5512651221179313838152661 129202762996390168081703)
                ·
                  rfl

theorem cell23_6793780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 7].length) (baseStart_6793780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793780 prefixEnd_6793780 := by exact prefixLift 6793780
  have htrace : WordTrace (prefixWord ++ tailWord_6793780) baseStart_6793780 baseEnd_6793780 := by
    simpa [prefixWord, tailWord_6793780, baseEnd_6793780] using wordTrace_append hprefix tailTrace_6793780
  have hstable : (prefixWord ++ tailWord_6793780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793780).length < 2 ^ (prefixWord ++ tailWord_6793780).sum := by decide
  have hdescent : baseEnd_6793780 < baseStart_6793780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793792 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 4]
def baseStart_6793792 : Nat := 118140960795 + 6793792 * 2 ^ 59
def prefixEnd_6793792 : Nat := 4983230072969 + 3 ^ 40 * 6793792 * 2
def baseEnd_6793792 : Nat := 3488480762670388491255925

theorem tailTrace_6793792 : CollatzResearch.WordTrace tailWord_6793792 prefixEnd_6793792 3488480762670388491255925 := by
  unfold tailWord_6793792
  simp only [CollatzResearch.WordTrace]
  refine ⟨123894975501629673071759815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165193300668839564095679753 123894975501629673071759815)
  ·
    refine ⟨185842463252444509607639723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123894975501629673071759815 185842463252444509607639723)
    ·
      refine ⟨278763694878666764411459585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185842463252444509607639723 278763694878666764411459585)
      ·
        refine ⟨209072771159000073308594689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278763694878666764411459585 209072771159000073308594689)
        ·
          refine ⟨156804578369250054981446017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209072771159000073308594689 156804578369250054981446017)
          ·
            refine ⟨117603433776937541236084513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156804578369250054981446017 117603433776937541236084513)
            ·
              refine ⟨88202575332703155927063385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117603433776937541236084513 88202575332703155927063385)
              ·
                refine ⟨66151931499527366945297539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88202575332703155927063385 66151931499527366945297539)
                ·
                  refine ⟨99227897249291050417946309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66151931499527366945297539 99227897249291050417946309)
                  ·
                    refine ⟨18605230734242071953364933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99227897249291050417946309 18605230734242071953364933)
                    ·
                      refine ⟨3488480762670388491255925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18605230734242071953364933 3488480762670388491255925)
                      ·
                        rfl

theorem cell23_6793792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_6793792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793792 prefixEnd_6793792 := by exact prefixLift 6793792
  have htrace : WordTrace (prefixWord ++ tailWord_6793792) baseStart_6793792 baseEnd_6793792 := by
    simpa [prefixWord, tailWord_6793792, baseEnd_6793792] using wordTrace_append hprefix tailTrace_6793792
  have hstable : (prefixWord ++ tailWord_6793792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793792).length < 2 ^ (prefixWord ++ tailWord_6793792).sum := by decide
  have hdescent : baseEnd_6793792 < baseStart_6793792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793799 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_6793799 : Nat := 118140960795 + 6793799 * 2 ^ 59
def prefixEnd_6793799 : Nat := 4983230072969 + 3 ^ 40 * 6793799 * 2
def baseEnd_6793799 : Nat := 3488484357034969963868393

theorem tailTrace_6793799 : CollatzResearch.WordTrace tailWord_6793799 prefixEnd_6793799 3488484357034969963868393 := by
  unfold tailWord_6793799
  simp only [CollatzResearch.WordTrace]
  refine ⟨247790206314233986339024451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165193470876155990892682967 247790206314233986339024451)
  ·
    refine ⟨371685309471350979508536677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247790206314233986339024451 371685309471350979508536677)
    ·
      refine ⟨69690995525878308657850627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371685309471350979508536677 69690995525878308657850627)
      ·
        refine ⟨104536493288817462986775941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69690995525878308657850627 104536493288817462986775941)
        ·
          refine ⟨19600592491653274310020489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104536493288817462986775941 19600592491653274310020489)
          ·
            refine ⟨14700444368739955732515367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19600592491653274310020489 14700444368739955732515367)
            ·
              refine ⟨22050666553109933598773051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14700444368739955732515367 22050666553109933598773051)
              ·
                refine ⟨33075999829664900398159577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22050666553109933598773051 33075999829664900398159577)
                ·
                  refine ⟨24806999872248675298619683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33075999829664900398159577 24806999872248675298619683)
                  ·
                    refine ⟨37210499808373012947929525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24806999872248675298619683 37210499808373012947929525)
                    ·
                      refine ⟨3488484357034969963868393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37210499808373012947929525 3488484357034969963868393)
                      ·
                        rfl

theorem cell23_6793799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_6793799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793799 prefixEnd_6793799 := by exact prefixLift 6793799
  have htrace : WordTrace (prefixWord ++ tailWord_6793799) baseStart_6793799 baseEnd_6793799 := by
    simpa [prefixWord, tailWord_6793799, baseEnd_6793799] using wordTrace_append hprefix tailTrace_6793799
  have hstable : (prefixWord ++ tailWord_6793799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793799).length < 2 ^ (prefixWord ++ tailWord_6793799).sum := by decide
  have hdescent : baseEnd_6793799 < baseStart_6793799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793849 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 2, 5]
def baseStart_6793849 : Nat := 118140960795 + 6793849 * 2 ^ 59
def prefixEnd_6793849 : Nat := 4983230072969 + 3 ^ 40 * 6793849 * 2
def baseEnd_6793849 : Nat := 1162836677022564922747721

theorem tailTrace_6793849 : CollatzResearch.WordTrace tailWord_6793849 prefixEnd_6793849 1162836677022564922747721 := by
  unfold tailWord_6793849
  simp only [CollatzResearch.WordTrace]
  refine ⟨247792029964052844878344601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165194686642701896585563067 247792029964052844878344601)
  ·
    refine ⟨185844022473039633658758451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247792029964052844878344601 185844022473039633658758451)
    ·
      refine ⟨278766033709559450488137677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185844022473039633658758451 278766033709559450488137677)
      ·
        refine ⟨104537262641084793933051629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278766033709559450488137677 104537262641084793933051629)
        ·
          refine ⟨39201473490406797724894361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104537262641084793933051629 39201473490406797724894361)
          ·
            refine ⟨29401105117805098293670771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39201473490406797724894361 29401105117805098293670771)
            ·
              refine ⟨44101657676707647440506157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29401105117805098293670771 44101657676707647440506157)
              ·
                refine ⟨16538121628765367790189809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44101657676707647440506157 16538121628765367790189809)
                ·
                  refine ⟨12403591221574025842642357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16538121628765367790189809 12403591221574025842642357)
                  ·
                    refine ⟨1162836677022564922747721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12403591221574025842642357 1162836677022564922747721)
                    ·
                      rfl

theorem cell23_6793849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 5].length) (baseStart_6793849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793849 prefixEnd_6793849 := by exact prefixLift 6793849
  have htrace : WordTrace (prefixWord ++ tailWord_6793849) baseStart_6793849 baseEnd_6793849 := by
    simpa [prefixWord, tailWord_6793849, baseEnd_6793849] using wordTrace_append hprefix tailTrace_6793849
  have hstable : (prefixWord ++ tailWord_6793849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793849).length < 2 ^ (prefixWord ++ tailWord_6793849).sum := by decide
  have hdescent : baseEnd_6793849 < baseStart_6793849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793876 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_6793876 : Nat := 118140960795 + 6793876 * 2 ^ 59
def prefixEnd_6793876 : Nat := 4983230072969 + 3 ^ 40 * 6793876 * 2
def baseEnd_6793876 : Nat := 3488523895045366162605539

theorem tailTrace_6793876 : CollatzResearch.WordTrace tailWord_6793876 prefixEnd_6793876 3488523895045366162605539 := by
  unfold tailWord_6793876
  simp only [CollatzResearch.WordTrace]
  refine ⟨123896507367477514244788741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165195343156636685659718321 123896507367477514244788741)
  ·
    refine ⟨23230595131402033920897889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123896507367477514244788741 23230595131402033920897889)
    ·
      refine ⟨17422946348551525440673417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23230595131402033920897889 17422946348551525440673417)
      ·
        refine ⟨13067209761413644080505063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17422946348551525440673417 13067209761413644080505063)
        ·
          refine ⟨19600814642120466120757595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13067209761413644080505063 19600814642120466120757595)
          ·
            refine ⟨29401221963180699181136393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19600814642120466120757595 29401221963180699181136393)
            ·
              refine ⟨22050916472385524385852295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29401221963180699181136393 22050916472385524385852295)
              ·
                refine ⟨33076374708578286578778443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22050916472385524385852295 33076374708578286578778443)
                ·
                  refine ⟨49614562062867429868167665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33076374708578286578778443 49614562062867429868167665)
                  ·
                    refine ⟨37210921547150572401125749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49614562062867429868167665 37210921547150572401125749)
                    ·
                      refine ⟨3488523895045366162605539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37210921547150572401125749 3488523895045366162605539)
                      ·
                        rfl

theorem cell23_6793876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_6793876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793876 prefixEnd_6793876 := by exact prefixLift 6793876
  have htrace : WordTrace (prefixWord ++ tailWord_6793876) baseStart_6793876 baseEnd_6793876 := by
    simpa [prefixWord, tailWord_6793876, baseEnd_6793876] using wordTrace_append hprefix tailTrace_6793876
  have hstable : (prefixWord ++ tailWord_6793876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793876).length < 2 ^ (prefixWord ++ tailWord_6793876).sum := by decide
  have hdescent : baseEnd_6793876 < baseStart_6793876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793886 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_6793886 : Nat := 118140960795 + 6793886 * 2 ^ 59
def prefixEnd_6793886 : Nat := 4983230072969 + 3 ^ 40 * 6793886 * 2
def baseEnd_6793886 : Nat := 3488529029851911123480493

theorem tailTrace_6793886 : CollatzResearch.WordTrace tailWord_6793886 prefixEnd_6793886 3488529029851911123480493 := by
  unfold tailWord_6793886
  simp only [CollatzResearch.WordTrace]
  refine ⟨30974172433114850024680189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165195586309945866798294341 30974172433114850024680189)
  ·
    refine ⟨11615314662418068759255071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30974172433114850024680189 11615314662418068759255071)
    ·
      refine ⟨17422971993627103138882607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11615314662418068759255071 17422971993627103138882607)
      ·
        refine ⟨26134457990440654708323911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17422971993627103138882607 26134457990440654708323911)
        ·
          refine ⟨39201686985660982062485867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26134457990440654708323911 39201686985660982062485867)
          ·
            refine ⟨58802530478491473093728801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39201686985660982062485867 58802530478491473093728801)
            ·
              refine ⟨44101897858868604820296601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58802530478491473093728801 44101897858868604820296601)
              ·
                refine ⟨33076423394151453615222451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44101897858868604820296601 33076423394151453615222451)
                ·
                  refine ⟨49614635091227180422833677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33076423394151453615222451 49614635091227180422833677)
                  ·
                    refine ⟨18605488159210192658562629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49614635091227180422833677 18605488159210192658562629)
                    ·
                      refine ⟨3488529029851911123480493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18605488159210192658562629 3488529029851911123480493)
                      ·
                        rfl

theorem cell23_6793886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_6793886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793886 prefixEnd_6793886 := by exact prefixLift 6793886
  have htrace : WordTrace (prefixWord ++ tailWord_6793886) baseStart_6793886 baseEnd_6793886 := by
    simpa [prefixWord, tailWord_6793886, baseEnd_6793886] using wordTrace_append hprefix tailTrace_6793886
  have hstable : (prefixWord ++ tailWord_6793886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793886).length < 2 ^ (prefixWord ++ tailWord_6793886).sum := by decide
  have hdescent : baseEnd_6793886 < baseStart_6793886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793946 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2]
def baseStart_6793946 : Nat := 118140960795 + 6793946 * 2 ^ 59
def prefixEnd_6793946 : Nat := 4983230072969 + 3 ^ 40 * 6793946 * 2
def baseEnd_6793946 : Nat := 3488559838691180888730217

theorem tailTrace_6793946 : CollatzResearch.WordTrace tailWord_6793946 prefixEnd_6793946 3488559838691180888730217 := by
  unfold tailWord_6793946
  simp only [CollatzResearch.WordTrace]
  refine ⟨61948891961175357611156423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165197045229800953629750461 61948891961175357611156423)
  ·
    refine ⟨92923337941763036416734635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61948891961175357611156423 92923337941763036416734635)
    ·
      refine ⟨139385006912644554625101953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92923337941763036416734635 139385006912644554625101953)
      ·
        refine ⟨104538755184483415968826465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139385006912644554625101953 104538755184483415968826465)
        ·
          refine ⟨78404066388362561976619849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104538755184483415968826465 78404066388362561976619849)
          ·
            refine ⟨58803049791271921482464887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78404066388362561976619849 58803049791271921482464887)
            ·
              refine ⟨88204574686907882223697331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58803049791271921482464887 88204574686907882223697331)
              ·
                refine ⟨132306862030361823335545997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88204574686907882223697331 132306862030361823335545997)
                ·
                  refine ⟨49615073261385683750829749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132306862030361823335545997 49615073261385683750829749)
                  ·
                    refine ⟨4651413118254907851640289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49615073261385683750829749 4651413118254907851640289)
                    ·
                      refine ⟨3488559838691180888730217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4651413118254907851640289 3488559838691180888730217)
                      ·
                        rfl

theorem cell23_6793946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_6793946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793946 prefixEnd_6793946 := by exact prefixLift 6793946
  have htrace : WordTrace (prefixWord ++ tailWord_6793946) baseStart_6793946 baseEnd_6793946 := by
    simpa [prefixWord, tailWord_6793946, baseEnd_6793946] using wordTrace_append hprefix tailTrace_6793946
  have hstable : (prefixWord ++ tailWord_6793946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793946).length < 2 ^ (prefixWord ++ tailWord_6793946).sum := by decide
  have hdescent : baseEnd_6793946 < baseStart_6793946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793953 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 3, 1, 3]
def baseStart_6793953 : Nat := 118140960795 + 6793953 * 2 ^ 59
def prefixEnd_6793953 : Nat := 4983230072969 + 3 ^ 40 * 6793953 * 2
def baseEnd_6793953 : Nat := 3488563433055762361342685

theorem tailTrace_6793953 : CollatzResearch.WordTrace tailWord_6793953 prefixEnd_6793953 3488563433055762361342685 := by
  unfold tailWord_6793953
  simp only [CollatzResearch.WordTrace]
  refine ⟨247795823155676070640130513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165197215437117380426753675 247795823155676070640130513)
  ·
    refine ⟨185846867366757052980097885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247795823155676070640130513 185846867366757052980097885)
    ·
      refine ⟨69692575262533894867536707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185846867366757052980097885 69692575262533894867536707)
      ·
        refine ⟨104538862893800842301305061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69692575262533894867536707 104538862893800842301305061)
        ·
          refine ⟨19601036792587657931494699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104538862893800842301305061 19601036792587657931494699)
          ·
            refine ⟨29401555188881486897242049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19601036792587657931494699 29401555188881486897242049)
            ·
              refine ⟨22051166391661115172931537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29401555188881486897242049 22051166391661115172931537)
              ·
                refine ⟨16538374793745836379698653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22051166391661115172931537 16538374793745836379698653)
                ·
                  refine ⟨6201890547654688642386995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16538374793745836379698653 6201890547654688642386995)
                  ·
                    refine ⟨9302835821482032963580493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6201890547654688642386995 9302835821482032963580493)
                    ·
                      refine ⟨3488563433055762361342685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9302835821482032963580493 3488563433055762361342685)
                      ·
                        rfl

theorem cell23_6793953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_6793953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793953 prefixEnd_6793953 := by exact prefixLift 6793953
  have htrace : WordTrace (prefixWord ++ tailWord_6793953) baseStart_6793953 baseEnd_6793953 := by
    simpa [prefixWord, tailWord_6793953, baseEnd_6793953] using wordTrace_append hprefix tailTrace_6793953
  have hstable : (prefixWord ++ tailWord_6793953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793953).length < 2 ^ (prefixWord ++ tailWord_6793953).sum := by decide
  have hdescent : baseEnd_6793953 < baseStart_6793953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793956 : List Nat := [2, 3, 1, 1, 1, 4, 1, 4, 1, 5]
def baseStart_6793956 : Nat := 118140960795 + 6793956 * 2 ^ 59
def prefixEnd_6793956 : Nat := 4983230072969 + 3 ^ 40 * 6793956 * 2
def baseEnd_6793956 : Nat := 1162854991165908616535057

theorem tailTrace_6793956 : CollatzResearch.WordTrace tailWord_6793956 prefixEnd_6793956 1162854991165908616535057 := by
  unfold tailWord_6793956
  simp only [CollatzResearch.WordTrace]
  refine ⟨123897966287332601076244861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165197288383110134768326481 123897966287332601076244861)
  ·
    refine ⟨46461737357749725403591823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123897966287332601076244861 46461737357749725403591823)
    ·
      refine ⟨69692606036624588105387735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46461737357749725403591823 69692606036624588105387735)
      ·
        refine ⟨104538909054936882158081603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69692606036624588105387735 104538909054936882158081603)
        ·
          refine ⟨156808363582405323237122405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104538909054936882158081603 156808363582405323237122405)
          ·
            refine ⟨29401568171700998106960451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156808363582405323237122405 29401568171700998106960451)
            ·
              refine ⟨44102352257551497160440677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29401568171700998106960451 44102352257551497160440677)
              ·
                refine ⟨8269191048290905717582627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44102352257551497160440677 8269191048290905717582627)
                ·
                  refine ⟨12403786572436358576373941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8269191048290905717582627 12403786572436358576373941)
                  ·
                    refine ⟨1162854991165908616535057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12403786572436358576373941 1162854991165908616535057)
                    ·
                      rfl

theorem cell23_6793956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_6793956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793956 prefixEnd_6793956 := by exact prefixLift 6793956
  have htrace : WordTrace (prefixWord ++ tailWord_6793956) baseStart_6793956 baseEnd_6793956 := by
    simpa [prefixWord, tailWord_6793956, baseEnd_6793956] using wordTrace_append hprefix tailTrace_6793956
  have hstable : (prefixWord ++ tailWord_6793956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793956).length < 2 ^ (prefixWord ++ tailWord_6793956).sum := by decide
  have hdescent : baseEnd_6793956 < baseStart_6793956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793969 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 3, 6]
def baseStart_6793969 : Nat := 118140960795 + 6793969 * 2 ^ 59
def prefixEnd_6793969 : Nat := 4983230072969 + 3 ^ 40 * 6793969 * 2
def baseEnd_6793969 : Nat := 1162857216248744766247537

theorem tailTrace_6793969 : CollatzResearch.WordTrace tailWord_6793969 prefixEnd_6793969 1162857216248744766247537 := by
  unfold tailWord_6793969
  simp only [CollatzResearch.WordTrace]
  refine ⟨247796406723618105372712961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165197604482412070248475307 247796406723618105372712961)
  ·
    refine ⟨185847305042713579029534721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247796406723618105372712961 185847305042713579029534721)
    ·
      refine ⟨139385478782035184272151041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185847305042713579029534721 139385478782035184272151041)
      ·
        refine ⟨104539109086526388204113281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139385478782035184272151041 104539109086526388204113281)
        ·
          refine ⟨78404331814894791153084961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104539109086526388204113281 78404331814894791153084961)
          ·
            refine ⟨58803248861171093364813721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78404331814894791153084961 58803248861171093364813721)
            ·
              refine ⟨44102436645878320023610291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58803248861171093364813721 44102436645878320023610291)
              ·
                refine ⟨66153654968817480035415437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44102436645878320023610291 66153654968817480035415437)
                ·
                  refine ⟨24807620613306555013280789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66153654968817480035415437 24807620613306555013280789)
                  ·
                    refine ⟨1162857216248744766247537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24807620613306555013280789 1162857216248744766247537)
                    ·
                      rfl

theorem cell23_6793969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_6793969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793969 prefixEnd_6793969 := by exact prefixLift 6793969
  have htrace : WordTrace (prefixWord ++ tailWord_6793969) baseStart_6793969 baseEnd_6793969 := by
    simpa [prefixWord, tailWord_6793969, baseEnd_6793969] using wordTrace_append hprefix tailTrace_6793969
  have hstable : (prefixWord ++ tailWord_6793969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793969).length < 2 ^ (prefixWord ++ tailWord_6793969).sum := by decide
  have hdescent : baseEnd_6793969 < baseStart_6793969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793976 : List Nat := [2, 1, 2, 1, 1, 2, 3, 5, 1, 1, 4]
def baseStart_6793976 : Nat := 118140960795 + 6793976 * 2 ^ 59
def prefixEnd_6793976 : Nat := 4983230072969 + 3 ^ 40 * 6793976 * 2
def baseEnd_6793976 : Nat := 3488575243110815771355079

theorem tailTrace_6793976 : CollatzResearch.WordTrace tailWord_6793976 prefixEnd_6793976 3488575243110815771355079 := by
  unfold tailWord_6793976
  simp only [CollatzResearch.WordTrace]
  refine ⟨123898331017296372784108891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165197774689728497045478521 123898331017296372784108891)
  ·
    refine ⟨185847496525944559176163337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123898331017296372784108891 185847496525944559176163337)
    ·
      refine ⟨139385622394458419382122503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185847496525944559176163337 139385622394458419382122503)
      ·
        refine ⟨209078433591687629073183755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139385622394458419382122503 209078433591687629073183755)
        ·
          refine ⟨313617650387531443609775633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209078433591687629073183755 313617650387531443609775633)
          ·
            refine ⟨235213237790648582707331725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313617650387531443609775633 235213237790648582707331725)
            ·
              refine ⟨88204964171493218515249397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235213237790648582707331725 88204964171493218515249397)
              ·
                refine ⟨8269215391077489235804631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88204964171493218515249397 8269215391077489235804631)
                ·
                  refine ⟨12403823086616233853706947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8269215391077489235804631 12403823086616233853706947)
                  ·
                    refine ⟨18605734629924350780560421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12403823086616233853706947 18605734629924350780560421)
                    ·
                      refine ⟨3488575243110815771355079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18605734629924350780560421 3488575243110815771355079)
                      ·
                        rfl

theorem cell23_6793976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_6793976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793976 prefixEnd_6793976 := by exact prefixLift 6793976
  have htrace : WordTrace (prefixWord ++ tailWord_6793976) baseStart_6793976 baseEnd_6793976 := by
    simpa [prefixWord, tailWord_6793976, baseEnd_6793976] using wordTrace_append hprefix tailTrace_6793976
  have hstable : (prefixWord ++ tailWord_6793976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793976).length < 2 ^ (prefixWord ++ tailWord_6793976).sum := by decide
  have hdescent : baseEnd_6793976 < baseStart_6793976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793979 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 3]
def baseStart_6793979 : Nat := 118140960795 + 6793979 * 2 ^ 59
def prefixEnd_6793979 : Nat := 4983230072969 + 3 ^ 40 * 6793979 * 2
def baseEnd_6793979 : Nat := 3488576783552779259617565

theorem tailTrace_6793979 : CollatzResearch.WordTrace tailWord_6793979 prefixEnd_6793979 3488576783552779259617565 := by
  unfold tailWord_6793979
  simp only [CollatzResearch.WordTrace]
  refine ⟨247796771453581877080576991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165197847635721251387051327 247796771453581877080576991)
  ·
    refine ⟨371695157180372815620865487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247796771453581877080576991 371695157180372815620865487)
    ·
      refine ⟨557542735770559223431298231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371695157180372815620865487 557542735770559223431298231)
      ·
        refine ⟨836314103655838835146947347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557542735770559223431298231 836314103655838835146947347)
        ·
          refine ⟨1254471155483758252720421021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836314103655838835146947347 1254471155483758252720421021)
          ·
            refine ⟨470426683306409344770157883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1254471155483758252720421021 470426683306409344770157883)
            ·
              refine ⟨705640024959614017155236825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470426683306409344770157883 705640024959614017155236825)
              ·
                refine ⟨529230018719710512866427619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705640024959614017155236825 529230018719710512866427619)
                ·
                  refine ⟨793845028079565769299641429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 529230018719710512866427619 793845028079565769299641429)
                  ·
                    refine ⟨9302871422807411358980173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 793845028079565769299641429 9302871422807411358980173)
                    ·
                      refine ⟨3488576783552779259617565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9302871422807411358980173 3488576783552779259617565)
                      ·
                        rfl

theorem cell23_6793979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 3].length) (baseStart_6793979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793979 prefixEnd_6793979 := by exact prefixLift 6793979
  have htrace : WordTrace (prefixWord ++ tailWord_6793979) baseStart_6793979 baseEnd_6793979 := by
    simpa [prefixWord, tailWord_6793979, baseEnd_6793979] using wordTrace_append hprefix tailTrace_6793979
  have hstable : (prefixWord ++ tailWord_6793979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793979).length < 2 ^ (prefixWord ++ tailWord_6793979).sum := by decide
  have hdescent : baseEnd_6793979 < baseStart_6793979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793996 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 3, 2, 3]
def baseStart_6793996 : Nat := 118140960795 + 6793996 * 2 ^ 59
def prefixEnd_6793996 : Nat := 4983230072969 + 3 ^ 40 * 6793996 * 2
def baseEnd_6793996 : Nat := 3488585512723905693104987

theorem tailTrace_6793996 : CollatzResearch.WordTrace tailWord_6793996 prefixEnd_6793996 3488585512723905693104987 := by
  unfold tailWord_6793996
  simp only [CollatzResearch.WordTrace]
  refine ⟨123898695747260144491972921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165198260996346859322630561 123898695747260144491972921)
  ·
    refine ⟨92924021810445108368979691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123898695747260144491972921 92924021810445108368979691)
    ·
      refine ⟨139386032715667662553469537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92924021810445108368979691 139386032715667662553469537)
      ·
        refine ⟨104539524536750746915102153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139386032715667662553469537 104539524536750746915102153)
        ·
          refine ⟨78404643402563060186326615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104539524536750746915102153 78404643402563060186326615)
          ·
            refine ⟨117606965103844590279489923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78404643402563060186326615 117606965103844590279489923)
            ·
              refine ⟨176410447655766885419234885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117606965103844590279489923 176410447655766885419234885)
              ·
                refine ⟨33076958935456291016106541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176410447655766885419234885 33076958935456291016106541)
                ·
                  refine ⟨12403859600796109131039953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33076958935456291016106541 12403859600796109131039953)
                  ·
                    refine ⟨9302894700597081848279965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12403859600796109131039953 9302894700597081848279965)
                    ·
                      refine ⟨3488585512723905693104987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9302894700597081848279965 3488585512723905693104987)
                      ·
                        rfl

theorem cell23_6793996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_6793996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793996 prefixEnd_6793996 := by exact prefixLift 6793996
  have htrace : WordTrace (prefixWord ++ tailWord_6793996) baseStart_6793996 baseEnd_6793996 := by
    simpa [prefixWord, tailWord_6793996, baseEnd_6793996] using wordTrace_append hprefix tailTrace_6793996
  have hstable : (prefixWord ++ tailWord_6793996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793996).length < 2 ^ (prefixWord ++ tailWord_6793996).sum := by decide
  have hdescent : baseEnd_6793996 < baseStart_6793996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6793999 : List Nat := [1, 1, 2, 1, 1, 1, 8, 8]
def baseStart_6793999 : Nat := 118140960795 + 6793999 * 2 ^ 59
def prefixEnd_6793999 : Nat := 4983230072969 + 3 ^ 40 * 6793999 * 2
def baseEnd_6793999 : Nat := 129206927895032191902499

theorem tailTrace_6793999 : CollatzResearch.WordTrace tailWord_6793999 prefixEnd_6793999 129206927895032191902499 := by
  unfold tailWord_6793999
  simp only [CollatzResearch.WordTrace]
  refine ⟨247797500913509420496305051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165198333942339613664203367 247797500913509420496305051)
  ·
    refine ⟨371696251370264130744457577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247797500913509420496305051 371696251370264130744457577)
    ·
      refine ⟨278772188527698098058343183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371696251370264130744457577 278772188527698098058343183)
      ·
        refine ⟨418158282791547147087514775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278772188527698098058343183 418158282791547147087514775)
        ·
          refine ⟨627237424187320720631272163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418158282791547147087514775 627237424187320720631272163)
          ·
            refine ⟨940856136280981080946908245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627237424187320720631272163 940856136280981080946908245)
            ·
              refine ⟨11025657847042747042346581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 940856136280981080946908245 11025657847042747042346581)
              ·
                refine ⟨129206927895032191902499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11025657847042747042346581 129206927895032191902499)
                ·
                  rfl

theorem cell23_6793999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 8].length) (baseStart_6793999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6793999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6793999 prefixEnd_6793999 := by exact prefixLift 6793999
  have htrace : WordTrace (prefixWord ++ tailWord_6793999) baseStart_6793999 baseEnd_6793999 := by
    simpa [prefixWord, tailWord_6793999, baseEnd_6793999] using wordTrace_append hprefix tailTrace_6793999
  have hstable : (prefixWord ++ tailWord_6793999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6793999).length < 2 ^ (prefixWord ++ tailWord_6793999).sum := by decide
  have hdescent : baseEnd_6793999 < baseStart_6793999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6793999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794030 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_6794030 : Nat := 118140960795 + 6794030 * 2 ^ 59
def prefixEnd_6794030 : Nat := 4983230072969 + 3 ^ 40 * 6794030 * 2
def baseEnd_6794030 : Nat := 3488602971066158560079831

theorem tailTrace_6794030 : CollatzResearch.WordTrace tailWord_6794030 prefixEnd_6794030 3488602971066158560079831 := by
  unfold tailWord_6794030
  simp only [CollatzResearch.WordTrace]
  refine ⟨30974828947049639098835443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165199087717598075193789029 30974828947049639098835443)
  ·
    refine ⟨46462243420574458648253165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30974828947049639098835443 46462243420574458648253165)
    ·
      refine ⟨17423341282715421993094937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46462243420574458648253165 17423341282715421993094937)
      ·
        refine ⟨13067505962036566494821203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17423341282715421993094937 13067505962036566494821203)
        ·
          refine ⟨19601258943054849742231805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13067505962036566494821203 19601258943054849742231805)
          ·
            refine ⟨7350472103645568653336927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19601258943054849742231805 7350472103645568653336927)
            ·
              refine ⟨11025708155468352980005391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7350472103645568653336927 11025708155468352980005391)
              ·
                refine ⟨16538562233202529470008087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11025708155468352980005391 16538562233202529470008087)
                ·
                  refine ⟨24807843349803794205012131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16538562233202529470008087 24807843349803794205012131)
                  ·
                    refine ⟨37211765024705691307518197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24807843349803794205012131 37211765024705691307518197)
                    ·
                      refine ⟨3488602971066158560079831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37211765024705691307518197 3488602971066158560079831)
                      ·
                        rfl

theorem cell23_6794030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_6794030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794030 prefixEnd_6794030 := by exact prefixLift 6794030
  have htrace : WordTrace (prefixWord ++ tailWord_6794030) baseStart_6794030 baseEnd_6794030 := by
    simpa [prefixWord, tailWord_6794030, baseEnd_6794030] using wordTrace_append hprefix tailTrace_6794030
  have hstable : (prefixWord ++ tailWord_6794030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794030).length < 2 ^ (prefixWord ++ tailWord_6794030).sum := by decide
  have hdescent : baseEnd_6794030 < baseStart_6794030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794038 : List Nat := [5, 1, 2, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_6794038 : Nat := 118140960795 + 6794038 * 2 ^ 59
def prefixEnd_6794038 : Nat := 4983230072969 + 3 ^ 40 * 6794038 * 2
def baseEnd_6794038 : Nat := 3488607078911394528779795

theorem tailTrace_6794038 : CollatzResearch.WordTrace tailWord_6794038 prefixEnd_6794038 3488607078911394528779795 := by
  unfold tailWord_6794038
  simp only [CollatzResearch.WordTrace]
  refine ⟨15487432710023008134810923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165199282240245420104649845 15487432710023008134810923)
  ·
    refine ⟨23231149065034512202216385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15487432710023008134810923 23231149065034512202216385)
    ·
      refine ⟨17423361798775884151662289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23231149065034512202216385 17423361798775884151662289)
      ·
        refine ⟨13067521349081913113746717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17423361798775884151662289 13067521349081913113746717)
        ·
          refine ⟨4900320505905717417655019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13067521349081913113746717 4900320505905717417655019)
          ·
            refine ⟨7350480758858576126482529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4900320505905717417655019 7350480758858576126482529)
            ·
              refine ⟨5512860569143932094861897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7350480758858576126482529 5512860569143932094861897)
              ·
                refine ⟨4134645426857949071146423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5512860569143932094861897 4134645426857949071146423)
                ·
                  refine ⟨6201968140286923606719635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4134645426857949071146423 6201968140286923606719635)
                  ·
                    refine ⟨9302952210430385410079453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6201968140286923606719635 9302952210430385410079453)
                    ·
                      refine ⟨3488607078911394528779795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9302952210430385410079453 3488607078911394528779795)
                      ·
                        rfl

theorem cell23_6794038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_6794038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794038 prefixEnd_6794038 := by exact prefixLift 6794038
  have htrace : WordTrace (prefixWord ++ tailWord_6794038) baseStart_6794038 baseEnd_6794038 := by
    simpa [prefixWord, tailWord_6794038, baseEnd_6794038] using wordTrace_append hprefix tailTrace_6794038
  have hstable : (prefixWord ++ tailWord_6794038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794038).length < 2 ^ (prefixWord ++ tailWord_6794038).sum := by decide
  have hdescent : baseEnd_6794038 < baseStart_6794038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794060 : List Nat := [2, 2, 1, 3, 3, 1, 2, 3, 2, 1, 3]
def baseStart_6794060 : Nat := 118140960795 + 6794060 * 2 ^ 59
def prefixEnd_6794060 : Nat := 4983230072969 + 3 ^ 40 * 6794060 * 2
def baseEnd_6794060 : Nat := 3488618375485793442704693

theorem tailTrace_6794060 : CollatzResearch.WordTrace tailWord_6794060 prefixEnd_6794060 3488618375485793442704693 := by
  unfold tailWord_6794060
  simp only [CollatzResearch.WordTrace]
  refine ⟨123899862883144213957137817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165199817177525618609517089 123899862883144213957137817)
  ·
    refine ⟨92924897162358160467853363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123899862883144213957137817 92924897162358160467853363)
    ·
      refine ⟨139387345743537240701780045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92924897162358160467853363 139387345743537240701780045)
      ·
        refine ⟨52270254653826465263167517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139387345743537240701780045 52270254653826465263167517)
        ·
          refine ⟨19601345495184924473687819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52270254653826465263167517 19601345495184924473687819)
          ·
            refine ⟨29402018242777386710531729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19601345495184924473687819 29402018242777386710531729)
            ·
              refine ⟨22051513682083040032898797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29402018242777386710531729 22051513682083040032898797)
              ·
                refine ⟨8269317630781140012337049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22051513682083040032898797 8269317630781140012337049)
                ·
                  refine ⟨6201988223085855009252787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8269317630781140012337049 6201988223085855009252787)
                  ·
                    refine ⟨9302982334628782513879181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6201988223085855009252787 9302982334628782513879181)
                    ·
                      refine ⟨3488618375485793442704693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9302982334628782513879181 3488618375485793442704693)
                      ·
                        rfl

theorem cell23_6794060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_6794060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794060 prefixEnd_6794060 := by exact prefixLift 6794060
  have htrace : WordTrace (prefixWord ++ tailWord_6794060) baseStart_6794060 baseEnd_6794060 := by
    simpa [prefixWord, tailWord_6794060, baseEnd_6794060] using wordTrace_append hprefix tailTrace_6794060
  have hstable : (prefixWord ++ tailWord_6794060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794060).length < 2 ^ (prefixWord ++ tailWord_6794060).sum := by decide
  have hdescent : baseEnd_6794060 < baseStart_6794060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794066 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_6794066 : Nat := 118140960795 + 6794066 * 2 ^ 59
def prefixEnd_6794066 : Nat := 4983230072969 + 3 ^ 40 * 6794066 * 2
def baseEnd_6794066 : Nat := 3488621456369720419229665

theorem tailTrace_6794066 : CollatzResearch.WordTrace tailWord_6794066 prefixEnd_6794066 3488621456369720419229665 := by
  unfold tailWord_6794066
  simp only [CollatzResearch.WordTrace]
  refine ⟨61949986151066672734748513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165199963069511127292662701 61949986151066672734748513)
  ·
    refine ⟨46462489613300004551061385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61949986151066672734748513 46462489613300004551061385)
    ·
      refine ⟨34846867209975003413296039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46462489613300004551061385 34846867209975003413296039)
      ·
        refine ⟨52270300814962505119944059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34846867209975003413296039 52270300814962505119944059)
        ·
          refine ⟨78405451222443757679916089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52270300814962505119944059 78405451222443757679916089)
          ·
            refine ⟨58804088416832818259937067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78405451222443757679916089 58804088416832818259937067)
            ·
              refine ⟨88206132625249227389905601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58804088416832818259937067 88206132625249227389905601)
              ·
                refine ⟨66154599468936920542429201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88206132625249227389905601 66154599468936920542429201)
                ·
                  refine ⟨49615949601702690406821901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66154599468936920542429201 49615949601702690406821901)
                  ·
                    refine ⟨18605981100638508902558213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49615949601702690406821901 18605981100638508902558213)
                    ·
                      refine ⟨3488621456369720419229665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18605981100638508902558213 3488621456369720419229665)
                      ·
                        rfl

theorem cell23_6794066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_6794066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794066 prefixEnd_6794066 := by exact prefixLift 6794066
  have htrace : WordTrace (prefixWord ++ tailWord_6794066) baseStart_6794066 baseEnd_6794066 := by
    simpa [prefixWord, tailWord_6794066, baseEnd_6794066] using wordTrace_append hprefix tailTrace_6794066
  have hstable : (prefixWord ++ tailWord_6794066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794066).length < 2 ^ (prefixWord ++ tailWord_6794066).sum := by decide
  have hdescent : baseEnd_6794066 < baseStart_6794066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794087 : List Nat := [1, 1, 5, 1, 2, 2, 4, 1, 1, 3, 2]
def baseStart_6794087 : Nat := 118140960795 + 6794087 * 2 ^ 59
def prefixEnd_6794087 : Nat := 4983230072969 + 3 ^ 40 * 6794087 * 2
def baseEnd_6794087 : Nat := 3488632239463464837067069

theorem tailTrace_6794087 : CollatzResearch.WordTrace tailWord_6794087 prefixEnd_6794087 3488632239463464837067069 := by
  unfold tailWord_6794087
  simp only [CollatzResearch.WordTrace]
  refine ⟨247800710537190611525508515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165200473691460407683672343 247800710537190611525508515)
  ·
    refine ⟨371701065805785917288262773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247800710537190611525508515 371701065805785917288262773)
    ·
      refine ⟨34846974919292429745774635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 371701065805785917288262773 34846974919292429745774635)
      ·
        refine ⟨52270462378938644618661953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34846974919292429745774635 52270462378938644618661953)
        ·
          refine ⟨39202846784203983463996465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52270462378938644618661953 39202846784203983463996465)
          ·
            refine ⟨29402135088152987597997349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39202846784203983463996465 29402135088152987597997349)
            ·
              refine ⟨5512900329028685174624503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29402135088152987597997349 5512900329028685174624503)
              ·
                refine ⟨8269350493543027761936755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5512900329028685174624503 8269350493543027761936755)
                ·
                  refine ⟨12404025740314541642905133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8269350493543027761936755 12404025740314541642905133)
                  ·
                    refine ⟨4651509652617953116089425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12404025740314541642905133 4651509652617953116089425)
                    ·
                      refine ⟨3488632239463464837067069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4651509652617953116089425 3488632239463464837067069)
                      ·
                        rfl

theorem cell23_6794087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_6794087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794087 prefixEnd_6794087 := by exact prefixLift 6794087
  have htrace : WordTrace (prefixWord ++ tailWord_6794087) baseStart_6794087 baseEnd_6794087 := by
    simpa [prefixWord, tailWord_6794087, baseEnd_6794087] using wordTrace_append hprefix tailTrace_6794087
  have hstable : (prefixWord ++ tailWord_6794087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794087).length < 2 ^ (prefixWord ++ tailWord_6794087).sum := by decide
  have hdescent : baseEnd_6794087 < baseStart_6794087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794094 : List Nat := [4, 1, 2, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_6794094 : Nat := 118140960795 + 6794094 * 2 ^ 59
def prefixEnd_6794094 : Nat := 4983230072969 + 3 ^ 40 * 6794094 * 2
def baseEnd_6794094 : Nat := 3488635833828046309679537

theorem tailTrace_6794094 : CollatzResearch.WordTrace tailWord_6794094 prefixEnd_6794094 3488635833828046309679537 := by
  unfold tailWord_6794094
  simp only [CollatzResearch.WordTrace]
  refine ⟨30975120731020656465126667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165200643898776834480675557 30975120731020656465126667)
  ·
    refine ⟨46462681096530984697690001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30975120731020656465126667 46462681096530984697690001)
    ·
      refine ⟨34847010822398238523267501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46462681096530984697690001 34847010822398238523267501)
      ·
        refine ⟨13067629058399339446225313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34847010822398238523267501 13067629058399339446225313)
        ·
          refine ⟨9800721793799504584668985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13067629058399339446225313 9800721793799504584668985)
          ·
            refine ⟨7350541345349628438501739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9800721793799504584668985 7350541345349628438501739)
            ·
              refine ⟨11025812018024442657752609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7350541345349628438501739 11025812018024442657752609)
              ·
                refine ⟨8269359013518331993314457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11025812018024442657752609 8269359013518331993314457)
                ·
                  refine ⟨6202019260138748994985843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8269359013518331993314457 6202019260138748994985843)
                  ·
                    refine ⟨9303028890208123492478765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6202019260138748994985843 9303028890208123492478765)
                    ·
                      refine ⟨3488635833828046309679537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9303028890208123492478765 3488635833828046309679537)
                      ·
                        rfl

theorem cell23_6794094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_6794094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794094 prefixEnd_6794094 := by exact prefixLift 6794094
  have htrace : WordTrace (prefixWord ++ tailWord_6794094) baseStart_6794094 baseEnd_6794094 := by
    simpa [prefixWord, tailWord_6794094, baseEnd_6794094] using wordTrace_append hprefix tailTrace_6794094
  have hstable : (prefixWord ++ tailWord_6794094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794094).length < 2 ^ (prefixWord ++ tailWord_6794094).sum := by decide
  have hdescent : baseEnd_6794094 < baseStart_6794094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794096 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 4]
def baseStart_6794096 : Nat := 118140960795 + 6794096 * 2 ^ 59
def prefixEnd_6794096 : Nat := 4983230072969 + 3 ^ 40 * 6794096 * 2
def baseEnd_6794096 : Nat := 3488636860789355301854527

theorem tailTrace_6794096 : CollatzResearch.WordTrace tailWord_6794096 prefixEnd_6794096 3488636860789355301854527 := by
  unfold tailWord_6794096
  simp only [CollatzResearch.WordTrace]
  refine ⟨123900519397079003031293071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165200692529438670708390761 123900519397079003031293071)
  ·
    refine ⟨185850779095618504546939607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123900519397079003031293071 185850779095618504546939607)
    ·
      refine ⟨278776168643427756820409411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185850779095618504546939607 278776168643427756820409411)
      ·
        refine ⟨418164252965141635230614117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278776168643427756820409411 418164252965141635230614117)
        ·
          refine ⟨78405797430964056605740147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 418164252965141635230614117 78405797430964056605740147)
          ·
            refine ⟨117608696146446084908610221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78405797430964056605740147 117608696146446084908610221)
            ·
              refine ⟨44103261054917281840728833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117608696146446084908610221 44103261054917281840728833)
              ·
                refine ⟨33077445791187961380546625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44103261054917281840728833 33077445791187961380546625)
                ·
                  refine ⟨24808084343390971035409969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33077445791187961380546625 24808084343390971035409969)
                  ·
                    refine ⟨18606063257543228276557477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24808084343390971035409969 18606063257543228276557477)
                    ·
                      refine ⟨3488636860789355301854527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18606063257543228276557477 3488636860789355301854527)
                      ·
                        rfl

theorem cell23_6794096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_6794096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794096 prefixEnd_6794096 := by exact prefixLift 6794096
  have htrace : WordTrace (prefixWord ++ tailWord_6794096) baseStart_6794096 baseEnd_6794096 := by
    simpa [prefixWord, tailWord_6794096, baseEnd_6794096] using wordTrace_append hprefix tailTrace_6794096
  have hstable : (prefixWord ++ tailWord_6794096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794096).length < 2 ^ (prefixWord ++ tailWord_6794096).sum := by decide
  have hdescent : baseEnd_6794096 < baseStart_6794096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794157 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 7]
def baseStart_6794157 : Nat := 118140960795 + 6794157 * 2 ^ 59
def prefixEnd_6794157 : Nat := 4983230072969 + 3 ^ 40 * 6794157 * 2
def baseEnd_6794157 : Nat := 387629798123253284799083

theorem tailTrace_6794157 : CollatzResearch.WordTrace tailWord_6794157 prefixEnd_6794157 387629798123253284799083 := by
  unfold tailWord_6794157
  simp only [CollatzResearch.WordTrace]
  refine ⟨247803263646937013480556725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165202175764624675653704483 247803263646937013480556725)
  ·
    refine ⟨23231555966900345013802193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247803263646937013480556725 23231555966900345013802193)
    ·
      refine ⟨17423666975175258760351645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23231555966900345013802193 17423666975175258760351645)
      ·
        refine ⟨6533875115690722035131867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17423666975175258760351645 6533875115690722035131867)
        ·
          refine ⟨9800812673536083052697801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6533875115690722035131867 9800812673536083052697801)
          ·
            refine ⟨7350609505152062289523351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9800812673536083052697801 7350609505152062289523351)
            ·
              refine ⟨11025914257728093434285027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7350609505152062289523351 11025914257728093434285027)
              ·
                refine ⟨16538871386592140151427541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11025914257728093434285027 16538871386592140151427541)
                ·
                  refine ⟨387629798123253284799083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16538871386592140151427541 387629798123253284799083)
                  ·
                    rfl

theorem cell23_6794157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_6794157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794157 prefixEnd_6794157 := by exact prefixLift 6794157
  have htrace : WordTrace (prefixWord ++ tailWord_6794157) baseStart_6794157 baseEnd_6794157 := by
    simpa [prefixWord, tailWord_6794157, baseEnd_6794157] using wordTrace_append hprefix tailTrace_6794157
  have hstable : (prefixWord ++ tailWord_6794157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794157).length < 2 ^ (prefixWord ++ tailWord_6794157).sum := by decide
  have hdescent : baseEnd_6794157 < baseStart_6794157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794183 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 3, 4]
def baseStart_6794183 : Nat := 118140960795 + 6794183 * 2 ^ 59
def prefixEnd_6794183 : Nat := 4983230072969 + 3 ^ 40 * 6794183 * 2
def baseEnd_6794183 : Nat := 1162893844535432153822209

theorem tailTrace_6794183 : CollatzResearch.WordTrace tailWord_6794183 prefixEnd_6794183 1162893844535432153822209 := by
  unfold tailWord_6794183
  simp only [CollatzResearch.WordTrace]
  refine ⟨247804211944842819921003203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165202807963228546614002135 247804211944842819921003203)
  ·
    refine ⟨371706317917264229881504805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247804211944842819921003203 371706317917264229881504805)
    ·
      refine ⟨69694934609487043102782151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371706317917264229881504805 69694934609487043102782151)
      ·
        refine ⟨104542401914230564654173227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69694934609487043102782151 104542401914230564654173227)
        ·
          refine ⟨156813602871345846981259841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104542401914230564654173227 156813602871345846981259841)
          ·
            refine ⟨117610202153509385235944881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156813602871345846981259841 117610202153509385235944881)
            ·
              refine ⟨88207651615132038926958661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117610202153509385235944881 88207651615132038926958661)
              ·
                refine ⟨16538934677837257298804749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88207651615132038926958661 16538934677837257298804749)
                ·
                  refine ⟨6202100504188971487051781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16538934677837257298804749 6202100504188971487051781)
                  ·
                    refine ⟨1162893844535432153822209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6202100504188971487051781 1162893844535432153822209)
                    ·
                      rfl

theorem cell23_6794183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_6794183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794183 prefixEnd_6794183 := by exact prefixLift 6794183
  have htrace : WordTrace (prefixWord ++ tailWord_6794183) baseStart_6794183 baseEnd_6794183 := by
    simpa [prefixWord, tailWord_6794183, baseEnd_6794183] using wordTrace_append hprefix tailTrace_6794183
  have hstable : (prefixWord ++ tailWord_6794183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794183).length < 2 ^ (prefixWord ++ tailWord_6794183).sum := by decide
  have hdescent : baseEnd_6794183 < baseStart_6794183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794186 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_6794186 : Nat := 118140960795 + 6794186 * 2 ^ 59
def prefixEnd_6794186 : Nat := 4983230072969 + 3 ^ 40 * 6794186 * 2
def baseEnd_6794186 : Nat := 3488683074048259949729113

theorem tailTrace_6794186 : CollatzResearch.WordTrace tailWord_6794186 prefixEnd_6794186 3488683074048259949729113 := by
  unfold tailWord_6794186
  simp only [CollatzResearch.WordTrace]
  refine ⟨61951080340957987858340603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165202880909221300955574941 61951080340957987858340603)
  ·
    refine ⟨92926620511436981787510905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61951080340957987858340603 92926620511436981787510905)
    ·
      refine ⟨69694965383577736340633179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92926620511436981787510905 69694965383577736340633179)
      ·
        refine ⟨104542448075366604510949769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69694965383577736340633179 104542448075366604510949769)
        ·
          refine ⟨78406836056524953383212327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104542448075366604510949769 78406836056524953383212327)
          ·
            refine ⟨117610254084787430074818491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78406836056524953383212327 117610254084787430074818491)
            ·
              refine ⟨176415381127181145112227737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117610254084787430074818491 176415381127181145112227737)
              ·
                refine ⟨132311535845385858834170803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176415381127181145112227737 132311535845385858834170803)
                ·
                  refine ⟨198467303768078788251256205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132311535845385858834170803 198467303768078788251256205)
                  ·
                    refine ⟨74425238913029545594221077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 198467303768078788251256205 74425238913029545594221077)
                    ·
                      refine ⟨3488683074048259949729113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74425238913029545594221077 3488683074048259949729113)
                      ·
                        rfl

theorem cell23_6794186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_6794186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794186 prefixEnd_6794186 := by exact prefixLift 6794186
  have htrace : WordTrace (prefixWord ++ tailWord_6794186) baseStart_6794186 baseEnd_6794186 := by
    simpa [prefixWord, tailWord_6794186, baseEnd_6794186] using wordTrace_append hprefix tailTrace_6794186
  have hstable : (prefixWord ++ tailWord_6794186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794186).length < 2 ^ (prefixWord ++ tailWord_6794186).sum := by decide
  have hdescent : baseEnd_6794186 < baseStart_6794186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
