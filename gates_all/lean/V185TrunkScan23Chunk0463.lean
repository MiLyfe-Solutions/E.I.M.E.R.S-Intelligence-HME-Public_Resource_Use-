import V185TrunkScan23Chunk0462

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2739036 : List Nat := [2, 2, 4, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_2739036 : Nat := 118140960795 + 2739036 * 2 ^ 59
def prefixEnd_2739036 : Nat := 4983230072969 + 3 ^ 40 * 2739036 * 2
def baseEnd_2739036 : Nat := 1406441997968450742753409

theorem tailTrace_2739036 : CollatzResearch.WordTrace tailWord_2739036 prefixEnd_2739036 1406441997968450742753409 := by
  unfold tailWord_2739036
  simp only [CollatzResearch.WordTrace]
  refine ⟨49950425052473918475618481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66600566736631891300824641 49950425052473918475618481)
  ·
    refine ⟨37462818789355438856713861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49950425052473918475618481 37462818789355438856713861)
    ·
      refine ⟨7024278523004144785633849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37462818789355438856713861 7024278523004144785633849)
      ·
        refine ⟨5268208892253108589225387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7024278523004144785633849 5268208892253108589225387)
        ·
          refine ⟨7902313338379662883838081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5268208892253108589225387 7902313338379662883838081)
          ·
            refine ⟨5926735003784747162878561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7902313338379662883838081 5926735003784747162878561)
            ·
              refine ⟨4445051252838560372158921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5926735003784747162878561 4445051252838560372158921)
              ·
                refine ⟨3333788439628920279119191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4445051252838560372158921 3333788439628920279119191)
                ·
                  refine ⟨5000682659443380418678787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3333788439628920279119191 5000682659443380418678787)
                  ·
                    refine ⟨7501023989165070628018181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5000682659443380418678787 7501023989165070628018181)
                    ·
                      refine ⟨1406441997968450742753409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7501023989165070628018181 1406441997968450742753409)
                      ·
                        rfl

theorem cell23_2739036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_2739036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739036 prefixEnd_2739036 := by exact prefixLift 2739036
  have htrace : WordTrace (prefixWord ++ tailWord_2739036) baseStart_2739036 baseEnd_2739036 := by
    simpa [prefixWord, tailWord_2739036, baseEnd_2739036] using wordTrace_append hprefix tailTrace_2739036
  have hstable : (prefixWord ++ tailWord_2739036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739036).length < 2 ^ (prefixWord ++ tailWord_2739036).sum := by decide
  have hdescent : baseEnd_2739036 < baseStart_2739036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739039 : List Nat := [1, 1, 2, 3, 1, 3, 4, 2, 1, 2, 3]
def baseStart_2739039 : Nat := 118140960795 + 2739039 * 2 ^ 59
def prefixEnd_2739039 : Nat := 4983230072969 + 3 ^ 40 * 2739039 * 2
def baseEnd_2739039 : Nat := 1406443538410414231015895

theorem tailTrace_2739039 : CollatzResearch.WordTrace tailWord_2739039 prefixEnd_2739039 1406443538410414231015895 := by
  unfold tailWord_2739039
  simp only [CollatzResearch.WordTrace]
  refine ⟨99900959523936968463596171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66600639682624645642397447 99900959523936968463596171)
  ·
    refine ⟨149851439285905452695394257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99900959523936968463596171 149851439285905452695394257)
    ·
      refine ⟨112388579464429089521545693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149851439285905452695394257 112388579464429089521545693)
      ·
        refine ⟨42145717299160908570579635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112388579464429089521545693 42145717299160908570579635)
        ·
          refine ⟨63218575948741362855869453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42145717299160908570579635 63218575948741362855869453)
          ·
            refine ⟨23706965980778011070951045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63218575948741362855869453 23706965980778011070951045)
            ·
              refine ⟨4445056121395877075803321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23706965980778011070951045 4445056121395877075803321)
              ·
                refine ⟨3333792091046907806852491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4445056121395877075803321 3333792091046907806852491)
                ·
                  refine ⟨5000688136570361710278737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3333792091046907806852491 5000688136570361710278737)
                  ·
                    refine ⟨3750516102427771282709053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5000688136570361710278737 3750516102427771282709053)
                    ·
                      refine ⟨1406443538410414231015895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3750516102427771282709053 1406443538410414231015895)
                      ·
                        rfl

theorem cell23_2739039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_2739039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739039 prefixEnd_2739039 := by exact prefixLift 2739039
  have htrace : WordTrace (prefixWord ++ tailWord_2739039) baseStart_2739039 baseEnd_2739039 := by
    simpa [prefixWord, tailWord_2739039, baseEnd_2739039] using wordTrace_append hprefix tailTrace_2739039
  have hstable : (prefixWord ++ tailWord_2739039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739039).length < 2 ^ (prefixWord ++ tailWord_2739039).sum := by decide
  have hdescent : baseEnd_2739039 < baseStart_2739039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739052 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 3]
def baseStart_2739052 : Nat := 118140960795 + 2739052 * 2 ^ 59
def prefixEnd_2739052 : Nat := 4983230072969 + 3 ^ 40 * 2739052 * 2
def baseEnd_2739052 : Nat := 1406450213658922680153335

theorem tailTrace_2739052 : CollatzResearch.WordTrace tailWord_2739052 prefixEnd_2739052 1406450213658922680153335 := by
  unfold tailWord_2739052
  simp only [CollatzResearch.WordTrace]
  refine ⟨49950716836444935841909705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66600955781926581122546273 49950716836444935841909705)
  ·
    refine ⟨37463037627333701881432279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49950716836444935841909705 37463037627333701881432279)
    ·
      refine ⟨56194556441000552822148419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37463037627333701881432279 56194556441000552822148419)
      ·
        refine ⟨84291834661500829233222629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56194556441000552822148419 84291834661500829233222629)
        ·
          refine ⟨15804718999031405481229243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84291834661500829233222629 15804718999031405481229243)
          ·
            refine ⟨23707078498547108221843865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15804718999031405481229243 23707078498547108221843865)
            ·
              refine ⟨17780308873910331166382899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23707078498547108221843865 17780308873910331166382899)
              ·
                refine ⟨26670463310865496749574349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17780308873910331166382899 26670463310865496749574349)
                ·
                  refine ⟨10001423741574561281090381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26670463310865496749574349 10001423741574561281090381)
                  ·
                    refine ⟨3750533903090460480408893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10001423741574561281090381 3750533903090460480408893)
                    ·
                      refine ⟨1406450213658922680153335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3750533903090460480408893 1406450213658922680153335)
                      ·
                        rfl

theorem cell23_2739052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_2739052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739052 prefixEnd_2739052 := by exact prefixLift 2739052
  have htrace : WordTrace (prefixWord ++ tailWord_2739052) baseStart_2739052 baseEnd_2739052 := by
    simpa [prefixWord, tailWord_2739052, baseEnd_2739052] using wordTrace_append hprefix tailTrace_2739052
  have hstable : (prefixWord ++ tailWord_2739052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739052).length < 2 ^ (prefixWord ++ tailWord_2739052).sum := by decide
  have hdescent : baseEnd_2739052 < baseStart_2739052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739069 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 4, 1, 3]
def baseStart_2739069 : Nat := 118140960795 + 2739069 * 2 ^ 59
def prefixEnd_2739069 : Nat := 4983230072969 + 3 ^ 40 * 2739069 * 2
def baseEnd_2739069 : Nat := 1406458942830049113640757

theorem tailTrace_2739069 : CollatzResearch.WordTrace tailWord_2739069 prefixEnd_2739069 1406458942830049113640757 := by
  unfold tailWord_2739069
  simp only [CollatzResearch.WordTrace]
  refine ⟨99902053713828283587188261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66601369142552189058125507 99902053713828283587188261)
  ·
    refine ⟨18731635071342803172597799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99902053713828283587188261 18731635071342803172597799)
    ·
      refine ⟨28097452607014204758896699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18731635071342803172597799 28097452607014204758896699)
      ·
        refine ⟨42146178910521307138345049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28097452607014204758896699 42146178910521307138345049)
        ·
          refine ⟨31609634182890980353758787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42146178910521307138345049 31609634182890980353758787)
          ·
            refine ⟨47414451274336470530638181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31609634182890980353758787 47414451274336470530638181)
            ·
              refine ⟨8890209613938088224494659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47414451274336470530638181 8890209613938088224494659)
              ·
                refine ⟨13335314420907132336741989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8890209613938088224494659 13335314420907132336741989)
                ·
                  refine ⟨2500371453920087313139123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13335314420907132336741989 2500371453920087313139123)
                  ·
                    refine ⟨3750557180880130969708685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2500371453920087313139123 3750557180880130969708685)
                    ·
                      refine ⟨1406458942830049113640757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3750557180880130969708685 1406458942830049113640757)
                      ·
                        rfl

theorem cell23_2739069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_2739069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739069 prefixEnd_2739069 := by exact prefixLift 2739069
  have htrace : WordTrace (prefixWord ++ tailWord_2739069) baseStart_2739069 baseEnd_2739069 := by
    simpa [prefixWord, tailWord_2739069, baseEnd_2739069] using wordTrace_append hprefix tailTrace_2739069
  have hstable : (prefixWord ++ tailWord_2739069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739069).length < 2 ^ (prefixWord ++ tailWord_2739069).sum := by decide
  have hdescent : baseEnd_2739069 < baseStart_2739069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739090 : List Nat := [3, 2, 3, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_2739090 : Nat := 118140960795 + 2739090 * 2 ^ 59
def prefixEnd_2739090 : Nat := 4983230072969 + 3 ^ 40 * 2739090 * 2
def baseEnd_2739090 : Nat := 1406469725923793531478161

theorem tailTrace_2739090 : CollatzResearch.WordTrace tailWord_2739090 prefixEnd_2739090 1406469725923793531478161 := by
  unfold tailWord_2739090
  simp only [CollatzResearch.WordTrace]
  refine ⟨24975704911688051043425681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66601879764501469449135149 24975704911688051043425681)
  ·
    refine ⟨18731778683766038282569261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24975704911688051043425681 18731778683766038282569261)
    ·
      refine ⟨7024417006412264355963473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18731778683766038282569261 7024417006412264355963473)
      ·
        refine ⟨5268312754809198266972605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7024417006412264355963473 5268312754809198266972605)
        ·
          refine ⟨1975617283053449350114727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5268312754809198266972605 1975617283053449350114727)
          ·
            refine ⟨2963425924580174025172091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1975617283053449350114727 2963425924580174025172091)
            ·
              refine ⟨4445138886870261037758137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2963425924580174025172091 4445138886870261037758137)
              ·
                refine ⟨3333854165152695778318603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4445138886870261037758137 3333854165152695778318603)
                ·
                  refine ⟨5000781247729043667477905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3333854165152695778318603 5000781247729043667477905)
                  ·
                    refine ⟨3750585935796782750608429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5000781247729043667477905 3750585935796782750608429)
                    ·
                      refine ⟨1406469725923793531478161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3750585935796782750608429 1406469725923793531478161)
                      ·
                        rfl

theorem cell23_2739090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_2739090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739090 prefixEnd_2739090 := by exact prefixLift 2739090
  have htrace : WordTrace (prefixWord ++ tailWord_2739090) baseStart_2739090 baseEnd_2739090 := by
    simpa [prefixWord, tailWord_2739090, baseEnd_2739090] using wordTrace_append hprefix tailTrace_2739090
  have hstable : (prefixWord ++ tailWord_2739090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739090).length < 2 ^ (prefixWord ++ tailWord_2739090).sum := by decide
  have hdescent : baseEnd_2739090 < baseStart_2739090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739115 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 9]
def baseStart_2739115 : Nat := 118140960795 + 2739115 * 2 ^ 59
def prefixEnd_2739115 : Nat := 4983230072969 + 3 ^ 40 * 2739115 * 2
def baseEnd_2739115 : Nat := 156275840326683992629505

theorem tailTrace_2739115 : CollatzResearch.WordTrace tailWord_2739115 prefixEnd_2739115 156275840326683992629505 := by
  unfold tailWord_2739115
  simp only [CollatzResearch.WordTrace]
  refine ⟨99903731471661633443362799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66602487647774422295575199 99903731471661633443362799)
  ·
    refine ⟨149855597207492450165044199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99903731471661633443362799 149855597207492450165044199)
    ·
      refine ⟨224783395811238675247566299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149855597207492450165044199 224783395811238675247566299)
      ·
        refine ⟨337175093716858012871349449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224783395811238675247566299 337175093716858012871349449)
        ·
          refine ⟨252881320287643509653512087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337175093716858012871349449 252881320287643509653512087)
          ·
            refine ⟨379321980431465264480268131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252881320287643509653512087 379321980431465264480268131)
            ·
              refine ⟨568982970647197896720402197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379321980431465264480268131 568982970647197896720402197)
              ·
                refine ⟨26671076749087401408768853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 568982970647197896720402197 26671076749087401408768853)
                ·
                  refine ⟨156275840326683992629505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26671076749087401408768853 156275840326683992629505)
                  ·
                    rfl

theorem cell23_2739115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 9].length) (baseStart_2739115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739115 prefixEnd_2739115 := by exact prefixLift 2739115
  have htrace : WordTrace (prefixWord ++ tailWord_2739115) baseStart_2739115 baseEnd_2739115 := by
    simpa [prefixWord, tailWord_2739115, baseEnd_2739115] using wordTrace_append hprefix tailTrace_2739115
  have hstable : (prefixWord ++ tailWord_2739115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739115).length < 2 ^ (prefixWord ++ tailWord_2739115).sum := by decide
  have hdescent : baseEnd_2739115 < baseStart_2739115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739172 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_2739172 : Nat := 118140960795 + 2739172 * 2 ^ 59
def prefixEnd_2739172 : Nat := 4983230072969 + 3 ^ 40 * 2739172 * 2
def baseEnd_2739172 : Nat := 1406511831337462210652783

theorem tailTrace_2739172 : CollatzResearch.WordTrace tailWord_2739172 prefixEnd_2739172 1406511831337462210652783 := by
  unfold tailWord_2739172
  simp only [CollatzResearch.WordTrace]
  refine ⟨49952905216227566089093885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66603873621636754785458513 49952905216227566089093885)
  ·
    refine ⟨18732339456085337283410207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49952905216227566089093885 18732339456085337283410207)
    ·
      refine ⟨28098509184128005925115311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18732339456085337283410207 28098509184128005925115311)
      ·
        refine ⟨42147763776192008887672967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28098509184128005925115311 42147763776192008887672967)
        ·
          refine ⟨63221645664288013331509451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42147763776192008887672967 63221645664288013331509451)
          ·
            refine ⟨94832468496432019997264177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63221645664288013331509451 94832468496432019997264177)
            ·
              refine ⟨71124351372324014997948133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94832468496432019997264177 71124351372324014997948133)
              ·
                refine ⟨13335815882310752812115275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71124351372324014997948133 13335815882310752812115275)
                ·
                  refine ⟨20003723823466129218172913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13335815882310752812115275 20003723823466129218172913)
                  ·
                    refine ⟨15002792867599596913629685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20003723823466129218172913 15002792867599596913629685)
                    ·
                      refine ⟨1406511831337462210652783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15002792867599596913629685 1406511831337462210652783)
                      ·
                        rfl

theorem cell23_2739172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_2739172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739172 prefixEnd_2739172 := by exact prefixLift 2739172
  have htrace : WordTrace (prefixWord ++ tailWord_2739172) baseStart_2739172 baseEnd_2739172 := by
    simpa [prefixWord, tailWord_2739172, baseEnd_2739172] using wordTrace_append hprefix tailTrace_2739172
  have hstable : (prefixWord ++ tailWord_2739172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739172).length < 2 ^ (prefixWord ++ tailWord_2739172).sum := by decide
  have hdescent : baseEnd_2739172 < baseStart_2739172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739219 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 3]
def baseStart_2739219 : Nat := 118140960795 + 2739219 * 2 ^ 59
def prefixEnd_2739219 : Nat := 4983230072969 + 3 ^ 40 * 2739219 * 2
def baseEnd_2739219 : Nat := 1406535964928223526765067

theorem tailTrace_2739219 : CollatzResearch.WordTrace tailWord_2739219 prefixEnd_2739219 1406535964928223526765067 := by
  unfold tailWord_2739219
  simp only [CollatzResearch.WordTrace]
  refine ⟨99907524663284859205148711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66605016442189906136765807 99907524663284859205148711)
  ·
    refine ⟨149861286994927288807723067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99907524663284859205148711 149861286994927288807723067)
    ·
      refine ⟨224791930492390933211584601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149861286994927288807723067 224791930492390933211584601)
      ·
        refine ⟨168593947869293199908688451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224791930492390933211584601 168593947869293199908688451)
        ·
          refine ⟨252890921803939799863032677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168593947869293199908688451 252890921803939799863032677)
          ·
            refine ⟨47417047838238712474318627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 252890921803939799863032677 47417047838238712474318627)
            ·
              refine ⟨71125571757358068711477941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47417047838238712474318627 71125571757358068711477941)
              ·
                refine ⟨6668022352252318941701057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71125571757358068711477941 6668022352252318941701057)
                ·
                  refine ⟨5001016764189239206275793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6668022352252318941701057 5001016764189239206275793)
                  ·
                    refine ⟨3750762573141929404706845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5001016764189239206275793 3750762573141929404706845)
                    ·
                      refine ⟨1406535964928223526765067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3750762573141929404706845 1406535964928223526765067)
                      ·
                        rfl

theorem cell23_2739219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 3].length) (baseStart_2739219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739219 prefixEnd_2739219 := by exact prefixLift 2739219
  have htrace : WordTrace (prefixWord ++ tailWord_2739219) baseStart_2739219 baseEnd_2739219 := by
    simpa [prefixWord, tailWord_2739219, baseEnd_2739219] using wordTrace_append hprefix tailTrace_2739219
  have hstable : (prefixWord ++ tailWord_2739219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739219).length < 2 ^ (prefixWord ++ tailWord_2739219).sum := by decide
  have hdescent : baseEnd_2739219 < baseStart_2739219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739236 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 4, 2, 3]
def baseStart_2739236 : Nat := 118140960795 + 2739236 * 2 ^ 59
def prefixEnd_2739236 : Nat := 4983230072969 + 3 ^ 40 * 2739236 * 2
def baseEnd_2739236 : Nat := 1406544694099349960252489

theorem tailTrace_2739236 : CollatzResearch.WordTrace tailWord_2739236 prefixEnd_2739236 1406544694099349960252489 := by
  unfold tailWord_2739236
  simp only [CollatzResearch.WordTrace]
  refine ⟨49954072352111635554258781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66605429802815514072345041 49954072352111635554258781)
  ·
    refine ⟨18732777132041863332847043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49954072352111635554258781 18732777132041863332847043)
    ·
      refine ⟨28099165698062794999270565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18732777132041863332847043 28099165698062794999270565)
      ·
        refine ⟨5268593568386774062363231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28099165698062794999270565 5268593568386774062363231)
        ·
          refine ⟨7902890352580161093544847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5268593568386774062363231 7902890352580161093544847)
          ·
            refine ⟨11854335528870241640317271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7902890352580161093544847 11854335528870241640317271)
            ·
              refine ⟨17781503293305362460475907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11854335528870241640317271 17781503293305362460475907)
              ·
                refine ⟨26672254939958043690713861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17781503293305362460475907 26672254939958043690713861)
                ·
                  refine ⟨5001047801242133192008849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26672254939958043690713861 5001047801242133192008849)
                  ·
                    refine ⟨3750785850931599894006637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5001047801242133192008849 3750785850931599894006637)
                    ·
                      refine ⟨1406544694099349960252489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3750785850931599894006637 1406544694099349960252489)
                      ·
                        rfl

theorem cell23_2739236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_2739236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739236 prefixEnd_2739236 := by exact prefixLift 2739236
  have htrace : WordTrace (prefixWord ++ tailWord_2739236) baseStart_2739236 baseEnd_2739236 := by
    simpa [prefixWord, tailWord_2739236, baseEnd_2739236] using wordTrace_append hprefix tailTrace_2739236
  have hstable : (prefixWord ++ tailWord_2739236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739236).length < 2 ^ (prefixWord ++ tailWord_2739236).sum := by decide
  have hdescent : baseEnd_2739236 < baseStart_2739236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739243 : List Nat := [1, 1, 1, 1, 2, 1, 9, 2, 1, 4]
def baseStart_2739243 : Nat := 118140960795 + 2739243 * 2 ^ 59
def prefixEnd_2739243 : Nat := 4983230072969 + 3 ^ 40 * 2739243 * 2
def baseEnd_2739243 : Nat := 468849429487977144288319

theorem tailTrace_2739243 : CollatzResearch.WordTrace tailWord_2739243 prefixEnd_2739243 468849429487977144288319 := by
  unfold tailWord_2739243
  simp only [CollatzResearch.WordTrace]
  refine ⟨99908400015197911304022383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66605600010131940869348255 99908400015197911304022383)
  ·
    refine ⟨149862600022796866956033575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99908400015197911304022383 149862600022796866956033575)
    ·
      refine ⟨224793900034195300434050363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149862600022796866956033575 224793900034195300434050363)
      ·
        refine ⟨337190850051292950651075545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224793900034195300434050363 337190850051292950651075545)
        ·
          refine ⟨252893137538469712988306659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337190850051292950651075545 252893137538469712988306659)
          ·
            refine ⟨379339706307704569482459989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252893137538469712988306659 379339706307704569482459989)
            ·
              refine ⟨2222693591646706461811289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 379339706307704569482459989 2222693591646706461811289)
              ·
                refine ⟨1667020193735029846358467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2222693591646706461811289 1667020193735029846358467)
                ·
                  refine ⟨2500530290602544769537701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1667020193735029846358467 2500530290602544769537701)
                  ·
                    refine ⟨468849429487977144288319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2500530290602544769537701 468849429487977144288319)
                    ·
                      rfl

theorem cell23_2739243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 1, 4].length) (baseStart_2739243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739243 prefixEnd_2739243 := by exact prefixLift 2739243
  have htrace : WordTrace (prefixWord ++ tailWord_2739243) baseStart_2739243 baseEnd_2739243 := by
    simpa [prefixWord, tailWord_2739243, baseEnd_2739243] using wordTrace_append hprefix tailTrace_2739243
  have hstable : (prefixWord ++ tailWord_2739243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739243).length < 2 ^ (prefixWord ++ tailWord_2739243).sum := by decide
  have hdescent : baseEnd_2739243 < baseStart_2739243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739256 : List Nat := [2, 1, 2, 1, 5, 1, 4, 1, 6]
def baseStart_2739256 : Nat := 118140960795 + 2739256 * 2 ^ 59
def prefixEnd_2739256 : Nat := 4983230072969 + 3 ^ 40 * 2739256 * 2
def baseEnd_2739256 : Nat := 156283884856937764666933

theorem tailTrace_2739256 : CollatzResearch.WordTrace tailWord_2739256 prefixEnd_2739256 156283884856937764666933 := by
  unfold tailWord_2739256
  simp only [CollatzResearch.WordTrace]
  refine ⟨49954437082075407262122811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66605916109433876349497081 49954437082075407262122811)
  ·
    refine ⟨74931655623113110893184217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49954437082075407262122811 74931655623113110893184217)
    ·
      refine ⟨56198741717334833169888163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74931655623113110893184217 56198741717334833169888163)
      ·
        refine ⟨84298112576002249754832245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56198741717334833169888163 84298112576002249754832245)
        ·
          refine ⟨7902948054000210914515523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84298112576002249754832245 7902948054000210914515523)
          ·
            refine ⟨11854422081000316371773285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7902948054000210914515523 11854422081000316371773285)
            ·
              refine ⟨2222704140187559319707491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11854422081000316371773285 2222704140187559319707491)
              ·
                refine ⟨3334056210281338979561237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2222704140187559319707491 3334056210281338979561237)
                ·
                  refine ⟨156283884856937764666933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3334056210281338979561237 156283884856937764666933)
                  ·
                    rfl

theorem cell23_2739256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 6].length) (baseStart_2739256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739256 prefixEnd_2739256 := by exact prefixLift 2739256
  have htrace : WordTrace (prefixWord ++ tailWord_2739256) baseStart_2739256 baseEnd_2739256 := by
    simpa [prefixWord, tailWord_2739256, baseEnd_2739256] using wordTrace_append hprefix tailTrace_2739256
  have hstable : (prefixWord ++ tailWord_2739256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739256).length < 2 ^ (prefixWord ++ tailWord_2739256).sum := by decide
  have hdescent : baseEnd_2739256 < baseStart_2739256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739270 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_2739270 : Nat := 118140960795 + 2739270 * 2 ^ 59
def prefixEnd_2739270 : Nat := 4983230072969 + 3 ^ 40 * 2739270 * 2
def baseEnd_2739270 : Nat := 1406562152441602827227333

theorem tailTrace_2739270 : CollatzResearch.WordTrace tailWord_2739270 prefixEnd_2739270 1406562152441602827227333 := by
  unfold tailWord_2739270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3122168274565627966101727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66606256524066729943503509 3122168274565627966101727)
  ·
    refine ⟨4683252411848441949152591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3122168274565627966101727 4683252411848441949152591)
    ·
      refine ⟨7024878617772662923728887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4683252411848441949152591 7024878617772662923728887)
      ·
        refine ⟨10537317926658994385593331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7024878617772662923728887 10537317926658994385593331)
        ·
          refine ⟨15805976889988491578389997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10537317926658994385593331 15805976889988491578389997)
          ·
            refine ⟨5927241333745684341896249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15805976889988491578389997 5927241333745684341896249)
            ·
              refine ⟨4445431000309263256422187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5927241333745684341896249 4445431000309263256422187)
              ·
                refine ⟨6668146500463894884633281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4445431000309263256422187 6668146500463894884633281)
                ·
                  refine ⟨5001109875347921163474961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6668146500463894884633281 5001109875347921163474961)
                  ·
                    refine ⟨3750832406510940872606221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5001109875347921163474961 3750832406510940872606221)
                    ·
                      refine ⟨1406562152441602827227333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3750832406510940872606221 1406562152441602827227333)
                      ·
                        rfl

theorem cell23_2739270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_2739270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739270 prefixEnd_2739270 := by exact prefixLift 2739270
  have htrace : WordTrace (prefixWord ++ tailWord_2739270) baseStart_2739270 baseEnd_2739270 := by
    simpa [prefixWord, tailWord_2739270, baseEnd_2739270] using wordTrace_append hprefix tailTrace_2739270
  have hstable : (prefixWord ++ tailWord_2739270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739270).length < 2 ^ (prefixWord ++ tailWord_2739270).sum := by decide
  have hdescent : baseEnd_2739270 < baseStart_2739270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739294 : List Nat := [4, 4, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_2739294 : Nat := 118140960795 + 2739294 * 2 ^ 59
def prefixEnd_2739294 : Nat := 4983230072969 + 3 ^ 40 * 2739294 * 2
def baseEnd_2739294 : Nat := 468858158659103577775741

theorem tailTrace_2739294 : CollatzResearch.WordTrace tailWord_2739294 prefixEnd_2739294 468858158659103577775741 := by
  unfold tailWord_2739294
  simp only [CollatzResearch.WordTrace]
  refine ⟨12488782517251643376766117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66606840092008764676085957 12488782517251643376766117)
  ·
    refine ⟨2341646721984683133143647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12488782517251643376766117 2341646721984683133143647)
    ·
      refine ⟨3512470082977024699715471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2341646721984683133143647 3512470082977024699715471)
      ·
        refine ⟨5268705124465537049573207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3512470082977024699715471 5268705124465537049573207)
        ·
          refine ⟨7903057686698305574359811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5268705124465537049573207 7903057686698305574359811)
          ·
            refine ⟨11854586530047458361539717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7903057686698305574359811 11854586530047458361539717)
            ·
              refine ⟨2222734974383898442788697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11854586530047458361539717 2222734974383898442788697)
              ·
                refine ⟨1667051230787923832091523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2222734974383898442788697 1667051230787923832091523)
                ·
                  refine ⟨2500576846181885748137285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1667051230787923832091523 2500576846181885748137285)
                  ·
                    refine ⟨468858158659103577775741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2500576846181885748137285 468858158659103577775741)
                    ·
                      rfl

theorem cell23_2739294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_2739294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739294 prefixEnd_2739294 := by exact prefixLift 2739294
  have htrace : WordTrace (prefixWord ++ tailWord_2739294) baseStart_2739294 baseEnd_2739294 := by
    simpa [prefixWord, tailWord_2739294, baseEnd_2739294] using wordTrace_append hprefix tailTrace_2739294
  have hstable : (prefixWord ++ tailWord_2739294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739294).length < 2 ^ (prefixWord ++ tailWord_2739294).sum := by decide
  have hdescent : baseEnd_2739294 < baseStart_2739294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739306 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_2739306 : Nat := 118140960795 + 2739306 * 2 ^ 59
def prefixEnd_2739306 : Nat := 4983230072969 + 3 ^ 40 * 2739306 * 2
def baseEnd_2739306 : Nat := 1406580637745164686377167

theorem tailTrace_2739306 : CollatzResearch.WordTrace tailWord_2739306 prefixEnd_2739306 1406580637745164686377167 := by
  unfold tailWord_2739306
  simp only [CollatzResearch.WordTrace]
  refine ⟨24977674453492418265891443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66607131875979782042377181 24977674453492418265891443)
  ·
    refine ⟨37466511680238627398837165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24977674453492418265891443 37466511680238627398837165)
    ·
      refine ⟨14049941880089485274563937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37466511680238627398837165 14049941880089485274563937)
      ·
        refine ⟨10537456410067113955922953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14049941880089485274563937 10537456410067113955922953)
        ·
          refine ⟨7903092307550335466942215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10537456410067113955922953 7903092307550335466942215)
          ·
            refine ⟨11854638461325503200413323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7903092307550335466942215 11854638461325503200413323)
            ·
              refine ⟨17781957691988254800619985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11854638461325503200413323 17781957691988254800619985)
              ·
                refine ⟨13336468268991191100464989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17781957691988254800619985 13336468268991191100464989)
                ·
                  refine ⟨5001175600871696662674371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13336468268991191100464989 5001175600871696662674371)
                  ·
                    refine ⟨7501763401307544994011557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5001175600871696662674371 7501763401307544994011557)
                    ·
                      refine ⟨1406580637745164686377167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7501763401307544994011557 1406580637745164686377167)
                      ·
                        rfl

theorem cell23_2739306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_2739306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739306 prefixEnd_2739306 := by exact prefixLift 2739306
  have htrace : WordTrace (prefixWord ++ tailWord_2739306) baseStart_2739306 baseEnd_2739306 := by
    simpa [prefixWord, tailWord_2739306, baseEnd_2739306] using wordTrace_append hprefix tailTrace_2739306
  have hstable : (prefixWord ++ tailWord_2739306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739306).length < 2 ^ (prefixWord ++ tailWord_2739306).sum := by decide
  have hdescent : baseEnd_2739306 < baseStart_2739306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739370 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_2739370 : Nat := 118140960795 + 2739370 * 2 ^ 59
def prefixEnd_2739370 : Nat := 4983230072969 + 3 ^ 40 * 2739370 * 2
def baseEnd_2739370 : Nat := 1406613500507052435976873

theorem tailTrace_2739370 : CollatzResearch.WordTrace tailWord_2739370 prefixEnd_2739370 1406613500507052435976873 := by
  unfold tailWord_2739370
  simp only [CollatzResearch.WordTrace]
  refine ⟨24978258021434452998473891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66608688057158541329263709 24978258021434452998473891)
  ·
    refine ⟨37467387032151679497710837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24978258021434452998473891 37467387032151679497710837)
    ·
      refine ⟨3512567534264219952910391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37467387032151679497710837 3512567534264219952910391)
      ·
        refine ⟨5268851301396329929365587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3512567534264219952910391 5268851301396329929365587)
        ·
          refine ⟨7903276952094494894048381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5268851301396329929365587 7903276952094494894048381)
          ·
            refine ⟨2963728857035435585268143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7903276952094494894048381 2963728857035435585268143)
            ·
              refine ⟨4445593285553153377902215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2963728857035435585268143 4445593285553153377902215)
              ·
                refine ⟨6668389928329730066853323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4445593285553153377902215 6668389928329730066853323)
                ·
                  refine ⟨10002584892494595100279985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6668389928329730066853323 10002584892494595100279985)
                  ·
                    refine ⟨7501938669370946325209989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10002584892494595100279985 7501938669370946325209989)
                    ·
                      refine ⟨1406613500507052435976873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7501938669370946325209989 1406613500507052435976873)
                      ·
                        rfl

theorem cell23_2739370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_2739370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739370 prefixEnd_2739370 := by exact prefixLift 2739370
  have htrace : WordTrace (prefixWord ++ tailWord_2739370) baseStart_2739370 baseEnd_2739370 := by
    simpa [prefixWord, tailWord_2739370, baseEnd_2739370] using wordTrace_append hprefix tailTrace_2739370
  have hstable : (prefixWord ++ tailWord_2739370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739370).length < 2 ^ (prefixWord ++ tailWord_2739370).sum := by decide
  have hdescent : baseEnd_2739370 < baseStart_2739370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739379 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 4]
def baseStart_2739379 : Nat := 118140960795 + 2739379 * 2 ^ 59
def prefixEnd_2739379 : Nat := 4983230072969 + 3 ^ 40 * 2739379 * 2
def baseEnd_2739379 : Nat := 1406618121832942900764331

theorem tailTrace_2739379 : CollatzResearch.WordTrace tailWord_2739379 prefixEnd_2739379 1406618121832942900764331 := by
  unfold tailWord_2739379
  simp only [CollatzResearch.WordTrace]
  refine ⟨99913360342705206530973191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66608906895136804353982127 99913360342705206530973191)
  ·
    refine ⟨149870040514057809796459787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99913360342705206530973191 149870040514057809796459787)
    ·
      refine ⟨224805060771086714694689681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149870040514057809796459787 224805060771086714694689681)
      ·
        refine ⟨168603795578315036021017261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224805060771086714694689681 168603795578315036021017261)
        ·
          refine ⟨63226423341868138507881473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168603795578315036021017261 63226423341868138507881473)
          ·
            refine ⟨47419817506401103880911105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63226423341868138507881473 47419817506401103880911105)
            ·
              refine ⟨35564863129800827910683329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47419817506401103880911105 35564863129800827910683329)
              ·
                refine ⟨26673647347350620933012497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35564863129800827910683329 26673647347350620933012497)
                ·
                  refine ⟨20005235510512965699759373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26673647347350620933012497 20005235510512965699759373)
                  ·
                    refine ⟨7501963316442362137409765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20005235510512965699759373 7501963316442362137409765)
                    ·
                      refine ⟨1406618121832942900764331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7501963316442362137409765 1406618121832942900764331)
                      ·
                        rfl

theorem cell23_2739379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_2739379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739379 prefixEnd_2739379 := by exact prefixLift 2739379
  have htrace : WordTrace (prefixWord ++ tailWord_2739379) baseStart_2739379 baseEnd_2739379 := by
    simpa [prefixWord, tailWord_2739379, baseEnd_2739379] using wordTrace_append hprefix tailTrace_2739379
  have hstable : (prefixWord ++ tailWord_2739379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739379).length < 2 ^ (prefixWord ++ tailWord_2739379).sum := by decide
  have hdescent : baseEnd_2739379 < baseStart_2739379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739389 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 1, 8]
def baseStart_2739389 : Nat := 118140960795 + 2739389 * 2 ^ 59
def prefixEnd_2739389 : Nat := 4983230072969 + 3 ^ 40 * 2739389 * 2
def baseEnd_2739389 : Nat := 468874418879829287213095

theorem tailTrace_2739389 : CollatzResearch.WordTrace tailWord_2739389 prefixEnd_2739389 468874418879829287213095 := by
  unfold tailWord_2739389
  simp only [CollatzResearch.WordTrace]
  refine ⟨99913725072668978238837221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66609150048445985492558147 99913725072668978238837221)
  ·
    refine ⟨18733823451125433419781979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99913725072668978238837221 18733823451125433419781979)
    ·
      refine ⟨28100735176688150129672969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18733823451125433419781979 28100735176688150129672969)
      ·
        refine ⟨21075551382516112597254727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28100735176688150129672969 21075551382516112597254727)
        ·
          refine ⟨31613327073774168895882091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21075551382516112597254727 31613327073774168895882091)
          ·
            refine ⟨47419990610661253343823137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31613327073774168895882091 47419990610661253343823137)
            ·
              refine ⟨35564992957995940007867353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47419990610661253343823137 35564992957995940007867353)
              ·
                refine ⟨26673744718496955005900515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35564992957995940007867353 26673744718496955005900515)
                ·
                  refine ⟨40010617077745432508850773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26673744718496955005900515 40010617077745432508850773)
                  ·
                    refine ⟨468874418879829287213095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40010617077745432508850773 468874418879829287213095)
                    ·
                      rfl

theorem cell23_2739389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_2739389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739389 prefixEnd_2739389 := by exact prefixLift 2739389
  have htrace : WordTrace (prefixWord ++ tailWord_2739389) baseStart_2739389 baseEnd_2739389 := by
    simpa [prefixWord, tailWord_2739389, baseEnd_2739389] using wordTrace_append hprefix tailTrace_2739389
  have hstable : (prefixWord ++ tailWord_2739389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739389).length < 2 ^ (prefixWord ++ tailWord_2739389).sum := by decide
  have hdescent : baseEnd_2739389 < baseStart_2739389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739470 : List Nat := [4, 1, 1, 2, 1, 3, 4, 2, 5]
def baseStart_2739470 : Nat := 118140960795 + 2739470 * 2 ^ 59
def prefixEnd_2739470 : Nat := 4983230072969 + 3 ^ 40 * 2739470 * 2
def baseEnd_2739470 : Nat := 156296094285833560525157

theorem tailTrace_2739470 : CollatzResearch.WordTrace tailWord_2739470 prefixEnd_2739470 156296094285833560525157 := by
  unfold tailWord_2739470
  simp only [CollatzResearch.WordTrace]
  refine ⟨12489584923171941134066983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66611119590250352715023909 12489584923171941134066983)
  ·
    refine ⟨18734377384757911701100475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12489584923171941134066983 18734377384757911701100475)
    ·
      refine ⟨28101566077136867551650713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18734377384757911701100475 28101566077136867551650713)
      ·
        refine ⟨21076174557852650663738035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28101566077136867551650713 21076174557852650663738035)
        ·
          refine ⟨31614261836778975995607053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21076174557852650663738035 31614261836778975995607053)
          ·
            refine ⟨11855348188792115998352645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31614261836778975995607053 11855348188792115998352645)
            ·
              refine ⟨2222877785398521749691121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11855348188792115998352645 2222877785398521749691121)
              ·
                refine ⟨1667158339048891312268341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2222877785398521749691121 1667158339048891312268341)
                ·
                  refine ⟨156296094285833560525157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1667158339048891312268341 156296094285833560525157)
                  ·
                    rfl

theorem cell23_2739470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_2739470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739470 prefixEnd_2739470 := by exact prefixLift 2739470
  have htrace : WordTrace (prefixWord ++ tailWord_2739470) baseStart_2739470 baseEnd_2739470 := by
    simpa [prefixWord, tailWord_2739470, baseEnd_2739470] using wordTrace_append hprefix tailTrace_2739470
  have hstable : (prefixWord ++ tailWord_2739470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739470).length < 2 ^ (prefixWord ++ tailWord_2739470).sum := by decide
  have hdescent : baseEnd_2739470 < baseStart_2739470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739516 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_2739516 : Nat := 118140960795 + 2739516 * 2 ^ 59
def prefixEnd_2739516 : Nat := 4983230072969 + 3 ^ 40 * 2739516 * 2
def baseEnd_2739516 : Nat := 1406688468682608864751201

theorem tailTrace_2739516 : CollatzResearch.WordTrace tailWord_2739516 prefixEnd_2739516 1406688468682608864751201 := by
  unfold tailWord_2739516
  simp only [CollatzResearch.WordTrace]
  refine ⟨49959178571604439464355201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66612238095472585952473601 49959178571604439464355201)
  ·
    refine ⟨37469383928703329598266401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49959178571604439464355201 37469383928703329598266401)
    ·
      refine ⟨28102037946527497198699801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37469383928703329598266401 28102037946527497198699801)
      ·
        refine ⟨21076528459895622899024851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28102037946527497198699801 21076528459895622899024851)
        ·
          refine ⟨31614792689843434348537277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21076528459895622899024851 31614792689843434348537277)
          ·
            refine ⟨11855547258691287880701479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31614792689843434348537277 11855547258691287880701479)
            ·
              refine ⟨17783320888036931821052219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11855547258691287880701479 17783320888036931821052219)
              ·
                refine ⟨26674981332055397731578329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17783320888036931821052219 26674981332055397731578329)
                ·
                  refine ⟨20006235999041548298683747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26674981332055397731578329 20006235999041548298683747)
                  ·
                    refine ⟨30009353998562322448025621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20006235999041548298683747 30009353998562322448025621)
                    ·
                      refine ⟨1406688468682608864751201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30009353998562322448025621 1406688468682608864751201)
                      ·
                        rfl

theorem cell23_2739516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_2739516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739516 prefixEnd_2739516 := by exact prefixLift 2739516
  have htrace : WordTrace (prefixWord ++ tailWord_2739516) baseStart_2739516 baseEnd_2739516 := by
    simpa [prefixWord, tailWord_2739516, baseEnd_2739516] using wordTrace_append hprefix tailTrace_2739516
  have hstable : (prefixWord ++ tailWord_2739516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739516).length < 2 ^ (prefixWord ++ tailWord_2739516).sum := by decide
  have hdescent : baseEnd_2739516 < baseStart_2739516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739580 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 2, 3, 2]
def baseStart_2739580 : Nat := 118140960795 + 2739580 * 2 ^ 59
def prefixEnd_2739580 : Nat := 4983230072969 + 3 ^ 40 * 2739580 * 2
def baseEnd_2739580 : Nat := 1406721331444496614350907

theorem tailTrace_2739580 : CollatzResearch.WordTrace tailWord_2739580 prefixEnd_2739580 1406721331444496614350907 := by
  unfold tailWord_2739580
  simp only [CollatzResearch.WordTrace]
  refine ⟨49960345707488508929520097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66613794276651345239360129 49960345707488508929520097)
  ·
    refine ⟨37470259280616381697140073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49960345707488508929520097 37470259280616381697140073)
    ·
      refine ⟨28102694460462286272855055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37470259280616381697140073 28102694460462286272855055)
      ·
        refine ⟨42154041690693429409282583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28102694460462286272855055 42154041690693429409282583)
        ·
          refine ⟨63231062536040144113923875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42154041690693429409282583 63231062536040144113923875)
          ·
            refine ⟨94846593804060216170885813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63231062536040144113923875 94846593804060216170885813)
            ·
              refine ⟨8891868169130645266020545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94846593804060216170885813 8891868169130645266020545)
              ·
                refine ⟨6668901126847983949515409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8891868169130645266020545 6668901126847983949515409)
                ·
                  refine ⟨5001675845135987962136557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6668901126847983949515409 5001675845135987962136557)
                  ·
                    refine ⟨1875628441925995485801209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5001675845135987962136557 1875628441925995485801209)
                    ·
                      refine ⟨1406721331444496614350907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1875628441925995485801209 1406721331444496614350907)
                      ·
                        rfl

theorem cell23_2739580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_2739580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739580 prefixEnd_2739580 := by exact prefixLift 2739580
  have htrace : WordTrace (prefixWord ++ tailWord_2739580) baseStart_2739580 baseEnd_2739580 := by
    simpa [prefixWord, tailWord_2739580, baseEnd_2739580] using wordTrace_append hprefix tailTrace_2739580
  have hstable : (prefixWord ++ tailWord_2739580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739580).length < 2 ^ (prefixWord ++ tailWord_2739580).sum := by decide
  have hdescent : baseEnd_2739580 < baseStart_2739580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739587 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 3, 1, 3]
def baseStart_2739587 : Nat := 118140960795 + 2739587 * 2 ^ 59
def prefixEnd_2739587 : Nat := 4983230072969 + 3 ^ 40 * 2739587 * 2
def baseEnd_2739587 : Nat := 1406724925809078086963375

theorem tailTrace_2739587 : CollatzResearch.WordTrace tailWord_2739587 prefixEnd_2739587 1406724925809078086963375 := by
  unfold tailWord_2739587
  simp only [CollatzResearch.WordTrace]
  refine ⟨99920946725951658054545015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66613964483967772036363343 99920946725951658054545015)
  ·
    refine ⟨149881420088927487081817523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99920946725951658054545015 149881420088927487081817523)
    ·
      refine ⟨224822130133391230622726285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149881420088927487081817523 224822130133391230622726285)
      ·
        refine ⟨84308298800021711483522357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224822130133391230622726285 84308298800021711483522357)
        ·
          refine ⟨7903903012502035451580221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84308298800021711483522357 7903903012502035451580221)
          ·
            refine ⟨2963963629688263294342583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7903903012502035451580221 2963963629688263294342583)
            ·
              refine ⟨4445945444532394941513875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2963963629688263294342583 4445945444532394941513875)
              ·
                refine ⟨6668918166798592412270813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4445945444532394941513875 6668918166798592412270813)
                ·
                  refine ⟨2500844312549472154601555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6668918166798592412270813 2500844312549472154601555)
                  ·
                    refine ⟨3751266468824208231902333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2500844312549472154601555 3751266468824208231902333)
                    ·
                      refine ⟨1406724925809078086963375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3751266468824208231902333 1406724925809078086963375)
                      ·
                        rfl

theorem cell23_2739587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 1, 3].length) (baseStart_2739587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739587 prefixEnd_2739587 := by exact prefixLift 2739587
  have htrace : WordTrace (prefixWord ++ tailWord_2739587) baseStart_2739587 baseEnd_2739587 := by
    simpa [prefixWord, tailWord_2739587, baseEnd_2739587] using wordTrace_append hprefix tailTrace_2739587
  have hstable : (prefixWord ++ tailWord_2739587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739587).length < 2 ^ (prefixWord ++ tailWord_2739587).sum := by decide
  have hdescent : baseEnd_2739587 < baseStart_2739587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739616 : List Nat := [2, 1, 1, 4, 1, 2, 1, 11]
def baseStart_2739616 : Nat := 118140960795 + 2739616 * 2 ^ 59
def prefixEnd_2739616 : Nat := 4983230072969 + 3 ^ 40 * 2739616 * 2
def baseEnd_2739616 : Nat := 52101474694372536055583

theorem tailTrace_2739616 : CollatzResearch.WordTrace tailWord_2739616 prefixEnd_2739616 52101474694372536055583 := by
  unfold tailWord_2739616
  simp only [CollatzResearch.WordTrace]
  refine ⟨49961002221423298003675351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66614669628564397338233801 49961002221423298003675351)
  ·
    refine ⟨74941503332134947005513027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49961002221423298003675351 74941503332134947005513027)
    ·
      refine ⟨112412254998202420508269541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74941503332134947005513027 112412254998202420508269541)
      ·
        refine ⟨21077297812162953845300539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112412254998202420508269541 21077297812162953845300539)
        ·
          refine ⟨31615946718244430767950809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21077297812162953845300539 31615946718244430767950809)
          ·
            refine ⟨23711960038683323075963107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31615946718244430767950809 23711960038683323075963107)
            ·
              refine ⟨35567940058024984613944661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23711960038683323075963107 35567940058024984613944661)
              ·
                refine ⟨52101474694372536055583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 35567940058024984613944661 52101474694372536055583)
                ·
                  rfl

theorem cell23_2739616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 11].length) (baseStart_2739616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739616 prefixEnd_2739616 := by exact prefixLift 2739616
  have htrace : WordTrace (prefixWord ++ tailWord_2739616) baseStart_2739616 baseEnd_2739616 := by
    simpa [prefixWord, tailWord_2739616, baseEnd_2739616] using wordTrace_append hprefix tailTrace_2739616
  have hstable : (prefixWord ++ tailWord_2739616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739616).length < 2 ^ (prefixWord ++ tailWord_2739616).sum := by decide
  have hdescent : baseEnd_2739616 < baseStart_2739616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739624 : List Nat := [2, 1, 6, 1, 2, 1, 3, 1, 1, 5]
def baseStart_2739624 : Nat := 118140960795 + 2739624 * 2 ^ 59
def prefixEnd_2739624 : Nat := 4983230072969 + 3 ^ 40 * 2739624 * 2
def baseEnd_2739624 : Nat := 468914641531098147400235

theorem tailTrace_2739624 : CollatzResearch.WordTrace tailWord_2739624 prefixEnd_2739624 468914641531098147400235 := by
  unfold tailWord_2739624
  simp only [CollatzResearch.WordTrace]
  refine ⟨49961148113408806686820963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66614864151211742249094617 49961148113408806686820963)
  ·
    refine ⟨74941722170113210030231445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49961148113408806686820963 74941722170113210030231445)
    ·
      refine ⟨3512893226724056720167099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74941722170113210030231445 3512893226724056720167099)
      ·
        refine ⟨5269339840086085080250649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3512893226724056720167099 5269339840086085080250649)
        ·
          refine ⟨3952004880064563810187987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5269339840086085080250649 3952004880064563810187987)
          ·
            refine ⟨5928007320096845715281981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3952004880064563810187987 5928007320096845715281981)
            ·
              refine ⟨2223002745036317143230743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5928007320096845715281981 2223002745036317143230743)
              ·
                refine ⟨3334504117554475714846115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2223002745036317143230743 3334504117554475714846115)
                ·
                  refine ⟨5001756176331713572269173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334504117554475714846115 5001756176331713572269173)
                  ·
                    refine ⟨468914641531098147400235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5001756176331713572269173 468914641531098147400235)
                    ·
                      rfl

theorem cell23_2739624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_2739624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739624 prefixEnd_2739624 := by exact prefixLift 2739624
  have htrace : WordTrace (prefixWord ++ tailWord_2739624) baseStart_2739624 baseEnd_2739624 := by
    simpa [prefixWord, tailWord_2739624, baseEnd_2739624] using wordTrace_append hprefix tailTrace_2739624
  have hstable : (prefixWord ++ tailWord_2739624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739624).length < 2 ^ (prefixWord ++ tailWord_2739624).sum := by decide
  have hdescent : baseEnd_2739624 < baseStart_2739624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739637 : List Nat := [1, 3, 3, 2, 2, 2, 2, 2, 2, 4]
def baseStart_2739637 : Nat := 118140960795 + 2739637 * 2 ^ 59
def prefixEnd_2739637 : Nat := 4983230072969 + 3 ^ 40 * 2739637 * 2
def baseEnd_2739637 : Nat := 468916866613934297112715

theorem tailTrace_2739637 : CollatzResearch.WordTrace tailWord_2739637 prefixEnd_2739637 468916866613934297112715 := by
  unfold tailWord_2739637
  simp only [CollatzResearch.WordTrace]
  refine ⟨99922770375770516593865165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66615180250513677729243443 99922770375770516593865165)
  ·
    refine ⟨37471038890913943722699437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99922770375770516593865165 37471038890913943722699437)
    ·
      refine ⟨14051639584092728896012289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37471038890913943722699437 14051639584092728896012289)
      ·
        refine ⟨10538729688069546672009217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14051639584092728896012289 10538729688069546672009217)
        ·
          refine ⟨7904047266052160004006913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10538729688069546672009217 7904047266052160004006913)
          ·
            refine ⟨5928035449539120003005185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7904047266052160004006913 5928035449539120003005185)
            ·
              refine ⟨4446026587154340002253889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5928035449539120003005185 4446026587154340002253889)
              ·
                refine ⟨3334519940365755001690417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4446026587154340002253889 3334519940365755001690417)
                ·
                  refine ⟨2500889955274316251267813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3334519940365755001690417 2500889955274316251267813)
                  ·
                    refine ⟨468916866613934297112715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2500889955274316251267813 468916866613934297112715)
                    ·
                      rfl

theorem cell23_2739637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_2739637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739637 prefixEnd_2739637 := by exact prefixLift 2739637
  have htrace : WordTrace (prefixWord ++ tailWord_2739637) baseStart_2739637 baseEnd_2739637 := by
    simpa [prefixWord, tailWord_2739637, baseEnd_2739637] using wordTrace_append hprefix tailTrace_2739637
  have hstable : (prefixWord ++ tailWord_2739637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739637).length < 2 ^ (prefixWord ++ tailWord_2739637).sum := by decide
  have hdescent : baseEnd_2739637 < baseStart_2739637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739660 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 1, 3, 3]
def baseStart_2739660 : Nat := 118140960795 + 2739660 * 2 ^ 59
def prefixEnd_2739660 : Nat := 4983230072969 + 3 ^ 40 * 2739660 * 2
def baseEnd_2739660 : Nat := 1406762409896856301350539

theorem tailTrace_2739660 : CollatzResearch.WordTrace tailWord_2739660 prefixEnd_2739660 1406762409896856301350539 := by
  unfold tailWord_2739660
  simp only [CollatzResearch.WordTrace]
  refine ⟨49961804627343595760976217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66615739503124794347968289 49961804627343595760976217)
  ·
    refine ⟨37471353470507696820732163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49961804627343595760976217 37471353470507696820732163)
    ·
      refine ⟨56207030205761545231098245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37471353470507696820732163 56207030205761545231098245)
      ·
        refine ⟨10538818163580289730830921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56207030205761545231098245 10538818163580289730830921)
        ·
          refine ⟨7904113622685217298123191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10538818163580289730830921 7904113622685217298123191)
          ·
            refine ⟨11856170434027825947184787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7904113622685217298123191 11856170434027825947184787)
            ·
              refine ⟨17784255651041738920777181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11856170434027825947184787 17784255651041738920777181)
              ·
                refine ⟨6669095869140652095291443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17784255651041738920777181 6669095869140652095291443)
                ·
                  refine ⟨10003643803710978142937165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6669095869140652095291443 10003643803710978142937165)
                  ·
                    refine ⟨3751366426391616803601437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10003643803710978142937165 3751366426391616803601437)
                    ·
                      refine ⟨1406762409896856301350539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3751366426391616803601437 1406762409896856301350539)
                      ·
                        rfl

theorem cell23_2739660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_2739660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739660 prefixEnd_2739660 := by exact prefixLift 2739660
  have htrace : WordTrace (prefixWord ++ tailWord_2739660) baseStart_2739660 baseEnd_2739660 := by
    simpa [prefixWord, tailWord_2739660, baseEnd_2739660] using wordTrace_append hprefix tailTrace_2739660
  have hstable : (prefixWord ++ tailWord_2739660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739660).length < 2 ^ (prefixWord ++ tailWord_2739660).sum := by decide
  have hdescent : baseEnd_2739660 < baseStart_2739660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739703 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 3]
def baseStart_2739703 : Nat := 118140960795 + 2739703 * 2 ^ 59
def prefixEnd_2739703 : Nat := 4983230072969 + 3 ^ 40 * 2739703 * 2
def baseEnd_2739703 : Nat := 1406784489564999633112841

theorem tailTrace_2739703 : CollatzResearch.WordTrace tailWord_2739703 prefixEnd_2739703 1406784489564999633112841 := by
  unfold tailWord_2739703
  simp only [CollatzResearch.WordTrace]
  refine ⟨99925177593531409865767763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66616785062354273243845175 99925177593531409865767763)
  ·
    refine ⟨149887766390297114798651645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99925177593531409865767763 149887766390297114798651645)
    ·
      refine ⟨56207912396361418049494367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149887766390297114798651645 56207912396361418049494367)
      ·
        refine ⟨84311868594542127074241551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56207912396361418049494367 84311868594542127074241551)
        ·
          refine ⟨126467802891813190611362327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84311868594542127074241551 126467802891813190611362327)
          ·
            refine ⟨189701704337719785917043491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126467802891813190611362327 189701704337719785917043491)
            ·
              refine ⟨284552556506579678875565237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189701704337719785917043491 284552556506579678875565237)
              ·
                refine ⟨26676802172491844894584241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 284552556506579678875565237 26676802172491844894584241)
                ·
                  refine ⟨20007601629368883670938181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26676802172491844894584241 20007601629368883670938181)
                  ·
                    refine ⟨3751425305506665688300909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20007601629368883670938181 3751425305506665688300909)
                    ·
                      refine ⟨1406784489564999633112841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3751425305506665688300909 1406784489564999633112841)
                      ·
                        rfl

theorem cell23_2739703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_2739703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739703 prefixEnd_2739703 := by exact prefixLift 2739703
  have htrace : WordTrace (prefixWord ++ tailWord_2739703) baseStart_2739703 baseEnd_2739703 := by
    simpa [prefixWord, tailWord_2739703, baseEnd_2739703] using wordTrace_append hprefix tailTrace_2739703
  have hstable : (prefixWord ++ tailWord_2739703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739703).length < 2 ^ (prefixWord ++ tailWord_2739703).sum := by decide
  have hdescent : baseEnd_2739703 < baseStart_2739703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739718 : List Nat := [6, 2, 1, 1, 3, 1, 2, 7]
def baseStart_2739718 : Nat := 118140960795 + 2739718 * 2 ^ 59
def prefixEnd_2739718 : Nat := 4983230072969 + 3 ^ 40 * 2739718 * 2
def baseEnd_2739718 : Nat := 52103414510178410163899

theorem tailTrace_2739718 : CollatzResearch.WordTrace tailWord_2739718 prefixEnd_2739718 52103414510178410163899 := by
  unfold tailWord_2739718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3122678896514908357111369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66617149792318044951709205 3122678896514908357111369)
  ·
    refine ⟨2342009172386181267833527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3122678896514908357111369 2342009172386181267833527)
    ·
      refine ⟨3513013758579271901750291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2342009172386181267833527 3513013758579271901750291)
      ·
        refine ⟨5269520637868907852625437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3513013758579271901750291 5269520637868907852625437)
        ·
          refine ⟨1976070239200840444734539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5269520637868907852625437 1976070239200840444734539)
          ·
            refine ⟨2964105358801260667101809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1976070239200840444734539 2964105358801260667101809)
            ·
              refine ⟨2223079019100945500326357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2964105358801260667101809 2223079019100945500326357)
              ·
                refine ⟨52103414510178410163899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2223079019100945500326357 52103414510178410163899)
                ·
                  rfl

theorem cell23_2739718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_2739718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739718 prefixEnd_2739718 := by exact prefixLift 2739718
  have htrace : WordTrace (prefixWord ++ tailWord_2739718) baseStart_2739718 baseEnd_2739718 := by
    simpa [prefixWord, tailWord_2739718, baseEnd_2739718] using wordTrace_append hprefix tailTrace_2739718
  have hstable : (prefixWord ++ tailWord_2739718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739718).length < 2 ^ (prefixWord ++ tailWord_2739718).sum := by decide
  have hdescent : baseEnd_2739718 < baseStart_2739718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739760 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 2, 5, 2]
def baseStart_2739760 : Nat := 118140960795 + 2739760 * 2 ^ 59
def prefixEnd_2739760 : Nat := 4983230072969 + 3 ^ 40 * 2739760 * 2
def baseEnd_2739760 : Nat := 1406813757962305910100079

theorem tailTrace_2739760 : CollatzResearch.WordTrace tailWord_2739760 prefixEnd_2739760 1406813757962305910100079 := by
  unfold tailWord_2739760
  simp only [CollatzResearch.WordTrace]
  refine ⟨49963628277162454300296367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66618171036216605733728489 49963628277162454300296367)
  ·
    refine ⟨74945442415743681450444551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49963628277162454300296367 74945442415743681450444551)
    ·
      refine ⟨112418163623615522175666827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74945442415743681450444551 112418163623615522175666827)
      ·
        refine ⟨168627245435423283263500241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112418163623615522175666827 168627245435423283263500241)
        ·
          refine ⟨126470434076567462447625181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168627245435423283263500241 126470434076567462447625181)
          ·
            refine ⟨47426412778712798417859443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126470434076567462447625181 47426412778712798417859443)
            ·
              refine ⟨71139619168069197626789165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47426412778712798417859443 71139619168069197626789165)
              ·
                refine ⟨26677357188025949110045937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71139619168069197626789165 26677357188025949110045937)
                ·
                  refine ⟨20008017891019461832534453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26677357188025949110045937 20008017891019461832534453)
                  ·
                    refine ⟨1875751677283074546800105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20008017891019461832534453 1875751677283074546800105)
                    ·
                      refine ⟨1406813757962305910100079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1875751677283074546800105 1406813757962305910100079)
                      ·
                        rfl

theorem cell23_2739760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2, 5, 2].length) (baseStart_2739760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739760 prefixEnd_2739760 := by exact prefixLift 2739760
  have htrace : WordTrace (prefixWord ++ tailWord_2739760) baseStart_2739760 baseEnd_2739760 := by
    simpa [prefixWord, tailWord_2739760, baseEnd_2739760] using wordTrace_append hprefix tailTrace_2739760
  have hstable : (prefixWord ++ tailWord_2739760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739760).length < 2 ^ (prefixWord ++ tailWord_2739760).sum := by decide
  have hdescent : baseEnd_2739760 < baseStart_2739760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739763 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 7]
def baseStart_2739763 : Nat := 118140960795 + 2739763 * 2 ^ 59
def prefixEnd_2739763 : Nat := 4983230072969 + 3 ^ 40 * 2739763 * 2
def baseEnd_2739763 : Nat := 1406815298404269398362565

theorem tailTrace_2739763 : CollatzResearch.WordTrace tailWord_2739763 prefixEnd_2739763 1406815298404269398362565 := by
  unfold tailWord_2739763
  simp only [CollatzResearch.WordTrace]
  refine ⟨99927365973314040112951943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66618243982209360075301295 99927365973314040112951943)
  ·
    refine ⟨149891048959971060169427915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99927365973314040112951943 149891048959971060169427915)
    ·
      refine ⟨224836573439956590254141873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149891048959971060169427915 224836573439956590254141873)
      ·
        refine ⟨168627430079967442690606405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224836573439956590254141873 168627430079967442690606405)
        ·
          refine ⟨31617643139993895504488701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168627430079967442690606405 31617643139993895504488701)
          ·
            refine ⟨11856616177497710814183263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31617643139993895504488701 11856616177497710814183263)
            ·
              refine ⟨17784924266246566221274895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11856616177497710814183263 17784924266246566221274895)
              ·
                refine ⟨26677386399369849331912343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17784924266246566221274895 26677386399369849331912343)
                ·
                  refine ⟨40016079599054773997868515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26677386399369849331912343 40016079599054773997868515)
                  ·
                    refine ⟨60024119398582160996802773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40016079599054773997868515 60024119398582160996802773)
                    ·
                      refine ⟨1406815298404269398362565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60024119398582160996802773 1406815298404269398362565)
                      ·
                        rfl

theorem cell23_2739763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_2739763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739763 prefixEnd_2739763 := by exact prefixLift 2739763
  have htrace : WordTrace (prefixWord ++ tailWord_2739763) baseStart_2739763 baseEnd_2739763 := by
    simpa [prefixWord, tailWord_2739763, baseEnd_2739763] using wordTrace_append hprefix tailTrace_2739763
  have hstable : (prefixWord ++ tailWord_2739763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739763).length < 2 ^ (prefixWord ++ tailWord_2739763).sum := by decide
  have hdescent : baseEnd_2739763 < baseStart_2739763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739897 : List Nat := [1, 2, 1, 4, 1, 1, 3, 4, 1, 1, 4]
def baseStart_2739897 : Nat := 118140960795 + 2739897 * 2 ^ 59
def prefixEnd_2739897 : Nat := 4983230072969 + 3 ^ 40 * 2739897 * 2
def baseEnd_2739897 : Nat := 1406884104811971874086949

theorem tailTrace_2739897 : CollatzResearch.WordTrace tailWord_2739897 prefixEnd_2739897 1406884104811971874086949 := by
  unfold tailWord_2739897
  simp only [CollatzResearch.WordTrace]
  refine ⟨99932253354828580998329945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66621502236552387332219963 99932253354828580998329945)
  ·
    refine ⟨74949190016121435748747459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99932253354828580998329945 74949190016121435748747459)
    ·
      refine ⟨112423785024182153623121189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74949190016121435748747459 112423785024182153623121189)
      ·
        refine ⟨21079459692034153804335223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112423785024182153623121189 21079459692034153804335223)
        ·
          refine ⟨31619189538051230706502835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21079459692034153804335223 31619189538051230706502835)
          ·
            refine ⟨47428784307076846059754253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31619189538051230706502835 47428784307076846059754253)
            ·
              refine ⟨17785794115153817272407845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47428784307076846059754253 17785794115153817272407845)
              ·
                refine ⟨3334836396591340738576471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17785794115153817272407845 3334836396591340738576471)
                ·
                  refine ⟨5002254594887011107864707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334836396591340738576471 5002254594887011107864707)
                  ·
                    refine ⟨7503381892330516661797061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5002254594887011107864707 7503381892330516661797061)
                    ·
                      refine ⟨1406884104811971874086949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7503381892330516661797061 1406884104811971874086949)
                      ·
                        rfl

theorem cell23_2739897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_2739897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739897 prefixEnd_2739897 := by exact prefixLift 2739897
  have htrace : WordTrace (prefixWord ++ tailWord_2739897) baseStart_2739897 baseEnd_2739897 := by
    simpa [prefixWord, tailWord_2739897, baseEnd_2739897] using wordTrace_append hprefix tailTrace_2739897
  have hstable : (prefixWord ++ tailWord_2739897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739897).length < 2 ^ (prefixWord ++ tailWord_2739897).sum := by decide
  have hdescent : baseEnd_2739897 < baseStart_2739897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739924 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_2739924 : Nat := 118140960795 + 2739924 * 2 ^ 59
def prefixEnd_2739924 : Nat := 4983230072969 + 3 ^ 40 * 2739924 * 2
def baseEnd_2739924 : Nat := 468965989596547756149775

theorem tailTrace_2739924 : CollatzResearch.WordTrace tailWord_2739924 prefixEnd_2739924 468965989596547756149775 := by
  unfold tailWord_2739924
  simp only [CollatzResearch.WordTrace]
  refine ⟨49966619062865382304781413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66622158750487176406375217 49966619062865382304781413)
  ·
    refine ⟨9368741074287259182146515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49966619062865382304781413 9368741074287259182146515)
    ·
      refine ⟨14053111611430888773219773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9368741074287259182146515 14053111611430888773219773)
      ·
        refine ⟨5269916854286583289957415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14053111611430888773219773 5269916854286583289957415)
        ·
          refine ⟨7904875281429874934936123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5269916854286583289957415 7904875281429874934936123)
          ·
            refine ⟨11857312922144812402404185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7904875281429874934936123 11857312922144812402404185)
            ·
              refine ⟨8892984691608609301803139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11857312922144812402404185 8892984691608609301803139)
              ·
                refine ⟨13339477037412913952704709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8892984691608609301803139 13339477037412913952704709)
                ·
                  refine ⟨2501151944514921366132133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13339477037412913952704709 2501151944514921366132133)
                  ·
                    refine ⟨468965989596547756149775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2501151944514921366132133 468965989596547756149775)
                    ·
                      rfl

theorem cell23_2739924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_2739924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739924 prefixEnd_2739924 := by exact prefixLift 2739924
  have htrace : WordTrace (prefixWord ++ tailWord_2739924) baseStart_2739924 baseEnd_2739924 := by
    simpa [prefixWord, tailWord_2739924, baseEnd_2739924] using wordTrace_append hprefix tailTrace_2739924
  have hstable : (prefixWord ++ tailWord_2739924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739924).length < 2 ^ (prefixWord ++ tailWord_2739924).sum := by decide
  have hdescent : baseEnd_2739924 < baseStart_2739924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739937 : List Nat := [1, 2, 3, 1, 5, 1, 2, 8]
def baseStart_2739937 : Nat := 118140960795 + 2739937 * 2 ^ 59
def prefixEnd_2739937 : Nat := 4983230072969 + 3 ^ 40 * 2739937 * 2
def baseEnd_2739937 : Nat := 52107579408820433984695

theorem tailTrace_2739937 : CollatzResearch.WordTrace tailWord_2739937 prefixEnd_2739937 52107579408820433984695 := by
  unfold tailWord_2739937
  simp only [CollatzResearch.WordTrace]
  refine ⟨99933712274683667829786065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66622474849789111886524043 99933712274683667829786065)
  ·
    refine ⟨74950284206012750872339549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99933712274683667829786065 74950284206012750872339549)
    ·
      refine ⟨28106356577254781577127331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74950284206012750872339549 28106356577254781577127331)
      ·
        refine ⟨42159534865882172365690997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28106356577254781577127331 42159534865882172365690997)
        ·
          refine ⟨3952456393676453659283531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42159534865882172365690997 3952456393676453659283531)
          ·
            refine ⟨5928684590514680488925297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3952456393676453659283531 5928684590514680488925297)
            ·
              refine ⟨4446513442886010366693973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5928684590514680488925297 4446513442886010366693973)
              ·
                refine ⟨52107579408820433984695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4446513442886010366693973 52107579408820433984695)
                ·
                  rfl

theorem cell23_2739937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 8].length) (baseStart_2739937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739937 prefixEnd_2739937 := by exact prefixLift 2739937
  have htrace : WordTrace (prefixWord ++ tailWord_2739937) baseStart_2739937 baseEnd_2739937 := by
    simpa [prefixWord, tailWord_2739937, baseEnd_2739937] using wordTrace_append hprefix tailTrace_2739937
  have hstable : (prefixWord ++ tailWord_2739937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739937).length < 2 ^ (prefixWord ++ tailWord_2739937).sum := by decide
  have hdescent : baseEnd_2739937 < baseStart_2739937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739940 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_2739940 : Nat := 118140960795 + 2739940 * 2 ^ 59
def prefixEnd_2739940 : Nat := 4983230072969 + 3 ^ 40 * 2739940 * 2
def baseEnd_2739940 : Nat := 1406906184480115205849251

theorem tailTrace_2739940 : CollatzResearch.WordTrace tailWord_2739940 prefixEnd_2739940 1406906184480115205849251 := by
  unfold tailWord_2739940
  simp only [CollatzResearch.WordTrace]
  refine ⟨49966910846836399671072637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66622547795781866228096849 49966910846836399671072637)
  ·
    refine ⟨18737591567563649876652239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49966910846836399671072637 18737591567563649876652239)
    ·
      refine ⟨28106387351345474814978359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18737591567563649876652239 28106387351345474814978359)
      ·
        refine ⟨42159581027018212222467539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28106387351345474814978359 42159581027018212222467539)
        ·
          refine ⟨63239371540527318333701309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42159581027018212222467539 63239371540527318333701309)
          ·
            refine ⟨23714764327697744375137991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63239371540527318333701309 23714764327697744375137991)
            ·
              refine ⟨35572146491546616562706987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23714764327697744375137991 35572146491546616562706987)
              ·
                refine ⟨53358219737319924844060481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35572146491546616562706987 53358219737319924844060481)
                ·
                  refine ⟨40018664802989943633045361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53358219737319924844060481 40018664802989943633045361)
                  ·
                    refine ⟨30013998602242457724784021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40018664802989943633045361 30013998602242457724784021)
                    ·
                      refine ⟨1406906184480115205849251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30013998602242457724784021 1406906184480115205849251)
                      ·
                        rfl

theorem cell23_2739940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_2739940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739940 prefixEnd_2739940 := by exact prefixLift 2739940
  have htrace : WordTrace (prefixWord ++ tailWord_2739940) baseStart_2739940 baseEnd_2739940 := by
    simpa [prefixWord, tailWord_2739940, baseEnd_2739940] using wordTrace_append hprefix tailTrace_2739940
  have hstable : (prefixWord ++ tailWord_2739940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739940).length < 2 ^ (prefixWord ++ tailWord_2739940).sum := by decide
  have hdescent : baseEnd_2739940 < baseStart_2739940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739960 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 2, 2, 5]
def baseStart_2739960 : Nat := 118140960795 + 2739960 * 2 ^ 59
def prefixEnd_2739960 : Nat := 4983230072969 + 3 ^ 40 * 2739960 * 2
def baseEnd_2739960 : Nat := 1406916454093205127599159

theorem tailTrace_2739960 : CollatzResearch.WordTrace tailWord_2739960 prefixEnd_2739960 1406916454093205127599159 := by
  unfold tailWord_2739960
  simp only [CollatzResearch.WordTrace]
  refine ⟨49967275576800171378936667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66623034102400228505248889 49967275576800171378936667)
  ·
    refine ⟨74950913365200257068405001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49967275576800171378936667 74950913365200257068405001)
    ·
      refine ⟨56213185023900192801303751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74950913365200257068405001 56213185023900192801303751)
      ·
        refine ⟨84319777535850289201955627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56213185023900192801303751 84319777535850289201955627)
        ·
          refine ⟨126479666303775433802933441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84319777535850289201955627 126479666303775433802933441)
          ·
            refine ⟨94859749727831575352200081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126479666303775433802933441 94859749727831575352200081)
            ·
              refine ⟨71144812295873681514150061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94859749727831575352200081 71144812295873681514150061)
              ·
                refine ⟨26679304610952630567806273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71144812295873681514150061 26679304610952630567806273)
                ·
                  refine ⟨20009478458214472925854705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26679304610952630567806273 20009478458214472925854705)
                  ·
                    refine ⟨15007108843660854694391029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20009478458214472925854705 15007108843660854694391029)
                    ·
                      refine ⟨1406916454093205127599159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15007108843660854694391029 1406916454093205127599159)
                      ·
                        rfl

theorem cell23_2739960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_2739960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739960 prefixEnd_2739960 := by exact prefixLift 2739960
  have htrace : WordTrace (prefixWord ++ tailWord_2739960) baseStart_2739960 baseEnd_2739960 := by
    simpa [prefixWord, tailWord_2739960, baseEnd_2739960] using wordTrace_append hprefix tailTrace_2739960
  have hstable : (prefixWord ++ tailWord_2739960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739960).length < 2 ^ (prefixWord ++ tailWord_2739960).sum := by decide
  have hdescent : baseEnd_2739960 < baseStart_2739960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739988 : List Nat := [2, 4, 4, 1, 1, 2, 1, 8]
def baseStart_2739988 : Nat := 118140960795 + 2739988 * 2 ^ 59
def prefixEnd_2739988 : Nat := 4983230072969 + 3 ^ 40 * 2739988 * 2
def baseEnd_2739988 : Nat := 52108549316723371038853

theorem tailTrace_2739988 : CollatzResearch.WordTrace tailWord_2739988 prefixEnd_2739988 52108549316723371038853 := by
  unfold tailWord_2739988
  simp only [CollatzResearch.WordTrace]
  refine ⟨49967786198749451769946309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66623714931665935693261745 49967786198749451769946309)
  ·
    refine ⟨9368959912265522206864933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49967786198749451769946309 9368959912265522206864933)
    ·
      refine ⟨1756679983549785413787175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9368959912265522206864933 1756679983549785413787175)
      ·
        refine ⟨2635019975324678120680763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1756679983549785413787175 2635019975324678120680763)
        ·
          refine ⟨3952529962987017181021145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2635019975324678120680763 3952529962987017181021145)
          ·
            refine ⟨2964397472240262885765859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3952529962987017181021145 2964397472240262885765859)
            ·
              refine ⟨4446596208360394328648789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2964397472240262885765859 4446596208360394328648789)
              ·
                refine ⟨52108549316723371038853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4446596208360394328648789 52108549316723371038853)
                ·
                  rfl

theorem cell23_2739988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 8].length) (baseStart_2739988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739988 prefixEnd_2739988 := by exact prefixLift 2739988
  have htrace : WordTrace (prefixWord ++ tailWord_2739988) baseStart_2739988 baseEnd_2739988 := by
    simpa [prefixWord, tailWord_2739988, baseEnd_2739988] using wordTrace_append hprefix tailTrace_2739988
  have hstable : (prefixWord ++ tailWord_2739988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739988).length < 2 ^ (prefixWord ++ tailWord_2739988).sum := by decide
  have hdescent : baseEnd_2739988 < baseStart_2739988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740037 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 4, 3, 3]
def baseStart_2740037 : Nat := 118140960795 + 2740037 * 2 ^ 59
def prefixEnd_2740037 : Nat := 4983230072969 + 3 ^ 40 * 2740037 * 2
def baseEnd_2740037 : Nat := 1406955992103601326336305

theorem tailTrace_2740037 : CollatzResearch.WordTrace tailWord_2740037 prefixEnd_2740037 1406955992103601326336305 := by
  unfold tailWord_2740037
  simp only [CollatzResearch.WordTrace]
  refine ⟨99937359574321384908426365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66624906382880923272284243 99937359574321384908426365)
  ·
    refine ⟨37476509840370519340659887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99937359574321384908426365 37476509840370519340659887)
    ·
      refine ⟨56214764760555779010989831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37476509840370519340659887 56214764760555779010989831)
      ·
        refine ⟨84322147140833668516484747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56214764760555779010989831 84322147140833668516484747)
        ·
          refine ⟨126483220711250502774727121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84322147140833668516484747 126483220711250502774727121)
          ·
            refine ⟨94862415533437877081045341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126483220711250502774727121 94862415533437877081045341)
            ·
              refine ⟨35573405825039203905392003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94862415533437877081045341 35573405825039203905392003)
              ·
                refine ⟨53360108737558805858088005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35573405825039203905392003 53360108737558805858088005)
                ·
                  refine ⟨10005020388292276098391501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53360108737558805858088005 10005020388292276098391501)
                  ·
                    refine ⟨3751882645609603536896813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10005020388292276098391501 3751882645609603536896813)
                    ·
                      refine ⟨1406955992103601326336305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3751882645609603536896813 1406955992103601326336305)
                      ·
                        rfl

theorem cell23_2740037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_2740037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740037 prefixEnd_2740037 := by exact prefixLift 2740037
  have htrace : WordTrace (prefixWord ++ tailWord_2740037) baseStart_2740037 baseEnd_2740037 := by
    simpa [prefixWord, tailWord_2740037, baseEnd_2740037] using wordTrace_append hprefix tailTrace_2740037
  have hstable : (prefixWord ++ tailWord_2740037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740037).length < 2 ^ (prefixWord ++ tailWord_2740037).sum := by decide
  have hdescent : baseEnd_2740037 < baseStart_2740037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740044 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 7]
def baseStart_2740044 : Nat := 118140960795 + 2740044 * 2 ^ 59
def prefixEnd_2740044 : Nat := 4983230072969 + 3 ^ 40 * 2740044 * 2
def baseEnd_2740044 : Nat := 156328842940909199883197

theorem tailTrace_2740044 : CollatzResearch.WordTrace tailWord_2740044 prefixEnd_2740044 156328842940909199883197 := by
  unfold tailWord_2740044
  simp only [CollatzResearch.WordTrace]
  refine ⟨49968807442648012551965593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66625076590197350069287457 49968807442648012551965593)
  ·
    refine ⟨37476605581986009413974195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49968807442648012551965593 37476605581986009413974195)
    ·
      refine ⟨56214908372979014120961293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37476605581986009413974195 56214908372979014120961293)
      ·
        refine ⟨21080590639867130295360485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56214908372979014120961293 21080590639867130295360485)
        ·
          refine ⟨3952610744975086930380091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21080590639867130295360485 3952610744975086930380091)
          ·
            refine ⟨5928916117462630395570137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3952610744975086930380091 5928916117462630395570137)
            ·
              refine ⟨4446687088096972796677603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5928916117462630395570137 4446687088096972796677603)
              ·
                refine ⟨6670030632145459195016405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4446687088096972796677603 6670030632145459195016405)
                ·
                  refine ⟨156328842940909199883197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6670030632145459195016405 156328842940909199883197)
                  ·
                    rfl

theorem cell23_2740044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 7].length) (baseStart_2740044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740044 prefixEnd_2740044 := by exact prefixLift 2740044
  have htrace : WordTrace (prefixWord ++ tailWord_2740044) baseStart_2740044 baseEnd_2740044 := by
    simpa [prefixWord, tailWord_2740044, baseEnd_2740044] using wordTrace_append hprefix tailTrace_2740044
  have hstable : (prefixWord ++ tailWord_2740044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740044).length < 2 ^ (prefixWord ++ tailWord_2740044).sum := by decide
  have hdescent : baseEnd_2740044 < baseStart_2740044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740055 : List Nat := [1, 1, 3, 2, 5, 1, 3, 1, 2, 2, 2]
def baseStart_2740055 : Nat := 118140960795 + 2740055 * 2 ^ 59
def prefixEnd_2740055 : Nat := 4983230072969 + 3 ^ 40 * 2740055 * 2
def baseEnd_2740055 : Nat := 1406965234755382255911223

theorem tailTrace_2740055 : CollatzResearch.WordTrace tailWord_2740055 prefixEnd_2740055 1406965234755382255911223 := by
  unfold tailWord_2740055
  simp only [CollatzResearch.WordTrace]
  refine ⟨99938016088256173982581619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66625344058837449321721079 99938016088256173982581619)
  ·
    refine ⟨149907024132384260973872429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99938016088256173982581619 149907024132384260973872429)
    ·
      refine ⟨56215134049644097865202161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149907024132384260973872429 56215134049644097865202161)
      ·
        refine ⟨42161350537233073398901621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56215134049644097865202161 42161350537233073398901621)
        ·
          refine ⟨3952626612865600631147027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42161350537233073398901621 3952626612865600631147027)
          ·
            refine ⟨5928939919298400946720541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3952626612865600631147027 5928939919298400946720541)
            ·
              refine ⟨2223352469736900355020203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5928939919298400946720541 2223352469736900355020203)
              ·
                refine ⟨3335028704605350532530305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2223352469736900355020203 3335028704605350532530305)
                ·
                  refine ⟨2501271528454012899397729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3335028704605350532530305 2501271528454012899397729)
                  ·
                    refine ⟨1875953646340509674548297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2501271528454012899397729 1875953646340509674548297)
                    ·
                      refine ⟨1406965234755382255911223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1875953646340509674548297 1406965234755382255911223)
                      ·
                        rfl

theorem cell23_2740055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_2740055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740055 prefixEnd_2740055 := by exact prefixLift 2740055
  have htrace : WordTrace (prefixWord ++ tailWord_2740055) baseStart_2740055 baseEnd_2740055 := by
    simpa [prefixWord, tailWord_2740055, baseEnd_2740055] using wordTrace_append hprefix tailTrace_2740055
  have hstable : (prefixWord ++ tailWord_2740055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740055).length < 2 ^ (prefixWord ++ tailWord_2740055).sum := by decide
  have hdescent : baseEnd_2740055 < baseStart_2740055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740078 : List Nat := [4, 1, 2, 3, 1, 3, 1, 3, 5]
def baseStart_2740078 : Nat := 118140960795 + 2740078 * 2 ^ 59
def prefixEnd_2740078 : Nat := 4983230072969 + 3 ^ 40 * 2740078 * 2
def baseEnd_2740078 : Nat := 156330782756715073991513

theorem tailTrace_2740078 : CollatzResearch.WordTrace tailWord_2740078 prefixEnd_2740078 156330782756715073991513 := by
  unfold tailWord_2740078
  simp only [CollatzResearch.WordTrace]
  refine ⟨12492356870896606113833611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66625903311448565940445925 12492356870896606113833611)
  ·
    refine ⟨18738535306344909170750417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12492356870896606113833611 18738535306344909170750417)
    ·
      refine ⟨14053901479758681878062813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18738535306344909170750417 14053901479758681878062813)
      ·
        refine ⟨5270213054909505704273555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14053901479758681878062813 5270213054909505704273555)
        ·
          refine ⟨7905319582364258556410333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5270213054909505704273555 7905319582364258556410333)
          ·
            refine ⟨2964494843386596958653875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7905319582364258556410333 2964494843386596958653875)
            ·
              refine ⟨4446742265079895437980813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2964494843386596958653875 4446742265079895437980813)
              ·
                refine ⟨1667528349404960789242805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4446742265079895437980813 1667528349404960789242805)
                ·
                  refine ⟨156330782756715073991513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1667528349404960789242805 156330782756715073991513)
                  ·
                    rfl

theorem cell23_2740078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_2740078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740078 prefixEnd_2740078 := by exact prefixLift 2740078
  have htrace : WordTrace (prefixWord ++ tailWord_2740078) baseStart_2740078 baseEnd_2740078 := by
    simpa [prefixWord, tailWord_2740078, baseEnd_2740078] using wordTrace_append hprefix tailTrace_2740078
  have hstable : (prefixWord ++ tailWord_2740078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740078).length < 2 ^ (prefixWord ++ tailWord_2740078).sum := by decide
  have hdescent : baseEnd_2740078 < baseStart_2740078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740182 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_2740182 : Nat := 118140960795 + 2740182 * 2 ^ 59
def prefixEnd_2740182 : Nat := 4983230072969 + 3 ^ 40 * 2740182 * 2
def baseEnd_2740182 : Nat := 1407030446798503259023139

theorem tailTrace_2740182 : CollatzResearch.WordTrace tailWord_2740182 prefixEnd_2740182 1407030446798503259023139 := by
  unfold tailWord_2740182
  simp only [CollatzResearch.WordTrace]
  refine ⟨6246415509924754667028425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66628432105864049781636533 6246415509924754667028425)
  ·
    refine ⟨4684811632443566000271319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6246415509924754667028425 4684811632443566000271319)
    ·
      refine ⟨7027217448665349000406979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4684811632443566000271319 7027217448665349000406979)
      ·
        refine ⟨10540826172998023500610469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7027217448665349000406979 10540826172998023500610469)
        ·
          refine ⟨1976404907437129406364463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10540826172998023500610469 1976404907437129406364463)
          ·
            refine ⟨2964607361155694109546695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1976404907437129406364463 2964607361155694109546695)
            ·
              refine ⟨4446911041733541164320043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2964607361155694109546695 4446911041733541164320043)
              ·
                refine ⟨6670366562600311746480065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4446911041733541164320043 6670366562600311746480065)
                ·
                  refine ⟨5002774921950233809860049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6670366562600311746480065 5002774921950233809860049)
                  ·
                    refine ⟨3752081191462675357395037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5002774921950233809860049 3752081191462675357395037)
                    ·
                      refine ⟨1407030446798503259023139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3752081191462675357395037 1407030446798503259023139)
                      ·
                        rfl

theorem cell23_2740182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_2740182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740182 prefixEnd_2740182 := by exact prefixLift 2740182
  have htrace : WordTrace (prefixWord ++ tailWord_2740182) baseStart_2740182 baseEnd_2740182 := by
    simpa [prefixWord, tailWord_2740182, baseEnd_2740182] using wordTrace_append hprefix tailTrace_2740182
  have hstable : (prefixWord ++ tailWord_2740182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740182).length < 2 ^ (prefixWord ++ tailWord_2740182).sum := by decide
  have hdescent : baseEnd_2740182 < baseStart_2740182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740184 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 3, 1, 4]
def baseStart_2740184 : Nat := 118140960795 + 2740184 * 2 ^ 59
def prefixEnd_2740184 : Nat := 4983230072969 + 3 ^ 40 * 2740184 * 2
def baseEnd_2740184 : Nat := 1407031473759812251198129

theorem tailTrace_2740184 : CollatzResearch.WordTrace tailWord_2740184 prefixEnd_2740184 1407031473759812251198129 := by
  unfold tailWord_2740184
  simp only [CollatzResearch.WordTrace]
  refine ⟨49971360552394414507013803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66628480736525886009351737 49971360552394414507013803)
  ·
    refine ⟨74957040828591621760520705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49971360552394414507013803 74957040828591621760520705)
    ·
      refine ⟨56217780621443716320390529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74957040828591621760520705 56217780621443716320390529)
      ·
        refine ⟨42163335466082787240292897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56217780621443716320390529 42163335466082787240292897)
        ·
          refine ⟨31622501599562090430219673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42163335466082787240292897 31622501599562090430219673)
          ·
            refine ⟨23716876199671567822664755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31622501599562090430219673 23716876199671567822664755)
            ·
              refine ⟨35575314299507351733997133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23716876199671567822664755 35575314299507351733997133)
              ·
                refine ⟨13340742862315256900248925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35575314299507351733997133 13340742862315256900248925)
                ·
                  refine ⟨5002778573368221337593347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13340742862315256900248925 5002778573368221337593347)
                  ·
                    refine ⟨7504167860052332006390021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5002778573368221337593347 7504167860052332006390021)
                    ·
                      refine ⟨1407031473759812251198129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7504167860052332006390021 1407031473759812251198129)
                      ·
                        rfl

theorem cell23_2740184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_2740184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740184 prefixEnd_2740184 := by exact prefixLift 2740184
  have htrace : WordTrace (prefixWord ++ tailWord_2740184) baseStart_2740184 baseEnd_2740184 := by
    simpa [prefixWord, tailWord_2740184, baseEnd_2740184] using wordTrace_append hprefix tailTrace_2740184
  have hstable : (prefixWord ++ tailWord_2740184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740184).length < 2 ^ (prefixWord ++ tailWord_2740184).sum := by decide
  have hdescent : baseEnd_2740184 < baseStart_2740184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740195 : List Nat := [1, 1, 1, 6, 1, 3, 2, 3, 1, 1, 3]
def baseStart_2740195 : Nat := 118140960795 + 2740195 * 2 ^ 59
def prefixEnd_2740195 : Nat := 4983230072969 + 3 ^ 40 * 2740195 * 2
def baseEnd_2740195 : Nat := 1407037122047011708160579

theorem tailTrace_2740195 : CollatzResearch.WordTrace tailWord_2740195 prefixEnd_2740195 1407037122047011708160579 := by
  unfold tailWord_2740195
  simp only [CollatzResearch.WordTrace]
  refine ⟨99943122307748977892678039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66628748205165985261785359 99943122307748977892678039)
  ·
    refine ⟨149914683461623466839017059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99943122307748977892678039 149914683461623466839017059)
    ·
      refine ⟨224872025192435200258525589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149914683461623466839017059 224872025192435200258525589)
      ·
        refine ⟨10540876180895400012118387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 224872025192435200258525589 10540876180895400012118387)
        ·
          refine ⟨15811314271343100018177581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10540876180895400012118387 15811314271343100018177581)
          ·
            refine ⟨5929242851753662506816593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15811314271343100018177581 5929242851753662506816593)
            ·
              refine ⟨4446932138815246880112445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5929242851753662506816593 4446932138815246880112445)
              ·
                refine ⟨1667599552055717580042167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4446932138815246880112445 1667599552055717580042167)
                ·
                  refine ⟨2501399328083576370063251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1667599552055717580042167 2501399328083576370063251)
                  ·
                    refine ⟨3752098992125364555094877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2501399328083576370063251 3752098992125364555094877)
                    ·
                      refine ⟨1407037122047011708160579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3752098992125364555094877 1407037122047011708160579)
                      ·
                        rfl

theorem cell23_2740195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_2740195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740195 prefixEnd_2740195 := by exact prefixLift 2740195
  have htrace : WordTrace (prefixWord ++ tailWord_2740195) baseStart_2740195 baseEnd_2740195 := by
    simpa [prefixWord, tailWord_2740195, baseEnd_2740195] using wordTrace_append hprefix tailTrace_2740195
  have hstable : (prefixWord ++ tailWord_2740195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740195).length < 2 ^ (prefixWord ++ tailWord_2740195).sum := by decide
  have hdescent : baseEnd_2740195 < baseStart_2740195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740207 : List Nat := [1, 1, 2, 1, 4, 2, 12]
def baseStart_2740207 : Nat := 118140960795 + 2740207 * 2 ^ 59
def prefixEnd_2740207 : Nat := 4983230072969 + 3 ^ 40 * 2740207 * 2
def baseEnd_2740207 : Nat := 17370904738455131619883

theorem tailTrace_2740207 : CollatzResearch.WordTrace tailWord_2740207 prefixEnd_2740207 17370904738455131619883 := by
  unfold tailWord_2740207
  simp only [CollatzResearch.WordTrace]
  refine ⟨99943559983705503942114875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66629039989137002628076583 99943559983705503942114875)
  ·
    refine ⟨149915339975558255913172313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99943559983705503942114875 149915339975558255913172313)
    ·
      refine ⟨112436504981668691934879235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149915339975558255913172313 112436504981668691934879235)
      ·
        refine ⟨168654757472503037902318853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112436504981668691934879235 168654757472503037902318853)
        ·
          refine ⟨31622767026094319606684785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168654757472503037902318853 31622767026094319606684785)
          ·
            refine ⟨23717075269570739705013589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31622767026094319606684785 23717075269570739705013589)
            ·
              refine ⟨17370904738455131619883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 23717075269570739705013589 17370904738455131619883)
              ·
                rfl

theorem cell23_2740207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 12].length) (baseStart_2740207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740207 prefixEnd_2740207 := by exact prefixLift 2740207
  have htrace : WordTrace (prefixWord ++ tailWord_2740207) baseStart_2740207 baseEnd_2740207 := by
    simpa [prefixWord, tailWord_2740207, baseEnd_2740207] using wordTrace_append hprefix tailTrace_2740207
  have hstable : (prefixWord ++ tailWord_2740207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740207).length < 2 ^ (prefixWord ++ tailWord_2740207).sum := by decide
  have hdescent : baseEnd_2740207 < baseStart_2740207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740231 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 4]
def baseStart_2740231 : Nat := 118140960795 + 2740231 * 2 ^ 59
def prefixEnd_2740231 : Nat := 4983230072969 + 3 ^ 40 * 2740231 * 2
def baseEnd_2740231 : Nat := 1407055607350573567310413

theorem tailTrace_2740231 : CollatzResearch.WordTrace tailWord_2740231 prefixEnd_2740231 1407055607350573567310413 := by
  unfold tailWord_2740231
  simp only [CollatzResearch.WordTrace]
  refine ⟨99944435335618556040988547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66629623557079037360659031 99944435335618556040988547)
  ·
    refine ⟨149916653003427834061482821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99944435335618556040988547 149916653003427834061482821)
    ·
      refine ⟨28109372438142718886528029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149916653003427834061482821 28109372438142718886528029)
      ·
        refine ⟨10541014664303519582448011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28109372438142718886528029 10541014664303519582448011)
        ·
          refine ⟨15811521996455279373672017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10541014664303519582448011 15811521996455279373672017)
          ·
            refine ⟨11858641497341459530254013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15811521996455279373672017 11858641497341459530254013)
            ·
              refine ⟨4446990561503047323845255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11858641497341459530254013 4446990561503047323845255)
              ·
                refine ⟨6670485842254570985767883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4446990561503047323845255 6670485842254570985767883)
                ·
                  refine ⟨10005728763381856478651825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6670485842254570985767883 10005728763381856478651825)
                  ·
                    refine ⟨7504296572536392358988869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10005728763381856478651825 7504296572536392358988869)
                    ·
                      refine ⟨1407055607350573567310413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7504296572536392358988869 1407055607350573567310413)
                      ·
                        rfl

theorem cell23_2740231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_2740231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740231 prefixEnd_2740231 := by exact prefixLift 2740231
  have htrace : WordTrace (prefixWord ++ tailWord_2740231) baseStart_2740231 baseEnd_2740231 := by
    simpa [prefixWord, tailWord_2740231, baseEnd_2740231] using wordTrace_append hprefix tailTrace_2740231
  have hstable : (prefixWord ++ tailWord_2740231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740231).length < 2 ^ (prefixWord ++ tailWord_2740231).sum := by decide
  have hdescent : baseEnd_2740231 < baseStart_2740231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740238 : List Nat := [4, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3]
def baseStart_2740238 : Nat := 118140960795 + 2740238 * 2 ^ 59
def prefixEnd_2740238 : Nat := 4983230072969 + 3 ^ 40 * 2740238 * 2
def baseEnd_2740238 : Nat := 1407059201715155039922881

theorem tailTrace_2740238 : CollatzResearch.WordTrace tailWord_2740238 prefixEnd_2740238 1407059201715155039922881 := by
  unfold tailWord_2740238
  simp only [CollatzResearch.WordTrace]
  refine ⟨12493086330824149529561671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66629793764395464157662245 12493086330824149529561671)
  ·
    refine ⟨18739629496236224294342507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12493086330824149529561671 18739629496236224294342507)
    ·
      refine ⟨28109444244354336441513761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18739629496236224294342507 28109444244354336441513761)
      ·
        refine ⟨21082083183265752331135321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28109444244354336441513761 21082083183265752331135321)
        ·
          refine ⟨15811562387449314248351491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21082083183265752331135321 15811562387449314248351491)
          ·
            refine ⟨23717343581173971372527237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15811562387449314248351491 23717343581173971372527237)
            ·
              refine ⟨4447001921470119632348857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23717343581173971372527237 4447001921470119632348857)
              ·
                refine ⟨3335251441102589724261643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4447001921470119632348857 3335251441102589724261643)
                ·
                  refine ⟨5002877161653884586392465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3335251441102589724261643 5002877161653884586392465)
                  ·
                    refine ⟨3752157871240413439794349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5002877161653884586392465 3752157871240413439794349)
                    ·
                      refine ⟨1407059201715155039922881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3752157871240413439794349 1407059201715155039922881)
                      ·
                        rfl

theorem cell23_2740238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_2740238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740238 prefixEnd_2740238 := by exact prefixLift 2740238
  have htrace : WordTrace (prefixWord ++ tailWord_2740238) baseStart_2740238 baseEnd_2740238 := by
    simpa [prefixWord, tailWord_2740238, baseEnd_2740238] using wordTrace_append hprefix tailTrace_2740238
  have hstable : (prefixWord ++ tailWord_2740238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740238).length < 2 ^ (prefixWord ++ tailWord_2740238).sum := by decide
  have hdescent : baseEnd_2740238 < baseStart_2740238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740252 : List Nat := [2, 2, 3, 1, 3, 1, 3, 3, 1, 2, 2]
def baseStart_2740252 : Nat := 118140960795 + 2740252 * 2 ^ 59
def prefixEnd_2740252 : Nat := 4983230072969 + 3 ^ 40 * 2740252 * 2
def baseEnd_2740252 : Nat := 1407066390444317985147817

theorem tailTrace_2740252 : CollatzResearch.WordTrace tailWord_2740252 prefixEnd_2740252 1407066390444317985147817 := by
  unfold tailWord_2740252
  simp only [CollatzResearch.WordTrace]
  refine ⟨49972600634271238313751505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66630134179028317751668673 49972600634271238313751505)
  ·
    refine ⟨37479450475703428735313629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49972600634271238313751505 37479450475703428735313629)
    ·
      refine ⟨14054793928388785775742611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37479450475703428735313629 14054793928388785775742611)
      ·
        refine ⟨21082190892583178663613917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14054793928388785775742611 21082190892583178663613917)
        ·
          refine ⟨7905821584718691998855219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21082190892583178663613917 7905821584718691998855219)
          ·
            refine ⟨11858732377078037998282829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7905821584718691998855219 11858732377078037998282829)
            ·
              refine ⟨4447024641404264249356061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11858732377078037998282829 4447024641404264249356061)
              ·
                refine ⟨1667634240526599093508523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4447024641404264249356061 1667634240526599093508523)
                ·
                  refine ⟨2501451360789898640262785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1667634240526599093508523 2501451360789898640262785)
                  ·
                    refine ⟨1876088520592423980197089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2501451360789898640262785 1876088520592423980197089)
                    ·
                      refine ⟨1407066390444317985147817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1876088520592423980197089 1407066390444317985147817)
                      ·
                        rfl

theorem cell23_2740252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_2740252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740252 prefixEnd_2740252 := by exact prefixLift 2740252
  have htrace : WordTrace (prefixWord ++ tailWord_2740252) baseStart_2740252 baseEnd_2740252 := by
    simpa [prefixWord, tailWord_2740252, baseEnd_2740252] using wordTrace_append hprefix tailTrace_2740252
  have hstable : (prefixWord ++ tailWord_2740252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740252).length < 2 ^ (prefixWord ++ tailWord_2740252).sum := by decide
  have hdescent : baseEnd_2740252 < baseStart_2740252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740284 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 1, 8]
def baseStart_2740284 : Nat := 118140960795 + 2740284 * 2 ^ 59
def prefixEnd_2740284 : Nat := 4983230072969 + 3 ^ 40 * 2740284 * 2
def baseEnd_2740284 : Nat := 469027607275087286649223

theorem tailTrace_2740284 : CollatzResearch.WordTrace tailWord_2740284 prefixEnd_2740284 469027607275087286649223 := by
  unfold tailWord_2740284
  simp only [CollatzResearch.WordTrace]
  refine ⟨49973184202213273046333953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66630912269617697395111937 49973184202213273046333953)
  ·
    refine ⟨37479888151659954784750465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49973184202213273046333953 37479888151659954784750465)
    ·
      refine ⟨28109916113744966088562849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37479888151659954784750465 28109916113744966088562849)
      ·
        refine ⟨21082437085308724566422137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28109916113744966088562849 21082437085308724566422137)
        ·
          refine ⟨15811827813981543424816603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21082437085308724566422137 15811827813981543424816603)
          ·
            refine ⟨23717741720972315137224905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15811827813981543424816603 23717741720972315137224905)
            ·
              refine ⟨17788306290729236352918679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23717741720972315137224905 17788306290729236352918679)
              ·
                refine ⟨26682459436093854529378019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17788306290729236352918679 26682459436093854529378019)
                ·
                  refine ⟨40023689154140781794067029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26682459436093854529378019 40023689154140781794067029)
                  ·
                    refine ⟨469027607275087286649223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40023689154140781794067029 469027607275087286649223)
                    ·
                      rfl

theorem cell23_2740284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_2740284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740284 prefixEnd_2740284 := by exact prefixLift 2740284
  have htrace : WordTrace (prefixWord ++ tailWord_2740284) baseStart_2740284 baseEnd_2740284 := by
    simpa [prefixWord, tailWord_2740284, baseEnd_2740284] using wordTrace_append hprefix tailTrace_2740284
  have hstable : (prefixWord ++ tailWord_2740284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740284).length < 2 ^ (prefixWord ++ tailWord_2740284).sum := by decide
  have hdescent : baseEnd_2740284 < baseStart_2740284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740304 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 4]
def baseStart_2740304 : Nat := 118140960795 + 2740304 * 2 ^ 59
def prefixEnd_2740304 : Nat := 4983230072969 + 3 ^ 40 * 2740304 * 2
def baseEnd_2740304 : Nat := 1407093091438351781697577

theorem tailTrace_2740304 : CollatzResearch.WordTrace tailWord_2740304 prefixEnd_2740304 1407093091438351781697577 := by
  unfold tailWord_2740304
  simp only [CollatzResearch.WordTrace]
  refine ⟨49973548932177044754197983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66631398576236059672263977 49973548932177044754197983)
  ·
    refine ⟨74960323398265567131296975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49973548932177044754197983 74960323398265567131296975)
    ·
      refine ⟨112440485097398350696945463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74960323398265567131296975 112440485097398350696945463)
      ·
        refine ⟨168660727646097526045418195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112440485097398350696945463 168660727646097526045418195)
        ·
          refine ⟨252991091469146289068127293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168660727646097526045418195 252991091469146289068127293)
          ·
            refine ⟨94871659300929858400547735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252991091469146289068127293 94871659300929858400547735)
            ·
              refine ⟨142307488951394787600821603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94871659300929858400547735 142307488951394787600821603)
              ·
                refine ⟨213461233427092181401232405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142307488951394787600821603 213461233427092181401232405)
                ·
                  refine ⟨10005995316894946003182769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 213461233427092181401232405 10005995316894946003182769)
                  ·
                    refine ⟨7504496487671209502387077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10005995316894946003182769 7504496487671209502387077)
                    ·
                      refine ⟨1407093091438351781697577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7504496487671209502387077 1407093091438351781697577)
                      ·
                        rfl

theorem cell23_2740304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_2740304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740304 prefixEnd_2740304 := by exact prefixLift 2740304
  have htrace : WordTrace (prefixWord ++ tailWord_2740304) baseStart_2740304 baseEnd_2740304 := by
    simpa [prefixWord, tailWord_2740304, baseEnd_2740304] using wordTrace_append hprefix tailTrace_2740304
  have hstable : (prefixWord ++ tailWord_2740304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740304).length < 2 ^ (prefixWord ++ tailWord_2740304).sum := by decide
  have hdescent : baseEnd_2740304 < baseStart_2740304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740324 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_2740324 : Nat := 118140960795 + 2740324 * 2 ^ 59
def prefixEnd_2740324 : Nat := 4983230072969 + 3 ^ 40 * 2740324 * 2
def baseEnd_2740324 : Nat := 1407103361051441703447485

theorem tailTrace_2740324 : CollatzResearch.WordTrace tailWord_2740324 prefixEnd_2740324 1407103361051441703447485 := by
  unfold tailWord_2740324
  simp only [CollatzResearch.WordTrace]
  refine ⟨49973913662140816462062013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66631884882854421949416017 49973913662140816462062013)
  ·
    refine ⟨18740217623302806173273255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49973913662140816462062013 18740217623302806173273255)
    ·
      refine ⟨28110326434954209259909883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18740217623302806173273255 28110326434954209259909883)
      ·
        refine ⟨42165489652431313889864825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28110326434954209259909883 42165489652431313889864825)
        ·
          refine ⟨31624117239323485417398619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42165489652431313889864825 31624117239323485417398619)
          ·
            refine ⟨47436175858985228126097929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31624117239323485417398619 47436175858985228126097929)
            ·
              refine ⟨35577131894238921094573447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47436175858985228126097929 35577131894238921094573447)
              ·
                refine ⟨53365697841358381641860171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35577131894238921094573447 53365697841358381641860171)
                ·
                  refine ⟨80048546762037572462790257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53365697841358381641860171 80048546762037572462790257)
                  ·
                    refine ⟨60036410071528179347092693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80048546762037572462790257 60036410071528179347092693)
                    ·
                      refine ⟨1407103361051441703447485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60036410071528179347092693 1407103361051441703447485)
                      ·
                        rfl

theorem cell23_2740324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_2740324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740324 prefixEnd_2740324 := by exact prefixLift 2740324
  have htrace : WordTrace (prefixWord ++ tailWord_2740324) baseStart_2740324 baseEnd_2740324 := by
    simpa [prefixWord, tailWord_2740324, baseEnd_2740324] using wordTrace_append hprefix tailTrace_2740324
  have hstable : (prefixWord ++ tailWord_2740324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740324).length < 2 ^ (prefixWord ++ tailWord_2740324).sum := by decide
  have hdescent : baseEnd_2740324 < baseStart_2740324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740325 : List Nat := [1, 3, 1, 3, 2, 2, 1, 4, 2, 2, 2]
def baseStart_2740325 : Nat := 118140960795 + 2740325 * 2 ^ 59
def prefixEnd_2740325 : Nat := 4983230072969 + 3 ^ 40 * 2740325 * 2
def baseEnd_2740325 : Nat := 1407103874532096199534981

theorem tailTrace_2740325 : CollatzResearch.WordTrace tailWord_2740325 prefixEnd_2740325 1407103874532096199534981 := by
  unfold tailWord_2740325
  simp only [CollatzResearch.WordTrace]
  refine ⟨99947863797278010094910429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66631909198185340063273619 99947863797278010094910429)
  ·
    refine ⟨37480448923979253785591411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99947863797278010094910429 37480448923979253785591411)
    ·
      refine ⟨56220673385968880678387117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37480448923979253785591411 56220673385968880678387117)
      ·
        refine ⟨21082752519738330254395169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56220673385968880678387117 21082752519738330254395169)
        ·
          refine ⟨15812064389803747690796377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21082752519738330254395169 15812064389803747690796377)
          ·
            refine ⟨11859048292352810768097283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15812064389803747690796377 11859048292352810768097283)
            ·
              refine ⟨17788572438529216152145925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11859048292352810768097283 17788572438529216152145925)
              ·
                refine ⟨3335357332224228028527361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17788572438529216152145925 3335357332224228028527361)
                ·
                  refine ⟨2501517999168171021395521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3335357332224228028527361 2501517999168171021395521)
                  ·
                    refine ⟨1876138499376128266046641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2501517999168171021395521 1876138499376128266046641)
                    ·
                      refine ⟨1407103874532096199534981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1876138499376128266046641 1407103874532096199534981)
                      ·
                        rfl

theorem cell23_2740325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_2740325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740325 prefixEnd_2740325 := by exact prefixLift 2740325
  have htrace : WordTrace (prefixWord ++ tailWord_2740325) baseStart_2740325 baseEnd_2740325 := by
    simpa [prefixWord, tailWord_2740325, baseEnd_2740325] using wordTrace_append hprefix tailTrace_2740325
  have hstable : (prefixWord ++ tailWord_2740325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740325).length < 2 ^ (prefixWord ++ tailWord_2740325).sum := by decide
  have hdescent : baseEnd_2740325 < baseStart_2740325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740342 : List Nat := [5, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2]
def baseStart_2740342 : Nat := 118140960795 + 2740342 * 2 ^ 59
def prefixEnd_2740342 : Nat := 4983230072969 + 3 ^ 40 * 2740342 * 2
def baseEnd_2740342 : Nat := 1407112603703222633022403

theorem tailTrace_2740342 : CollatzResearch.WordTrace tailWord_2740342 prefixEnd_2740342 1407112603703222633022403 := by
  unfold tailWord_2740342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6246780239888526374892455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66632322558810947998852853 6246780239888526374892455)
  ·
    refine ⟨9370170359832789562338683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6246780239888526374892455 9370170359832789562338683)
    ·
      refine ⟨14055255539749184343508025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9370170359832789562338683 14055255539749184343508025)
      ·
        refine ⟨10541441654811888257631019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14055255539749184343508025 10541441654811888257631019)
        ·
          refine ⟨15812162482217832386446529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10541441654811888257631019 15812162482217832386446529)
          ·
            refine ⟨11859121861663374289834897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15812162482217832386446529 11859121861663374289834897)
            ·
              refine ⟨8894341396247530717376173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11859121861663374289834897 8894341396247530717376173)
              ·
                refine ⟨3335378023592824019016065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8894341396247530717376173 3335378023592824019016065)
                ·
                  refine ⟨2501533517694618014262049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3335378023592824019016065 2501533517694618014262049)
                  ·
                    refine ⟨1876150138270963510696537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2501533517694618014262049 1876150138270963510696537)
                    ·
                      refine ⟨1407112603703222633022403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1876150138270963510696537 1407112603703222633022403)
                      ·
                        rfl

theorem cell23_2740342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_2740342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740342 prefixEnd_2740342 := by exact prefixLift 2740342
  have htrace : WordTrace (prefixWord ++ tailWord_2740342) baseStart_2740342 baseEnd_2740342 := by
    simpa [prefixWord, tailWord_2740342, baseEnd_2740342] using wordTrace_append hprefix tailTrace_2740342
  have hstable : (prefixWord ++ tailWord_2740342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740342).length < 2 ^ (prefixWord ++ tailWord_2740342).sum := by decide
  have hdescent : baseEnd_2740342 < baseStart_2740342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740344 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 1, 7]
def baseStart_2740344 : Nat := 118140960795 + 2740344 * 2 ^ 59
def prefixEnd_2740344 : Nat := 4983230072969 + 3 ^ 40 * 2740344 * 2
def baseEnd_2740344 : Nat := 469037876888177208399131

theorem tailTrace_2740344 : CollatzResearch.WordTrace tailWord_2740344 prefixEnd_2740344 469037876888177208399131 := by
  unfold tailWord_2740344
  simp only [CollatzResearch.WordTrace]
  refine ⟨49974278392104588169926043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66632371189472784226568057 49974278392104588169926043)
  ·
    refine ⟨74961417588156882254889065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49974278392104588169926043 74961417588156882254889065)
    ·
      refine ⟨56221063191117661691166799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74961417588156882254889065 56221063191117661691166799)
      ·
        refine ⟨84331594786676492536750199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56221063191117661691166799 84331594786676492536750199)
        ·
          refine ⟨126497392180014738805125299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84331594786676492536750199 126497392180014738805125299)
          ·
            refine ⟨189746088270022108207687949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126497392180014738805125299 189746088270022108207687949)
            ·
              refine ⟨71154783101258290577882981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189746088270022108207687949 71154783101258290577882981)
              ·
                refine ⟨13341521831485929483353059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71154783101258290577882981 13341521831485929483353059)
                ·
                  refine ⟨20012282747228894225029589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13341521831485929483353059 20012282747228894225029589)
                  ·
                    refine ⟨469037876888177208399131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20012282747228894225029589 469037876888177208399131)
                    ·
                      rfl

theorem cell23_2740344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_2740344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740344 prefixEnd_2740344 := by exact prefixLift 2740344
  have htrace : WordTrace (prefixWord ++ tailWord_2740344) baseStart_2740344 baseEnd_2740344 := by
    simpa [prefixWord, tailWord_2740344, baseEnd_2740344] using wordTrace_append hprefix tailTrace_2740344
  have hstable : (prefixWord ++ tailWord_2740344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740344).length < 2 ^ (prefixWord ++ tailWord_2740344).sum := by decide
  have hdescent : baseEnd_2740344 < baseStart_2740344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740455 : List Nat := [1, 1, 5, 3, 1, 1, 4, 1, 6]
def baseStart_2740455 : Nat := 118140960795 + 2740455 * 2 ^ 59
def prefixEnd_2740455 : Nat := 4983230072969 + 3 ^ 40 * 2740455 * 2
def baseEnd_2740455 : Nat := 156352291890797854545487

theorem tailTrace_2740455 : CollatzResearch.WordTrace tailWord_2740455 prefixEnd_2740455 156352291890797854545487 := by
  unfold tailWord_2740455
  simp only [CollatzResearch.WordTrace]
  refine ⟨99952605286807042297142819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66635070191204694864761879 99952605286807042297142819)
  ·
    refine ⟨149928907930210563445714229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99952605286807042297142819 149928907930210563445714229)
    ·
      refine ⟨14055835118457240323035709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149928907930210563445714229 14055835118457240323035709)
      ·
        refine ⟨5270938169421465121138391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14055835118457240323035709 5270938169421465121138391)
        ·
          refine ⟨7906407254132197681707587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5270938169421465121138391 7906407254132197681707587)
          ·
            refine ⟨11859610881198296522561381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7906407254132197681707587 11859610881198296522561381)
            ·
              refine ⟨2223677040224680597980259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11859610881198296522561381 2223677040224680597980259)
              ·
                refine ⟨3335515560337020896970389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2223677040224680597980259 3335515560337020896970389)
                ·
                  refine ⟨156352291890797854545487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3335515560337020896970389 156352291890797854545487)
                  ·
                    rfl

theorem cell23_2740455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 6].length) (baseStart_2740455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740455 prefixEnd_2740455 := by exact prefixLift 2740455
  have htrace : WordTrace (prefixWord ++ tailWord_2740455) baseStart_2740455 baseEnd_2740455 := by
    simpa [prefixWord, tailWord_2740455, baseEnd_2740455] using wordTrace_append hprefix tailTrace_2740455
  have hstable : (prefixWord ++ tailWord_2740455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740455).length < 2 ^ (prefixWord ++ tailWord_2740455).sum := by decide
  have hdescent : baseEnd_2740455 < baseStart_2740455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740501 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_2740501 : Nat := 118140960795 + 2740501 * 2 ^ 59
def prefixEnd_2740501 : Nat := 4983230072969 + 3 ^ 40 * 2740501 * 2
def baseEnd_2740501 : Nat := 1407194247127287510934171

theorem tailTrace_2740501 : CollatzResearch.WordTrace tailWord_2740501 prefixEnd_2740501 1407194247127287510934171 := by
  unfold tailWord_2740501
  simp only [CollatzResearch.WordTrace]
  refine ⟨99954283044640392153317357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66636188696426928102211571 99954283044640392153317357)
  ·
    refine ⟨37482856141740147057494009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99954283044640392153317357 37482856141740147057494009)
    ·
      refine ⟨28112142106305110293120507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37482856141740147057494009 28112142106305110293120507)
      ·
        refine ⟨42168213159457665439680761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28112142106305110293120507 42168213159457665439680761)
        ·
          refine ⟨31626159869593249079760571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42168213159457665439680761 31626159869593249079760571)
          ·
            refine ⟨47439239804389873619640857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31626159869593249079760571 47439239804389873619640857)
            ·
              refine ⟨35579429853292405214730643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47439239804389873619640857 35579429853292405214730643)
              ·
                refine ⟨53369144779938607822095965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35579429853292405214730643 53369144779938607822095965)
                ·
                  refine ⟨20013429292476977933285987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53369144779938607822095965 20013429292476977933285987)
                  ·
                    refine ⟨30020143938715466899928981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20013429292476977933285987 30020143938715466899928981)
                    ·
                      refine ⟨1407194247127287510934171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30020143938715466899928981 1407194247127287510934171)
                      ·
                        rfl

theorem cell23_2740501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_2740501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740501 prefixEnd_2740501 := by exact prefixLift 2740501
  have htrace : WordTrace (prefixWord ++ tailWord_2740501) baseStart_2740501 baseEnd_2740501 := by
    simpa [prefixWord, tailWord_2740501, baseEnd_2740501] using wordTrace_append hprefix tailTrace_2740501
  have hstable : (prefixWord ++ tailWord_2740501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740501).length < 2 ^ (prefixWord ++ tailWord_2740501).sum := by decide
  have hdescent : baseEnd_2740501 < baseStart_2740501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740526 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_2740526 : Nat := 118140960795 + 2740526 * 2 ^ 59
def prefixEnd_2740526 : Nat := 4983230072969 + 3 ^ 40 * 2740526 * 2
def baseEnd_2740526 : Nat := 1407207084143649913121557

theorem tailTrace_2740526 : CollatzResearch.WordTrace tailWord_2740526 prefixEnd_2740526 1407207084143649913121557 := by
  unfold tailWord_2740526
  simp only [CollatzResearch.WordTrace]
  refine ⟨12494399358693727677872179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66636796579699880948651621 12494399358693727677872179)
  ·
    refine ⟨18741599038040591516808269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12494399358693727677872179 18741599038040591516808269)
    ·
      refine ⟨7028099639265221818803101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18741599038040591516808269 7028099639265221818803101)
      ·
        refine ⟨2635537364724458182051163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7028099639265221818803101 2635537364724458182051163)
        ·
          refine ⟨3953306047086687273076745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2635537364724458182051163 3953306047086687273076745)
          ·
            refine ⟨2964979535315015454807559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3953306047086687273076745 2964979535315015454807559)
            ·
              refine ⟨4447469302972523182211339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2964979535315015454807559 4447469302972523182211339)
              ·
                refine ⟨6671203954458784773317009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4447469302972523182211339 6671203954458784773317009)
                ·
                  refine ⟨5003402965844088579987757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6671203954458784773317009 5003402965844088579987757)
                  ·
                    refine ⟨1876276112191533217495409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5003402965844088579987757 1876276112191533217495409)
                    ·
                      refine ⟨1407207084143649913121557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1876276112191533217495409 1407207084143649913121557)
                      ·
                        rfl

theorem cell23_2740526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_2740526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740526 prefixEnd_2740526 := by exact prefixLift 2740526
  have htrace : WordTrace (prefixWord ++ tailWord_2740526) baseStart_2740526 baseEnd_2740526 := by
    simpa [prefixWord, tailWord_2740526, baseEnd_2740526] using wordTrace_append hprefix tailTrace_2740526
  have hstable : (prefixWord ++ tailWord_2740526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740526).length < 2 ^ (prefixWord ++ tailWord_2740526).sum := by decide
  have hdescent : baseEnd_2740526 < baseStart_2740526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740542 : List Nat := [4, 2, 1, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_2740542 : Nat := 118140960795 + 2740542 * 2 ^ 59
def prefixEnd_2740542 : Nat := 4983230072969 + 3 ^ 40 * 2740542 * 2
def baseEnd_2740542 : Nat := 1407215299834121850521483

theorem tailTrace_2740542 : CollatzResearch.WordTrace tailWord_2740542 prefixEnd_2740542 1407215299834121850521483 := by
  unfold tailWord_2740542
  simp only [CollatzResearch.WordTrace]
  refine ⟨12494472304686482019444985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66637185624994570770373253 12494472304686482019444985)
  ·
    refine ⟨9370854228514861514583739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12494472304686482019444985 9370854228514861514583739)
    ·
      refine ⟨14056281342772292271875609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9370854228514861514583739 14056281342772292271875609)
      ·
        refine ⟨10542211007079219203906707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14056281342772292271875609 10542211007079219203906707)
        ·
          refine ⟨15813316510618828805860061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10542211007079219203906707 15813316510618828805860061)
          ·
            refine ⟨5929993691482060802197523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15813316510618828805860061 5929993691482060802197523)
            ·
              refine ⟨8894990537223091203296285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5929993691482060802197523 8894990537223091203296285)
              ·
                refine ⟨3335621451458659201236107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8894990537223091203296285 3335621451458659201236107)
                ·
                  refine ⟨5003432177187988801854161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3335621451458659201236107 5003432177187988801854161)
                  ·
                    refine ⟨3752574132890991601390621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5003432177187988801854161 3752574132890991601390621)
                    ·
                      refine ⟨1407215299834121850521483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3752574132890991601390621 1407215299834121850521483)
                      ·
                        rfl

theorem cell23_2740542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_2740542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740542 prefixEnd_2740542 := by exact prefixLift 2740542
  have htrace : WordTrace (prefixWord ++ tailWord_2740542) baseStart_2740542 baseEnd_2740542 := by
    simpa [prefixWord, tailWord_2740542, baseEnd_2740542] using wordTrace_append hprefix tailTrace_2740542
  have hstable : (prefixWord ++ tailWord_2740542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740542).length < 2 ^ (prefixWord ++ tailWord_2740542).sum := by decide
  have hdescent : baseEnd_2740542 < baseStart_2740542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740555 : List Nat := [1, 1, 1, 1, 3, 1, 1, 8, 2, 1, 3]
def baseStart_2740555 : Nat := 118140960795 + 2740555 * 2 ^ 59
def prefixEnd_2740555 : Nat := 4983230072969 + 3 ^ 40 * 2740555 * 2
def baseEnd_2740555 : Nat := 1407221975082630299658923

theorem tailTrace_2740555 : CollatzResearch.WordTrace tailWord_2740555 prefixEnd_2740555 1407221975082630299658923 := by
  unfold tailWord_2740555
  simp only [CollatzResearch.WordTrace]
  refine ⟨99956252586444759375783119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66637501724296506250522079 99956252586444759375783119)
  ·
    refine ⟨149934378879667139063674679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99956252586444759375783119 149934378879667139063674679)
    ·
      refine ⟨224901568319500708595512019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149934378879667139063674679 224901568319500708595512019)
      ·
        refine ⟨337352352479251062893268029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224901568319500708595512019 337352352479251062893268029)
        ·
          refine ⟨126507132179719148584975511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337352352479251062893268029 126507132179719148584975511)
          ·
            refine ⟨189760698269578722877463267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126507132179719148584975511 189760698269578722877463267)
            ·
              refine ⟨284641047404368084316194901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189760698269578722877463267 284641047404368084316194901)
              ·
                refine ⟨3335637274269938488080409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 284641047404368084316194901 3335637274269938488080409)
                ·
                  refine ⟨2501727955702453866060307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3335637274269938488080409 2501727955702453866060307)
                  ·
                    refine ⟨3752591933553680799090461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2501727955702453866060307 3752591933553680799090461)
                    ·
                      refine ⟨1407221975082630299658923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3752591933553680799090461 1407221975082630299658923)
                      ·
                        rfl

theorem cell23_2740555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 1, 3].length) (baseStart_2740555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740555 prefixEnd_2740555 := by exact prefixLift 2740555
  have htrace : WordTrace (prefixWord ++ tailWord_2740555) baseStart_2740555 baseEnd_2740555 := by
    simpa [prefixWord, tailWord_2740555, baseEnd_2740555] using wordTrace_append hprefix tailTrace_2740555
  have hstable : (prefixWord ++ tailWord_2740555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740555).length < 2 ^ (prefixWord ++ tailWord_2740555).sum := by decide
  have hdescent : baseEnd_2740555 < baseStart_2740555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740612 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 4, 2, 2]
def baseStart_2740612 : Nat := 118140960795 + 2740612 * 2 ^ 59
def prefixEnd_2740612 : Nat := 4983230072969 + 3 ^ 40 * 2740612 * 2
def baseEnd_2740612 : Nat := 1407251243479936576646161

theorem tailTrace_2740612 : CollatzResearch.WordTrace tailWord_2740612 prefixEnd_2740612 1407251243479936576646161 := by
  unfold tailWord_2740612
  simp only [CollatzResearch.WordTrace]
  refine ⟨49979165773619129055304045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66638887698158838740405393 49979165773619129055304045)
  ·
    refine ⟨18742187165107173395739017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49979165773619129055304045 18742187165107173395739017)
    ·
      refine ⟨14056640373830380046804263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18742187165107173395739017 14056640373830380046804263)
      ·
        refine ⟨21084960560745570070206395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14056640373830380046804263 21084960560745570070206395)
        ·
          refine ⟨31627440841118355105309593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21084960560745570070206395 31627440841118355105309593)
          ·
            refine ⟨23720580630838766328982195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31627440841118355105309593 23720580630838766328982195)
            ·
              refine ⟨35580870946258149493473293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23720580630838766328982195 35580870946258149493473293)
              ·
                refine ⟨13342826604846806060052485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35580870946258149493473293 13342826604846806060052485)
                ·
                  refine ⟨2501779988408776136259841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13342826604846806060052485 2501779988408776136259841)
                  ·
                    refine ⟨1876334991306582102194881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2501779988408776136259841 1876334991306582102194881)
                    ·
                      refine ⟨1407251243479936576646161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1876334991306582102194881 1407251243479936576646161)
                      ·
                        rfl

theorem cell23_2740612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_2740612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740612 prefixEnd_2740612 := by exact prefixLift 2740612
  have htrace : WordTrace (prefixWord ++ tailWord_2740612) baseStart_2740612 baseEnd_2740612 := by
    simpa [prefixWord, tailWord_2740612, baseEnd_2740612] using wordTrace_append hprefix tailTrace_2740612
  have hstable : (prefixWord ++ tailWord_2740612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740612).length < 2 ^ (prefixWord ++ tailWord_2740612).sum := by decide
  have hdescent : baseEnd_2740612 < baseStart_2740612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740650 : List Nat := [3, 1, 6, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_2740650 : Nat := 118140960795 + 2740650 * 2 ^ 59
def prefixEnd_2740650 : Nat := 4983230072969 + 3 ^ 40 * 2740650 * 2
def baseEnd_2740650 : Nat := 1407270755744807427970987

theorem tailTrace_2740650 : CollatzResearch.WordTrace tailWord_2740650 prefixEnd_2740650 1407270755744807427970987 := by
  unfold tailWord_2740650
  simp only [CollatzResearch.WordTrace]
  refine ⟨24989929380275147650122851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66639811680733727066994269 24989929380275147650122851)
  ·
    refine ⟨37484894070412721475184277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24989929380275147650122851 37484894070412721475184277)
    ·
      refine ⟨1757104409550596319149263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37484894070412721475184277 1757104409550596319149263)
      ·
        refine ⟨2635656614325894478723895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1757104409550596319149263 2635656614325894478723895)
        ·
          refine ⟨3953484921488841718085843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2635656614325894478723895 3953484921488841718085843)
          ·
            refine ⟨5930227382233262577128765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3953484921488841718085843 5930227382233262577128765)
            ·
              refine ⟨2223835268337473466423287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5930227382233262577128765 2223835268337473466423287)
              ·
                refine ⟨3335752902506210199634931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2223835268337473466423287 3335752902506210199634931)
                ·
                  refine ⟨5003629353759315299452397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3335752902506210199634931 5003629353759315299452397)
                  ·
                    refine ⟨1876361007659743237294649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5003629353759315299452397 1876361007659743237294649)
                    ·
                      refine ⟨1407270755744807427970987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1876361007659743237294649 1407270755744807427970987)
                      ·
                        rfl

theorem cell23_2740650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_2740650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740650 prefixEnd_2740650 := by exact prefixLift 2740650
  have htrace : WordTrace (prefixWord ++ tailWord_2740650) baseStart_2740650 baseEnd_2740650 := by
    simpa [prefixWord, tailWord_2740650, baseEnd_2740650] using wordTrace_append hprefix tailTrace_2740650
  have hstable : (prefixWord ++ tailWord_2740650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740650).length < 2 ^ (prefixWord ++ tailWord_2740650).sum := by decide
  have hdescent : baseEnd_2740650 < baseStart_2740650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740658 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_2740658 : Nat := 118140960795 + 2740658 * 2 ^ 59
def prefixEnd_2740658 : Nat := 4983230072969 + 3 ^ 40 * 2740658 * 2
def baseEnd_2740658 : Nat := 1407274863590043396670949

theorem tailTrace_2740658 : CollatzResearch.WordTrace tailWord_2740658 prefixEnd_2740658 1407274863590043396670949 := by
  unfold tailWord_2740658
  simp only [CollatzResearch.WordTrace]
  refine ⟨24990002326267901991695657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66640006203381071977855085 24990002326267901991695657)
  ·
    refine ⟨18742501744700926493771743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24990002326267901991695657 18742501744700926493771743)
    ·
      refine ⟨28113752617051389740657615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18742501744700926493771743 28113752617051389740657615)
      ·
        refine ⟨42170628925577084610986423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28113752617051389740657615 42170628925577084610986423)
        ·
          refine ⟨63255943388365626916479635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42170628925577084610986423 63255943388365626916479635)
          ·
            refine ⟨94883915082548440374719453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63255943388365626916479635 94883915082548440374719453)
            ·
              refine ⟨35581468155955665140519795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94883915082548440374719453 35581468155955665140519795)
              ·
                refine ⟨53372202233933497710779693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35581468155955665140519795 53372202233933497710779693)
                ·
                  refine ⟨20014575837725061641542385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53372202233933497710779693 20014575837725061641542385)
                  ·
                    refine ⟨15010931878293796231156789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20014575837725061641542385 15010931878293796231156789)
                    ·
                      refine ⟨1407274863590043396670949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15010931878293796231156789 1407274863590043396670949)
                      ·
                        rfl

theorem cell23_2740658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_2740658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740658 prefixEnd_2740658 := by exact prefixLift 2740658
  have htrace : WordTrace (prefixWord ++ tailWord_2740658) baseStart_2740658 baseEnd_2740658 := by
    simpa [prefixWord, tailWord_2740658, baseEnd_2740658] using wordTrace_append hprefix tailTrace_2740658
  have hstable : (prefixWord ++ tailWord_2740658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740658).length < 2 ^ (prefixWord ++ tailWord_2740658).sum := by decide
  have hdescent : baseEnd_2740658 < baseStart_2740658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740665 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 2, 5]
def baseStart_2740665 : Nat := 118140960795 + 2740665 * 2 ^ 59
def prefixEnd_2740665 : Nat := 4983230072969 + 3 ^ 40 * 2740665 * 2
def baseEnd_2740665 : Nat := 469092819318208289761139

theorem tailTrace_2740665 : CollatzResearch.WordTrace tailWord_2740665 prefixEnd_2740665 469092819318208289761139 := by
  unfold tailWord_2740665
  simp only [CollatzResearch.WordTrace]
  refine ⟨99960264616046248162287449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66640176410697498774858299 99960264616046248162287449)
  ·
    refine ⟨74970198462034686121715587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99960264616046248162287449 74970198462034686121715587)
    ·
      refine ⟨112455297693052029182573381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74970198462034686121715587 112455297693052029182573381)
      ·
        refine ⟨21085368317447255471732509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112455297693052029182573381 21085368317447255471732509)
        ·
          refine ⟨7907013119042720801899691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21085368317447255471732509 7907013119042720801899691)
          ·
            refine ⟨11860519678564081202849537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7907013119042720801899691 11860519678564081202849537)
            ·
              refine ⟨8895389758923060902137153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11860519678564081202849537 8895389758923060902137153)
              ·
                refine ⟨6671542319192295676602865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8895389758923060902137153 6671542319192295676602865)
                ·
                  refine ⟨5003656739394221757452149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6671542319192295676602865 5003656739394221757452149)
                  ·
                    refine ⟨469092819318208289761139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5003656739394221757452149 469092819318208289761139)
                    ·
                      rfl

theorem cell23_2740665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 5].length) (baseStart_2740665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740665 prefixEnd_2740665 := by exact prefixLift 2740665
  have htrace : WordTrace (prefixWord ++ tailWord_2740665) baseStart_2740665 baseEnd_2740665 := by
    simpa [prefixWord, tailWord_2740665, baseEnd_2740665] using wordTrace_append hprefix tailTrace_2740665
  have hstable : (prefixWord ++ tailWord_2740665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740665).length < 2 ^ (prefixWord ++ tailWord_2740665).sum := by decide
  have hdescent : baseEnd_2740665 < baseStart_2740665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740669 : List Nat := [1, 4, 1, 2, 2, 4, 2, 2, 5]
def baseStart_2740669 : Nat := 118140960795 + 2740669 * 2 ^ 59
def prefixEnd_2740669 : Nat := 4983230072969 + 3 ^ 40 * 2740669 * 2
def baseEnd_2740669 : Nat := 156364501319693650403711

theorem tailTrace_2740669 : CollatzResearch.WordTrace tailWord_2740669 prefixEnd_2740669 156364501319693650403711 := by
  unfold tailWord_2740669
  simp only [CollatzResearch.WordTrace]
  refine ⟨99960410508031756845433061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66640273672021171230288707 99960410508031756845433061)
  ·
    refine ⟨18742576970255954408518699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99960410508031756845433061 18742576970255954408518699)
    ·
      refine ⟨28113865455383931612778049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18742576970255954408518699 28113865455383931612778049)
      ·
        refine ⟨21085399091537948709583537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28113865455383931612778049 21085399091537948709583537)
        ·
          refine ⟨15814049318653461532187653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21085399091537948709583537 15814049318653461532187653)
          ·
            refine ⟨2965134247247524037285185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15814049318653461532187653 2965134247247524037285185)
            ·
              refine ⟨2223850685435643027963889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2965134247247524037285185 2223850685435643027963889)
              ·
                refine ⟨1667888014076732270972917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2223850685435643027963889 1667888014076732270972917)
                ·
                  refine ⟨156364501319693650403711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1667888014076732270972917 156364501319693650403711)
                  ·
                    rfl

theorem cell23_2740669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_2740669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740669 prefixEnd_2740669 := by exact prefixLift 2740669
  have htrace : WordTrace (prefixWord ++ tailWord_2740669) baseStart_2740669 baseEnd_2740669 := by
    simpa [prefixWord, tailWord_2740669, baseEnd_2740669] using wordTrace_append hprefix tailTrace_2740669
  have hstable : (prefixWord ++ tailWord_2740669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740669).length < 2 ^ (prefixWord ++ tailWord_2740669).sum := by decide
  have hdescent : baseEnd_2740669 < baseStart_2740669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740705 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 1, 4, 3]
def baseStart_2740705 : Nat := 118140960795 + 2740705 * 2 ^ 59
def prefixEnd_2740705 : Nat := 4983230072969 + 3 ^ 40 * 2740705 * 2
def baseEnd_2740705 : Nat := 1407298997180804712783233

theorem tailTrace_2740705 : CollatzResearch.WordTrace tailWord_2740705 prefixEnd_2740705 1407298997180804712783233 := by
  unfold tailWord_2740705
  simp only [CollatzResearch.WordTrace]
  refine ⟨99961723535901334993743569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66641149023934223329162379 99961723535901334993743569)
  ·
    refine ⟨74971292651926001245307677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99961723535901334993743569 74971292651926001245307677)
    ·
      refine ⟨28114234744472250466990379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74971292651926001245307677 28114234744472250466990379)
      ·
        refine ⟨42171352116708375700485569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28114234744472250466990379 42171352116708375700485569)
        ·
          refine ⟨31628514087531281775364177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42171352116708375700485569 31628514087531281775364177)
          ·
            refine ⟨23721385565648461331523133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31628514087531281775364177 23721385565648461331523133)
            ·
              refine ⟨8895519587118172999321175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23721385565648461331523133 8895519587118172999321175)
              ·
                refine ⟨13343279380677259498981763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8895519587118172999321175 13343279380677259498981763)
                ·
                  refine ⟨20014919071015889248472645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13343279380677259498981763 20014919071015889248472645)
                  ·
                    refine ⟨3752797325815479234088621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20014919071015889248472645 3752797325815479234088621)
                    ·
                      refine ⟨1407298997180804712783233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3752797325815479234088621 1407298997180804712783233)
                      ·
                        rfl

theorem cell23_2740705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_2740705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740705 prefixEnd_2740705 := by exact prefixLift 2740705
  have htrace : WordTrace (prefixWord ++ tailWord_2740705) baseStart_2740705 baseEnd_2740705 := by
    simpa [prefixWord, tailWord_2740705, baseEnd_2740705] using wordTrace_append hprefix tailTrace_2740705
  have hstable : (prefixWord ++ tailWord_2740705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740705).length < 2 ^ (prefixWord ++ tailWord_2740705).sum := by decide
  have hdescent : baseEnd_2740705 < baseStart_2740705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740728 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 1, 1, 8]
def baseStart_2740728 : Nat := 118140960795 + 2740728 * 2 ^ 59
def prefixEnd_2740728 : Nat := 4983230072969 + 3 ^ 40 * 2740728 * 2
def baseEnd_2740728 : Nat := 1407310807235858122795627

theorem tailTrace_2740728 : CollatzResearch.WordTrace tailWord_2740728 prefixEnd_2740728 1407310807235858122795627 := by
  unfold tailWord_2740728
  simp only [CollatzResearch.WordTrace]
  refine ⟨49981281207409004960915419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66641708276545339947887225 49981281207409004960915419)
  ·
    refine ⟨74971921811113507441373129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49981281207409004960915419 74971921811113507441373129)
    ·
      refine ⟨56228941358335130581029847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74971921811113507441373129 56228941358335130581029847)
      ·
        refine ⟨84343412037502695871544771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56228941358335130581029847 84343412037502695871544771)
        ·
          refine ⟨126515118056254043807317157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84343412037502695871544771 126515118056254043807317157)
          ·
            refine ⟨23721584635547633213871967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126515118056254043807317157 23721584635547633213871967)
            ·
              refine ⟨35582376953321449820807951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23721584635547633213871967 35582376953321449820807951)
              ·
                refine ⟨53373565429982174731211927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35582376953321449820807951 53373565429982174731211927)
                ·
                  refine ⟨80060348144973262096817891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53373565429982174731211927 80060348144973262096817891)
                  ·
                    refine ⟨120090522217459893145226837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80060348144973262096817891 120090522217459893145226837)
                    ·
                      refine ⟨1407310807235858122795627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 120090522217459893145226837 1407310807235858122795627)
                      ·
                        rfl

theorem cell23_2740728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_2740728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740728 prefixEnd_2740728 := by exact prefixLift 2740728
  have htrace : WordTrace (prefixWord ++ tailWord_2740728) baseStart_2740728 baseEnd_2740728 := by
    simpa [prefixWord, tailWord_2740728, baseEnd_2740728] using wordTrace_append hprefix tailTrace_2740728
  have hstable : (prefixWord ++ tailWord_2740728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740728).length < 2 ^ (prefixWord ++ tailWord_2740728).sum := by decide
  have hdescent : baseEnd_2740728 < baseStart_2740728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740762 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2]
def baseStart_2740762 : Nat := 118140960795 + 2740762 * 2 ^ 59
def prefixEnd_2740762 : Nat := 4983230072969 + 3 ^ 40 * 2740762 * 2
def baseEnd_2740762 : Nat := 1407328265578110989770471

theorem tailTrace_2740762 : CollatzResearch.WordTrace tailWord_2740762 prefixEnd_2740762 1407328265578110989770471 := by
  unfold tailWord_2740762
  simp only [CollatzResearch.WordTrace]
  refine ⟨24990950624173708432142135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66642534997796555819045693 24990950624173708432142135)
  ·
    refine ⟨37486425936260562648213203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24990950624173708432142135 37486425936260562648213203)
    ·
      refine ⟨56229638904390843972319805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37486425936260562648213203 56229638904390843972319805)
      ·
        refine ⟨21086114589146566489619927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56229638904390843972319805 21086114589146566489619927)
        ·
          refine ⟨31629171883719849734429891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21086114589146566489619927 31629171883719849734429891)
          ·
            refine ⟨47443757825579774601644837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31629171883719849734429891 47443757825579774601644837)
            ·
              refine ⟨8895704592296207737808407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47443757825579774601644837 8895704592296207737808407)
              ·
                refine ⟨13343556888444311606712611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8895704592296207737808407 13343556888444311606712611)
                ·
                  refine ⟨20015335332666467410068917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13343556888444311606712611 20015335332666467410068917)
                  ·
                    refine ⟨1876437687437481319693961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20015335332666467410068917 1876437687437481319693961)
                    ·
                      refine ⟨1407328265578110989770471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1876437687437481319693961 1407328265578110989770471)
                      ·
                        rfl

theorem cell23_2740762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_2740762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740762 prefixEnd_2740762 := by exact prefixLift 2740762
  have htrace : WordTrace (prefixWord ++ tailWord_2740762) baseStart_2740762 baseEnd_2740762 := by
    simpa [prefixWord, tailWord_2740762, baseEnd_2740762] using wordTrace_append hprefix tailTrace_2740762
  have hstable : (prefixWord ++ tailWord_2740762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740762).length < 2 ^ (prefixWord ++ tailWord_2740762).sum := by decide
  have hdescent : baseEnd_2740762 < baseStart_2740762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740805 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 1, 1, 6]
def baseStart_2740805 : Nat := 118140960795 + 2740805 * 2 ^ 59
def prefixEnd_2740805 : Nat := 4983230072969 + 3 ^ 40 * 2740805 * 2
def baseEnd_2740805 : Nat := 1407350345246254321532773

theorem tailTrace_2740805 : CollatzResearch.WordTrace tailWord_2740805 prefixEnd_2740805 1407350345246254321532773 := by
  unfold tailWord_2740805
  simp only [CollatzResearch.WordTrace]
  refine ⟨99965370835539052072383869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66643580557026034714922579 99965370835539052072383869)
  ·
    refine ⟨37487014063327144527143951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99965370835539052072383869 37487014063327144527143951)
    ·
      refine ⟨56230521094990716790715927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37487014063327144527143951 56230521094990716790715927)
      ·
        refine ⟨84345781642486075186073891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56230521094990716790715927 84345781642486075186073891)
        ·
          refine ⟨126518672463729112779110837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84345781642486075186073891 126518672463729112779110837)
          ·
            refine ⟨11861125543474604323041641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126518672463729112779110837 11861125543474604323041641)
            ·
              refine ⟨8895844157605953242281231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11861125543474604323041641 8895844157605953242281231)
              ·
                refine ⟨13343766236408929863421847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8895844157605953242281231 13343766236408929863421847)
                ·
                  refine ⟨20015649354613394795132771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13343766236408929863421847 20015649354613394795132771)
                  ·
                    refine ⟨30023474031920092192699157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20015649354613394795132771 30023474031920092192699157)
                    ·
                      refine ⟨1407350345246254321532773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30023474031920092192699157 1407350345246254321532773)
                      ·
                        rfl

theorem cell23_2740805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_2740805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740805 prefixEnd_2740805 := by exact prefixLift 2740805
  have htrace : WordTrace (prefixWord ++ tailWord_2740805) baseStart_2740805 baseEnd_2740805 := by
    simpa [prefixWord, tailWord_2740805, baseEnd_2740805] using wordTrace_append hprefix tailTrace_2740805
  have hstable : (prefixWord ++ tailWord_2740805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740805).length < 2 ^ (prefixWord ++ tailWord_2740805).sum := by decide
  have hdescent : baseEnd_2740805 < baseStart_2740805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740806 : List Nat := [6, 1, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_2740806 : Nat := 118140960795 + 2740806 * 2 ^ 59
def prefixEnd_2740806 : Nat := 4983230072969 + 3 ^ 40 * 2740806 * 2
def baseEnd_2740806 : Nat := 469116952908969605873423

theorem tailTrace_2740806 : CollatzResearch.WordTrace tailWord_2740806 prefixEnd_2740806 469116952908969605873423 := by
  unfold tailWord_2740806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3123918978391732163849071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66643604872356952828780181 3123918978391732163849071)
  ·
    refine ⟨4685878467587598245773607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3123918978391732163849071 4685878467587598245773607)
    ·
      refine ⟨7028817701381397368660411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4685878467587598245773607 7028817701381397368660411)
      ·
        refine ⟨10543226552072096052990617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7028817701381397368660411 10543226552072096052990617)
        ·
          refine ⟨7907419914054072039742963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10543226552072096052990617 7907419914054072039742963)
          ·
            refine ⟨11861129871081108059614445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7907419914054072039742963 11861129871081108059614445)
            ·
              refine ⟨4447923701655415522355417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11861129871081108059614445 4447923701655415522355417)
              ·
                refine ⟨3335942776241561641766563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4447923701655415522355417 3335942776241561641766563)
                ·
                  refine ⟨5003914164362342462649845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3335942776241561641766563 5003914164362342462649845)
                  ·
                    refine ⟨469116952908969605873423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5003914164362342462649845 469116952908969605873423)
                    ·
                      rfl

theorem cell23_2740806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_2740806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740806 prefixEnd_2740806 := by exact prefixLift 2740806
  have htrace : WordTrace (prefixWord ++ tailWord_2740806) baseStart_2740806 baseEnd_2740806 := by
    simpa [prefixWord, tailWord_2740806, baseEnd_2740806] using wordTrace_append hprefix tailTrace_2740806
  have hstable : (prefixWord ++ tailWord_2740806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740806).length < 2 ^ (prefixWord ++ tailWord_2740806).sum := by decide
  have hdescent : baseEnd_2740806 < baseStart_2740806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740812 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 3, 2, 3]
def baseStart_2740812 : Nat := 118140960795 + 2740812 * 2 ^ 59
def prefixEnd_2740812 : Nat := 4983230072969 + 3 ^ 40 * 2740812 * 2
def baseEnd_2740812 : Nat := 1407353939610835794145241

theorem tailTrace_2740812 : CollatzResearch.WordTrace tailWord_2740812 prefixEnd_2740812 1407353939610835794145241 := by
  unfold tailWord_2740812
  simp only [CollatzResearch.WordTrace]
  refine ⟨49982813073256846133944345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66643750764342461511925793 49982813073256846133944345)
  ·
    refine ⟨37487109804942634600458259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49982813073256846133944345 37487109804942634600458259)
    ·
      refine ⟨56230664707413951900687389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37487109804942634600458259 56230664707413951900687389)
      ·
        refine ⟨21086499265280231962757771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56230664707413951900687389 21086499265280231962757771)
        ·
          refine ⟨31629748897920347944136657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21086499265280231962757771 31629748897920347944136657)
          ·
            refine ⟨23722311673440260958102493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31629748897920347944136657 23722311673440260958102493)
            ·
              refine ⟨8895866877540097859288435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23722311673440260958102493 8895866877540097859288435)
              ·
                refine ⟨13343800316310146788932653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8895866877540097859288435 13343800316310146788932653)
                ·
                  refine ⟨5003925118616305045849745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13343800316310146788932653 5003925118616305045849745)
                  ·
                    refine ⟨3752943838962228784387309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5003925118616305045849745 3752943838962228784387309)
                    ·
                      refine ⟨1407353939610835794145241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3752943838962228784387309 1407353939610835794145241)
                      ·
                        rfl

theorem cell23_2740812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_2740812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740812 prefixEnd_2740812 := by exact prefixLift 2740812
  have htrace : WordTrace (prefixWord ++ tailWord_2740812) baseStart_2740812 baseEnd_2740812 := by
    simpa [prefixWord, tailWord_2740812, baseEnd_2740812] using wordTrace_append hprefix tailTrace_2740812
  have hstable : (prefixWord ++ tailWord_2740812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740812).length < 2 ^ (prefixWord ++ tailWord_2740812).sum := by decide
  have hdescent : baseEnd_2740812 < baseStart_2740812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740842 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_2740842 : Nat := 118140960795 + 2740842 * 2 ^ 59
def prefixEnd_2740842 : Nat := 4983230072969 + 3 ^ 40 * 2740842 * 2
def baseEnd_2740842 : Nat := 1407369344030470676770103

theorem tailTrace_2740842 : CollatzResearch.WordTrace tailWord_2740842 prefixEnd_2740842 1407369344030470676770103 := by
  unfold tailWord_2740842
  simp only [CollatzResearch.WordTrace]
  refine ⟨24991680084101251847870195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66644480224270004927653853 24991680084101251847870195)
  ·
    refine ⟨37487520126151877771805293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24991680084101251847870195 37487520126151877771805293)
    ·
      refine ⟨14057820047306954164426985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37487520126151877771805293 14057820047306954164426985)
      ·
        refine ⟨10543365035480215623320239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14057820047306954164426985 10543365035480215623320239)
        ·
          refine ⟨15815047553220323434980359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10543365035480215623320239 15815047553220323434980359)
          ·
            refine ⟨23722571329830485152470539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15815047553220323434980359 23722571329830485152470539)
            ·
              refine ⟨35583856994745727728705809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23722571329830485152470539 35583856994745727728705809)
              ·
                refine ⟨26687892746059295796529357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35583856994745727728705809 26687892746059295796529357)
                ·
                  refine ⟨10007959779772235923698509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26687892746059295796529357 10007959779772235923698509)
                  ·
                    refine ⟨3752984917414588471386941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10007959779772235923698509 3752984917414588471386941)
                    ·
                      refine ⟨1407369344030470676770103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3752984917414588471386941 1407369344030470676770103)
                      ·
                        rfl

theorem cell23_2740842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_2740842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740842 prefixEnd_2740842 := by exact prefixLift 2740842
  have htrace : WordTrace (prefixWord ++ tailWord_2740842) baseStart_2740842 baseEnd_2740842 := by
    simpa [prefixWord, tailWord_2740842, baseEnd_2740842] using wordTrace_append hprefix tailTrace_2740842
  have hstable : (prefixWord ++ tailWord_2740842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740842).length < 2 ^ (prefixWord ++ tailWord_2740842).sum := by decide
  have hdescent : baseEnd_2740842 < baseStart_2740842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740869 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 3, 3, 2]
def baseStart_2740869 : Nat := 118140960795 + 2740869 * 2 ^ 59
def prefixEnd_2740869 : Nat := 4983230072969 + 3 ^ 40 * 2740869 * 2
def baseEnd_2740869 : Nat := 1407383208008142071132479

theorem tailTrace_2740869 : CollatzResearch.WordTrace tailWord_2740869 prefixEnd_2740869 1407383208008142071132479 := by
  unfold tailWord_2740869
  simp only [CollatzResearch.WordTrace]
  refine ⟨99967705107307191002713661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66645136738204794001809107 99967705107307191002713661)
  ·
    refine ⟨37487889415240196626017623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99967705107307191002713661 37487889415240196626017623)
    ·
      refine ⟨56231834122860294939026435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37487889415240196626017623 56231834122860294939026435)
      ·
        refine ⟨84347751184290442408539653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56231834122860294939026435 84347751184290442408539653)
        ·
          refine ⟨15815203347054457951601185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84347751184290442408539653 15815203347054457951601185)
          ·
            refine ⟨11861402510290843463700889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15815203347054457951601185 11861402510290843463700889)
            ·
              refine ⟨8896051882718132597775667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11861402510290843463700889 8896051882718132597775667)
              ·
                refine ⟨13344077824077198896663501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8896051882718132597775667 13344077824077198896663501)
                ·
                  refine ⟨5004029184028949586248813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13344077824077198896663501 5004029184028949586248813)
                  ·
                    refine ⟨1876510944010856094843305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5004029184028949586248813 1876510944010856094843305)
                    ·
                      refine ⟨1407383208008142071132479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1876510944010856094843305 1407383208008142071132479)
                      ·
                        rfl

theorem cell23_2740869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 3, 2].length) (baseStart_2740869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740869 prefixEnd_2740869 := by exact prefixLift 2740869
  have htrace : WordTrace (prefixWord ++ tailWord_2740869) baseStart_2740869 baseEnd_2740869 := by
    simpa [prefixWord, tailWord_2740869, baseEnd_2740869] using wordTrace_append hprefix tailTrace_2740869
  have hstable : (prefixWord ++ tailWord_2740869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740869).length < 2 ^ (prefixWord ++ tailWord_2740869).sum := by decide
  have hdescent : baseEnd_2740869 < baseStart_2740869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740892 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 2, 6]
def baseStart_2740892 : Nat := 118140960795 + 2740892 * 2 ^ 59
def prefixEnd_2740892 : Nat := 4983230072969 + 3 ^ 40 * 2740892 * 2
def baseEnd_2740892 : Nat := 469131672687731827048291

theorem tailTrace_2740892 : CollatzResearch.WordTrace tailWord_2740892 prefixEnd_2740892 469131672687731827048291 := by
  unfold tailWord_2740892
  simp only [CollatzResearch.WordTrace]
  refine ⟨49984271993111932965400465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66645695990815910620533953 49984271993111932965400465)
  ·
    refine ⟨37488203994833949724050349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49984271993111932965400465 37488203994833949724050349)
    ·
      refine ⟨14058076498062731146518881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37488203994833949724050349 14058076498062731146518881)
      ·
        refine ⟨10543557373547048359889161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14058076498062731146518881 10543557373547048359889161)
        ·
          refine ⟨7907668030160286269916871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10543557373547048359889161 7907668030160286269916871)
          ·
            refine ⟨11861502045240429404875307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7907668030160286269916871 11861502045240429404875307)
            ·
              refine ⟨17792253067860644107312961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11861502045240429404875307 17792253067860644107312961)
              ·
                refine ⟨13344189800895483080484721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17792253067860644107312961 13344189800895483080484721)
                ·
                  refine ⟨10008142350671612310363541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13344189800895483080484721 10008142350671612310363541)
                  ·
                    refine ⟨469131672687731827048291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10008142350671612310363541 469131672687731827048291)
                    ·
                      rfl

theorem cell23_2740892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_2740892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740892 prefixEnd_2740892 := by exact prefixLift 2740892
  have htrace : WordTrace (prefixWord ++ tailWord_2740892) baseStart_2740892 baseEnd_2740892 := by
    simpa [prefixWord, tailWord_2740892, baseEnd_2740892] using wordTrace_append hprefix tailTrace_2740892
  have hstable : (prefixWord ++ tailWord_2740892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740892).length < 2 ^ (prefixWord ++ tailWord_2740892).sum := by decide
  have hdescent : baseEnd_2740892 < baseStart_2740892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740905 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 7]
def baseStart_2740905 : Nat := 118140960795 + 2740905 * 2 ^ 59
def prefixEnd_2740905 : Nat := 4983230072969 + 3 ^ 40 * 2740905 * 2
def baseEnd_2740905 : Nat := 156377965923522658920257

theorem tailTrace_2740905 : CollatzResearch.WordTrace tailWord_2740905 prefixEnd_2740905 156377965923522658920257 := by
  unfold tailWord_2740905
  simp only [CollatzResearch.WordTrace]
  refine ⟨99969018135176769151024169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66646012090117846100682779 99969018135176769151024169)
  ·
    refine ⟨74976763601382576863268127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99969018135176769151024169 74976763601382576863268127)
    ·
      refine ⟨112465145402073865294902191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74976763601382576863268127 112465145402073865294902191)
      ·
        refine ⟨168697718103110797942353287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112465145402073865294902191 168697718103110797942353287)
        ·
          refine ⟨253046577154666196913529931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168697718103110797942353287 253046577154666196913529931)
          ·
            refine ⟨379569865731999295370294897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253046577154666196913529931 379569865731999295370294897)
            ·
              refine ⟨284677399298999471527721173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379569865731999295370294897 284677399298999471527721173)
              ·
                refine ⟨6672126546070300113930965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 284677399298999471527721173 6672126546070300113930965)
                ·
                  refine ⟨156377965923522658920257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6672126546070300113930965 156377965923522658920257)
                  ·
                    rfl

theorem cell23_2740905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 7].length) (baseStart_2740905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740905 prefixEnd_2740905 := by exact prefixLift 2740905
  have htrace : WordTrace (prefixWord ++ tailWord_2740905) baseStart_2740905 baseEnd_2740905 := by
    simpa [prefixWord, tailWord_2740905, baseEnd_2740905] using wordTrace_append hprefix tailTrace_2740905
  have hstable : (prefixWord ++ tailWord_2740905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740905).length < 2 ^ (prefixWord ++ tailWord_2740905).sum := by decide
  have hdescent : baseEnd_2740905 < baseStart_2740905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740910 : List Nat := [4, 1, 4, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_2740910 : Nat := 118140960795 + 2740910 * 2 ^ 59
def prefixEnd_2740910 : Nat := 4983230072969 + 3 ^ 40 * 2740910 * 2
def baseEnd_2740910 : Nat := 1407404260714976410719791

theorem tailTrace_2740910 : CollatzResearch.WordTrace tailWord_2740910 prefixEnd_2740910 1407404260714976410719791 := by
  unfold tailWord_2740910
  simp only [CollatzResearch.WordTrace]
  refine ⟨12496150062519831875619523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66646133666772436669970789 12496150062519831875619523)
  ·
    refine ⟨18744225093779747813429285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12496150062519831875619523 18744225093779747813429285)
    ·
      refine ⟨3514542205083702715017991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18744225093779747813429285 3514542205083702715017991)
      ·
        refine ⟨5271813307625554072526987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3514542205083702715017991 5271813307625554072526987)
        ·
          refine ⟨7907719961438331108790481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5271813307625554072526987 7907719961438331108790481)
          ·
            refine ⟨5930789971078748331592861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7907719961438331108790481 5930789971078748331592861)
            ·
              refine ⟨2224046239154530624347323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5930789971078748331592861 2224046239154530624347323)
              ·
                refine ⟨3336069358731795936520985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2224046239154530624347323 3336069358731795936520985)
                ·
                  refine ⟨2502052019048846952390739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3336069358731795936520985 2502052019048846952390739)
                  ·
                    refine ⟨3753078028573270428586109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2502052019048846952390739 3753078028573270428586109)
                    ·
                      refine ⟨1407404260714976410719791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3753078028573270428586109 1407404260714976410719791)
                      ·
                        rfl

theorem cell23_2740910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_2740910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740910 prefixEnd_2740910 := by exact prefixLift 2740910
  have htrace : WordTrace (prefixWord ++ tailWord_2740910) baseStart_2740910 baseEnd_2740910 := by
    simpa [prefixWord, tailWord_2740910, baseEnd_2740910] using wordTrace_append hprefix tailTrace_2740910
  have hstable : (prefixWord ++ tailWord_2740910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740910).length < 2 ^ (prefixWord ++ tailWord_2740910).sum := by decide
  have hdescent : baseEnd_2740910 < baseStart_2740910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740952 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 4, 5]
def baseStart_2740952 : Nat := 118140960795 + 2740952 * 2 ^ 59
def prefixEnd_2740952 : Nat := 4983230072969 + 3 ^ 40 * 2740952 * 2
def baseEnd_2740952 : Nat := 469141942300821748798199

theorem tailTrace_2740952 : CollatzResearch.WordTrace tailWord_2740952 prefixEnd_2740952 469141942300821748798199 := by
  unfold tailWord_2740952
  simp only [CollatzResearch.WordTrace]
  refine ⟨49985366183003248088992555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66647154910670997451990073 49985366183003248088992555)
  ·
    refine ⟨74978049274504872133488833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49985366183003248088992555 74978049274504872133488833)
    ·
      refine ⟨56233536955878654100116625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74978049274504872133488833 56233536955878654100116625)
      ·
        refine ⟨42175152716908990575087469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56233536955878654100116625 42175152716908990575087469)
        ·
          refine ⟨15815682268840871465657801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42175152716908990575087469 15815682268840871465657801)
          ·
            refine ⟨11861761701630653599243351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15815682268840871465657801 11861761701630653599243351)
            ·
              refine ⟨17792642552445980398865027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11861761701630653599243351 17792642552445980398865027)
              ·
                refine ⟨26688963828668970598297541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17792642552445980398865027 26688963828668970598297541)
                ·
                  refine ⟨5004180717875431987180789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26688963828668970598297541 5004180717875431987180789)
                  ·
                    refine ⟨469141942300821748798199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5004180717875431987180789 469141942300821748798199)
                    ·
                      rfl

theorem cell23_2740952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_2740952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740952 prefixEnd_2740952 := by exact prefixLift 2740952
  have htrace : WordTrace (prefixWord ++ tailWord_2740952) baseStart_2740952 baseEnd_2740952 := by
    simpa [prefixWord, tailWord_2740952, baseEnd_2740952] using wordTrace_append hprefix tailTrace_2740952
  have hstable : (prefixWord ++ tailWord_2740952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740952).length < 2 ^ (prefixWord ++ tailWord_2740952).sum := by decide
  have hdescent : baseEnd_2740952 < baseStart_2740952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740956 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 7]
def baseStart_2740956 : Nat := 118140960795 + 2740956 * 2 ^ 59
def prefixEnd_2740956 : Nat := 4983230072969 + 3 ^ 40 * 2740956 * 2
def baseEnd_2740956 : Nat := 156380875647231470082731

theorem tailTrace_2740956 : CollatzResearch.WordTrace tailWord_2740956 prefixEnd_2740956 156380875647231470082731 := by
  unfold tailWord_2740956
  simp only [CollatzResearch.WordTrace]
  refine ⟨49985439128996002430565361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66647252171994669907420481 49985439128996002430565361)
  ·
    refine ⟨37489079346747001822924021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49985439128996002430565361 37489079346747001822924021)
    ·
      refine ⟨3514601188757531420899127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37489079346747001822924021 3514601188757531420899127)
      ·
        refine ⟨5271901783136297131348691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3514601188757531420899127 5271901783136297131348691)
        ·
          refine ⟨7907852674704445697023037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5271901783136297131348691 7907852674704445697023037)
          ·
            refine ⟨2965444753014167136383639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7907852674704445697023037 2965444753014167136383639)
            ·
              refine ⟨4448167129521250704575459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2965444753014167136383639 4448167129521250704575459)
              ·
                refine ⟨6672250694281876056863189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4448167129521250704575459 6672250694281876056863189)
                ·
                  refine ⟨156380875647231470082731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6672250694281876056863189 156380875647231470082731)
                  ·
                    rfl

theorem cell23_2740956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 7].length) (baseStart_2740956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740956 prefixEnd_2740956 := by exact prefixLift 2740956
  have htrace : WordTrace (prefixWord ++ tailWord_2740956) baseStart_2740956 baseEnd_2740956 := by
    simpa [prefixWord, tailWord_2740956, baseEnd_2740956] using wordTrace_append hprefix tailTrace_2740956
  have hstable : (prefixWord ++ tailWord_2740956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740956).length < 2 ^ (prefixWord ++ tailWord_2740956).sum := by decide
  have hdescent : baseEnd_2740956 < baseStart_2740956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740972 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 4]
def baseStart_2740972 : Nat := 118140960795 + 2740972 * 2 ^ 59
def prefixEnd_2740972 : Nat := 4983230072969 + 3 ^ 40 * 2740972 * 2
def baseEnd_2740972 : Nat := 1407436096515555168144505

theorem tailTrace_2740972 : CollatzResearch.WordTrace tailWord_2740972 prefixEnd_2740972 1407436096515555168144505 := by
  unfold tailWord_2740972
  simp only [CollatzResearch.WordTrace]
  refine ⟨49985730912967019796856585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66647641217289359729142113 49985730912967019796856585)
  ·
    refine ⟨37489298184725264847642439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49985730912967019796856585 37489298184725264847642439)
    ·
      refine ⟨56233947277087897271463659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37489298184725264847642439 56233947277087897271463659)
      ·
        refine ⟨84350920915631845907195489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56233947277087897271463659 84350920915631845907195489)
        ·
          refine ⟨63263190686723884430396617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84350920915631845907195489 63263190686723884430396617)
          ·
            refine ⟨47447393015042913322797463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63263190686723884430396617 47447393015042913322797463)
            ·
              refine ⟨71171089522564369984196195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47447393015042913322797463 71171089522564369984196195)
              ·
                refine ⟨106756634283846554976294293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71171089522564369984196195 106756634283846554976294293)
                ·
                  refine ⟨5004217232055307264513795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106756634283846554976294293 5004217232055307264513795)
                  ·
                    refine ⟨7506325848082960896770693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5004217232055307264513795 7506325848082960896770693)
                    ·
                      refine ⟨1407436096515555168144505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7506325848082960896770693 1407436096515555168144505)
                      ·
                        rfl

theorem cell23_2740972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_2740972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740972 prefixEnd_2740972 := by exact prefixLift 2740972
  have htrace : WordTrace (prefixWord ++ tailWord_2740972) baseStart_2740972 baseEnd_2740972 := by
    simpa [prefixWord, tailWord_2740972, baseEnd_2740972] using wordTrace_append hprefix tailTrace_2740972
  have hstable : (prefixWord ++ tailWord_2740972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740972).length < 2 ^ (prefixWord ++ tailWord_2740972).sum := by decide
  have hdescent : baseEnd_2740972 < baseStart_2740972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740989 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 2, 1, 4]
def baseStart_2740989 : Nat := 118140960795 + 2740989 * 2 ^ 59
def prefixEnd_2740989 : Nat := 4983230072969 + 3 ^ 40 * 2740989 * 2
def baseEnd_2740989 : Nat := 1407444825686681601631927

theorem tailTrace_2740989 : CollatzResearch.WordTrace tailWord_2740989 prefixEnd_2740989 1407444825686681601631927 := by
  unfold tailWord_2740989
  simp only [CollatzResearch.WordTrace]
  refine ⟨99972081866872451497082021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66648054577914967664721347 99972081866872451497082021)
  ·
    refine ⟨18744765350038584655702879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99972081866872451497082021 18744765350038584655702879)
    ·
      refine ⟨28117148025057876983554319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18744765350038584655702879 28117148025057876983554319)
      ·
        refine ⟨42175722037586815475331479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28117148025057876983554319 42175722037586815475331479)
        ·
          refine ⟨63263583056380223212997219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42175722037586815475331479 63263583056380223212997219)
          ·
            refine ⟨94895374584570334819495829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63263583056380223212997219 94895374584570334819495829)
            ·
              refine ⟨4448220683651734444663867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94895374584570334819495829 4448220683651734444663867)
              ·
                refine ⟨6672331025477601666995801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4448220683651734444663867 6672331025477601666995801)
                ·
                  refine ⟨5004248269108201250246851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6672331025477601666995801 5004248269108201250246851)
                  ·
                    refine ⟨7506372403662301875370277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5004248269108201250246851 7506372403662301875370277)
                    ·
                      refine ⟨1407444825686681601631927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7506372403662301875370277 1407444825686681601631927)
                      ·
                        rfl

theorem cell23_2740989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_2740989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2740989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2740989 prefixEnd_2740989 := by exact prefixLift 2740989
  have htrace : WordTrace (prefixWord ++ tailWord_2740989) baseStart_2740989 baseEnd_2740989 := by
    simpa [prefixWord, tailWord_2740989, baseEnd_2740989] using wordTrace_append hprefix tailTrace_2740989
  have hstable : (prefixWord ++ tailWord_2740989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740989).length < 2 ^ (prefixWord ++ tailWord_2740989).sum := by decide
  have hdescent : baseEnd_2740989 < baseStart_2740989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741002 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_2741002 : Nat := 118140960795 + 2741002 * 2 ^ 59
def prefixEnd_2741002 : Nat := 4983230072969 + 3 ^ 40 * 2741002 * 2
def baseEnd_2741002 : Nat := 1407451500935190050769367

theorem tailTrace_2741002 : CollatzResearch.WordTrace tailWord_2741002 prefixEnd_2741002 1407451500935190050769367 := by
  unfold tailWord_2741002
  simp only [CollatzResearch.WordTrace]
  refine ⟨24993139003956338679326315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66648370677216903144870173 24993139003956338679326315)
  ·
    refine ⟨37489708505934508018989473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24993139003956338679326315 37489708505934508018989473)
    ·
      refine ⟨28117281379450881014242105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37489708505934508018989473 28117281379450881014242105)
      ·
        refine ⟨21087961034588160760681579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28117281379450881014242105 21087961034588160760681579)
        ·
          refine ⟨31631941551882241141022369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21087961034588160760681579 31631941551882241141022369)
          ·
            refine ⟨23723956163911680855766777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31631941551882241141022369 23723956163911680855766777)
            ·
              refine ⟨17792967122933760641825083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23723956163911680855766777 17792967122933760641825083)
              ·
                refine ⟨26689450684400640962737625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17792967122933760641825083 26689450684400640962737625)
                ·
                  refine ⟨20017088013300480722053219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26689450684400640962737625 20017088013300480722053219)
                  ·
                    refine ⟨30025632019950721083079829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20017088013300480722053219 30025632019950721083079829)
                    ·
                      refine ⟨1407451500935190050769367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30025632019950721083079829 1407451500935190050769367)
                      ·
                        rfl

theorem cell23_2741002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_2741002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741002 prefixEnd_2741002 := by exact prefixLift 2741002
  have htrace : WordTrace (prefixWord ++ tailWord_2741002) baseStart_2741002 baseEnd_2741002 := by
    simpa [prefixWord, tailWord_2741002, baseEnd_2741002] using wordTrace_append hprefix tailTrace_2741002
  have hstable : (prefixWord ++ tailWord_2741002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741002).length < 2 ^ (prefixWord ++ tailWord_2741002).sum := by decide
  have hdescent : baseEnd_2741002 < baseStart_2741002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741009 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 3]
def baseStart_2741009 : Nat := 118140960795 + 2741009 * 2 ^ 59
def prefixEnd_2741009 : Nat := 4983230072969 + 3 ^ 40 * 2741009 * 2
def baseEnd_2741009 : Nat := 1407455095299771523381835

theorem tailTrace_2741009 : CollatzResearch.WordTrace tailWord_2741009 prefixEnd_2741009 1407455095299771523381835 := by
  unfold tailWord_2741009
  simp only [CollatzResearch.WordTrace]
  refine ⟨99972811326799994912810081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66648540884533329941873387 99972811326799994912810081)
  ·
    refine ⟨74979608495099996184607561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99972811326799994912810081 74979608495099996184607561)
    ·
      refine ⟨56234706371324997138455671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74979608495099996184607561 56234706371324997138455671)
      ·
        refine ⟨84352059556987495707683507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56234706371324997138455671 84352059556987495707683507)
        ·
          refine ⟨126528089335481243561525261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84352059556987495707683507 126528089335481243561525261)
          ·
            refine ⟨47448033500805466335571973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126528089335481243561525261 47448033500805466335571973)
            ·
              refine ⟨8896506281401024937919745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47448033500805466335571973 8896506281401024937919745)
              ·
                refine ⟨6672379711050768703439809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8896506281401024937919745 6672379711050768703439809)
                ·
                  refine ⟨5004284783288076527579857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6672379711050768703439809 5004284783288076527579857)
                  ·
                    refine ⟨3753213587466057395684893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5004284783288076527579857 3753213587466057395684893)
                    ·
                      refine ⟨1407455095299771523381835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3753213587466057395684893 1407455095299771523381835)
                      ·
                        rfl

theorem cell23_2741009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_2741009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741009 prefixEnd_2741009 := by exact prefixLift 2741009
  have htrace : WordTrace (prefixWord ++ tailWord_2741009) baseStart_2741009 baseEnd_2741009 := by
    simpa [prefixWord, tailWord_2741009, baseEnd_2741009] using wordTrace_append hprefix tailTrace_2741009
  have hstable : (prefixWord ++ tailWord_2741009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741009).length < 2 ^ (prefixWord ++ tailWord_2741009).sum := by decide
  have hdescent : baseEnd_2741009 < baseStart_2741009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741052 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_2741052 : Nat := 118140960795 + 2741052 * 2 ^ 59
def prefixEnd_2741052 : Nat := 4983230072969 + 3 ^ 40 * 2741052 * 2
def baseEnd_2741052 : Nat := 1407477174967914855144137

theorem tailTrace_2741052 : CollatzResearch.WordTrace tailWord_2741052 prefixEnd_2741052 1407477174967914855144137 := by
  unfold tailWord_2741052
  simp only [CollatzResearch.WordTrace]
  refine ⟨49987189832822106628312705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66649586443762808837750273 49987189832822106628312705)
  ·
    refine ⟨37490392374616579971234529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49987189832822106628312705 37490392374616579971234529)
    ·
      refine ⟨28117794280962434978425897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37490392374616579971234529 28117794280962434978425897)
      ·
        refine ⟨21088345710721826233819423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28117794280962434978425897 21088345710721826233819423)
        ·
          refine ⟨31632518566082739350729135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21088345710721826233819423 31632518566082739350729135)
          ·
            refine ⟨47448777849124109026093703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31632518566082739350729135 47448777849124109026093703)
            ·
              refine ⟨71173166773686163539140555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47448777849124109026093703 71173166773686163539140555)
              ·
                refine ⟨106759750160529245308710833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71173166773686163539140555 106759750160529245308710833)
                ·
                  refine ⟨80069812620396933981533125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106759750160529245308710833 80069812620396933981533125)
                  ·
                    refine ⟨15013089866324425121537461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80069812620396933981533125 15013089866324425121537461)
                    ·
                      refine ⟨1407477174967914855144137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15013089866324425121537461 1407477174967914855144137)
                      ·
                        rfl

theorem cell23_2741052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_2741052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741052 prefixEnd_2741052 := by exact prefixLift 2741052
  have htrace : WordTrace (prefixWord ++ tailWord_2741052) baseStart_2741052 baseEnd_2741052 := by
    simpa [prefixWord, tailWord_2741052, baseEnd_2741052] using wordTrace_append hprefix tailTrace_2741052
  have hstable : (prefixWord ++ tailWord_2741052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741052).length < 2 ^ (prefixWord ++ tailWord_2741052).sum := by decide
  have hdescent : baseEnd_2741052 < baseStart_2741052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741059 : List Nat := [1, 1, 1, 3, 1, 4, 3, 3, 1, 5]
def baseStart_2741059 : Nat := 118140960795 + 2741059 * 2 ^ 59
def prefixEnd_2741059 : Nat := 4983230072969 + 3 ^ 40 * 2741059 * 2
def baseEnd_2741059 : Nat := 469160256444165442585535

theorem tailTrace_2741059 : CollatzResearch.WordTrace tailWord_2741059 prefixEnd_2741059 469160256444165442585535 := by
  unfold tailWord_2741059
  simp only [CollatzResearch.WordTrace]
  refine ⟨99974634976618853452130231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66649756651079235634753487 99974634976618853452130231)
  ·
    refine ⟨149961952464928280178195347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99974634976618853452130231 149961952464928280178195347)
    ·
      refine ⟨224942928697392420267293021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149961952464928280178195347 224942928697392420267293021)
      ·
        refine ⟨84353598261522157600234883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224942928697392420267293021 84353598261522157600234883)
        ·
          refine ⟨126530397392283236400352325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84353598261522157600234883 126530397392283236400352325)
          ·
            refine ⟨23724449511053106825066061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126530397392283236400352325 23724449511053106825066061)
            ·
              refine ⟨8896668566644915059399773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23724449511053106825066061 8896668566644915059399773)
              ·
                refine ⟨3336250712491843147274915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8896668566644915059399773 3336250712491843147274915)
                ·
                  refine ⟨5004376068737764720912373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3336250712491843147274915 5004376068737764720912373)
                  ·
                    refine ⟨469160256444165442585535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5004376068737764720912373 469160256444165442585535)
                    ·
                      rfl

theorem cell23_2741059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 5].length) (baseStart_2741059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741059 prefixEnd_2741059 := by exact prefixLift 2741059
  have htrace : WordTrace (prefixWord ++ tailWord_2741059) baseStart_2741059 baseEnd_2741059 := by
    simpa [prefixWord, tailWord_2741059, baseEnd_2741059] using wordTrace_append hprefix tailTrace_2741059
  have hstable : (prefixWord ++ tailWord_2741059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741059).length < 2 ^ (prefixWord ++ tailWord_2741059).sum := by decide
  have hdescent : baseEnd_2741059 < baseStart_2741059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741072 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 3, 6]
def baseStart_2741072 : Nat := 118140960795 + 2741072 * 2 ^ 59
def prefixEnd_2741072 : Nat := 4983230072969 + 3 ^ 40 * 2741072 * 2
def baseEnd_2741072 : Nat := 469162481527001592298015

theorem tailTrace_2741072 : CollatzResearch.WordTrace tailWord_2741072 prefixEnd_2741072 469162481527001592298015 := by
  unfold tailWord_2741072
  simp only [CollatzResearch.WordTrace]
  refine ⟨49987554562785878336176735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66650072750381171114902313 49987554562785878336176735)
  ·
    refine ⟨74981331844178817504265103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49987554562785878336176735 74981331844178817504265103)
    ·
      refine ⟨112471997766268226256397655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74981331844178817504265103 112471997766268226256397655)
      ·
        refine ⟨168707996649402339384596483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112471997766268226256397655 168707996649402339384596483)
        ·
          refine ⟨253061994974103509076894725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168707996649402339384596483 253061994974103509076894725)
          ·
            refine ⟨47449124057644407951917761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 253061994974103509076894725 47449124057644407951917761)
            ·
              refine ⟨35586843043233305963938321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47449124057644407951917761 35586843043233305963938321)
              ·
                refine ⟨26690132282424979472953741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35586843043233305963938321 26690132282424979472953741)
                ·
                  refine ⟨10008799605909367302357653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26690132282424979472953741 10008799605909367302357653)
                  ·
                    refine ⟨469162481527001592298015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10008799605909367302357653 469162481527001592298015)
                    ·
                      rfl

theorem cell23_2741072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 3, 6].length) (baseStart_2741072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741072 prefixEnd_2741072 := by exact prefixLift 2741072
  have htrace : WordTrace (prefixWord ++ tailWord_2741072) baseStart_2741072 baseEnd_2741072 := by
    simpa [prefixWord, tailWord_2741072, baseEnd_2741072] using wordTrace_append hprefix tailTrace_2741072
  have hstable : (prefixWord ++ tailWord_2741072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741072).length < 2 ^ (prefixWord ++ tailWord_2741072).sum := by decide
  have hdescent : baseEnd_2741072 < baseStart_2741072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741073 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 3, 1, 3]
def baseStart_2741073 : Nat := 118140960795 + 2741073 * 2 ^ 59
def prefixEnd_2741073 : Nat := 4983230072969 + 3 ^ 40 * 2741073 * 2
def baseEnd_2741073 : Nat := 1407487958061659272981541

theorem tailTrace_2741073 : CollatzResearch.WordTrace tailWord_2741073 prefixEnd_2741073 1407487958061659272981541 := by
  unfold tailWord_2741073
  simp only [CollatzResearch.WordTrace]
  refine ⟨99975145598568133843139873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66650097065712089228759915 99975145598568133843139873)
  ·
    refine ⟨74981359198926100382354905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99975145598568133843139873 74981359198926100382354905)
    ·
      refine ⟨56236019399194575286766179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74981359198926100382354905 56236019399194575286766179)
      ·
        refine ⟨84354029098791862930149269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56236019399194575286766179 84354029098791862930149269)
        ·
          refine ⟨3954095114005868574850747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84354029098791862930149269 3954095114005868574850747)
          ·
            refine ⟨5931142671008802862276121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3954095114005868574850747 5931142671008802862276121)
            ·
              refine ⟨4448357003256602146707091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5931142671008802862276121 4448357003256602146707091)
              ·
                refine ⟨6672535504884903220060637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4448357003256602146707091 6672535504884903220060637)
                ·
                  refine ⟨2502200814331838707522739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6672535504884903220060637 2502200814331838707522739)
                  ·
                    refine ⟨3753301221497758061284109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2502200814331838707522739 3753301221497758061284109)
                    ·
                      refine ⟨1407487958061659272981541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3753301221497758061284109 1407487958061659272981541)
                      ·
                        rfl

theorem cell23_2741073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 1, 3].length) (baseStart_2741073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741073 prefixEnd_2741073 := by exact prefixLift 2741073
  have htrace : WordTrace (prefixWord ++ tailWord_2741073) baseStart_2741073 baseEnd_2741073 := by
    simpa [prefixWord, tailWord_2741073, baseEnd_2741073] using wordTrace_append hprefix tailTrace_2741073
  have hstable : (prefixWord ++ tailWord_2741073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741073).length < 2 ^ (prefixWord ++ tailWord_2741073).sum := by decide
  have hdescent : baseEnd_2741073 < baseStart_2741073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741096 : List Nat := [2, 1, 4, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_2741096 : Nat := 118140960795 + 2741096 * 2 ^ 59
def prefixEnd_2741096 : Nat := 4983230072969 + 3 ^ 40 * 2741096 * 2
def baseEnd_2741096 : Nat := 1407499768116712682993935

theorem tailTrace_2741096 : CollatzResearch.WordTrace tailWord_2741096 prefixEnd_2741096 1407499768116712682993935 := by
  unfold tailWord_2741096
  simp only [CollatzResearch.WordTrace]
  refine ⟨49987992238742404385613571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66650656318323205847484761 49987992238742404385613571)
  ·
    refine ⟨74981988358113606578420357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49987992238742404385613571 74981988358113606578420357)
    ·
      refine ⟨14059122817146301233453817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74981988358113606578420357 14059122817146301233453817)
      ·
        refine ⟨10544342112859725925090363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14059122817146301233453817 10544342112859725925090363)
        ·
          refine ⟨15816513169289588887635545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10544342112859725925090363 15816513169289588887635545)
          ·
            refine ⟨11862384876967191665726659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15816513169289588887635545 11862384876967191665726659)
            ·
              refine ⟨17793577315450787498589989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11862384876967191665726659 17793577315450787498589989)
              ·
                refine ⟨3336295746647022655985623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17793577315450787498589989 3336295746647022655985623)
                ·
                  refine ⟨5004443619970533983978435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3336295746647022655985623 5004443619970533983978435)
                  ·
                    refine ⟨7506665429955800975967653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5004443619970533983978435 7506665429955800975967653)
                    ·
                      refine ⟨1407499768116712682993935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7506665429955800975967653 1407499768116712682993935)
                      ·
                        rfl

theorem cell23_2741096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_2741096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741096 prefixEnd_2741096 := by exact prefixLift 2741096
  have htrace : WordTrace (prefixWord ++ tailWord_2741096) baseStart_2741096 baseEnd_2741096 := by
    simpa [prefixWord, tailWord_2741096, baseEnd_2741096] using wordTrace_append hprefix tailTrace_2741096
  have hstable : (prefixWord ++ tailWord_2741096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741096).length < 2 ^ (prefixWord ++ tailWord_2741096).sum := by decide
  have hdescent : baseEnd_2741096 < baseStart_2741096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741099 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 3]
def baseStart_2741099 : Nat := 118140960795 + 2741099 * 2 ^ 59
def prefixEnd_2741099 : Nat := 4983230072969 + 3 ^ 40 * 2741099 * 2
def baseEnd_2741099 : Nat := 1407501308558676171256421

theorem tailTrace_2741099 : CollatzResearch.WordTrace tailWord_2741099 prefixEnd_2741099 1407501308558676171256421 := by
  unfold tailWord_2741099
  simp only [CollatzResearch.WordTrace]
  refine ⟨99976093896473940283586351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66650729264315960189057567 99976093896473940283586351)
  ·
    refine ⟨149964140844710910425379527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99976093896473940283586351 149964140844710910425379527)
    ·
      refine ⟨224946211267066365638069291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149964140844710910425379527 224946211267066365638069291)
      ·
        refine ⟨337419316900599548457103937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224946211267066365638069291 337419316900599548457103937)
        ·
          refine ⟨253064487675449661342827953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337419316900599548457103937 253064487675449661342827953)
          ·
            refine ⟨189798365756587246007120965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253064487675449661342827953 189798365756587246007120965)
            ·
              refine ⟨35587193579360108626335181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189798365756587246007120965 35587193579360108626335181)
              ·
                refine ⟨13345197592260040734875693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35587193579360108626335181 13345197592260040734875693)
                ·
                  refine ⟨5004449097097515275578385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13345197592260040734875693 5004449097097515275578385)
                  ·
                    refine ⟨3753336822823136456683789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5004449097097515275578385 3753336822823136456683789)
                    ·
                      refine ⟨1407501308558676171256421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3753336822823136456683789 1407501308558676171256421)
                      ·
                        rfl

theorem cell23_2741099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 3].length) (baseStart_2741099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741099 prefixEnd_2741099 := by exact prefixLift 2741099
  have htrace : WordTrace (prefixWord ++ tailWord_2741099) baseStart_2741099 baseEnd_2741099 := by
    simpa [prefixWord, tailWord_2741099, baseEnd_2741099] using wordTrace_append hprefix tailTrace_2741099
  have hstable : (prefixWord ++ tailWord_2741099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741099).length < 2 ^ (prefixWord ++ tailWord_2741099).sum := by decide
  have hdescent : baseEnd_2741099 < baseStart_2741099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741130 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 3, 2, 2]
def baseStart_2741130 : Nat := 118140960795 + 2741130 * 2 ^ 59
def prefixEnd_2741130 : Nat := 4983230072969 + 3 ^ 40 * 2741130 * 2
def baseEnd_2741130 : Nat := 1407517226458965549968779

theorem tailTrace_2741130 : CollatzResearch.WordTrace tailWord_2741130 prefixEnd_2741130 1407517226458965549968779 := by
  unfold tailWord_2741130
  simp only [CollatzResearch.WordTrace]
  refine ⟨24994306139840408144491211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66651483039574421718643229 24994306139840408144491211)
  ·
    refine ⟨37491459209760612216736817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24994306139840408144491211 37491459209760612216736817)
    ·
      refine ⟨28118594407320459162552613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37491459209760612216736817 28118594407320459162552613)
      ·
        refine ⟨5272236451372586092978615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28118594407320459162552613 5272236451372586092978615)
        ·
          refine ⟨7908354677058879139467923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5272236451372586092978615 7908354677058879139467923)
          ·
            refine ⟨11862532015588318709201885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7908354677058879139467923 11862532015588318709201885)
            ·
              refine ⟨4448449505845619515950707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11862532015588318709201885 4448449505845619515950707)
              ·
                refine ⟨6672674258768429273926061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4448449505845619515950707 6672674258768429273926061)
                ·
                  refine ⟨2502252847038160977722273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6672674258768429273926061 2502252847038160977722273)
                  ·
                    refine ⟨1876689635278620733291705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2502252847038160977722273 1876689635278620733291705)
                    ·
                      refine ⟨1407517226458965549968779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1876689635278620733291705 1407517226458965549968779)
                      ·
                        rfl

theorem cell23_2741130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_2741130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741130 prefixEnd_2741130 := by exact prefixLift 2741130
  have htrace : WordTrace (prefixWord ++ tailWord_2741130) baseStart_2741130 baseEnd_2741130 := by
    simpa [prefixWord, tailWord_2741130, baseEnd_2741130] using wordTrace_append hprefix tailTrace_2741130
  have hstable : (prefixWord ++ tailWord_2741130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741130).length < 2 ^ (prefixWord ++ tailWord_2741130).sum := by decide
  have hdescent : baseEnd_2741130 < baseStart_2741130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741174 : List Nat := [5, 1, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2741174 : Nat := 118140960795 + 2741174 * 2 ^ 59
def prefixEnd_2741174 : Nat := 4983230072969 + 3 ^ 40 * 2741174 * 2
def baseEnd_2741174 : Nat := 469179939869254459272859

theorem tailTrace_2741174 : CollatzResearch.WordTrace tailWord_2741174 prefixEnd_2741174 469179939869254459272859 := by
  unfold tailWord_2741174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6248676835700139255785411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66652552914134818728377717 6248676835700139255785411)
  ·
    refine ⟨9373015253550208883678117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6248676835700139255785411 9373015253550208883678117)
    ·
      refine ⟨1757440360040664165689647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9373015253550208883678117 1757440360040664165689647)
      ·
        refine ⟨2636160540060996248534471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1757440360040664165689647 2636160540060996248534471)
        ·
          refine ⟨3954240810091494372801707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2636160540060996248534471 3954240810091494372801707)
          ·
            refine ⟨5931361215137241559202561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3954240810091494372801707 5931361215137241559202561)
            ·
              refine ⟨4448520911352931169401921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5931361215137241559202561 4448520911352931169401921)
              ·
                refine ⟨3336390683514698377051441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4448520911352931169401921 3336390683514698377051441)
                ·
                  refine ⟨2502293012636023782788581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3336390683514698377051441 2502293012636023782788581)
                  ·
                    refine ⟨469179939869254459272859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2502293012636023782788581 469179939869254459272859)
                    ·
                      rfl

theorem cell23_2741174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2741174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741174 prefixEnd_2741174 := by exact prefixLift 2741174
  have htrace : WordTrace (prefixWord ++ tailWord_2741174) baseStart_2741174 baseEnd_2741174 := by
    simpa [prefixWord, tailWord_2741174, baseEnd_2741174] using wordTrace_append hprefix tailTrace_2741174
  have hstable : (prefixWord ++ tailWord_2741174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741174).length < 2 ^ (prefixWord ++ tailWord_2741174).sum := by decide
  have hdescent : baseEnd_2741174 < baseStart_2741174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741181 : List Nat := [1, 4, 1, 2, 5, 1, 2, 2, 1, 2, 2]
def baseStart_2741181 : Nat := 118140960795 + 2741181 * 2 ^ 59
def prefixEnd_2741181 : Nat := 4983230072969 + 3 ^ 40 * 2741181 * 2
def baseEnd_2741181 : Nat := 1407543413972344850431045

theorem tailTrace_2741181 : CollatzResearch.WordTrace tailWord_2741181 prefixEnd_2741181 1407543413972344850431045 := by
  unfold tailWord_2741181
  simp only [CollatzResearch.WordTrace]
  refine ⟨99979084682176868288071397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66652723121451245525380931 99979084682176868288071397)
  ·
    refine ⟨18746078377908162804013387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99979084682176868288071397 18746078377908162804013387)
    ·
      refine ⟨28119117566862244206020081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18746078377908162804013387 28119117566862244206020081)
      ·
        refine ⟨21089338175146683154515061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28119117566862244206020081 21089338175146683154515061)
        ·
          refine ⟨1977125453920001545735787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21089338175146683154515061 1977125453920001545735787)
          ·
            refine ⟨2965688180880002318603681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977125453920001545735787 2965688180880002318603681)
            ·
              refine ⟨2224266135660001738952761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2965688180880002318603681 2224266135660001738952761)
              ·
                refine ⟨1668199601745001304214571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2224266135660001738952761 1668199601745001304214571)
                ·
                  refine ⟨2502299402617501956321857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1668199601745001304214571 2502299402617501956321857)
                  ·
                    refine ⟨1876724551963126467241393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2502299402617501956321857 1876724551963126467241393)
                    ·
                      refine ⟨1407543413972344850431045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1876724551963126467241393 1407543413972344850431045)
                      ·
                        rfl

theorem cell23_2741181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_2741181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741181 prefixEnd_2741181 := by exact prefixLift 2741181
  have htrace : WordTrace (prefixWord ++ tailWord_2741181) baseStart_2741181 baseEnd_2741181 := by
    simpa [prefixWord, tailWord_2741181, baseEnd_2741181] using wordTrace_append hprefix tailTrace_2741181
  have hstable : (prefixWord ++ tailWord_2741181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741181).length < 2 ^ (prefixWord ++ tailWord_2741181).sum := by decide
  have hdescent : baseEnd_2741181 < baseStart_2741181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741199 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 4]
def baseStart_2741199 : Nat := 118140960795 + 2741199 * 2 ^ 59
def prefixEnd_2741199 : Nat := 4983230072969 + 3 ^ 40 * 2741199 * 2
def baseEnd_2741199 : Nat := 1407552656624125780005961

theorem tailTrace_2741199 : CollatzResearch.WordTrace tailWord_2741199 prefixEnd_2741199 1407552656624125780005961 := by
  unfold tailWord_2741199
  simp only [CollatzResearch.WordTrace]
  refine ⟨99979741196111657362226651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66653160797407771574817767 99979741196111657362226651)
  ·
    refine ⟨149969611794167486043339977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99979741196111657362226651 149969611794167486043339977)
    ·
      refine ⟨112477208845625614532504983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149969611794167486043339977 112477208845625614532504983)
      ·
        refine ⟨168715813268438421798757475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112477208845625614532504983 168715813268438421798757475)
        ·
          refine ⟨253073719902657632698136213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168715813268438421798757475 253073719902657632698136213)
          ·
            refine ⟨11862830620437076532725135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 253073719902657632698136213 11862830620437076532725135)
            ·
              refine ⟨17794245930655614799087703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11862830620437076532725135 17794245930655614799087703)
              ·
                refine ⟨26691368895983422198631555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17794245930655614799087703 26691368895983422198631555)
                ·
                  refine ⟨40037053343975133297947333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26691368895983422198631555 40037053343975133297947333)
                  ·
                    refine ⟨7506947501995337493365125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40037053343975133297947333 7506947501995337493365125)
                    ·
                      refine ⟨1407552656624125780005961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7506947501995337493365125 1407552656624125780005961)
                      ·
                        rfl

theorem cell23_2741199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_2741199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741199 prefixEnd_2741199 := by exact prefixLift 2741199
  have htrace : WordTrace (prefixWord ++ tailWord_2741199) baseStart_2741199 baseEnd_2741199 := by
    simpa [prefixWord, tailWord_2741199, baseEnd_2741199] using wordTrace_append hprefix tailTrace_2741199
  have hstable : (prefixWord ++ tailWord_2741199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741199).length < 2 ^ (prefixWord ++ tailWord_2741199).sum := by decide
  have hdescent : baseEnd_2741199 < baseStart_2741199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741209 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 9]
def baseStart_2741209 : Nat := 118140960795 + 2741209 * 2 ^ 59
def prefixEnd_2741209 : Nat := 4983230072969 + 3 ^ 40 * 2741209 * 2
def baseEnd_2741209 : Nat := 156395310158963415653435

theorem tailTrace_2741209 : CollatzResearch.WordTrace tailWord_2741209 prefixEnd_2741209 156395310158963415653435 := by
  unfold tailWord_2741209
  simp only [CollatzResearch.WordTrace]
  refine ⟨99980105926075429070090681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66653403950716952713393787 99980105926075429070090681)
  ·
    refine ⟨74985079444556571802568011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99980105926075429070090681 74985079444556571802568011)
    ·
      refine ⟨112477619166834857703852017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74985079444556571802568011 112477619166834857703852017)
      ·
        refine ⟨84358214375126143277889013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112477619166834857703852017 84358214375126143277889013)
        ·
          refine ⟨7908582597668075932302095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84358214375126143277889013 7908582597668075932302095)
          ·
            refine ⟨11862873896502113898453143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7908582597668075932302095 11862873896502113898453143)
            ·
              refine ⟨17794310844753170847679715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11862873896502113898453143 17794310844753170847679715)
              ·
                refine ⟨26691466267129756271519573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17794310844753170847679715 26691466267129756271519573)
                ·
                  refine ⟨156395310158963415653435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26691466267129756271519573 156395310158963415653435)
                  ·
                    rfl

theorem cell23_2741209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 9].length) (baseStart_2741209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741209 prefixEnd_2741209 := by exact prefixLift 2741209
  have htrace : WordTrace (prefixWord ++ tailWord_2741209) baseStart_2741209 baseEnd_2741209 := by
    simpa [prefixWord, tailWord_2741209, baseEnd_2741209] using wordTrace_append hprefix tailTrace_2741209
  have hstable : (prefixWord ++ tailWord_2741209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741209).length < 2 ^ (prefixWord ++ tailWord_2741209).sum := by decide
  have hdescent : baseEnd_2741209 < baseStart_2741209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741277 : List Nat := [1, 4, 2, 2, 4, 1, 1, 3, 5]
def baseStart_2741277 : Nat := 118140960795 + 2741277 * 2 ^ 59
def prefixEnd_2741277 : Nat := 4983230072969 + 3 ^ 40 * 2741277 * 2
def baseEnd_2741277 : Nat := 156399189790575163870067

theorem tailTrace_2741277 : CollatzResearch.WordTrace tailWord_2741277 prefixEnd_2741277 156399189790575163870067 := by
  unfold tailWord_2741277
  simp only [CollatzResearch.WordTrace]
  refine ⟨99982586089829076683566085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66655057393219384455710723 99982586089829076683566085)
  ·
    refine ⟨18746734891842951878168641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99982586089829076683566085 18746734891842951878168641)
    ·
      refine ⟨14060051168882213908626481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18746734891842951878168641 14060051168882213908626481)
      ·
        refine ⟨10545038376661660431469861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14060051168882213908626481 10545038376661660431469861)
        ·
          refine ⟨1977194695624061330900599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10545038376661660431469861 1977194695624061330900599)
          ·
            refine ⟨2965792043436091996350899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977194695624061330900599 2965792043436091996350899)
            ·
              refine ⟨4448688065154137994526349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2965792043436091996350899 4448688065154137994526349)
              ·
                refine ⟨1668258024432801747947381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4448688065154137994526349 1668258024432801747947381)
                ·
                  refine ⟨156399189790575163870067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1668258024432801747947381 156399189790575163870067)
                  ·
                    rfl

theorem cell23_2741277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_2741277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741277 prefixEnd_2741277 := by exact prefixLift 2741277
  have htrace : WordTrace (prefixWord ++ tailWord_2741277) baseStart_2741277 baseEnd_2741277 := by
    simpa [prefixWord, tailWord_2741277, baseEnd_2741277] using wordTrace_append hprefix tailTrace_2741277
  have hstable : (prefixWord ++ tailWord_2741277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741277).length < 2 ^ (prefixWord ++ tailWord_2741277).sum := by decide
  have hdescent : baseEnd_2741277 < baseStart_2741277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741330 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_2741330 : Nat := 118140960795 + 2741330 * 2 ^ 59
def prefixEnd_2741330 : Nat := 4983230072969 + 3 ^ 40 * 2741330 * 2
def baseEnd_2741330 : Nat := 1407619922589864767467859

theorem tailTrace_2741330 : CollatzResearch.WordTrace tailWord_2741330 prefixEnd_2741330 1407619922589864767467859 := by
  unfold tailWord_2741330
  simp only [CollatzResearch.WordTrace]
  refine ⟨24996129789659266683811361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66656346105758044490163629 24996129789659266683811361)
  ·
    refine ⟨18747097342244450012858521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24996129789659266683811361 18747097342244450012858521)
    ·
      refine ⟨14060323006683337509643891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18747097342244450012858521 14060323006683337509643891)
      ·
        refine ⟨21090484510025006264465837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14060323006683337509643891 21090484510025006264465837)
        ·
          refine ⟨7908931691259377349174689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21090484510025006264465837 7908931691259377349174689)
          ·
            refine ⟨5931698768444533011881017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7908931691259377349174689 5931698768444533011881017)
            ·
              refine ⟨4448774076333399758910763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5931698768444533011881017 4448774076333399758910763)
              ·
                refine ⟨6673161114500099638366145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4448774076333399758910763 6673161114500099638366145)
                ·
                  refine ⟨5004870835875074728774609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6673161114500099638366145 5004870835875074728774609)
                  ·
                    refine ⟨3753653126906306046580957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5004870835875074728774609 3753653126906306046580957)
                    ·
                      refine ⟨1407619922589864767467859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3753653126906306046580957 1407619922589864767467859)
                      ·
                        rfl

theorem cell23_2741330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_2741330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741330 prefixEnd_2741330 := by exact prefixLift 2741330
  have htrace : WordTrace (prefixWord ++ tailWord_2741330) baseStart_2741330 baseEnd_2741330 := by
    simpa [prefixWord, tailWord_2741330, baseEnd_2741330] using wordTrace_append hprefix tailTrace_2741330
  have hstable : (prefixWord ++ tailWord_2741330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741330).length < 2 ^ (prefixWord ++ tailWord_2741330).sum := by decide
  have hdescent : baseEnd_2741330 < baseStart_2741330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741354 : List Nat := [3, 1, 3, 2, 2, 3, 2, 2, 1, 4]
def baseStart_2741354 : Nat := 118140960795 + 2741354 * 2 ^ 59
def prefixEnd_2741354 : Nat := 4983230072969 + 3 ^ 40 * 2741354 * 2
def baseEnd_2741354 : Nat := 469210748708524224522583

theorem tailTrace_2741354 : CollatzResearch.WordTrace tailWord_2741354 prefixEnd_2741354 469210748708524224522583 := by
  unfold tailWord_2741354
  simp only [CollatzResearch.WordTrace]
  refine ⟨24996348627637529708529779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66656929673700079222746077 24996348627637529708529779)
  ·
    refine ⟨37494522941456294562794669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24996348627637529708529779 37494522941456294562794669)
    ·
      refine ⟨14060446103046110461048001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37494522941456294562794669 14060446103046110461048001)
      ·
        refine ⟨10545334577284582845786001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14060446103046110461048001 10545334577284582845786001)
        ·
          refine ⟨7909000932963437134339501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10545334577284582845786001 7909000932963437134339501)
          ·
            refine ⟨2965875349861288925377313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7909000932963437134339501 2965875349861288925377313)
            ·
              refine ⟨2224406512395966694032985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2965875349861288925377313 2224406512395966694032985)
              ·
                refine ⟨1668304884296975020524739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2224406512395966694032985 1668304884296975020524739)
                ·
                  refine ⟨2502457326445462530787109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1668304884296975020524739 2502457326445462530787109)
                  ·
                    refine ⟨469210748708524224522583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2502457326445462530787109 469210748708524224522583)
                    ·
                      rfl

theorem cell23_2741354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_2741354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741354 prefixEnd_2741354 := by exact prefixLift 2741354
  have htrace : WordTrace (prefixWord ++ tailWord_2741354) baseStart_2741354 baseEnd_2741354 := by
    simpa [prefixWord, tailWord_2741354, baseEnd_2741354] using wordTrace_append hprefix tailTrace_2741354
  have hstable : (prefixWord ++ tailWord_2741354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741354).length < 2 ^ (prefixWord ++ tailWord_2741354).sum := by decide
  have hdescent : baseEnd_2741354 < baseStart_2741354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741376 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 1, 6]
def baseStart_2741376 : Nat := 118140960795 + 2741376 * 2 ^ 59
def prefixEnd_2741376 : Nat := 4983230072969 + 3 ^ 40 * 2741376 * 2
def baseEnd_2741376 : Nat := 469214514233323862497549

theorem tailTrace_2741376 : CollatzResearch.WordTrace tailWord_2741376 prefixEnd_2741376 469214514233323862497549 := by
  unfold tailWord_2741376
  simp only [CollatzResearch.WordTrace]
  refine ⟨49993098458235208295709991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66657464610980277727613321 49993098458235208295709991)
  ·
    refine ⟨74989647687352812443564987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49993098458235208295709991 74989647687352812443564987)
    ·
      refine ⟨112484471531029218665347481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74989647687352812443564987 112484471531029218665347481)
      ·
        refine ⟨84363353648271913999010611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112484471531029218665347481 84363353648271913999010611)
        ·
          refine ⟨126545030472407870998515917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84363353648271913999010611 126545030472407870998515917)
          ·
            refine ⟨47454386427152951624443469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126545030472407870998515917 47454386427152951624443469)
            ·
              refine ⟨17795394910182356859166301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47454386427152951624443469 17795394910182356859166301)
              ·
                refine ⟨6673273091318383822187363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17795394910182356859166301 6673273091318383822187363)
                ·
                  refine ⟨10009909636977575733281045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6673273091318383822187363 10009909636977575733281045)
                  ·
                    refine ⟨469214514233323862497549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10009909636977575733281045 469214514233323862497549)
                    ·
                      rfl

theorem cell23_2741376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 1, 6].length) (baseStart_2741376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741376 prefixEnd_2741376 := by exact prefixLift 2741376
  have htrace : WordTrace (prefixWord ++ tailWord_2741376) baseStart_2741376 baseEnd_2741376 := by
    simpa [prefixWord, tailWord_2741376, baseEnd_2741376] using wordTrace_append hprefix tailTrace_2741376
  have hstable : (prefixWord ++ tailWord_2741376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741376).length < 2 ^ (prefixWord ++ tailWord_2741376).sum := by decide
  have hdescent : baseEnd_2741376 < baseStart_2741376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741383 : List Nat := [1, 1, 4, 2, 1, 1, 1, 6, 1, 1, 4]
def baseStart_2741383 : Nat := 118140960795 + 2741383 * 2 ^ 59
def prefixEnd_2741383 : Nat := 4983230072969 + 3 ^ 40 * 2741383 * 2
def baseEnd_2741383 : Nat := 1407647137064553060105115

theorem tailTrace_2741383 : CollatzResearch.WordTrace tailWord_2741383 prefixEnd_2741383 1407647137064553060105115 := by
  unfold tailWord_2741383
  simp only [CollatzResearch.WordTrace]
  refine ⟨99986452227445056786924803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66657634818296704524616535 99986452227445056786924803)
  ·
    refine ⟨149979678341167585180387205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99986452227445056786924803 149979678341167585180387205)
    ·
      refine ⟨28121189688968922221322601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149979678341167585180387205 28121189688968922221322601)
      ·
        refine ⟨21090892266726691665991951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28121189688968922221322601 21090892266726691665991951)
        ·
          refine ⟨31636338400090037498987927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21090892266726691665991951 31636338400090037498987927)
          ·
            refine ⟨47454507600135056248481891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31636338400090037498987927 47454507600135056248481891)
            ·
              refine ⟨71181761400202584372722837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47454507600135056248481891 71181761400202584372722837)
              ·
                refine ⟨3336645065634496142471383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71181761400202584372722837 3336645065634496142471383)
                ·
                  refine ⟨5004967598451744213707075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3336645065634496142471383 5004967598451744213707075)
                  ·
                    refine ⟨7507451397677616320560613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5004967598451744213707075 7507451397677616320560613)
                    ·
                      refine ⟨1407647137064553060105115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7507451397677616320560613 1407647137064553060105115)
                      ·
                        rfl

theorem cell23_2741383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_2741383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741383 prefixEnd_2741383 := by exact prefixLift 2741383
  have htrace : WordTrace (prefixWord ++ tailWord_2741383) baseStart_2741383 baseEnd_2741383 := by
    simpa [prefixWord, tailWord_2741383, baseEnd_2741383] using wordTrace_append hprefix tailTrace_2741383
  have hstable : (prefixWord ++ tailWord_2741383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741383).length < 2 ^ (prefixWord ++ tailWord_2741383).sum := by decide
  have hdescent : baseEnd_2741383 < baseStart_2741383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741394 : List Nat := [3, 2, 3, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_2741394 : Nat := 118140960795 + 2741394 * 2 ^ 59
def prefixEnd_2741394 : Nat := 4983230072969 + 3 ^ 40 * 2741394 * 2
def baseEnd_2741394 : Nat := 1407652785351752517067565

theorem tailTrace_2741394 : CollatzResearch.WordTrace tailWord_2741394 prefixEnd_2741394 1407652785351752517067565 := by
  unfold tailWord_2741394
  simp only [CollatzResearch.WordTrace]
  refine ⟨24996713357601301416393809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66657902286936803777050157 24996713357601301416393809)
  ·
    refine ⟨18747535018200976062295357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24996713357601301416393809 18747535018200976062295357)
    ·
      refine ⟨7030325631825366023360759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18747535018200976062295357 7030325631825366023360759)
      ·
        refine ⟨10545488447738049035041139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7030325631825366023360759 10545488447738049035041139)
        ·
          refine ⟨15818232671607073552561709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10545488447738049035041139 15818232671607073552561709)
          ·
            refine ⟨5931837251852652582210641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15818232671607073552561709 5931837251852652582210641)
            ·
              refine ⟨4448877938889489436657981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5931837251852652582210641 4448877938889489436657981)
              ·
                refine ⟨1668329227083558538746743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4448877938889489436657981 1668329227083558538746743)
                ·
                  refine ⟨2502493840625337808120115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1668329227083558538746743 2502493840625337808120115)
                  ·
                    refine ⟨3753740760938006712180173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2502493840625337808120115 3753740760938006712180173)
                    ·
                      refine ⟨1407652785351752517067565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3753740760938006712180173 1407652785351752517067565)
                      ·
                        rfl

theorem cell23_2741394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_2741394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741394 prefixEnd_2741394 := by exact prefixLift 2741394
  have htrace : WordTrace (prefixWord ++ tailWord_2741394) baseStart_2741394 baseEnd_2741394 := by
    simpa [prefixWord, tailWord_2741394, baseEnd_2741394] using wordTrace_append hprefix tailTrace_2741394
  have hstable : (prefixWord ++ tailWord_2741394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741394).length < 2 ^ (prefixWord ++ tailWord_2741394).sum := by decide
  have hdescent : baseEnd_2741394 < baseStart_2741394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741400 : List Nat := [2, 1, 2, 4, 2, 2, 1, 3, 1, 1, 4]
def baseStart_2741400 : Nat := 118140960795 + 2741400 * 2 ^ 59
def prefixEnd_2741400 : Nat := 4983230072969 + 3 ^ 40 * 2741400 * 2
def baseEnd_2741400 : Nat := 1407655866235679493592537

theorem tailTrace_2741400 : CollatzResearch.WordTrace tailWord_2741400 prefixEnd_2741400 1407655866235679493592537 := by
  unfold tailWord_2741400
  simp only [CollatzResearch.WordTrace]
  refine ⟨49993536134191734345146827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66658048178922312460195769 49993536134191734345146827)
  ·
    refine ⟨74990304201287601517720241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49993536134191734345146827 74990304201287601517720241)
    ·
      refine ⟨56242728150965701138290181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74990304201287601517720241 56242728150965701138290181)
      ·
        refine ⟨10545511528306068963429409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56242728150965701138290181 10545511528306068963429409)
        ·
          refine ⟨7909133646229551722572057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10545511528306068963429409 7909133646229551722572057)
          ·
            refine ⟨5931850234672163791929043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7909133646229551722572057 5931850234672163791929043)
            ·
              refine ⟨8897775352008245687893565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5931850234672163791929043 8897775352008245687893565)
              ·
                refine ⟨3336665757003092132960087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8897775352008245687893565 3336665757003092132960087)
                ·
                  refine ⟨5004998635504638199440131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3336665757003092132960087 5004998635504638199440131)
                  ·
                    refine ⟨7507497953256957299160197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5004998635504638199440131 7507497953256957299160197)
                    ·
                      refine ⟨1407655866235679493592537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7507497953256957299160197 1407655866235679493592537)
                      ·
                        rfl

theorem cell23_2741400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_2741400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741400 prefixEnd_2741400 := by exact prefixLift 2741400
  have htrace : WordTrace (prefixWord ++ tailWord_2741400) baseStart_2741400 baseEnd_2741400 := by
    simpa [prefixWord, tailWord_2741400, baseEnd_2741400] using wordTrace_append hprefix tailTrace_2741400
  have hstable : (prefixWord ++ tailWord_2741400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741400).length < 2 ^ (prefixWord ++ tailWord_2741400).sum := by decide
  have hdescent : baseEnd_2741400 < baseStart_2741400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741440 : List Nat := [2, 1, 1, 2, 6, 2, 2, 7]
def baseStart_2741440 : Nat := 118140960795 + 2741440 * 2 ^ 59
def prefixEnd_2741440 : Nat := 4983230072969 + 3 ^ 40 * 2741440 * 2
def baseEnd_2741440 : Nat := 52136163165254049521939

theorem tailTrace_2741440 : CollatzResearch.WordTrace tailWord_2741440 prefixEnd_2741440 52136163165254049521939 := by
  unfold tailWord_2741440
  simp only [CollatzResearch.WordTrace]
  refine ⟨49994265594119277760874887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66659020792159037014499849 49994265594119277760874887)
  ·
    refine ⟨74991398391178916641312331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49994265594119277760874887 74991398391178916641312331)
    ·
      refine ⟨112487097586768374961968497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74991398391178916641312331 112487097586768374961968497)
      ·
        refine ⟨84365323190076281221476373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112487097586768374961968497 84365323190076281221476373)
        ·
          refine ⟨3954624524534825682256705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84365323190076281221476373 3954624524534825682256705)
          ·
            refine ⟨2965968393401119261692529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3954624524534825682256705 2965968393401119261692529)
            ·
              refine ⟨2224476295050839446269397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2965968393401119261692529 2224476295050839446269397)
              ·
                refine ⟨52136163165254049521939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2224476295050839446269397 52136163165254049521939)
                ·
                  rfl

theorem cell23_2741440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 7].length) (baseStart_2741440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741440 prefixEnd_2741440 := by exact prefixLift 2741440
  have htrace : WordTrace (prefixWord ++ tailWord_2741440) baseStart_2741440 baseEnd_2741440 := by
    simpa [prefixWord, tailWord_2741440, baseEnd_2741440] using wordTrace_append hprefix tailTrace_2741440
  have hstable : (prefixWord ++ tailWord_2741440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741440).length < 2 ^ (prefixWord ++ tailWord_2741440).sum := by decide
  have hdescent : baseEnd_2741440 < baseStart_2741440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741450 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 4, 1, 3]
def baseStart_2741450 : Nat := 118140960795 + 2741450 * 2 ^ 59
def prefixEnd_2741450 : Nat := 4983230072969 + 3 ^ 40 * 2741450 * 2
def baseEnd_2741450 : Nat := 1407681540268404297967307

theorem tailTrace_2741450 : CollatzResearch.WordTrace tailWord_2741450 prefixEnd_2741450 1407681540268404297967307 := by
  unfold tailWord_2741450
  simp only [CollatzResearch.WordTrace]
  refine ⟨24997223979550581807403451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66659263945468218153075869 24997223979550581807403451)
  ·
    refine ⟨37495835969325872711105177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24997223979550581807403451 37495835969325872711105177)
    ·
      refine ⟨28121876976994404533328883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37495835969325872711105177 28121876976994404533328883)
      ·
        refine ⟨42182815465491606799993325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28121876976994404533328883 42182815465491606799993325)
        ·
          refine ⟨15818555799559352549997497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42182815465491606799993325 15818555799559352549997497)
          ·
            refine ⟨11863916849669514412498123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15818555799559352549997497 11863916849669514412498123)
            ·
              refine ⟨17795875274504271618747185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11863916849669514412498123 17795875274504271618747185)
              ·
                refine ⟨13346906455878203714060389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17795875274504271618747185 13346906455878203714060389)
                ·
                  refine ⟨2502544960477163196386323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13346906455878203714060389 2502544960477163196386323)
                  ·
                    refine ⟨3753817440715744794579485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2502544960477163196386323 3753817440715744794579485)
                    ·
                      refine ⟨1407681540268404297967307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3753817440715744794579485 1407681540268404297967307)
                      ·
                        rfl

theorem cell23_2741450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_2741450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741450 prefixEnd_2741450 := by exact prefixLift 2741450
  have htrace : WordTrace (prefixWord ++ tailWord_2741450) baseStart_2741450 baseEnd_2741450 := by
    simpa [prefixWord, tailWord_2741450, baseEnd_2741450] using wordTrace_append hprefix tailTrace_2741450
  have hstable : (prefixWord ++ tailWord_2741450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741450).length < 2 ^ (prefixWord ++ tailWord_2741450).sum := by decide
  have hdescent : baseEnd_2741450 < baseStart_2741450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741484 : List Nat := [2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 3]
def baseStart_2741484 : Nat := 118140960795 + 2741484 * 2 ^ 59
def prefixEnd_2741484 : Nat := 4983230072969 + 3 ^ 40 * 2741484 * 2
def baseEnd_2741484 : Nat := 1407698998610657164942151

theorem tailTrace_2741484 : CollatzResearch.WordTrace tailWord_2741484 prefixEnd_2741484 1407698998610657164942151 := by
  unfold tailWord_2741484
  simp only [CollatzResearch.WordTrace]
  refine ⟨49995068000039575518175753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66660090666719434024234337 49995068000039575518175753)
  ·
    refine ⟨37496301000029681638631815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49995068000039575518175753 37496301000029681638631815)
    ·
      refine ⟨56244451500044522457947723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37496301000029681638631815 56244451500044522457947723)
      ·
        refine ⟨84366677250066783686921585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56244451500044522457947723 84366677250066783686921585)
        ·
          refine ⟨63275007937550087765191189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84366677250066783686921585 63275007937550087765191189)
          ·
            refine ⟨2966015997072660363993337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 63275007937550087765191189 2966015997072660363993337)
            ·
              refine ⟨2224511997804495272995003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2966015997072660363993337 2224511997804495272995003)
              ·
                refine ⟨3336767996706742909492505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2224511997804495272995003 3336767996706742909492505)
                ·
                  refine ⟨2502575997530057182119379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3336767996706742909492505 2502575997530057182119379)
                  ·
                    refine ⟨3753863996295085773179069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2502575997530057182119379 3753863996295085773179069)
                    ·
                      refine ⟨1407698998610657164942151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3753863996295085773179069 1407698998610657164942151)
                      ·
                        rfl

theorem cell23_2741484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 3].length) (baseStart_2741484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741484 prefixEnd_2741484 := by exact prefixLift 2741484
  have htrace : WordTrace (prefixWord ++ tailWord_2741484) baseStart_2741484 baseEnd_2741484 := by
    simpa [prefixWord, tailWord_2741484, baseEnd_2741484] using wordTrace_append hprefix tailTrace_2741484
  have hstable : (prefixWord ++ tailWord_2741484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741484).length < 2 ^ (prefixWord ++ tailWord_2741484).sum := by decide
  have hdescent : baseEnd_2741484 < baseStart_2741484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741540 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 2, 3, 3]
def baseStart_2741540 : Nat := 118140960795 + 2741540 * 2 ^ 59
def prefixEnd_2741540 : Nat := 4983230072969 + 3 ^ 40 * 2741540 * 2
def baseEnd_2741540 : Nat := 1407727753527308945841893

theorem tailTrace_2741540 : CollatzResearch.WordTrace tailWord_2741540 prefixEnd_2741540 1407727753527308945841893 := by
  unfold tailWord_2741540
  simp only [CollatzResearch.WordTrace]
  refine ⟨49996089243938136300195037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66661452325250848400260049 49996089243938136300195037)
  ·
    refine ⟨18748533466476801112573139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49996089243938136300195037 18748533466476801112573139)
    ·
      refine ⟨28122800199715201668859709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18748533466476801112573139 28122800199715201668859709)
      ·
        refine ⟨10546050074893200625822391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28122800199715201668859709 10546050074893200625822391)
        ·
          refine ⟨15819075112339800938733587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10546050074893200625822391 15819075112339800938733587)
          ·
            refine ⟨23728612668509701408100381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15819075112339800938733587 23728612668509701408100381)
            ·
              refine ⟨8898229750691138028037643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23728612668509701408100381 8898229750691138028037643)
              ·
                refine ⟨13347344626036707042056465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8898229750691138028037643 13347344626036707042056465)
                ·
                  refine ⟨10010508469527530281542349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13347344626036707042056465 10010508469527530281542349)
                  ·
                    refine ⟨3753940676072823855578381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10010508469527530281542349 3753940676072823855578381)
                    ·
                      refine ⟨1407727753527308945841893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3753940676072823855578381 1407727753527308945841893)
                      ·
                        rfl

theorem cell23_2741540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_2741540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741540 prefixEnd_2741540 := by exact prefixLift 2741540
  have htrace : WordTrace (prefixWord ++ tailWord_2741540) baseStart_2741540 baseEnd_2741540 := by
    simpa [prefixWord, tailWord_2741540, baseEnd_2741540] using wordTrace_append hprefix tailTrace_2741540
  have hstable : (prefixWord ++ tailWord_2741540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741540).length < 2 ^ (prefixWord ++ tailWord_2741540).sum := by decide
  have hdescent : baseEnd_2741540 < baseStart_2741540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741600 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 3]
def baseStart_2741600 : Nat := 118140960795 + 2741600 * 2 ^ 59
def prefixEnd_2741600 : Nat := 4983230072969 + 3 ^ 40 * 2741600 * 2
def baseEnd_2741600 : Nat := 1407758562366578711091617

theorem tailTrace_2741600 : CollatzResearch.WordTrace tailWord_2741600 prefixEnd_2741600 1407758562366578711091617 := by
  unfold tailWord_2741600
  simp only [CollatzResearch.WordTrace]
  refine ⟨49997183433829451423787127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66662911245105935231716169 49997183433829451423787127)
  ·
    refine ⟨74995775150744177135680691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49997183433829451423787127 74995775150744177135680691)
    ·
      refine ⟨112493662726116265703521037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74995775150744177135680691 112493662726116265703521037)
      ·
        refine ⟨42185123522293599638820389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112493662726116265703521037 42185123522293599638820389)
        ·
          refine ⟨7909710660430049932278823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42185123522293599638820389 7909710660430049932278823)
          ·
            refine ⟨11864565990645074898418235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7909710660430049932278823 11864565990645074898418235)
            ·
              refine ⟨17796848985967612347627353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11864565990645074898418235 17796848985967612347627353)
              ·
                refine ⟨13347636739475709260720515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17796848985967612347627353 13347636739475709260720515)
                ·
                  refine ⟨20021455109213563891080773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13347636739475709260720515 20021455109213563891080773)
                  ·
                    refine ⟨3754022832977543229577645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20021455109213563891080773 3754022832977543229577645)
                    ·
                      refine ⟨1407758562366578711091617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3754022832977543229577645 1407758562366578711091617)
                      ·
                        rfl

theorem cell23_2741600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_2741600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741600 prefixEnd_2741600 := by exact prefixLift 2741600
  have htrace : WordTrace (prefixWord ++ tailWord_2741600) baseStart_2741600 baseEnd_2741600 := by
    simpa [prefixWord, tailWord_2741600, baseEnd_2741600] using wordTrace_append hprefix tailTrace_2741600
  have hstable : (prefixWord ++ tailWord_2741600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741600).length < 2 ^ (prefixWord ++ tailWord_2741600).sum := by decide
  have hdescent : baseEnd_2741600 < baseStart_2741600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741634 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_2741634 : Nat := 118140960795 + 2741634 * 2 ^ 59
def prefixEnd_2741634 : Nat := 4983230072969 + 3 ^ 40 * 2741634 * 2
def baseEnd_2741634 : Nat := 1407776020708831578066461

theorem tailTrace_2741634 : CollatzResearch.WordTrace tailWord_2741634 prefixEnd_2741634 1407776020708831578066461 := by
  unfold tailWord_2741634
  simp only [CollatzResearch.WordTrace]
  refine ⟨24998901737383931663577989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66663737966357151102874637 24998901737383931663577989)
  ·
    refine ⟨4687294075759487186920873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24998901737383931663577989 4687294075759487186920873)
    ·
      refine ⟨3515470556819615390190655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4687294075759487186920873 3515470556819615390190655)
      ·
        refine ⟨5273205835229423085285983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3515470556819615390190655 5273205835229423085285983)
        ·
          refine ⟨7909808752844134627928975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5273205835229423085285983 7909808752844134627928975)
          ·
            refine ⟨11864713129266201941893463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7909808752844134627928975 11864713129266201941893463)
            ·
              refine ⟨17797069693899302912840195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11864713129266201941893463 17797069693899302912840195)
              ·
                refine ⟨26695604540848954369260293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17797069693899302912840195 26695604540848954369260293)
                ·
                  refine ⟨5005425851409178944236305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26695604540848954369260293 5005425851409178944236305)
                  ·
                    refine ⟨3754069388556884208177229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5005425851409178944236305 3754069388556884208177229)
                    ·
                      refine ⟨1407776020708831578066461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3754069388556884208177229 1407776020708831578066461)
                      ·
                        rfl

theorem cell23_2741634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_2741634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741634 prefixEnd_2741634 := by exact prefixLift 2741634
  have htrace : WordTrace (prefixWord ++ tailWord_2741634) baseStart_2741634 baseEnd_2741634 := by
    simpa [prefixWord, tailWord_2741634, baseEnd_2741634] using wordTrace_append hprefix tailTrace_2741634
  have hstable : (prefixWord ++ tailWord_2741634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741634).length < 2 ^ (prefixWord ++ tailWord_2741634).sum := by decide
  have hdescent : baseEnd_2741634 < baseStart_2741634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741641 : List Nat := [1, 2, 1, 1, 7, 1, 3, 2, 1, 4]
def baseStart_2741641 : Nat := 118140960795 + 2741641 * 2 ^ 59
def prefixEnd_2741641 : Nat := 4983230072969 + 3 ^ 40 * 2741641 * 2
def baseEnd_2741641 : Nat := 469259871691137683559643

theorem tailTrace_2741641 : CollatzResearch.WordTrace tailWord_2741641 prefixEnd_2741641 469259871691137683559643 := by
  unfold tailWord_2741641
  simp only [CollatzResearch.WordTrace]
  refine ⟨99995862260510366849816777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66663908173673577899877851 99995862260510366849816777)
  ·
    refine ⟨74996896695382775137362583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99995862260510366849816777 74996896695382775137362583)
    ·
      refine ⟨112495345043074162706043875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74996896695382775137362583 112495345043074162706043875)
      ·
        refine ⟨168743017564611244059065813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112495345043074162706043875 168743017564611244059065813)
        ·
          refine ⟨3954914474170576032634355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 168743017564611244059065813 3954914474170576032634355)
          ·
            refine ⟨5932371711255864048951533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3954914474170576032634355 5932371711255864048951533)
            ·
              refine ⟨2224639391720949018356825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5932371711255864048951533 2224639391720949018356825)
              ·
                refine ⟨1668479543790711763767619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2224639391720949018356825 1668479543790711763767619)
                ·
                  refine ⟨2502719315686067645651429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1668479543790711763767619 2502719315686067645651429)
                  ·
                    refine ⟨469259871691137683559643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2502719315686067645651429 469259871691137683559643)
                    ·
                      rfl

theorem cell23_2741641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 1, 4].length) (baseStart_2741641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741641 prefixEnd_2741641 := by exact prefixLift 2741641
  have htrace : WordTrace (prefixWord ++ tailWord_2741641) baseStart_2741641 baseEnd_2741641 := by
    simpa [prefixWord, tailWord_2741641, baseEnd_2741641] using wordTrace_append hprefix tailTrace_2741641
  have hstable : (prefixWord ++ tailWord_2741641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741641).length < 2 ^ (prefixWord ++ tailWord_2741641).sum := by decide
  have hdescent : baseEnd_2741641 < baseStart_2741641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741673 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 2, 5, 5]
def baseStart_2741673 : Nat := 118140960795 + 2741673 * 2 ^ 59
def prefixEnd_2741673 : Nat := 4983230072969 + 3 ^ 40 * 2741673 * 2
def baseEnd_2741673 : Nat := 1407796046454356925478781

theorem tailTrace_2741673 : CollatzResearch.WordTrace tailWord_2741673 prefixEnd_2741673 1407796046454356925478781 := by
  unfold tailWord_2741673
  simp only [CollatzResearch.WordTrace]
  refine ⟨99997029396394436314981673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66664686264262957543321115 99997029396394436314981673)
  ·
    refine ⟨74997772047295827236236255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99997029396394436314981673 74997772047295827236236255)
    ·
      refine ⟨112496658070943740854354383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74997772047295827236236255 112496658070943740854354383)
      ·
        refine ⟨168744987106415611281531575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112496658070943740854354383 168744987106415611281531575)
        ·
          refine ⟨253117480659623416922297363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168744987106415611281531575 253117480659623416922297363)
          ·
            refine ⟨379676220989435125383446045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253117480659623416922297363 379676220989435125383446045)
            ·
              refine ⟨142378582871038172018792267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 379676220989435125383446045 142378582871038172018792267)
              ·
                refine ⟨213567874306557258028188401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142378582871038172018792267 213567874306557258028188401)
                ·
                  refine ⟨160175905729917943521141301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213567874306557258028188401 160175905729917943521141301)
                  ·
                    refine ⟨15016491162179807205106997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 160175905729917943521141301 15016491162179807205106997)
                    ·
                      refine ⟨1407796046454356925478781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15016491162179807205106997 1407796046454356925478781)
                      ·
                        rfl

theorem cell23_2741673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_2741673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741673 prefixEnd_2741673 := by exact prefixLift 2741673
  have htrace : WordTrace (prefixWord ++ tailWord_2741673) baseStart_2741673 baseEnd_2741673 := by
    simpa [prefixWord, tailWord_2741673, baseEnd_2741673] using wordTrace_append hprefix tailTrace_2741673
  have hstable : (prefixWord ++ tailWord_2741673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741673).length < 2 ^ (prefixWord ++ tailWord_2741673).sum := by decide
  have hdescent : baseEnd_2741673 < baseStart_2741673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741680 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 4, 4]
def baseStart_2741680 : Nat := 118140960795 + 2741680 * 2 ^ 59
def prefixEnd_2741680 : Nat := 4983230072969 + 3 ^ 40 * 2741680 * 2
def baseEnd_2741680 : Nat := 469266546939646132697083

theorem tailTrace_2741680 : CollatzResearch.WordTrace tailWord_2741680 prefixEnd_2741680 469266546939646132697083 := by
  unfold tailWord_2741680
  simp only [CollatzResearch.WordTrace]
  refine ⟨49998642353684538255243247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66664856471579384340324329 49998642353684538255243247)
  ·
    refine ⟨74997963530526807382864871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49998642353684538255243247 74997963530526807382864871)
    ·
      refine ⟨112496945295790211074297307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74997963530526807382864871 112496945295790211074297307)
      ·
        refine ⟨168745417943685316611445961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112496945295790211074297307 168745417943685316611445961)
        ·
          refine ⟨126559063457763987458584471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168745417943685316611445961 126559063457763987458584471)
          ·
            refine ⟨189838595186645981187876707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126559063457763987458584471 189838595186645981187876707)
            ·
              refine ⟨284757892779968971781815061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189838595186645981187876707 284757892779968971781815061)
              ·
                refine ⟨13348026224061045552272581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 284757892779968971781815061 13348026224061045552272581)
                ·
                  refine ⟨2502754917011446041051109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13348026224061045552272581 2502754917011446041051109)
                  ·
                    refine ⟨469266546939646132697083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2502754917011446041051109 469266546939646132697083)
                    ·
                      rfl

theorem cell23_2741680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 4, 4].length) (baseStart_2741680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741680 prefixEnd_2741680 := by exact prefixLift 2741680
  have htrace : WordTrace (prefixWord ++ tailWord_2741680) baseStart_2741680 baseEnd_2741680 := by
    simpa [prefixWord, tailWord_2741680, baseEnd_2741680] using wordTrace_append hprefix tailTrace_2741680
  have hstable : (prefixWord ++ tailWord_2741680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741680).length < 2 ^ (prefixWord ++ tailWord_2741680).sum := by decide
  have hdescent : baseEnd_2741680 < baseStart_2741680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741704 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 3, 2, 2]
def baseStart_2741704 : Nat := 118140960795 + 2741704 * 2 ^ 59
def prefixEnd_2741704 : Nat := 4983230072969 + 3 ^ 40 * 2741704 * 2
def baseEnd_2741704 : Nat := 1407811964354646304191139

theorem tailTrace_2741704 : CollatzResearch.WordTrace tailWord_2741704 prefixEnd_2741704 1407811964354646304191139 := by
  unfold tailWord_2741704
  simp only [CollatzResearch.WordTrace]
  refine ⟨49999080029641064304680083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66665440039521419072906777 49999080029641064304680083)
  ·
    refine ⟨74998620044461596457020125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49999080029641064304680083 74998620044461596457020125)
    ·
      refine ⟨28124482516673098671382547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74998620044461596457020125 28124482516673098671382547)
      ·
        refine ⟨42186723775009648007073821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28124482516673098671382547 42186723775009648007073821)
        ·
          refine ⟨15820021415628618002652683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42186723775009648007073821 15820021415628618002652683)
          ·
            refine ⟨23730032123442927003979025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15820021415628618002652683 23730032123442927003979025)
            ·
              refine ⟨17797524092582195252984269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23730032123442927003979025 17797524092582195252984269)
              ·
                refine ⟨6674071534718323219869101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17797524092582195252984269 6674071534718323219869101)
                ·
                  refine ⟨2502776825519371207450913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6674071534718323219869101 2502776825519371207450913)
                  ·
                    refine ⟨1877082619139528405588185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2502776825519371207450913 1877082619139528405588185)
                    ·
                      refine ⟨1407811964354646304191139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1877082619139528405588185 1407811964354646304191139)
                      ·
                        rfl

theorem cell23_2741704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_2741704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741704 prefixEnd_2741704 := by exact prefixLift 2741704
  have htrace : WordTrace (prefixWord ++ tailWord_2741704) baseStart_2741704 baseEnd_2741704 := by
    simpa [prefixWord, tailWord_2741704, baseEnd_2741704] using wordTrace_append hprefix tailTrace_2741704
  have hstable : (prefixWord ++ tailWord_2741704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741704).length < 2 ^ (prefixWord ++ tailWord_2741704).sum := by decide
  have hdescent : baseEnd_2741704 < baseStart_2741704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741710 : List Nat := [4, 1, 1, 1, 2, 1, 5, 8]
def baseStart_2741710 : Nat := 118140960795 + 2741710 * 2 ^ 59
def prefixEnd_2741710 : Nat := 4983230072969 + 3 ^ 40 * 2741710 * 2
def baseEnd_2741710 : Nat := 52141297971799010396893

theorem tailTrace_2741710 : CollatzResearch.WordTrace tailWord_2741710 prefixEnd_2741710 52141297971799010396893 := by
  unfold tailWord_2741710
  simp only [CollatzResearch.WordTrace]
  refine ⟨12499797362157548954259823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66665585931506927756052389 12499797362157548954259823)
  ·
    refine ⟨18749696043236323431389735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12499797362157548954259823 18749696043236323431389735)
    ·
      refine ⟨28124544064854485147084603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18749696043236323431389735 28124544064854485147084603)
      ·
        refine ⟨42186816097281727720626905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28124544064854485147084603 42186816097281727720626905)
        ·
          refine ⟨31640112072961295790470179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42186816097281727720626905 31640112072961295790470179)
          ·
            refine ⟨47460168109441943685705269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31640112072961295790470179 47460168109441943685705269)
            ·
              refine ⟨4449390760260182220534869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47460168109441943685705269 4449390760260182220534869)
              ·
                refine ⟨52141297971799010396893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4449390760260182220534869 52141297971799010396893)
                ·
                  rfl

theorem cell23_2741710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 8].length) (baseStart_2741710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741710 prefixEnd_2741710 := by exact prefixLift 2741710
  have htrace : WordTrace (prefixWord ++ tailWord_2741710) baseStart_2741710 baseEnd_2741710 := by
    simpa [prefixWord, tailWord_2741710, baseEnd_2741710] using wordTrace_append hprefix tailTrace_2741710
  have hstable : (prefixWord ++ tailWord_2741710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741710).length < 2 ^ (prefixWord ++ tailWord_2741710).sum := by decide
  have hdescent : baseEnd_2741710 < baseStart_2741710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741717 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 1, 2, 4]
def baseStart_2741717 : Nat := 118140960795 + 2741717 * 2 ^ 59
def prefixEnd_2741717 : Nat := 4983230072969 + 3 ^ 40 * 2741717 * 2
def baseEnd_2741717 : Nat := 1407818639603154753328579

theorem tailTrace_2741717 : CollatzResearch.WordTrace tailWord_2741717 prefixEnd_2741717 1407818639603154753328579 := by
  unfold tailWord_2741717
  simp only [CollatzResearch.WordTrace]
  refine ⟨99998634208235031829583405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66665756138823354553055603 99998634208235031829583405)
  ·
    refine ⟨37499487828088136936093777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99998634208235031829583405 37499487828088136936093777)
    ·
      refine ⟨28124615871066102702070333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37499487828088136936093777 28124615871066102702070333)
      ·
        refine ⟨10546730951649788513276375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28124615871066102702070333 10546730951649788513276375)
        ·
          refine ⟨15820096427474682769914563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10546730951649788513276375 15820096427474682769914563)
          ·
            refine ⟨23730144641212024154871845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15820096427474682769914563 23730144641212024154871845)
            ·
              refine ⟨4449402120227254529038471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23730144641212024154871845 4449402120227254529038471)
              ·
                refine ⟨6674103180340881793557707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4449402120227254529038471 6674103180340881793557707)
                ·
                  refine ⟨10011154770511322690336561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6674103180340881793557707 10011154770511322690336561)
                  ·
                    refine ⟨7508366077883492017752421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10011154770511322690336561 7508366077883492017752421)
                    ·
                      refine ⟨1407818639603154753328579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7508366077883492017752421 1407818639603154753328579)
                      ·
                        rfl

theorem cell23_2741717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_2741717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741717 prefixEnd_2741717 := by exact prefixLift 2741717
  have htrace : WordTrace (prefixWord ++ tailWord_2741717) baseStart_2741717 baseEnd_2741717 := by
    simpa [prefixWord, tailWord_2741717, baseEnd_2741717] using wordTrace_append hprefix tailTrace_2741717
  have hstable : (prefixWord ++ tailWord_2741717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741717).length < 2 ^ (prefixWord ++ tailWord_2741717).sum := by decide
  have hdescent : baseEnd_2741717 < baseStart_2741717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741738 : List Nat := [3, 1, 3, 1, 5, 1, 2, 1, 1, 1, 4]
def baseStart_2741738 : Nat := 118140960795 + 2741738 * 2 ^ 59
def prefixEnd_2741738 : Nat := 4983230072969 + 3 ^ 40 * 2741738 * 2
def baseEnd_2741738 : Nat := 1407829422696899171165983

theorem tailTrace_2741738 : CollatzResearch.WordTrace tailWord_2741738 prefixEnd_2741738 1407829422696899171165983 := by
  unfold tailWord_2741738
  simp only [CollatzResearch.WordTrace]
  refine ⟨24999850035289738104024467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66666266760772634944065245 24999850035289738104024467)
  ·
    refine ⟨37499775052934607156036701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24999850035289738104024467 37499775052934607156036701)
    ·
      refine ⟨14062415644850477683513763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37499775052934607156036701 14062415644850477683513763)
      ·
        refine ⟨21093623467275716525270645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14062415644850477683513763 21093623467275716525270645)
        ·
          refine ⟨1977527200057098424244123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21093623467275716525270645 1977527200057098424244123)
          ·
            refine ⟨2966290800085647636366185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977527200057098424244123 2966290800085647636366185)
            ·
              refine ⟨2224718100064235727274639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2966290800085647636366185 2224718100064235727274639)
              ·
                refine ⟨3337077150096353590911959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2224718100064235727274639 3337077150096353590911959)
                ·
                  refine ⟨5005615725144530386367939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3337077150096353590911959 5005615725144530386367939)
                  ·
                    refine ⟨7508423587716795579551909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5005615725144530386367939 7508423587716795579551909)
                    ·
                      refine ⟨1407829422696899171165983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7508423587716795579551909 1407829422696899171165983)
                      ·
                        rfl

theorem cell23_2741738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_2741738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741738 prefixEnd_2741738 := by exact prefixLift 2741738
  have htrace : WordTrace (prefixWord ++ tailWord_2741738) baseStart_2741738 baseEnd_2741738 := by
    simpa [prefixWord, tailWord_2741738, baseEnd_2741738] using wordTrace_append hprefix tailTrace_2741738
  have hstable : (prefixWord ++ tailWord_2741738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741738).length < 2 ^ (prefixWord ++ tailWord_2741738).sum := by decide
  have hdescent : baseEnd_2741738 < baseStart_2741738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741741 : List Nat := [1, 5, 1, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_2741741 : Nat := 118140960795 + 2741741 * 2 ^ 59
def prefixEnd_2741741 : Nat := 4983230072969 + 3 ^ 40 * 2741741 * 2
def baseEnd_2741741 : Nat := 1407830963138862659428469

theorem tailTrace_2741741 : CollatzResearch.WordTrace tailWord_2741741 prefixEnd_2741741 1407830963138862659428469 := by
  unfold tailWord_2741741
  simp only [CollatzResearch.WordTrace]
  refine ⟨99999509560148083928457077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66666339706765389285638051 99999509560148083928457077)
  ·
    refine ⟨9374954021263882868292851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99999509560148083928457077 9374954021263882868292851)
    ·
      refine ⟨14062431031895824302439277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9374954021263882868292851 14062431031895824302439277)
      ·
        refine ⟨5273411636960934113414729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14062431031895824302439277 5273411636960934113414729)
        ·
          refine ⟨3955058727720700585061047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5273411636960934113414729 3955058727720700585061047)
          ·
            refine ⟨5932588091581050877591571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3955058727720700585061047 5932588091581050877591571)
            ·
              refine ⟨8898882137371576316387357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5932588091581050877591571 8898882137371576316387357)
              ·
                refine ⟨3337080801514341118645259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8898882137371576316387357 3337080801514341118645259)
                ·
                  refine ⟨5005621202271511677967889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3337080801514341118645259 5005621202271511677967889)
                  ·
                    refine ⟨3754215901703633758475917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5005621202271511677967889 3754215901703633758475917)
                    ·
                      refine ⟨1407830963138862659428469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3754215901703633758475917 1407830963138862659428469)
                      ·
                        rfl

theorem cell23_2741741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_2741741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741741 prefixEnd_2741741 := by exact prefixLift 2741741
  have htrace : WordTrace (prefixWord ++ tailWord_2741741) baseStart_2741741 baseEnd_2741741 := by
    simpa [prefixWord, tailWord_2741741, baseEnd_2741741] using wordTrace_append hprefix tailTrace_2741741
  have hstable : (prefixWord ++ tailWord_2741741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741741).length < 2 ^ (prefixWord ++ tailWord_2741741).sum := by decide
  have hdescent : baseEnd_2741741 < baseStart_2741741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741747 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 5, 3, 2]
def baseStart_2741747 : Nat := 118140960795 + 2741747 * 2 ^ 59
def prefixEnd_2741747 : Nat := 4983230072969 + 3 ^ 40 * 2741747 * 2
def baseEnd_2741747 : Nat := 1407834044022789635953441

theorem tailTrace_2741747 : CollatzResearch.WordTrace tailWord_2741747 prefixEnd_2741747 1407834044022789635953441 := by
  unfold tailWord_2741747
  simp only [CollatzResearch.WordTrace]
  refine ⟨99999728398126346953175495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66666485598750897968783663 99999728398126346953175495)
  ·
    refine ⟨149999592597189520429763243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99999728398126346953175495 149999592597189520429763243)
    ·
      refine ⟨224999388895784280644644865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149999592597189520429763243 224999388895784280644644865)
      ·
        refine ⟨168749541671838210483483649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224999388895784280644644865 168749541671838210483483649)
        ·
          refine ⟨126562156253878657862612737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168749541671838210483483649 126562156253878657862612737)
          ·
            refine ⟨94921617190408993396959553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126562156253878657862612737 94921617190408993396959553)
            ·
              refine ⟨71191212892806745047719665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94921617190408993396959553 71191212892806745047719665)
              ·
                refine ⟨53393409669605058785789749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71191212892806745047719665 53393409669605058785789749)
                ·
                  refine ⟨5005632156525474261167789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53393409669605058785789749 5005632156525474261167789)
                  ·
                    refine ⟨1877112058697052847937921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5005632156525474261167789 1877112058697052847937921)
                    ·
                      refine ⟨1407834044022789635953441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1877112058697052847937921 1407834044022789635953441)
                      ·
                        rfl

theorem cell23_2741747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 3, 2].length) (baseStart_2741747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741747 prefixEnd_2741747 := by exact prefixLift 2741747
  have htrace : WordTrace (prefixWord ++ tailWord_2741747) baseStart_2741747 baseEnd_2741747 := by
    simpa [prefixWord, tailWord_2741747, baseEnd_2741747] using wordTrace_append hprefix tailTrace_2741747
  have hstable : (prefixWord ++ tailWord_2741747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741747).length < 2 ^ (prefixWord ++ tailWord_2741747).sum := by decide
  have hdescent : baseEnd_2741747 < baseStart_2741747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741771 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 1, 3, 3]
def baseStart_2741771 : Nat := 118140960795 + 2741771 * 2 ^ 59
def prefixEnd_2741771 : Nat := 4983230072969 + 3 ^ 40 * 2741771 * 2
def baseEnd_2741771 : Nat := 1407846367558497542053331

theorem tailTrace_2741771 : CollatzResearch.WordTrace tailWord_2741771 prefixEnd_2741771 1407846367558497542053331 := by
  unfold tailWord_2741771
  simp only [CollatzResearch.WordTrace]
  refine ⟨100000603750039399052049167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66667069166692932701366111 100000603750039399052049167)
  ·
    refine ⟨150000905625059098578073751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100000603750039399052049167 150000905625059098578073751)
    ·
      refine ⟨225001358437588647867110627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150000905625059098578073751 225001358437588647867110627)
      ·
        refine ⟨337502037656382971800665941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225001358437588647867110627 337502037656382971800665941)
        ·
          refine ⟨1977551001892868975394527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 337502037656382971800665941 1977551001892868975394527)
          ·
            refine ⟨2966326502839303463091791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977551001892868975394527 2966326502839303463091791)
            ·
              refine ⟨4449489754258955194637687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2966326502839303463091791 4449489754258955194637687)
              ·
                refine ⟨6674234631388432791956531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4449489754258955194637687 6674234631388432791956531)
                ·
                  refine ⟨10011351947082649187934797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6674234631388432791956531 10011351947082649187934797)
                  ·
                    refine ⟨3754256980155993445475549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10011351947082649187934797 3754256980155993445475549)
                    ·
                      refine ⟨1407846367558497542053331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3754256980155993445475549 1407846367558497542053331)
                      ·
                        rfl

theorem cell23_2741771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 3, 3].length) (baseStart_2741771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741771 prefixEnd_2741771 := by exact prefixLift 2741771
  have htrace : WordTrace (prefixWord ++ tailWord_2741771) baseStart_2741771 baseEnd_2741771 := by
    simpa [prefixWord, tailWord_2741771, baseEnd_2741771] using wordTrace_append hprefix tailTrace_2741771
  have hstable : (prefixWord ++ tailWord_2741771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741771).length < 2 ^ (prefixWord ++ tailWord_2741771).sum := by decide
  have hdescent : baseEnd_2741771 < baseStart_2741771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741781 : List Nat := [1, 3, 2, 1, 3, 3, 2, 2, 1, 3, 2]
def baseStart_2741781 : Nat := 118140960795 + 2741781 * 2 ^ 59
def prefixEnd_2741781 : Nat := 4983230072969 + 3 ^ 40 * 2741781 * 2
def baseEnd_2741781 : Nat := 1407851502365042502928285

theorem tailTrace_2741781 : CollatzResearch.WordTrace tailWord_2741781 prefixEnd_2741781 1407851502365042502928285 := by
  unfold tailWord_2741781
  simp only [CollatzResearch.WordTrace]
  refine ⟨100000968480003170759913197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66667312320002113839942131 100000968480003170759913197)
  ·
    refine ⟨37500363180001189034967449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100000968480003170759913197 37500363180001189034967449)
    ·
      refine ⟨28125272385000891776225587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37500363180001189034967449 28125272385000891776225587)
      ·
        refine ⟨42187908577501337664338381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28125272385000891776225587 42187908577501337664338381)
        ·
          refine ⟨15820465716563001624126893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42187908577501337664338381 15820465716563001624126893)
          ·
            refine ⟨5932674643711125609047585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15820465716563001624126893 5932674643711125609047585)
            ·
              refine ⟨4449505982783344206785689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5932674643711125609047585 4449505982783344206785689)
              ·
                refine ⟨3337129487087508155089267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4449505982783344206785689 3337129487087508155089267)
                ·
                  refine ⟨5005694230631262232633901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3337129487087508155089267 5005694230631262232633901)
                  ·
                    refine ⟨1877135336486723337237713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5005694230631262232633901 1877135336486723337237713)
                    ·
                      refine ⟨1407851502365042502928285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1877135336486723337237713 1407851502365042502928285)
                      ·
                        rfl

theorem cell23_2741781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_2741781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741781 prefixEnd_2741781 := by exact prefixLift 2741781
  have htrace : WordTrace (prefixWord ++ tailWord_2741781) baseStart_2741781 baseEnd_2741781 := by
    simpa [prefixWord, tailWord_2741781, baseEnd_2741781] using wordTrace_append hprefix tailTrace_2741781
  have hstable : (prefixWord ++ tailWord_2741781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741781).length < 2 ^ (prefixWord ++ tailWord_2741781).sum := by decide
  have hdescent : baseEnd_2741781 < baseStart_2741781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741794 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 1, 4, 2]
def baseStart_2741794 : Nat := 118140960795 + 2741794 * 2 ^ 59
def prefixEnd_2741794 : Nat := 4983230072969 + 3 ^ 40 * 2741794 * 2
def baseEnd_2741794 : Nat := 1407858177613550952065725

theorem tailTrace_2741794 : CollatzResearch.WordTrace tailWord_2741794 prefixEnd_2741794 1407858177613550952065725 := by
  unfold tailWord_2741794
  simp only [CollatzResearch.WordTrace]
  refine ⟨25000360657239018495034109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66667628419304049320090957 25000360657239018495034109)
  ·
    refine ⟨9375135246464631935637791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25000360657239018495034109 9375135246464631935637791)
    ·
      refine ⟨14062702869696947903456687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9375135246464631935637791 14062702869696947903456687)
      ·
        refine ⟨21094054304545421855185031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14062702869696947903456687 21094054304545421855185031)
        ·
          refine ⟨31641081456818132782777547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21094054304545421855185031 31641081456818132782777547)
          ·
            refine ⟨47461622185227199174166321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31641081456818132782777547 47461622185227199174166321)
            ·
              refine ⟨35596216638920399380624741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47461622185227199174166321 35596216638920399380624741)
              ·
                refine ⟨6674290619797574883867139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35596216638920399380624741 6674290619797574883867139)
                ·
                  refine ⟨10011435929696362325800709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6674290619797574883867139 10011435929696362325800709)
                  ·
                    refine ⟨1877144236818067936087633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10011435929696362325800709 1877144236818067936087633)
                    ·
                      refine ⟨1407858177613550952065725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1877144236818067936087633 1407858177613550952065725)
                      ·
                        rfl

theorem cell23_2741794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_2741794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741794 prefixEnd_2741794 := by exact prefixLift 2741794
  have htrace : WordTrace (prefixWord ++ tailWord_2741794) baseStart_2741794 baseEnd_2741794 := by
    simpa [prefixWord, tailWord_2741794, baseEnd_2741794] using wordTrace_append hprefix tailTrace_2741794
  have hstable : (prefixWord ++ tailWord_2741794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741794).length < 2 ^ (prefixWord ++ tailWord_2741794).sum := by decide
  have hdescent : baseEnd_2741794 < baseStart_2741794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741810 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_2741810 : Nat := 118140960795 + 2741810 * 2 ^ 59
def prefixEnd_2741810 : Nat := 4983230072969 + 3 ^ 40 * 2741810 * 2
def baseEnd_2741810 : Nat := 1407866393304022889465651

theorem tailTrace_2741810 : CollatzResearch.WordTrace tailWord_2741810 prefixEnd_2741810 1407866393304022889465651 := by
  unfold tailWord_2741810
  simp only [CollatzResearch.WordTrace]
  refine ⟨25000506549224527178179721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66668017464598739141812589 25000506549224527178179721)
  ·
    refine ⟨18750379911918395383634791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25000506549224527178179721 18750379911918395383634791)
    ·
      refine ⟨28125569867877593075452187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18750379911918395383634791 28125569867877593075452187)
      ·
        refine ⟨42188354801816389613178281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28125569867877593075452187 42188354801816389613178281)
        ·
          refine ⟨31641266101362292209883711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42188354801816389613178281 31641266101362292209883711)
          ·
            refine ⟨47461899152043438314825567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31641266101362292209883711 47461899152043438314825567)
            ·
              refine ⟨71192848728065157472238351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47461899152043438314825567 71192848728065157472238351)
              ·
                refine ⟨106789273092097736208357527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71192848728065157472238351 106789273092097736208357527)
                ·
                  refine ⟨160183909638146604312536291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106789273092097736208357527 160183909638146604312536291)
                  ·
                    refine ⟨240275864457219906468804437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 160183909638146604312536291 240275864457219906468804437)
                    ·
                      refine ⟨1407866393304022889465651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 240275864457219906468804437 1407866393304022889465651)
                      ·
                        rfl

theorem cell23_2741810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_2741810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741810 prefixEnd_2741810 := by exact prefixLift 2741810
  have htrace : WordTrace (prefixWord ++ tailWord_2741810) baseStart_2741810 baseEnd_2741810 := by
    simpa [prefixWord, tailWord_2741810, baseEnd_2741810] using wordTrace_append hprefix tailTrace_2741810
  have hstable : (prefixWord ++ tailWord_2741810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741810).length < 2 ^ (prefixWord ++ tailWord_2741810).sum := by decide
  have hdescent : baseEnd_2741810 < baseStart_2741810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741817 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 7]
def baseStart_2741817 : Nat := 118140960795 + 2741817 * 2 ^ 59
def prefixEnd_2741817 : Nat := 4983230072969 + 3 ^ 40 * 2741817 * 2
def baseEnd_2741817 : Nat := 156429998629844929119791

theorem tailTrace_2741817 : CollatzResearch.WordTrace tailWord_2741817 prefixEnd_2741817 156429998629844929119791 := by
  unfold tailWord_2741817
  simp only [CollatzResearch.WordTrace]
  refine ⟨100002281507872748908223705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66668187671915165938815803 100002281507872748908223705)
  ·
    refine ⟨75001711130904561681167779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100002281507872748908223705 75001711130904561681167779)
    ·
      refine ⟨112502566696356842521751669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75001711130904561681167779 112502566696356842521751669)
      ·
        refine ⟨10547115627783453986414219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112502566696356842521751669 10547115627783453986414219)
        ·
          refine ⟨15820673441675180979621329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10547115627783453986414219 15820673441675180979621329)
          ·
            refine ⟨11865505081256385734715997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15820673441675180979621329 11865505081256385734715997)
            ·
              refine ⟨4449564405471144650518499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11865505081256385734715997 4449564405471144650518499)
              ·
                refine ⟨6674346608206716975777749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4449564405471144650518499 6674346608206716975777749)
                ·
                  refine ⟨156429998629844929119791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6674346608206716975777749 156429998629844929119791)
                  ·
                    rfl

theorem cell23_2741817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 7].length) (baseStart_2741817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741817 prefixEnd_2741817 := by exact prefixLift 2741817
  have htrace : WordTrace (prefixWord ++ tailWord_2741817) baseStart_2741817 baseEnd_2741817 := by
    simpa [prefixWord, tailWord_2741817, baseEnd_2741817] using wordTrace_append hprefix tailTrace_2741817
  have hstable : (prefixWord ++ tailWord_2741817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741817).length < 2 ^ (prefixWord ++ tailWord_2741817).sum := by decide
  have hdescent : baseEnd_2741817 < baseStart_2741817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741840 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 7]
def baseStart_2741840 : Nat := 118140960795 + 2741840 * 2 ^ 59
def prefixEnd_2741840 : Nat := 4983230072969 + 3 ^ 40 * 2741840 * 2
def baseEnd_2741840 : Nat := 1407881797723657772090513

theorem tailTrace_2741840 : CollatzResearch.WordTrace tailWord_2741840 prefixEnd_2741840 1407881797723657772090513 := by
  unfold tailWord_2741840
  simp only [CollatzResearch.WordTrace]
  refine ⟨50001560193394711918155487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66668746924526282557540649 50001560193394711918155487)
  ·
    refine ⟨75002340290092067877233231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50001560193394711918155487 75002340290092067877233231)
    ·
      refine ⟨112503510435138101815849847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75002340290092067877233231 112503510435138101815849847)
      ·
        refine ⟨168755265652707152723774771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112503510435138101815849847 168755265652707152723774771)
        ·
          refine ⟨253132898479060729085662157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168755265652707152723774771 253132898479060729085662157)
          ·
            refine ⟨94924836929647773407123309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253132898479060729085662157 94924836929647773407123309)
            ·
              refine ⟨35596813848617915027671241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94924836929647773407123309 35596813848617915027671241)
              ·
                refine ⟨26697610386463436270753431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35596813848617915027671241 26697610386463436270753431)
                ·
                  refine ⟨40046415579695154406130147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26697610386463436270753431 40046415579695154406130147)
                  ·
                    refine ⟨60069623369542731609195221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40046415579695154406130147 60069623369542731609195221)
                    ·
                      refine ⟨1407881797723657772090513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60069623369542731609195221 1407881797723657772090513)
                      ·
                        rfl

theorem cell23_2741840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_2741840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741840 prefixEnd_2741840 := by exact prefixLift 2741840
  have htrace : WordTrace (prefixWord ++ tailWord_2741840) baseStart_2741840 baseEnd_2741840 := by
    simpa [prefixWord, tailWord_2741840, baseEnd_2741840] using wordTrace_append hprefix tailTrace_2741840
  have hstable : (prefixWord ++ tailWord_2741840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741840).length < 2 ^ (prefixWord ++ tailWord_2741840).sum := by decide
  have hdescent : baseEnd_2741840 < baseStart_2741840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741847 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 2, 5]
def baseStart_2741847 : Nat := 118140960795 + 2741847 * 2 ^ 59
def prefixEnd_2741847 : Nat := 4983230072969 + 3 ^ 40 * 2741847 * 2
def baseEnd_2741847 : Nat := 469295130696079748234327

theorem tailTrace_2741847 : CollatzResearch.WordTrace tailWord_2741847 prefixEnd_2741847 469295130696079748234327 := by
  unfold tailWord_2741847
  simp only [CollatzResearch.WordTrace]
  refine ⟨100003375697764064031815795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66668917131842709354543863 100003375697764064031815795)
  ·
    refine ⟨150005063546646096047723693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100003375697764064031815795 150005063546646096047723693)
    ·
      refine ⟨56251898829992286017896385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150005063546646096047723693 56251898829992286017896385)
      ·
        refine ⟨42188924122494214513422289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56251898829992286017896385 42188924122494214513422289)
        ·
          refine ⟨31641693091870660885066717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42188924122494214513422289 31641693091870660885066717)
          ·
            refine ⟨11865634909451497831900019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31641693091870660885066717 11865634909451497831900019)
            ·
              refine ⟨17798452364177246747850029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11865634909451497831900019 17798452364177246747850029)
              ·
                refine ⟨6674419636566467530443761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17798452364177246747850029 6674419636566467530443761)
                ·
                  refine ⟨5005814727424850647832821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6674419636566467530443761 5005814727424850647832821)
                  ·
                    refine ⟨469295130696079748234327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5005814727424850647832821 469295130696079748234327)
                    ·
                      rfl

theorem cell23_2741847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_2741847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741847 prefixEnd_2741847 := by exact prefixLift 2741847
  have htrace : WordTrace (prefixWord ++ tailWord_2741847) baseStart_2741847 baseEnd_2741847 := by
    simpa [prefixWord, tailWord_2741847, baseEnd_2741847] using wordTrace_append hprefix tailTrace_2741847
  have hstable : (prefixWord ++ tailWord_2741847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741847).length < 2 ^ (prefixWord ++ tailWord_2741847).sum := by decide
  have hdescent : baseEnd_2741847 < baseStart_2741847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741864 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 2, 5]
def baseStart_2741864 : Nat := 118140960795 + 2741864 * 2 ^ 59
def prefixEnd_2741864 : Nat := 4983230072969 + 3 ^ 40 * 2741864 * 2
def baseEnd_2741864 : Nat := 469298040419788559396801

theorem tailTrace_2741864 : CollatzResearch.WordTrace tailWord_2741864 prefixEnd_2741864 469298040419788559396801 := by
  unfold tailWord_2741864
  simp only [CollatzResearch.WordTrace]
  refine ⟨50001997869351237967592323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66669330492468317290123097 50001997869351237967592323)
  ·
    refine ⟨75002996804026856951388485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50001997869351237967592323 75002996804026856951388485)
    ·
      refine ⟨14063061900755035678385341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75002996804026856951388485 14063061900755035678385341)
      ·
        refine ⟨5273648212783138379394503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14063061900755035678385341 5273648212783138379394503)
        ·
          refine ⟨7910472319174707569091755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5273648212783138379394503 7910472319174707569091755)
          ·
            refine ⟨11865708478762061353637633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7910472319174707569091755 11865708478762061353637633)
            ·
              refine ⟨8899281359071546015228225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11865708478762061353637633 8899281359071546015228225)
              ·
                refine ⟨6674461019303659511421169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8899281359071546015228225 6674461019303659511421169)
                ·
                  refine ⟨5005845764477744633565877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6674461019303659511421169 5005845764477744633565877)
                  ·
                    refine ⟨469298040419788559396801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5005845764477744633565877 469298040419788559396801)
                    ·
                      rfl

theorem cell23_2741864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_2741864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741864 prefixEnd_2741864 := by exact prefixLift 2741864
  have htrace : WordTrace (prefixWord ++ tailWord_2741864) baseStart_2741864 baseEnd_2741864 := by
    simpa [prefixWord, tailWord_2741864, baseEnd_2741864] using wordTrace_append hprefix tailTrace_2741864
  have hstable : (prefixWord ++ tailWord_2741864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741864).length < 2 ^ (prefixWord ++ tailWord_2741864).sum := by decide
  have hdescent : baseEnd_2741864 < baseStart_2741864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741911 : List Nat := [1, 1, 3, 3, 2, 2, 1, 5, 1, 4]
def baseStart_2741911 : Nat := 118140960795 + 2741911 * 2 ^ 59
def prefixEnd_2741911 : Nat := 4983230072969 + 3 ^ 40 * 2741911 * 2
def baseEnd_2741911 : Nat := 469306084950042331434229

theorem tailTrace_2741911 : CollatzResearch.WordTrace tailWord_2741911 prefixEnd_2741911 469306084950042331434229 := by
  unfold tailWord_2741911
  simp only [CollatzResearch.WordTrace]
  refine ⟨100005709969532202962145587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66670473313021468641430391 100005709969532202962145587)
  ·
    refine ⟨150008564954298304443218381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100005709969532202962145587 150008564954298304443218381)
    ·
      refine ⟨56253211857861864166206893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150008564954298304443218381 56253211857861864166206893)
      ·
        refine ⟨21094954446698199062327585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56253211857861864166206893 21094954446698199062327585)
        ·
          refine ⟨15821215835023649296745689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21094954446698199062327585 15821215835023649296745689)
          ·
            refine ⟨11865911876267736972559267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15821215835023649296745689 11865911876267736972559267)
            ·
              refine ⟨17798867814401605458838901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11865911876267736972559267 17798867814401605458838901)
              ·
                refine ⟨1668643857600150511766147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17798867814401605458838901 1668643857600150511766147)
                ·
                  refine ⟨2502965786400225767649221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1668643857600150511766147 2502965786400225767649221)
                  ·
                    refine ⟨469306084950042331434229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2502965786400225767649221 469306084950042331434229)
                    ·
                      rfl

theorem cell23_2741911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 1, 4].length) (baseStart_2741911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741911 prefixEnd_2741911 := by exact prefixLift 2741911
  have htrace : WordTrace (prefixWord ++ tailWord_2741911) baseStart_2741911 baseEnd_2741911 := by
    simpa [prefixWord, tailWord_2741911, baseEnd_2741911] using wordTrace_append hprefix tailTrace_2741911
  have hstable : (prefixWord ++ tailWord_2741911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741911).length < 2 ^ (prefixWord ++ tailWord_2741911).sum := by decide
  have hdescent : baseEnd_2741911 < baseStart_2741911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741924 : List Nat := [2, 3, 1, 2, 2, 2, 3, 2, 6]
def baseStart_2741924 : Nat := 118140960795 + 2741924 * 2 ^ 59
def prefixEnd_2741924 : Nat := 4983230072969 + 3 ^ 40 * 2741924 * 2
def baseEnd_2741924 : Nat := 156436103344292827048903

theorem tailTrace_2741924 : CollatzResearch.WordTrace tailWord_2741924 prefixEnd_2741924 156436103344292827048903 := by
  unfold tailWord_2741924
  simp only [CollatzResearch.WordTrace]
  refine ⟨50003092059242553091184413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66670789412323404121579217 50003092059242553091184413)
  ·
    refine ⟨18751159522215957409194155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50003092059242553091184413 18751159522215957409194155)
    ·
      refine ⟨28126739283323936113791233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18751159522215957409194155 28126739283323936113791233)
      ·
        refine ⟨21095054462492952085343425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28126739283323936113791233 21095054462492952085343425)
        ·
          refine ⟨15821290846869714064007569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21095054462492952085343425 15821290846869714064007569)
          ·
            refine ⟨11865968135152285548005677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15821290846869714064007569 11865968135152285548005677)
            ·
              refine ⟨4449738050682107080502129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11865968135152285548005677 4449738050682107080502129)
              ·
                refine ⟨3337303538011580310376597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4449738050682107080502129 3337303538011580310376597)
                ·
                  refine ⟨156436103344292827048903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3337303538011580310376597 156436103344292827048903)
                  ·
                    rfl

theorem cell23_2741924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_2741924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741924 prefixEnd_2741924 := by exact prefixLift 2741924
  have htrace : WordTrace (prefixWord ++ tailWord_2741924) baseStart_2741924 baseEnd_2741924 := by
    simpa [prefixWord, tailWord_2741924, baseEnd_2741924] using wordTrace_append hprefix tailTrace_2741924
  have hstable : (prefixWord ++ tailWord_2741924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741924).length < 2 ^ (prefixWord ++ tailWord_2741924).sum := by decide
  have hdescent : baseEnd_2741924 < baseStart_2741924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741967 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 1, 6]
def baseStart_2741967 : Nat := 118140960795 + 2741967 * 2 ^ 59
def prefixEnd_2741967 : Nat := 4983230072969 + 3 ^ 40 * 2741967 * 2
def baseEnd_2741967 : Nat := 469315669922259591734143

theorem tailTrace_2741967 : CollatzResearch.WordTrace tailWord_2741967 prefixEnd_2741967 469315669922259591734143 := by
  unfold tailWord_2741967
  simp only [CollatzResearch.WordTrace]
  refine ⟨100007752457329324526184155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66671834971552883017456103 100007752457329324526184155)
  ·
    refine ⟨150011628685993986789276233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100007752457329324526184155 150011628685993986789276233)
    ·
      refine ⟨112508721514495490091957175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150011628685993986789276233 112508721514495490091957175)
      ·
        refine ⟨168763082271743235137935763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112508721514495490091957175 168763082271743235137935763)
        ·
          refine ⟨253144623407614852706903645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168763082271743235137935763 253144623407614852706903645)
          ·
            refine ⟨94929233777855569765088867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253144623407614852706903645 94929233777855569765088867)
            ·
              refine ⟨142393850666783354647633301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94929233777855569765088867 142393850666783354647633301)
              ·
                refine ⟨6674711750005469749107811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142393850666783354647633301 6674711750005469749107811)
                ·
                  refine ⟨10012067625008204623661717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6674711750005469749107811 10012067625008204623661717)
                  ·
                    refine ⟨469315669922259591734143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10012067625008204623661717 469315669922259591734143)
                    ·
                      rfl

theorem cell23_2741967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 6].length) (baseStart_2741967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741967 prefixEnd_2741967 := by exact prefixLift 2741967
  have htrace : WordTrace (prefixWord ++ tailWord_2741967) baseStart_2741967 baseEnd_2741967 := by
    simpa [prefixWord, tailWord_2741967, baseEnd_2741967] using wordTrace_append hprefix tailTrace_2741967
  have hstable : (prefixWord ++ tailWord_2741967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741967).length < 2 ^ (prefixWord ++ tailWord_2741967).sum := by decide
  have hdescent : baseEnd_2741967 < baseStart_2741967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741984 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 4, 4]
def baseStart_2741984 : Nat := 118140960795 + 2741984 * 2 ^ 59
def prefixEnd_2741984 : Nat := 4983230072969 + 3 ^ 40 * 2741984 * 2
def baseEnd_2741984 : Nat := 469318579645968402896617

theorem tailTrace_2741984 : CollatzResearch.WordTrace tailWord_2741984 prefixEnd_2741984 469318579645968402896617 := by
  unfold tailWord_2741984
  simp only [CollatzResearch.WordTrace]
  refine ⟨50004186249133868214776503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66672248332178490953035337 50004186249133868214776503)
  ·
    refine ⟨75006279373700802322164755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50004186249133868214776503 75006279373700802322164755)
    ·
      refine ⟨112509419060551203483247133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75006279373700802322164755 112509419060551203483247133)
      ·
        refine ⟨42191032147706701306217675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112509419060551203483247133 42191032147706701306217675)
        ·
          refine ⟨63286548221560051959326513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42191032147706701306217675 63286548221560051959326513)
          ·
            refine ⟨47464911166170038969494885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63286548221560051959326513 47464911166170038969494885)
            ·
              refine ⟨8899670843656882306780291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47464911166170038969494885 8899670843656882306780291)
              ·
                refine ⟨13349506265485323460170437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8899670843656882306780291 13349506265485323460170437)
                ·
                  refine ⟨2503032424778498148781957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13349506265485323460170437 2503032424778498148781957)
                  ·
                    refine ⟨469318579645968402896617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2503032424778498148781957 469318579645968402896617)
                    ·
                      rfl

theorem cell23_2741984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 4, 4].length) (baseStart_2741984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741984 prefixEnd_2741984 := by exact prefixLift 2741984
  have htrace : WordTrace (prefixWord ++ tailWord_2741984) baseStart_2741984 baseEnd_2741984 := by
    simpa [prefixWord, tailWord_2741984, baseEnd_2741984] using wordTrace_append hprefix tailTrace_2741984
  have hstable : (prefixWord ++ tailWord_2741984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741984).length < 2 ^ (prefixWord ++ tailWord_2741984).sum := by decide
  have hdescent : baseEnd_2741984 < baseStart_2741984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741985 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 3, 1, 3]
def baseStart_2741985 : Nat := 118140960795 + 2741985 * 2 ^ 59
def prefixEnd_2741985 : Nat := 4983230072969 + 3 ^ 40 * 2741985 * 2
def baseEnd_2741985 : Nat := 1407956252418559704777347

theorem tailTrace_2741985 : CollatzResearch.WordTrace tailWord_2741985 prefixEnd_2741985 1407956252418559704777347 := by
  unfold tailWord_2741985
  simp only [CollatzResearch.WordTrace]
  refine ⟨100008408971264113600339409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66672272647509409066892939 100008408971264113600339409)
  ·
    refine ⟨75006306728448085200254557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100008408971264113600339409 75006306728448085200254557)
    ·
      refine ⟨28127365023168031950095459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75006306728448085200254557 28127365023168031950095459)
      ·
        refine ⟨42191047534752047925143189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28127365023168031950095459 42191047534752047925143189)
        ·
          refine ⟨1977705353191502246491087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42191047534752047925143189 1977705353191502246491087)
          ·
            refine ⟨2966558029787253369736631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977705353191502246491087 2966558029787253369736631)
            ·
              refine ⟨4449837044680880054604947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2966558029787253369736631 4449837044680880054604947)
              ·
                refine ⟨6674755567021320081907421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4449837044680880054604947 6674755567021320081907421)
                ·
                  refine ⟨2503033337632995030715283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6674755567021320081907421 2503033337632995030715283)
                  ·
                    refine ⟨3754550006449492546072925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2503033337632995030715283 3754550006449492546072925)
                    ·
                      refine ⟨1407956252418559704777347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3754550006449492546072925 1407956252418559704777347)
                      ·
                        rfl

theorem cell23_2741985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_2741985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741985 prefixEnd_2741985 := by exact prefixLift 2741985
  have htrace : WordTrace (prefixWord ++ tailWord_2741985) baseStart_2741985 baseEnd_2741985 := by
    simpa [prefixWord, tailWord_2741985, baseEnd_2741985] using wordTrace_append hprefix tailTrace_2741985
  have hstable : (prefixWord ++ tailWord_2741985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741985).length < 2 ^ (prefixWord ++ tailWord_2741985).sum := by decide
  have hdescent : baseEnd_2741985 < baseStart_2741985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741994 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_2741994 : Nat := 118140960795 + 2741994 * 2 ^ 59
def prefixEnd_2741994 : Nat := 4983230072969 + 3 ^ 40 * 2741994 * 2
def baseEnd_2741994 : Nat := 1407960873744450169564805

theorem tailTrace_2741994 : CollatzResearch.WordTrace tailWord_2741994 prefixEnd_2741994 1407960873744450169564805 := by
  unfold tailWord_2741994
  simp only [CollatzResearch.WordTrace]
  refine ⟨25002184307057877034354259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66672491485487672091611357 25002184307057877034354259)
  ·
    refine ⟨37503276460586815551531389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25002184307057877034354259 37503276460586815551531389)
    ·
      refine ⟨14063728672720055831824271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37503276460586815551531389 14063728672720055831824271)
      ·
        refine ⟨21095593009080083747736407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14063728672720055831824271 21095593009080083747736407)
        ·
          refine ⟨31643389513620125621604611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21095593009080083747736407 31643389513620125621604611)
          ·
            refine ⟨47465084270430188432406917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31643389513620125621604611 47465084270430188432406917)
            ·
              refine ⟨8899703300705660331076297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47465084270430188432406917 8899703300705660331076297)
              ·
                refine ⟨6674777475529245248307223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8899703300705660331076297 6674777475529245248307223)
                ·
                  refine ⟨10012166213293867872460835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6674777475529245248307223 10012166213293867872460835)
                  ·
                    refine ⟨15018249319940801808691253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10012166213293867872460835 15018249319940801808691253)
                    ·
                      refine ⟨1407960873744450169564805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15018249319940801808691253 1407960873744450169564805)
                      ·
                        rfl

theorem cell23_2741994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_2741994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741994 prefixEnd_2741994 := by exact prefixLift 2741994
  have htrace : WordTrace (prefixWord ++ tailWord_2741994) baseStart_2741994 baseEnd_2741994 := by
    simpa [prefixWord, tailWord_2741994, baseEnd_2741994] using wordTrace_append hprefix tailTrace_2741994
  have hstable : (prefixWord ++ tailWord_2741994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741994).length < 2 ^ (prefixWord ++ tailWord_2741994).sum := by decide
  have hdescent : baseEnd_2741994 < baseStart_2741994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742001 : List Nat := [1, 2, 2, 2, 2, 4, 1, 3, 2, 4]
def baseStart_2742001 : Nat := 118140960795 + 2742001 * 2 ^ 59
def prefixEnd_2742001 : Nat := 4983230072969 + 3 ^ 40 * 2742001 * 2
def baseEnd_2742001 : Nat := 469321489369677214059091

theorem tailTrace_2742001 : CollatzResearch.WordTrace tailWord_2742001 prefixEnd_2742001 469321489369677214059091 := by
  unfold tailWord_2742001
  simp only [CollatzResearch.WordTrace]
  refine ⟨100008992539206148332921857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66672661692804098888614571 100008992539206148332921857)
  ·
    refine ⟨75006744404404611249691393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100008992539206148332921857 75006744404404611249691393)
    ·
      refine ⟨56255058303303458437268545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75006744404404611249691393 56255058303303458437268545)
      ·
        refine ⟨42191293727477593827951409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56255058303303458437268545 42191293727477593827951409)
        ·
          refine ⟨31643470295608195370963557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42191293727477593827951409 31643470295608195370963557)
          ·
            refine ⟨5933150680426536632055667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31643470295608195370963557 5933150680426536632055667)
            ·
              refine ⟨8899726020639804948083501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5933150680426536632055667 8899726020639804948083501)
              ·
                refine ⟨3337397257739926855531313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8899726020639804948083501 3337397257739926855531313)
                ·
                  refine ⟨2503047943304945141648485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3337397257739926855531313 2503047943304945141648485)
                  ·
                    refine ⟨469321489369677214059091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2503047943304945141648485 469321489369677214059091)
                    ·
                      rfl

theorem cell23_2742001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_2742001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742001 prefixEnd_2742001 := by exact prefixLift 2742001
  have htrace : WordTrace (prefixWord ++ tailWord_2742001) baseStart_2742001 baseEnd_2742001 := by
    simpa [prefixWord, tailWord_2742001, baseEnd_2742001] using wordTrace_append hprefix tailTrace_2742001
  have hstable : (prefixWord ++ tailWord_2742001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742001).length < 2 ^ (prefixWord ++ tailWord_2742001).sum := by decide
  have hdescent : baseEnd_2742001 < baseStart_2742001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742042 : List Nat := [3, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2]
def baseStart_2742042 : Nat := 118140960795 + 2742042 * 2 ^ 59
def prefixEnd_2742042 : Nat := 4983230072969 + 3 ^ 40 * 2742042 * 2
def baseEnd_2742042 : Nat := 1407985520815865981764585

theorem tailTrace_2742042 : CollatzResearch.WordTrace tailWord_2742042 prefixEnd_2742042 1407985520815865981764585 := by
  unfold tailWord_2742042
  simp only [CollatzResearch.WordTrace]
  refine ⟨25002621983014403083791095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66673658621371741556776253 25002621983014403083791095)
  ·
    refine ⟨37503932974521604625686643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25002621983014403083791095 37503932974521604625686643)
    ·
      refine ⟨56255899461782406938529965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37503932974521604625686643 56255899461782406938529965)
      ·
        refine ⟨21095962298168402601948737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56255899461782406938529965 21095962298168402601948737)
        ·
          refine ⟨15821971723626301951461553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21095962298168402601948737 15821971723626301951461553)
          ·
            refine ⟨11866478792719726463596165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15821971723626301951461553 11866478792719726463596165)
            ·
              refine ⟨2224964773634948711924281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11866478792719726463596165 2224964773634948711924281)
              ·
                refine ⟨1668723580226211533943211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2224964773634948711924281 1668723580226211533943211)
                ·
                  refine ⟨2503085370339317300914817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1668723580226211533943211 2503085370339317300914817)
                  ·
                    refine ⟨1877314027754487975686113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2503085370339317300914817 1877314027754487975686113)
                    ·
                      refine ⟨1407985520815865981764585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1877314027754487975686113 1407985520815865981764585)
                      ·
                        rfl

theorem cell23_2742042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_2742042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742042 prefixEnd_2742042 := by exact prefixLift 2742042
  have htrace : WordTrace (prefixWord ++ tailWord_2742042) baseStart_2742042 baseEnd_2742042 := by
    simpa [prefixWord, tailWord_2742042, baseEnd_2742042] using wordTrace_append hprefix tailTrace_2742042
  have hstable : (prefixWord ++ tailWord_2742042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742042).length < 2 ^ (prefixWord ++ tailWord_2742042).sum := by decide
  have hdescent : baseEnd_2742042 < baseStart_2742042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742051 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 3, 3, 2]
def baseStart_2742051 : Nat := 118140960795 + 2742051 * 2 ^ 59
def prefixEnd_2742051 : Nat := 4983230072969 + 3 ^ 40 * 2742051 * 2
def baseEnd_2742051 : Nat := 1407990142141756446552043

theorem tailTrace_2742051 : CollatzResearch.WordTrace tailWord_2742051 prefixEnd_2742051 1407990142141756446552043 := by
  unfold tailWord_2742051
  simp only [CollatzResearch.WordTrace]
  refine ⟨100010816189025006872242007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66673877459350004581494671 100010816189025006872242007)
  ·
    refine ⟨150016224283537510308363011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100010816189025006872242007 150016224283537510308363011)
    ·
      refine ⟨225024336425306265462544517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150016224283537510308363011 225024336425306265462544517)
      ·
        refine ⟨42192063079744924774227097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225024336425306265462544517 42192063079744924774227097)
        ·
          refine ⟨31644047309808693580670323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42192063079744924774227097 31644047309808693580670323)
          ·
            refine ⟨47466070964713040371005485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31644047309808693580670323 47466070964713040371005485)
            ·
              refine ⟨17799776611767390139127057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47466070964713040371005485 17799776611767390139127057)
              ·
                refine ⟨13349832458825542604345293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17799776611767390139127057 13349832458825542604345293)
                ·
                  refine ⟨5006187172059578476629485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13349832458825542604345293 5006187172059578476629485)
                  ·
                    refine ⟨1877320189522341928736057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5006187172059578476629485 1877320189522341928736057)
                    ·
                      refine ⟨1407990142141756446552043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1877320189522341928736057 1407990142141756446552043)
                      ·
                        rfl

theorem cell23_2742051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_2742051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742051 prefixEnd_2742051 := by exact prefixLift 2742051
  have htrace : WordTrace (prefixWord ++ tailWord_2742051) baseStart_2742051 baseEnd_2742051 := by
    simpa [prefixWord, tailWord_2742051, baseEnd_2742051] using wordTrace_append hprefix tailTrace_2742051
  have hstable : (prefixWord ++ tailWord_2742051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742051).length < 2 ^ (prefixWord ++ tailWord_2742051).sum := by decide
  have hdescent : baseEnd_2742051 < baseStart_2742051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742092 : List Nat := [2, 2, 1, 3, 5, 1, 1, 2, 2, 1, 3]
def baseStart_2742092 : Nat := 118140960795 + 2742092 * 2 ^ 59
def prefixEnd_2742092 : Nat := 4983230072969 + 3 ^ 40 * 2742092 * 2
def baseEnd_2742092 : Nat := 1408011194848590786139355

theorem tailTrace_2742092 : CollatzResearch.WordTrace tailWord_2742092 prefixEnd_2742092 1408011194848590786139355 := by
  unfold tailWord_2742092
  simp only [CollatzResearch.WordTrace]
  refine ⟨50006155790938235437242265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66674874387917647249656353 50006155790938235437242265)
  ·
    refine ⟨37504616843203676577931699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50006155790938235437242265 37504616843203676577931699)
    ·
      refine ⟨56256925264805514866897549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37504616843203676577931699 56256925264805514866897549)
      ·
        refine ⟨21096346974302068075086581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56256925264805514866897549 21096346974302068075086581)
        ·
          refine ⟨1977782528840818882039367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21096346974302068075086581 1977782528840818882039367)
          ·
            refine ⟨2966673793261228323059051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977782528840818882039367 2966673793261228323059051)
            ·
              refine ⟨4450010689891842484588577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2966673793261228323059051 4450010689891842484588577)
              ·
                refine ⟨3337508017418881863441433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4450010689891842484588577 3337508017418881863441433)
                ·
                  refine ⟨2503131013064161397581075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3337508017418881863441433 2503131013064161397581075)
                  ·
                    refine ⟨3754696519596242096371613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2503131013064161397581075 3754696519596242096371613)
                    ·
                      refine ⟨1408011194848590786139355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3754696519596242096371613 1408011194848590786139355)
                      ·
                        rfl

theorem cell23_2742092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_2742092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742092 prefixEnd_2742092 := by exact prefixLift 2742092
  have htrace : WordTrace (prefixWord ++ tailWord_2742092) baseStart_2742092 baseEnd_2742092 := by
    simpa [prefixWord, tailWord_2742092, baseEnd_2742092] using wordTrace_append hprefix tailTrace_2742092
  have hstable : (prefixWord ++ tailWord_2742092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742092).length < 2 ^ (prefixWord ++ tailWord_2742092).sum := by decide
  have hdescent : baseEnd_2742092 < baseStart_2742092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742115 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 1, 4, 2]
def baseStart_2742115 : Nat := 118140960795 + 2742115 * 2 ^ 59
def prefixEnd_2742115 : Nat := 4983230072969 + 3 ^ 40 * 2742115 * 2
def baseEnd_2742115 : Nat := 1408023004903644196151749

theorem tailTrace_2742115 : CollatzResearch.WordTrace tailWord_2742115 prefixEnd_2742115 1408023004903644196151749 := by
  unfold tailWord_2742115
  simp only [CollatzResearch.WordTrace]
  refine ⟨100013150460793145802571799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66675433640528763868381199 100013150460793145802571799)
  ·
    refine ⟨150019725691189718703857699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100013150460793145802571799 150019725691189718703857699)
    ·
      refine ⟨225029588536784578055786549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150019725691189718703857699 225029588536784578055786549)
      ·
        refine ⟨21096523925323554192729989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 225029588536784578055786549 21096523925323554192729989)
        ·
          refine ⟨3955598235998166411136873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21096523925323554192729989 3955598235998166411136873)
          ·
            refine ⟨2966698676998624808352655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3955598235998166411136873 2966698676998624808352655)
            ·
              refine ⟨4450048015497937212528983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2966698676998624808352655 4450048015497937212528983)
              ·
                refine ⟨6675072023246905818793475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4450048015497937212528983 6675072023246905818793475)
                ·
                  refine ⟨10012608034870358728190213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6675072023246905818793475 10012608034870358728190213)
                  ·
                    refine ⟨1877364006538192261535665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10012608034870358728190213 1877364006538192261535665)
                    ·
                      refine ⟨1408023004903644196151749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1877364006538192261535665 1408023004903644196151749)
                      ·
                        rfl

theorem cell23_2742115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_2742115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742115 prefixEnd_2742115 := by exact prefixLift 2742115
  have htrace : WordTrace (prefixWord ++ tailWord_2742115) baseStart_2742115 baseEnd_2742115 := by
    simpa [prefixWord, tailWord_2742115, baseEnd_2742115] using wordTrace_append hprefix tailTrace_2742115
  have hstable : (prefixWord ++ tailWord_2742115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742115).length < 2 ^ (prefixWord ++ tailWord_2742115).sum := by decide
  have hdescent : baseEnd_2742115 < baseStart_2742115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742141 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 1, 7, 2]
def baseStart_2742141 : Nat := 118140960795 + 2742141 * 2 ^ 59
def prefixEnd_2742141 : Nat := 4983230072969 + 3 ^ 40 * 2742141 * 2
def baseEnd_2742141 : Nat := 1408036355400661094426629

theorem tailTrace_2742141 : CollatzResearch.WordTrace tailWord_2742141 prefixEnd_2742141 1408036355400661094426629 := by
  unfold tailWord_2742141
  simp only [CollatzResearch.WordTrace]
  refine ⟨100014098758698952243018277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66676065839132634828678851 100014098758698952243018277)
  ·
    refine ⟨18752643517256053545565927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100014098758698952243018277 18752643517256053545565927)
    ·
      refine ⟨28128965275884080318348891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18752643517256053545565927 28128965275884080318348891)
      ·
        refine ⟨42193447913826120477523337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28128965275884080318348891 42193447913826120477523337)
        ·
          refine ⟨31645085935369590358142503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42193447913826120477523337 31645085935369590358142503)
          ·
            refine ⟨47467628903054385537213755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31645085935369590358142503 47467628903054385537213755)
            ·
              refine ⟨71201443354581578305820633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47467628903054385537213755 71201443354581578305820633)
              ·
                refine ⟨53401082515936183729365475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71201443354581578305820633 53401082515936183729365475)
                ·
                  refine ⟨80101623773904275594048213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53401082515936183729365475 80101623773904275594048213)
                  ·
                    refine ⟨1877381807200881459235505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 80101623773904275594048213 1877381807200881459235505)
                    ·
                      refine ⟨1408036355400661094426629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1877381807200881459235505 1408036355400661094426629)
                      ·
                        rfl

theorem cell23_2742141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_2742141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742141 prefixEnd_2742141 := by exact prefixLift 2742141
  have htrace : WordTrace (prefixWord ++ tailWord_2742141) baseStart_2742141 baseEnd_2742141 := by
    simpa [prefixWord, tailWord_2742141, baseEnd_2742141] using wordTrace_append hprefix tailTrace_2742141
  have hstable : (prefixWord ++ tailWord_2742141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742141).length < 2 ^ (prefixWord ++ tailWord_2742141).sum := by decide
  have hdescent : baseEnd_2742141 < baseStart_2742141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742144 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 5]
def baseStart_2742144 : Nat := 118140960795 + 2742144 * 2 ^ 59
def prefixEnd_2742144 : Nat := 4983230072969 + 3 ^ 40 * 2742144 * 2
def baseEnd_2742144 : Nat := 1408037895842624582689115

theorem tailTrace_2742144 : CollatzResearch.WordTrace tailWord_2742144 prefixEnd_2742144 1408037895842624582689115 := by
  unfold tailWord_2742144
  simp only [CollatzResearch.WordTrace]
  refine ⟨50007104088844041877688743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66676138785125389170251657 50007104088844041877688743)
  ·
    refine ⟨75010656133266062816533115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50007104088844041877688743 75010656133266062816533115)
    ·
      refine ⟨112515984199899094224799673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75010656133266062816533115 112515984199899094224799673)
      ·
        refine ⟨84386988149924320668599755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112515984199899094224799673 84386988149924320668599755)
        ·
          refine ⟨126580482224886481002899633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84386988149924320668599755 126580482224886481002899633)
          ·
            refine ⟨94935361668664860752174725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126580482224886481002899633 94935361668664860752174725)
            ·
              refine ⟨17800380312874661391032761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94935361668664860752174725 17800380312874661391032761)
              ·
                refine ⟨13350285234655996043274571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17800380312874661391032761 13350285234655996043274571)
                ·
                  refine ⟨20025427851983994064911857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13350285234655996043274571 20025427851983994064911857)
                  ·
                    refine ⟨15019070888987995548683893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20025427851983994064911857 15019070888987995548683893)
                    ·
                      refine ⟨1408037895842624582689115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15019070888987995548683893 1408037895842624582689115)
                      ·
                        rfl

theorem cell23_2742144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_2742144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742144 prefixEnd_2742144 := by exact prefixLift 2742144
  have htrace : WordTrace (prefixWord ++ tailWord_2742144) baseStart_2742144 baseEnd_2742144 := by
    simpa [prefixWord, tailWord_2742144, baseEnd_2742144] using wordTrace_append hprefix tailTrace_2742144
  have hstable : (prefixWord ++ tailWord_2742144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742144).length < 2 ^ (prefixWord ++ tailWord_2742144).sum := by decide
  have hdescent : baseEnd_2742144 < baseStart_2742144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742166 : List Nat := [5, 3, 1, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_2742166 : Nat := 118140960795 + 2742166 * 2 ^ 59
def prefixEnd_2742166 : Nat := 4983230072969 + 3 ^ 40 * 2742166 * 2
def baseEnd_2742166 : Nat := 1408049192417023496614015

theorem tailTrace_2742166 : CollatzResearch.WordTrace tailWord_2742166 prefixEnd_2742166 1408049192417023496614015 := by
  unfold tailWord_2742166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6250938161475523844542397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66676673722405587675118901 6250938161475523844542397)
  ·
    refine ⟨2344101810553321441703399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6250938161475523844542397 2344101810553321441703399)
    ·
      refine ⟨3516152715829982162555099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2344101810553321441703399 3516152715829982162555099)
      ·
        refine ⟨5274229073744973243832649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3516152715829982162555099 5274229073744973243832649)
        ·
          refine ⟨3955671805308729932874487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5274229073744973243832649 3955671805308729932874487)
          ·
            refine ⟨5933507707963094899311731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3955671805308729932874487 5933507707963094899311731)
            ·
              refine ⟨8900261561944642348967597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5933507707963094899311731 8900261561944642348967597)
              ·
                refine ⟨3337598085729240880862849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8900261561944642348967597 3337598085729240880862849)
                ·
                  refine ⟨2503198564296930660647137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3337598085729240880862849 2503198564296930660647137)
                  ·
                    refine ⟨1877398923222697995485353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2503198564296930660647137 1877398923222697995485353)
                    ·
                      refine ⟨1408049192417023496614015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1877398923222697995485353 1408049192417023496614015)
                      ·
                        rfl

theorem cell23_2742166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_2742166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742166 prefixEnd_2742166 := by exact prefixLift 2742166
  have htrace : WordTrace (prefixWord ++ tailWord_2742166) baseStart_2742166 baseEnd_2742166 := by
    simpa [prefixWord, tailWord_2742166, baseEnd_2742166] using wordTrace_append hprefix tailTrace_2742166
  have hstable : (prefixWord ++ tailWord_2742166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742166).length < 2 ^ (prefixWord ++ tailWord_2742166).sum := by decide
  have hdescent : baseEnd_2742166 < baseStart_2742166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742181 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 3, 4]
def baseStart_2742181 : Nat := 118140960795 + 2742181 * 2 ^ 59
def prefixEnd_2742181 : Nat := 4983230072969 + 3 ^ 40 * 2742181 * 2
def baseEnd_2742181 : Nat := 469352298208946979308815

theorem tailTrace_2742181 : CollatzResearch.WordTrace tailWord_2742181 prefixEnd_2742181 469352298208946979308815 := by
  unfold tailWord_2742181
  simp only [CollatzResearch.WordTrace]
  refine ⟨100015557678554039074474397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66677038452369359382982931 100015557678554039074474397)
  ·
    refine ⟨37505834129457764652927899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100015557678554039074474397 37505834129457764652927899)
    ·
      refine ⟨56258751194186646979391849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37505834129457764652927899 56258751194186646979391849)
      ·
        refine ⟨42194063395639985234543887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56258751194186646979391849 42194063395639985234543887)
        ·
          refine ⟨63291095093459977851815831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42194063395639985234543887 63291095093459977851815831)
          ·
            refine ⟨94936642640189966777723747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63291095093459977851815831 94936642640189966777723747)
            ·
              refine ⟨142404963960284950166585621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94936642640189966777723747 142404963960284950166585621)
              ·
                refine ⟨6675232685638357039058701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142404963960284950166585621 6675232685638357039058701)
                ·
                  refine ⟨2503212257114383889647013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6675232685638357039058701 2503212257114383889647013)
                  ·
                    refine ⟨469352298208946979308815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2503212257114383889647013 469352298208946979308815)
                    ·
                      rfl

theorem cell23_2742181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_2742181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742181 prefixEnd_2742181 := by exact prefixLift 2742181
  have htrace : WordTrace (prefixWord ++ tailWord_2742181) baseStart_2742181 baseEnd_2742181 := by
    simpa [prefixWord, tailWord_2742181, baseEnd_2742181] using wordTrace_append hprefix tailTrace_2742181
  have hstable : (prefixWord ++ tailWord_2742181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742181).length < 2 ^ (prefixWord ++ tailWord_2742181).sum := by decide
  have hdescent : baseEnd_2742181 < baseStart_2742181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742194 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 10]
def baseStart_2742194 : Nat := 118140960795 + 2742194 * 2 ^ 59
def prefixEnd_2742194 : Nat := 4983230072969 + 3 ^ 40 * 2742194 * 2
def baseEnd_2742194 : Nat := 156451507763927709673765

theorem tailTrace_2742194 : CollatzResearch.WordTrace tailWord_2742194 prefixEnd_2742194 156451507763927709673765 := by
  unfold tailWord_2742194
  simp only [CollatzResearch.WordTrace]
  refine ⟨25004007956876735573674409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66677354551671294863131757 25004007956876735573674409)
  ·
    refine ⟨18753005967657551680255807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25004007956876735573674409 18753005967657551680255807)
    ·
      refine ⟨28129508951486327520383711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18753005967657551680255807 28129508951486327520383711)
      ·
        refine ⟨42194263427229491280575567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28129508951486327520383711 42194263427229491280575567)
        ·
          refine ⟨63291395140844236920863351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42194263427229491280575567 63291395140844236920863351)
          ·
            refine ⟨94937092711266355381295027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63291395140844236920863351 94937092711266355381295027)
            ·
              refine ⟨142405639066899533071942541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94937092711266355381295027 142405639066899533071942541)
              ·
                refine ⟨53402114650087324901978453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142405639066899533071942541 53402114650087324901978453)
                ·
                  refine ⟨156451507763927709673765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 53402114650087324901978453 156451507763927709673765)
                  ·
                    rfl

theorem cell23_2742194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_2742194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742194 prefixEnd_2742194 := by exact prefixLift 2742194
  have htrace : WordTrace (prefixWord ++ tailWord_2742194) baseStart_2742194 baseEnd_2742194 := by
    simpa [prefixWord, tailWord_2742194, baseEnd_2742194] using wordTrace_append hprefix tailTrace_2742194
  have hstable : (prefixWord ++ tailWord_2742194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742194).length < 2 ^ (prefixWord ++ tailWord_2742194).sum := by decide
  have hdescent : baseEnd_2742194 < baseStart_2742194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742241 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 3, 5]
def baseStart_2742241 : Nat := 118140960795 + 2742241 * 2 ^ 59
def prefixEnd_2742241 : Nat := 4983230072969 + 3 ^ 40 * 2742241 * 2
def baseEnd_2742241 : Nat := 469362567822036901058723

theorem tailTrace_2742241 : CollatzResearch.WordTrace tailWord_2742241 prefixEnd_2742241 469362567822036901058723 := by
  unfold tailWord_2742241
  simp only [CollatzResearch.WordTrace]
  refine ⟨100017746058336669321658577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66678497372224446214439051 100017746058336669321658577)
  ·
    refine ⟨75013309543752501991243933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100017746058336669321658577 75013309543752501991243933)
    ·
      refine ⟨28129991078907188246716475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75013309543752501991243933 28129991078907188246716475)
      ·
        refine ⟨42194986618360782370074713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28129991078907188246716475 42194986618360782370074713)
        ·
          refine ⟨31646239963770586777556035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42194986618360782370074713 31646239963770586777556035)
          ·
            refine ⟨47469359945655880166334053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31646239963770586777556035 47469359945655880166334053)
            ·
              refine ⟨8900504989810477531187635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47469359945655880166334053 8900504989810477531187635)
              ·
                refine ⟨13350757484715716296781453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8900504989810477531187635 13350757484715716296781453)
                ·
                  refine ⟨5006534056768393611293045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13350757484715716296781453 5006534056768393611293045)
                  ·
                    refine ⟨469362567822036901058723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5006534056768393611293045 469362567822036901058723)
                    ·
                      rfl

theorem cell23_2742241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_2742241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742241 prefixEnd_2742241 := by exact prefixLift 2742241
  have htrace : WordTrace (prefixWord ++ tailWord_2742241) baseStart_2742241 baseEnd_2742241 := by
    simpa [prefixWord, tailWord_2742241, baseEnd_2742241] using wordTrace_append hprefix tailTrace_2742241
  have hstable : (prefixWord ++ tailWord_2742241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742241).length < 2 ^ (prefixWord ++ tailWord_2742241).sum := by decide
  have hdescent : baseEnd_2742241 < baseStart_2742241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742262 : List Nat := [5, 1, 1, 1, 5, 1, 1, 2, 6]
def baseStart_2742262 : Nat := 118140960795 + 2742262 * 2 ^ 59
def prefixEnd_2742262 : Nat := 4983230072969 + 3 ^ 40 * 2742262 * 2
def baseEnd_2742262 : Nat := 156455387395539457890397

theorem tailTrace_2742262 : CollatzResearch.WordTrace tailWord_2742262 prefixEnd_2742262 156455387395539457890397 := by
  unfold tailWord_2742262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6251156999453786869260815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66679007994173726605448693 6251156999453786869260815)
  ·
    refine ⟨9376735499180680303891223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6251156999453786869260815 9376735499180680303891223)
    ·
      refine ⟨14065103248771020455836835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9376735499180680303891223 14065103248771020455836835)
      ·
        refine ⟨21097654873156530683755253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14065103248771020455836835 21097654873156530683755253)
        ·
          refine ⟨1977905144358424751602055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21097654873156530683755253 1977905144358424751602055)
          ·
            refine ⟨2966857716537637127403083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977905144358424751602055 2966857716537637127403083)
            ·
              refine ⟨4450286574806455691104625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2966857716537637127403083 4450286574806455691104625)
              ·
                refine ⟨3337714931104841768328469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4450286574806455691104625 3337714931104841768328469)
                ·
                  refine ⟨156455387395539457890397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3337714931104841768328469 156455387395539457890397)
                  ·
                    rfl

theorem cell23_2742262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_2742262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742262 prefixEnd_2742262 := by exact prefixLift 2742262
  have htrace : WordTrace (prefixWord ++ tailWord_2742262) baseStart_2742262 baseEnd_2742262 := by
    simpa [prefixWord, tailWord_2742262, baseEnd_2742262] using wordTrace_append hprefix tailTrace_2742262
  have hstable : (prefixWord ++ tailWord_2742262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742262).length < 2 ^ (prefixWord ++ tailWord_2742262).sum := by decide
  have hdescent : baseEnd_2742262 < baseStart_2742262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742318 : List Nat := [4, 1, 3, 1, 1, 4, 9]
def baseStart_2742318 : Nat := 118140960795 + 2742318 * 2 ^ 59
def prefixEnd_2742318 : Nat := 4983230072969 + 3 ^ 40 * 2742318 * 2
def baseEnd_2742318 : Nat := 17384286931808727184115

theorem tailTrace_2742318 : CollatzResearch.WordTrace tailWord_2742318 prefixEnd_2742318 17384286931808727184115 := by
  unfold tailWord_2742318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12502569309882213934026451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66680369652705140981474405 12502569309882213934026451)
  ·
    refine ⟨18753853964823320901039677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12502569309882213934026451 18753853964823320901039677)
    ·
      refine ⟨7032695236808745337889879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18753853964823320901039677 7032695236808745337889879)
      ·
        refine ⟨10549042855213118006834819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7032695236808745337889879 10549042855213118006834819)
        ·
          refine ⟨15823564282819677010252229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10549042855213118006834819 15823564282819677010252229)
          ·
            refine ⟨2966918303028689439422293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15823564282819677010252229 2966918303028689439422293)
            ·
              refine ⟨17384286931808727184115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2966918303028689439422293 17384286931808727184115)
              ·
                rfl

theorem cell23_2742318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 9].length) (baseStart_2742318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742318 prefixEnd_2742318 := by exact prefixLift 2742318
  have htrace : WordTrace (prefixWord ++ tailWord_2742318) baseStart_2742318 baseEnd_2742318 := by
    simpa [prefixWord, tailWord_2742318, baseEnd_2742318] using wordTrace_append hprefix tailTrace_2742318
  have hstable : (prefixWord ++ tailWord_2742318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742318).length < 2 ^ (prefixWord ++ tailWord_2742318).sum := by decide
  have hdescent : baseEnd_2742318 < baseStart_2742318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742329 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 3, 2, 2]
def baseStart_2742329 : Nat := 118140960795 + 2742329 * 2 ^ 59
def prefixEnd_2742329 : Nat := 4983230072969 + 3 ^ 40 * 2742329 * 2
def baseEnd_2742329 : Nat := 1408132889763706358875765

theorem tailTrace_2742329 : CollatzResearch.WordTrace tailWord_2742329 prefixEnd_2742329 1408132889763706358875765 := by
  unfold tailWord_2742329
  simp only [CollatzResearch.WordTrace]
  refine ⟨100020955682017860350862041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66680637121345240233908027 100020955682017860350862041)
  ·
    refine ⟨75015716761513395263146531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100020955682017860350862041 75015716761513395263146531)
    ·
      refine ⟨112523575142270092894719797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75015716761513395263146531 112523575142270092894719797)
      ·
        refine ⟨10549085169587821208879981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112523575142270092894719797 10549085169587821208879981)
        ·
          refine ⟨3955906938595432953329993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10549085169587821208879981 3955906938595432953329993)
          ·
            refine ⟨2966930203946574714997495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3955906938595432953329993 2966930203946574714997495)
            ·
              refine ⟨4450395305919862072496243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2966930203946574714997495 4450395305919862072496243)
              ·
                refine ⟨6675592958879793108744365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4450395305919862072496243 6675592958879793108744365)
                ·
                  refine ⟨2503347359579922415779137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6675592958879793108744365 2503347359579922415779137)
                  ·
                    refine ⟨1877510519684941811834353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2503347359579922415779137 1877510519684941811834353)
                    ·
                      refine ⟨1408132889763706358875765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1877510519684941811834353 1408132889763706358875765)
                      ·
                        rfl

theorem cell23_2742329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_2742329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742329 prefixEnd_2742329 := by exact prefixLift 2742329
  have htrace : WordTrace (prefixWord ++ tailWord_2742329) baseStart_2742329 baseEnd_2742329 := by
    simpa [prefixWord, tailWord_2742329, baseEnd_2742329] using wordTrace_append hprefix tailTrace_2742329
  have hstable : (prefixWord ++ tailWord_2742329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742329).length < 2 ^ (prefixWord ++ tailWord_2742329).sum := by decide
  have hdescent : baseEnd_2742329 < baseStart_2742329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742345 : List Nat := [1, 2, 1, 1, 2, 2, 5, 3, 2, 1, 3]
def baseStart_2742345 : Nat := 118140960795 + 2742345 * 2 ^ 59
def prefixEnd_2742345 : Nat := 4983230072969 + 3 ^ 40 * 2742345 * 2
def baseEnd_2742345 : Nat := 1408141105454178296275691

theorem tailTrace_2742345 : CollatzResearch.WordTrace tailWord_2742345 prefixEnd_2742345 1408141105454178296275691 := by
  unfold tailWord_2742345
  simp only [CollatzResearch.WordTrace]
  refine ⟨100021539249959895083444489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66681026166639930055629659 100021539249959895083444489)
  ·
    refine ⟨75016154437469921312583367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100021539249959895083444489 75016154437469921312583367)
    ·
      refine ⟨112524231656204881968875051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75016154437469921312583367 112524231656204881968875051)
      ·
        refine ⟨168786347484307322953312577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112524231656204881968875051 168786347484307322953312577)
        ·
          refine ⟨126589760613230492214984433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168786347484307322953312577 126589760613230492214984433)
          ·
            refine ⟨94942320459922869161238325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126589760613230492214984433 94942320459922869161238325)
            ·
              refine ⟨8900842543117768983866093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94942320459922869161238325 8900842543117768983866093)
              ·
                refine ⟨3337815953669163368949785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8900842543117768983866093 3337815953669163368949785)
                ·
                  refine ⟨2503361965251872526712339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3337815953669163368949785 2503361965251872526712339)
                  ·
                    refine ⟨3755042947877808790068509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2503361965251872526712339 3755042947877808790068509)
                    ·
                      refine ⟨1408141105454178296275691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3755042947877808790068509 1408141105454178296275691)
                      ·
                        rfl

theorem cell23_2742345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 1, 3].length) (baseStart_2742345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742345 prefixEnd_2742345 := by exact prefixLift 2742345
  have htrace : WordTrace (prefixWord ++ tailWord_2742345) baseStart_2742345 baseEnd_2742345 := by
    simpa [prefixWord, tailWord_2742345, baseEnd_2742345] using wordTrace_append hprefix tailTrace_2742345
  have hstable : (prefixWord ++ tailWord_2742345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742345).length < 2 ^ (prefixWord ++ tailWord_2742345).sum := by decide
  have hdescent : baseEnd_2742345 < baseStart_2742345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742351 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 4]
def baseStart_2742351 : Nat := 118140960795 + 2742351 * 2 ^ 59
def prefixEnd_2742351 : Nat := 4983230072969 + 3 ^ 40 * 2742351 * 2
def baseEnd_2742351 : Nat := 1408144186338105272800663

theorem tailTrace_2742351 : CollatzResearch.WordTrace tailWord_2742351 prefixEnd_2742351 1408144186338105272800663 := by
  unfold tailWord_2742351
  simp only [CollatzResearch.WordTrace]
  refine ⟨100021758087938158108162907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66681172058625438738775271 100021758087938158108162907)
  ·
    refine ⟨150032637131907237162244361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100021758087938158108162907 150032637131907237162244361)
    ·
      refine ⟨112524477848930427871683271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150032637131907237162244361 112524477848930427871683271)
      ·
        refine ⟨168786716773395641807524907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112524477848930427871683271 168786716773395641807524907)
        ·
          refine ⟨253180075160093462711287361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168786716773395641807524907 253180075160093462711287361)
          ·
            refine ⟨189885056370070097033465521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253180075160093462711287361 189885056370070097033465521)
            ·
              refine ⟨142413792277552572775099141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189885056370070097033465521 142413792277552572775099141)
              ·
                refine ⟨26702586052041107395331089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142413792277552572775099141 26702586052041107395331089)
                ·
                  refine ⟨20026939539030830546498317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26702586052041107395331089 20026939539030830546498317)
                  ·
                    refine ⟨7510102327136561454936869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20026939539030830546498317 7510102327136561454936869)
                    ·
                      refine ⟨1408144186338105272800663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7510102327136561454936869 1408144186338105272800663)
                      ·
                        rfl

theorem cell23_2742351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_2742351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742351 prefixEnd_2742351 := by exact prefixLift 2742351
  have htrace : WordTrace (prefixWord ++ tailWord_2742351) baseStart_2742351 baseEnd_2742351 := by
    simpa [prefixWord, tailWord_2742351, baseEnd_2742351] using wordTrace_append hprefix tailTrace_2742351
  have hstable : (prefixWord ++ tailWord_2742351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742351).length < 2 ^ (prefixWord ++ tailWord_2742351).sum := by decide
  have hdescent : baseEnd_2742351 < baseStart_2742351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742366 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_2742366 : Nat := 118140960795 + 2742366 * 2 ^ 59
def prefixEnd_2742366 : Nat := 4983230072969 + 3 ^ 40 * 2742366 * 2
def baseEnd_2742366 : Nat := 1408151888547922714113095

theorem tailTrace_2742366 : CollatzResearch.WordTrace tailWord_2742366 prefixEnd_2742366 1408151888547922714113095 := by
  unfold tailWord_2742366
  simp only [CollatzResearch.WordTrace]
  refine ⟨12502788147860476958744869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66681536788589210446639301 12502788147860476958744869)
  ·
    refine ⟨2344272777723839429764663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12502788147860476958744869 2344272777723839429764663)
    ·
      refine ⟨3516409166585759144646995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2344272777723839429764663 3516409166585759144646995)
      ·
        refine ⟨5274613749878638716970493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3516409166585759144646995 5274613749878638716970493)
        ·
          refine ⟨1977980156204489518863935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5274613749878638716970493 1977980156204489518863935)
          ·
            refine ⟨2966970234306734278295903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977980156204489518863935 2966970234306734278295903)
            ·
              refine ⟨4450455351460101417443855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2966970234306734278295903 4450455351460101417443855)
              ·
                refine ⟨6675683027190152126165783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4450455351460101417443855 6675683027190152126165783)
                ·
                  refine ⟨10013524540785228189248675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6675683027190152126165783 10013524540785228189248675)
                  ·
                    refine ⟨15020286811177842283873013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10013524540785228189248675 15020286811177842283873013)
                    ·
                      refine ⟨1408151888547922714113095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15020286811177842283873013 1408151888547922714113095)
                      ·
                        rfl

theorem cell23_2742366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_2742366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742366 prefixEnd_2742366 := by exact prefixLift 2742366
  have htrace : WordTrace (prefixWord ++ tailWord_2742366) baseStart_2742366 baseEnd_2742366 := by
    simpa [prefixWord, tailWord_2742366, baseEnd_2742366] using wordTrace_append hprefix tailTrace_2742366
  have hstable : (prefixWord ++ tailWord_2742366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742366).length < 2 ^ (prefixWord ++ tailWord_2742366).sum := by decide
  have hdescent : baseEnd_2742366 < baseStart_2742366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742408 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 9]
def baseStart_2742408 : Nat := 118140960795 + 2742408 * 2 ^ 59
def prefixEnd_2742408 : Nat := 4983230072969 + 3 ^ 40 * 2742408 * 2
def baseEnd_2742408 : Nat := 156463717192823505531989

theorem tailTrace_2742408 : CollatzResearch.WordTrace tailWord_2742408 prefixEnd_2742408 156463717192823505531989 := by
  unfold tailWord_2742408
  simp only [CollatzResearch.WordTrace]
  refine ⟨50011918524365828421493939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66682558032487771228658585 50011918524365828421493939)
  ·
    refine ⟨75017877786548742632240909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50011918524365828421493939 75017877786548742632240909)
    ·
      refine ⟨28131704169955778487090341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75017877786548742632240909 28131704169955778487090341)
      ·
        refine ⟨5274694531866708466329439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28131704169955778487090341 5274694531866708466329439)
        ·
          refine ⟨7912041797800062699494159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5274694531866708466329439 7912041797800062699494159)
          ·
            refine ⟨11868062696700094049241239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7912041797800062699494159 11868062696700094049241239)
            ·
              refine ⟨17802094045050141073861859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11868062696700094049241239 17802094045050141073861859)
              ·
                refine ⟨26703141067575211610792789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17802094045050141073861859 26703141067575211610792789)
                ·
                  refine ⟨156463717192823505531989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26703141067575211610792789 156463717192823505531989)
                  ·
                    rfl

theorem cell23_2742408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 9].length) (baseStart_2742408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742408 prefixEnd_2742408 := by exact prefixLift 2742408
  have htrace : WordTrace (prefixWord ++ tailWord_2742408) baseStart_2742408 baseEnd_2742408 := by
    simpa [prefixWord, tailWord_2742408, baseEnd_2742408] using wordTrace_append hprefix tailTrace_2742408
  have hstable : (prefixWord ++ tailWord_2742408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742408).length < 2 ^ (prefixWord ++ tailWord_2742408).sum := by decide
  have hdescent : baseEnd_2742408 < baseStart_2742408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742436 : List Nat := [2, 3, 1, 2, 4, 2, 1, 2, 2, 2, 2]
def baseStart_2742436 : Nat := 118140960795 + 2742436 * 2 ^ 59
def prefixEnd_2742436 : Nat := 4983230072969 + 3 ^ 40 * 2742436 * 2
def baseEnd_2742436 : Nat := 1408187832193737440237773

theorem tailTrace_2742436 : CollatzResearch.WordTrace tailWord_2742436 prefixEnd_2742436 1408187832193737440237773 := by
  unfold tailWord_2742436
  simp only [CollatzResearch.WordTrace]
  refine ⟨50012429146315108812503581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66683238861753478416671441 50012429146315108812503581)
  ·
    refine ⟨18754660929868165804688843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50012429146315108812503581 18754660929868165804688843)
    ·
      refine ⟨28131991394802248707033265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18754660929868165804688843 28131991394802248707033265)
      ·
        refine ⟨21098993546101686530274949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28131991394802248707033265 21098993546101686530274949)
        ·
          refine ⟨3956061289894066224426553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21098993546101686530274949 3956061289894066224426553)
          ·
            refine ⟨2967045967420549668319915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3956061289894066224426553 2967045967420549668319915)
            ·
              refine ⟨4450568951130824502479873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2967045967420549668319915 4450568951130824502479873)
              ·
                refine ⟨3337926713348118376859905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4450568951130824502479873 3337926713348118376859905)
                ·
                  refine ⟨2503445035011088782644929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3337926713348118376859905 2503445035011088782644929)
                  ·
                    refine ⟨1877583776258316586983697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2503445035011088782644929 1877583776258316586983697)
                    ·
                      refine ⟨1408187832193737440237773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1877583776258316586983697 1408187832193737440237773)
                      ·
                        rfl

theorem cell23_2742436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_2742436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742436 prefixEnd_2742436 := by exact prefixLift 2742436
  have htrace : WordTrace (prefixWord ++ tailWord_2742436) baseStart_2742436 baseEnd_2742436 := by
    simpa [prefixWord, tailWord_2742436, baseEnd_2742436] using wordTrace_append hprefix tailTrace_2742436
  have hstable : (prefixWord ++ tailWord_2742436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742436).length < 2 ^ (prefixWord ++ tailWord_2742436).sum := by decide
  have hdescent : baseEnd_2742436 < baseStart_2742436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742441 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 8]
def baseStart_2742441 : Nat := 118140960795 + 2742441 * 2 ^ 59
def prefixEnd_2742441 : Nat := 4983230072969 + 3 ^ 40 * 2742441 * 2
def baseEnd_2742441 : Nat := 1408190399597009920675249

theorem tailTrace_2742441 : CollatzResearch.WordTrace tailWord_2742441 prefixEnd_2742441 1408190399597009920675249 := by
  unfold tailWord_2742441
  simp only [CollatzResearch.WordTrace]
  refine ⟨100025040657612103478939177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66683360438408068985959451 100025040657612103478939177)
  ·
    refine ⟨75018780493209077609204383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100025040657612103478939177 75018780493209077609204383)
    ·
      refine ⟨112528170739813616413806575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75018780493209077609204383 112528170739813616413806575)
      ·
        refine ⟨168792256109720424620709863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112528170739813616413806575 168792256109720424620709863)
        ·
          refine ⟨253188384164580636931064795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168792256109720424620709863 253188384164580636931064795)
          ·
            refine ⟨379782576246870955396597193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253188384164580636931064795 379782576246870955396597193)
            ·
              refine ⟨284836932185153216547447895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379782576246870955396597193 284836932185153216547447895)
              ·
                refine ⟨427255398277729824821171843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284836932185153216547447895 427255398277729824821171843)
                ·
                  refine ⟨640883097416594737231757765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427255398277729824821171843 640883097416594737231757765)
                  ·
                    refine ⟨120165580765611513230954581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 640883097416594737231757765 120165580765611513230954581)
                    ·
                      refine ⟨1408190399597009920675249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 120165580765611513230954581 1408190399597009920675249)
                      ·
                        rfl

theorem cell23_2742441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_2742441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742441 prefixEnd_2742441 := by exact prefixLift 2742441
  have htrace : WordTrace (prefixWord ++ tailWord_2742441) baseStart_2742441 baseEnd_2742441 := by
    simpa [prefixWord, tailWord_2742441, baseEnd_2742441] using wordTrace_append hprefix tailTrace_2742441
  have hstable : (prefixWord ++ tailWord_2742441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742441).length < 2 ^ (prefixWord ++ tailWord_2742441).sum := by decide
  have hdescent : baseEnd_2742441 < baseStart_2742441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742442 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 7]
def baseStart_2742442 : Nat := 118140960795 + 2742442 * 2 ^ 59
def prefixEnd_2742442 : Nat := 4983230072969 + 3 ^ 40 * 2742442 * 2
def baseEnd_2742442 : Nat := 156465657008629379640305

theorem tailTrace_2742442 : CollatzResearch.WordTrace tailWord_2742442 prefixEnd_2742442 156465657008629379640305 := by
  unfold tailWord_2742442
  simp only [CollatzResearch.WordTrace]
  refine ⟨25006269282652120162431395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66683384753738987099817053 25006269282652120162431395)
  ·
    refine ⟨37509403923978180243647093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25006269282652120162431395 37509403923978180243647093)
    ·
      refine ⟨3516506617872954397841915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37509403923978180243647093 3516506617872954397841915)
      ·
        refine ⟨5274759926809431596762873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3516506617872954397841915 5274759926809431596762873)
        ·
          refine ⟨3956069945107073697572155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5274759926809431596762873 3956069945107073697572155)
          ·
            refine ⟨5934104917660610546358233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3956069945107073697572155 5934104917660610546358233)
            ·
              refine ⟨4450578688245457909768675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5934104917660610546358233 4450578688245457909768675)
              ·
                refine ⟨6675868032368186864653013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4450578688245457909768675 6675868032368186864653013)
                ·
                  refine ⟨156465657008629379640305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6675868032368186864653013 156465657008629379640305)
                  ·
                    rfl

theorem cell23_2742442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 7].length) (baseStart_2742442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742442 prefixEnd_2742442 := by exact prefixLift 2742442
  have htrace : WordTrace (prefixWord ++ tailWord_2742442) baseStart_2742442 baseEnd_2742442 := by
    simpa [prefixWord, tailWord_2742442, baseEnd_2742442] using wordTrace_append hprefix tailTrace_2742442
  have hstable : (prefixWord ++ tailWord_2742442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742442).length < 2 ^ (prefixWord ++ tailWord_2742442).sum := by decide
  have hdescent : baseEnd_2742442 < baseStart_2742442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742453 : List Nat := [1, 3, 3, 4, 1, 1, 3, 1, 2, 2, 2]
def baseStart_2742453 : Nat := 118140960795 + 2742453 * 2 ^ 59
def prefixEnd_2742453 : Nat := 4983230072969 + 3 ^ 40 * 2742453 * 2
def baseEnd_2742453 : Nat := 1408196561364863873725195

theorem tailTrace_2742453 : CollatzResearch.WordTrace tailWord_2742453 prefixEnd_2742453 1408196561364863873725195 := by
  unfold tailWord_2742453
  simp only [CollatzResearch.WordTrace]
  refine ⟨100025478333568629528376013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66683652222379086352250675 100025478333568629528376013)
  ·
    refine ⟨37509554375088236073141005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100025478333568629528376013 37509554375088236073141005)
    ·
      refine ⟨14066082890658088527427877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37509554375088236073141005 14066082890658088527427877)
      ·
        refine ⟨2637390541998391598892727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14066082890658088527427877 2637390541998391598892727)
        ·
          refine ⟨3956085812997587398339091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2637390541998391598892727 3956085812997587398339091)
          ·
            refine ⟨5934128719496381097508637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3956085812997587398339091 5934128719496381097508637)
            ·
              refine ⟨2225298269811142911565739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5934128719496381097508637 2225298269811142911565739)
              ·
                refine ⟨3337947404716714367348609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2225298269811142911565739 3337947404716714367348609)
                ·
                  refine ⟨2503460553537535775511457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3337947404716714367348609 2503460553537535775511457)
                  ·
                    refine ⟨1877595415153151831633593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2503460553537535775511457 1877595415153151831633593)
                    ·
                      refine ⟨1408196561364863873725195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1877595415153151831633593 1408196561364863873725195)
                      ·
                        rfl

theorem cell23_2742453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_2742453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742453 prefixEnd_2742453 := by exact prefixLift 2742453
  have htrace : WordTrace (prefixWord ++ tailWord_2742453) baseStart_2742453 baseEnd_2742453 := by
    simpa [prefixWord, tailWord_2742453, baseEnd_2742453] using wordTrace_append hprefix tailTrace_2742453
  have hstable : (prefixWord ++ tailWord_2742453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742453).length < 2 ^ (prefixWord ++ tailWord_2742453).sum := by decide
  have hdescent : baseEnd_2742453 < baseStart_2742453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742458 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4]
def baseStart_2742458 : Nat := 118140960795 + 2742458 * 2 ^ 59
def prefixEnd_2742458 : Nat := 4983230072969 + 3 ^ 40 * 2742458 * 2
def baseEnd_2742458 : Nat := 1408199128768136354162671

theorem tailTrace_2742458 : CollatzResearch.WordTrace tailWord_2742458 prefixEnd_2742458 1408199128768136354162671 := by
  unfold tailWord_2742458
  simp only [CollatzResearch.WordTrace]
  refine ⟨25006415174637628845577007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66683773799033676921538685 25006415174637628845577007)
  ·
    refine ⟨37509622761956443268365511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25006415174637628845577007 37509622761956443268365511)
    ·
      refine ⟨56264434142934664902548267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37509622761956443268365511 56264434142934664902548267)
      ·
        refine ⟨84396651214401997353822401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56264434142934664902548267 84396651214401997353822401)
        ·
          refine ⟨63297488410801498015366801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84396651214401997353822401 63297488410801498015366801)
          ·
            refine ⟨47473116308101123511525101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63297488410801498015366801 47473116308101123511525101)
            ·
              refine ⟨17802418615537921316821913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47473116308101123511525101 17802418615537921316821913)
              ·
                refine ⟨13351813961653440987616435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17802418615537921316821913 13351813961653440987616435)
                ·
                  refine ⟨20027720942480161481424653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13351813961653440987616435 20027720942480161481424653)
                  ·
                    refine ⟨7510395353430060555534245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20027720942480161481424653 7510395353430060555534245)
                    ·
                      refine ⟨1408199128768136354162671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7510395353430060555534245 1408199128768136354162671)
                      ·
                        rfl

theorem cell23_2742458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_2742458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742458 prefixEnd_2742458 := by exact prefixLift 2742458
  have htrace : WordTrace (prefixWord ++ tailWord_2742458) baseStart_2742458 baseEnd_2742458 := by
    simpa [prefixWord, tailWord_2742458, baseEnd_2742458] using wordTrace_append hprefix tailTrace_2742458
  have hstable : (prefixWord ++ tailWord_2742458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742458).length < 2 ^ (prefixWord ++ tailWord_2742458).sum := by decide
  have hdescent : baseEnd_2742458 < baseStart_2742458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742476 : List Nat := [2, 2, 1, 6, 2, 1, 1, 3, 5]
def baseStart_2742476 : Nat := 118140960795 + 2742476 * 2 ^ 59
def prefixEnd_2742476 : Nat := 4983230072969 + 3 ^ 40 * 2742476 * 2
def baseEnd_2742476 : Nat := 156467596824435253748621

theorem tailTrace_2742476 : CollatzResearch.WordTrace tailWord_2742476 prefixEnd_2742476 156467596824435253748621 := by
  unfold tailWord_2742476
  simp only [CollatzResearch.WordTrace]
  refine ⟨50013158606242652228231641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66684211474990202970975521 50013158606242652228231641)
  ·
    refine ⟨37509868954681989171173731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50013158606242652228231641 37509868954681989171173731)
    ·
      refine ⟨56264803432022983756760597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37509868954681989171173731 56264803432022983756760597)
      ·
        refine ⟨2637412660876077363598153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56264803432022983756760597 2637412660876077363598153)
        ·
          refine ⟨1978059495657058022698615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2637412660876077363598153 1978059495657058022698615)
          ·
            refine ⟨2967089243485587034047923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1978059495657058022698615 2967089243485587034047923)
            ·
              refine ⟨4450633865228380551071885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2967089243485587034047923 4450633865228380551071885)
              ·
                refine ⟨1668987699460642706651957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4450633865228380551071885 1668987699460642706651957)
                ·
                  refine ⟨156467596824435253748621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1668987699460642706651957 156467596824435253748621)
                  ·
                    rfl

theorem cell23_2742476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 5].length) (baseStart_2742476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742476 prefixEnd_2742476 := by exact prefixLift 2742476
  have htrace : WordTrace (prefixWord ++ tailWord_2742476) baseStart_2742476 baseEnd_2742476 := by
    simpa [prefixWord, tailWord_2742476, baseEnd_2742476] using wordTrace_append hprefix tailTrace_2742476
  have hstable : (prefixWord ++ tailWord_2742476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742476).length < 2 ^ (prefixWord ++ tailWord_2742476).sum := by decide
  have hdescent : baseEnd_2742476 < baseStart_2742476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742552 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 2, 3, 2]
def baseStart_2742552 : Nat := 118140960795 + 2742552 * 2 ^ 59
def prefixEnd_2742552 : Nat := 4983230072969 + 3 ^ 40 * 2742552 * 2
def baseEnd_2742552 : Nat := 1408247395949658986387239

theorem tailTrace_2742552 : CollatzResearch.WordTrace tailWord_2742552 prefixEnd_2742552 1408247395949658986387239 := by
  unfold tailWord_2742552
  simp only [CollatzResearch.WordTrace]
  refine ⟨50014544580104984718114955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66686059440139979624153273 50014544580104984718114955)
  ·
    refine ⟨75021816870157477077172433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50014544580104984718114955 75021816870157477077172433)
    ·
      refine ⟨56266362652618107807879325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75021816870157477077172433 56266362652618107807879325)
      ·
        refine ⟨21099885994731790427954747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56266362652618107807879325 21099885994731790427954747)
        ·
          refine ⟨31649828992097685641932121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21099885994731790427954747 31649828992097685641932121)
          ·
            refine ⟨23737371744073264231449091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31649828992097685641932121 23737371744073264231449091)
            ·
              refine ⟨35606057616109896347173637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23737371744073264231449091 35606057616109896347173637)
              ·
                refine ⟨6676135803020605565095057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35606057616109896347173637 6676135803020605565095057)
                ·
                  refine ⟨5007101852265454173821293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6676135803020605565095057 5007101852265454173821293)
                  ·
                    refine ⟨1877663194599545315182985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5007101852265454173821293 1877663194599545315182985)
                    ·
                      refine ⟨1408247395949658986387239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1877663194599545315182985 1408247395949658986387239)
                      ·
                        rfl

theorem cell23_2742552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_2742552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742552 prefixEnd_2742552 := by exact prefixLift 2742552
  have htrace : WordTrace (prefixWord ++ tailWord_2742552) baseStart_2742552 baseEnd_2742552 := by
    simpa [prefixWord, tailWord_2742552, baseEnd_2742552] using wordTrace_append hprefix tailTrace_2742552
  have hstable : (prefixWord ++ tailWord_2742552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742552).length < 2 ^ (prefixWord ++ tailWord_2742552).sum := by decide
  have hdescent : baseEnd_2742552 < baseStart_2742552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742593 : List Nat := [1, 2, 5, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_2742593 : Nat := 118140960795 + 2742593 * 2 ^ 59
def prefixEnd_2742593 : Nat := 4983230072969 + 3 ^ 40 * 2742593 * 2
def baseEnd_2742593 : Nat := 1408268448656493325974551

theorem tailTrace_2742593 : CollatzResearch.WordTrace tailWord_2742593 prefixEnd_2742593 1408268448656493325974551 := by
  unfold tailWord_2742593
  simp only [CollatzResearch.WordTrace]
  refine ⟨100030584553061433438472433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66687056368707622292314955 100030584553061433438472433)
  ·
    refine ⟨75022938414796075078854325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100030584553061433438472433 75022938414796075078854325)
    ·
      refine ⟨7033400476387132038642593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75022938414796075078854325 7033400476387132038642593)
      ·
        refine ⟨5275050357290349028981945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7033400476387132038642593 5275050357290349028981945)
        ·
          refine ⟨3956287767967761771736459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5275050357290349028981945 3956287767967761771736459)
          ·
            refine ⟨5934431651951642657604689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3956287767967761771736459 5934431651951642657604689)
            ·
              refine ⟨4450823738963731993203517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5934431651951642657604689 4450823738963731993203517)
              ·
                refine ⟨1669058902111399497451319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4450823738963731993203517 1669058902111399497451319)
                ·
                  refine ⟨2503588353167099246176979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669058902111399497451319 2503588353167099246176979)
                  ·
                    refine ⟨3755382529750648869265469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2503588353167099246176979 3755382529750648869265469)
                    ·
                      refine ⟨1408268448656493325974551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3755382529750648869265469 1408268448656493325974551)
                      ·
                        rfl

theorem cell23_2742593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_2742593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742593 prefixEnd_2742593 := by exact prefixLift 2742593
  have htrace : WordTrace (prefixWord ++ tailWord_2742593) baseStart_2742593 baseEnd_2742593 := by
    simpa [prefixWord, tailWord_2742593, baseEnd_2742593] using wordTrace_append hprefix tailTrace_2742593
  have hstable : (prefixWord ++ tailWord_2742593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742593).length < 2 ^ (prefixWord ++ tailWord_2742593).sum := by decide
  have hdescent : baseEnd_2742593 < baseStart_2742593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742595 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 4]
def baseStart_2742595 : Nat := 118140960795 + 2742595 * 2 ^ 59
def prefixEnd_2742595 : Nat := 4983230072969 + 3 ^ 40 * 2742595 * 2
def baseEnd_2742595 : Nat := 1408269475617802318149541

theorem tailTrace_2742595 : CollatzResearch.WordTrace tailWord_2742595 prefixEnd_2742595 1408269475617802318149541 := by
  unfold tailWord_2742595
  simp only [CollatzResearch.WordTrace]
  refine ⟨100030657499054187780045239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66687104999369458520030159 100030657499054187780045239)
  ·
    refine ⟨150045986248581281670067859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100030657499054187780045239 150045986248581281670067859)
    ·
      refine ⟨225068979372871922505101789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150045986248581281670067859 225068979372871922505101789)
      ·
        refine ⟨84400867264826970939413171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225068979372871922505101789 84400867264826970939413171)
        ·
          refine ⟨126601300897240456409119757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84400867264826970939413171 126601300897240456409119757)
          ·
            refine ⟨47475487836465171153419909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126601300897240456409119757 47475487836465171153419909)
            ·
              refine ⟨8901653969337219591266233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47475487836465171153419909 8901653969337219591266233)
              ·
                refine ⟨6676240477002914693449675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8901653969337219591266233 6676240477002914693449675)
                ·
                  refine ⟨10014360715504372040174513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6676240477002914693449675 10014360715504372040174513)
                  ·
                    refine ⟨7510770536628279030130885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10014360715504372040174513 7510770536628279030130885)
                    ·
                      refine ⟨1408269475617802318149541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7510770536628279030130885 1408269475617802318149541)
                      ·
                        rfl

theorem cell23_2742595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_2742595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742595 prefixEnd_2742595 := by exact prefixLift 2742595
  have htrace : WordTrace (prefixWord ++ tailWord_2742595) baseStart_2742595 baseEnd_2742595 := by
    simpa [prefixWord, tailWord_2742595, baseEnd_2742595] using wordTrace_append hprefix tailTrace_2742595
  have hstable : (prefixWord ++ tailWord_2742595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742595).length < 2 ^ (prefixWord ++ tailWord_2742595).sum := by decide
  have hdescent : baseEnd_2742595 < baseStart_2742595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742609 : List Nat := [1, 2, 2, 1, 4, 4, 1, 2, 2, 4]
def baseStart_2742609 : Nat := 118140960795 + 2742609 * 2 ^ 59
def prefixEnd_2742609 : Nat := 4983230072969 + 3 ^ 40 * 2742609 * 2
def baseEnd_2742609 : Nat := 469425554782321754458159

theorem tailTrace_2742609 : CollatzResearch.WordTrace tailWord_2742609 prefixEnd_2742609 469425554782321754458159 := by
  unfold tailWord_2742609
  simp only [CollatzResearch.WordTrace]
  refine ⟨100031168121003468171054881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66687445414002312114036587 100031168121003468171054881)
  ·
    refine ⟨75023376090752601128291161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100031168121003468171054881 75023376090752601128291161)
    ·
      refine ⟨56267532068064450846218371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75023376090752601128291161 56267532068064450846218371)
      ·
        refine ⟨84401298102096676269327557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56267532068064450846218371 84401298102096676269327557)
        ·
          refine ⟨15825243394143126800498917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84401298102096676269327557 15825243394143126800498917)
          ·
            refine ⟨2967233136401836275093547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15825243394143126800498917 2967233136401836275093547)
            ·
              refine ⟨4450849704602754412640321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2967233136401836275093547 4450849704602754412640321)
              ·
                refine ⟨3338137278452065809480241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4450849704602754412640321 3338137278452065809480241)
                ·
                  refine ⟨2503602958839049357110181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3338137278452065809480241 2503602958839049357110181)
                  ·
                    refine ⟨469425554782321754458159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2503602958839049357110181 469425554782321754458159)
                    ·
                      rfl

theorem cell23_2742609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_2742609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742609 prefixEnd_2742609 := by exact prefixLift 2742609
  have htrace : WordTrace (prefixWord ++ tailWord_2742609) baseStart_2742609 baseEnd_2742609 := by
    simpa [prefixWord, tailWord_2742609, baseEnd_2742609] using wordTrace_append hprefix tailTrace_2742609
  have hstable : (prefixWord ++ tailWord_2742609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742609).length < 2 ^ (prefixWord ++ tailWord_2742609).sum := by decide
  have hdescent : baseEnd_2742609 < baseStart_2742609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742626 : List Nat := [3, 3, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_2742626 : Nat := 118140960795 + 2742626 * 2 ^ 59
def prefixEnd_2742626 : Nat := 4983230072969 + 3 ^ 40 * 2742626 * 2
def baseEnd_2742626 : Nat := 469428464506030565620633

theorem tailTrace_2742626 : CollatzResearch.WordTrace tailWord_2742626 prefixEnd_2742626 469428464506030565620633 := by
  unfold tailWord_2742626
  simp only [CollatzResearch.WordTrace]
  refine ⟨25007947040485470018605933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66687858774627920049615821 25007947040485470018605933)
  ·
    refine ⟨9377980140182051256977225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25007947040485470018605933 9377980140182051256977225)
    ·
      refine ⟨7033485105136538442732919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9377980140182051256977225 7033485105136538442732919)
      ·
        refine ⟨10550227657704807664099379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7033485105136538442732919 10550227657704807664099379)
        ·
          refine ⟨15825341486557211496149069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10550227657704807664099379 15825341486557211496149069)
          ·
            refine ⟨5934503057458954311055901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15825341486557211496149069 5934503057458954311055901)
            ·
              refine ⟨2225438646547107866645963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5934503057458954311055901 2225438646547107866645963)
              ·
                refine ⟨3338157969820661799968945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2225438646547107866645963 3338157969820661799968945)
                ·
                  refine ⟨2503618477365496349976709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3338157969820661799968945 2503618477365496349976709)
                  ·
                    refine ⟨469428464506030565620633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2503618477365496349976709 469428464506030565620633)
                    ·
                      rfl

theorem cell23_2742626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_2742626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742626 prefixEnd_2742626 := by exact prefixLift 2742626
  have htrace : WordTrace (prefixWord ++ tailWord_2742626) baseStart_2742626 baseEnd_2742626 := by
    simpa [prefixWord, tailWord_2742626, baseEnd_2742626] using wordTrace_append hprefix tailTrace_2742626
  have hstable : (prefixWord ++ tailWord_2742626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742626).length < 2 ^ (prefixWord ++ tailWord_2742626).sum := by decide
  have hdescent : baseEnd_2742626 < baseStart_2742626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742712 : List Nat := [2, 1, 2, 1, 2, 2, 1, 7, 5]
def baseStart_2742712 : Nat := 118140960795 + 2742712 * 2 ^ 59
def prefixEnd_2742712 : Nat := 4983230072969 + 3 ^ 40 * 2742712 * 2
def baseEnd_2742712 : Nat := 156481061428264262265167

theorem tailTrace_2742712 : CollatzResearch.WordTrace tailWord_2742712 prefixEnd_2742712 156481061428264262265167 := by
  unfold tailWord_2742712
  simp only [CollatzResearch.WordTrace]
  refine ⟨50017462419815158381027195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66689949893086877841369593 50017462419815158381027195)
  ·
    refine ⟨75026193629722737571540793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50017462419815158381027195 75026193629722737571540793)
    ·
      refine ⟨56269645222292053178655595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75026193629722737571540793 56269645222292053178655595)
      ·
        refine ⟨84404467833438079767983393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56269645222292053178655595 84404467833438079767983393)
        ·
          refine ⟨63303350875078559825987545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84404467833438079767983393 63303350875078559825987545)
          ·
            refine ⟨47477513156308919869490659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63303350875078559825987545 47477513156308919869490659)
            ·
              refine ⟨71216269734463379804235989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47477513156308919869490659 71216269734463379804235989)
              ·
                refine ⟨1669131321901485464161781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 71216269734463379804235989 1669131321901485464161781)
                ·
                  refine ⟨156481061428264262265167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1669131321901485464161781 156481061428264262265167)
                  ·
                    rfl

theorem cell23_2742712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 5].length) (baseStart_2742712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742712 prefixEnd_2742712 := by exact prefixLift 2742712
  have htrace : WordTrace (prefixWord ++ tailWord_2742712) baseStart_2742712 baseEnd_2742712 := by
    simpa [prefixWord, tailWord_2742712, baseEnd_2742712] using wordTrace_append hprefix tailTrace_2742712
  have hstable : (prefixWord ++ tailWord_2742712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742712).length < 2 ^ (prefixWord ++ tailWord_2742712).sum := by decide
  have hdescent : baseEnd_2742712 < baseStart_2742712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742729 : List Nat := [1, 2, 1, 1, 2, 1, 8, 2, 5]
def baseStart_2742729 : Nat := 118140960795 + 2742729 * 2 ^ 59
def prefixEnd_2742729 : Nat := 4983230072969 + 3 ^ 40 * 2742729 * 2
def baseEnd_2742729 : Nat := 156482031336167199319325

theorem tailTrace_2742729 : CollatzResearch.WordTrace tailWord_2742729 prefixEnd_2742729 156482031336167199319325 := by
  unfold tailWord_2742729
  simp only [CollatzResearch.WordTrace]
  refine ⟨100035544880568728665423241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66690363253712485776948827 100035544880568728665423241)
  ·
    refine ⟨75026658660426546499067431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100035544880568728665423241 75026658660426546499067431)
    ·
      refine ⟨112539987990639819748601147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75026658660426546499067431 112539987990639819748601147)
      ·
        refine ⟨168809981985959729622901721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112539987990639819748601147 168809981985959729622901721)
        ·
          refine ⟨126607486489469797217176291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168809981985959729622901721 126607486489469797217176291)
          ·
            refine ⟨189911229734204695825764437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126607486489469797217176291 189911229734204695825764437)
            ·
              refine ⟨2225522223447711279208177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 189911229734204695825764437 2225522223447711279208177)
              ·
                refine ⟨1669141667585783459406133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2225522223447711279208177 1669141667585783459406133)
                ·
                  refine ⟨156482031336167199319325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1669141667585783459406133 156482031336167199319325)
                  ·
                    rfl

theorem cell23_2742729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 5].length) (baseStart_2742729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742729 prefixEnd_2742729 := by exact prefixLift 2742729
  have htrace : WordTrace (prefixWord ++ tailWord_2742729) baseStart_2742729 baseEnd_2742729 := by
    simpa [prefixWord, tailWord_2742729, baseEnd_2742729] using wordTrace_append hprefix tailTrace_2742729
  have hstable : (prefixWord ++ tailWord_2742729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742729).length < 2 ^ (prefixWord ++ tailWord_2742729).sum := by decide
  have hdescent : baseEnd_2742729 < baseStart_2742729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742749 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_2742749 : Nat := 118140960795 + 2742749 * 2 ^ 59
def prefixEnd_2742749 : Nat := 4983230072969 + 3 ^ 40 * 2742749 * 2
def baseEnd_2742749 : Nat := 1408348551638594715623833

theorem tailTrace_2742749 : CollatzResearch.WordTrace tailWord_2742749 prefixEnd_2742749 1408348551638594715623833 := by
  unfold tailWord_2742749
  simp only [CollatzResearch.WordTrace]
  refine ⟨100036274340496272081151301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66690849560330848054100867 100036274340496272081151301)
  ·
    refine ⟨18756801438843051015215869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100036274340496272081151301 18756801438843051015215869)
    ·
      refine ⟨7033800539566144130705951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18756801438843051015215869 7033800539566144130705951)
      ·
        refine ⟨10550700809349216196058927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7033800539566144130705951 10550700809349216196058927)
        ·
          refine ⟨15826051214023824294088391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10550700809349216196058927 15826051214023824294088391)
          ·
            refine ⟨23739076821035736441132587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15826051214023824294088391 23739076821035736441132587)
            ·
              refine ⟨35608615231553604661698881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23739076821035736441132587 35608615231553604661698881)
              ·
                refine ⟨26706461423665203496274161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35608615231553604661698881 26706461423665203496274161)
                ·
                  refine ⟨20029846067748902622205621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26706461423665203496274161 20029846067748902622205621)
                  ·
                    refine ⟨1877798068851459620831777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20029846067748902622205621 1877798068851459620831777)
                    ·
                      refine ⟨1408348551638594715623833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1877798068851459620831777 1408348551638594715623833)
                      ·
                        rfl

theorem cell23_2742749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_2742749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742749 prefixEnd_2742749 := by exact prefixLift 2742749
  have htrace : WordTrace (prefixWord ++ tailWord_2742749) baseStart_2742749 baseEnd_2742749 := by
    simpa [prefixWord, tailWord_2742749, baseEnd_2742749] using wordTrace_append hprefix tailTrace_2742749
  have hstable : (prefixWord ++ tailWord_2742749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742749).length < 2 ^ (prefixWord ++ tailWord_2742749).sum := by decide
  have hdescent : baseEnd_2742749 < baseStart_2742749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742869 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 2, 6, 2]
def baseStart_2742869 : Nat := 118140960795 + 2742869 * 2 ^ 59
def prefixEnd_2742869 : Nat := 4983230072969 + 3 ^ 40 * 2742869 * 2
def baseEnd_2742869 : Nat := 1408410169317134246123281

theorem tailTrace_2742869 : CollatzResearch.WordTrace tailWord_2742869 prefixEnd_2742869 1408410169317134246123281 := by
  unfold tailWord_2742869
  simp only [CollatzResearch.WordTrace]
  refine ⟨100040651100061532575519661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66693767400041021717013107 100040651100061532575519661)
  ·
    refine ⟨37515244162523074715819873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100040651100061532575519661 37515244162523074715819873)
    ·
      refine ⟨28136433121892306036864905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37515244162523074715819873 28136433121892306036864905)
      ·
        refine ⟨21102324841419229527648679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28136433121892306036864905 21102324841419229527648679)
        ·
          refine ⟨31653487262128844291473019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21102324841419229527648679 31653487262128844291473019)
          ·
            refine ⟨47480230893193266437209529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31653487262128844291473019 47480230893193266437209529)
            ·
              refine ⟨35610173169894949827907147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47480230893193266437209529 35610173169894949827907147)
              ·
                refine ⟨53415259754842424741860721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35610173169894949827907147 53415259754842424741860721)
                ·
                  refine ⟨40061444816131818556395541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53415259754842424741860721 40061444816131818556395541)
                  ·
                    refine ⟨1877880225756178994831041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40061444816131818556395541 1877880225756178994831041)
                    ·
                      refine ⟨1408410169317134246123281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1877880225756178994831041 1408410169317134246123281)
                      ·
                        rfl

theorem cell23_2742869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_2742869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742869 prefixEnd_2742869 := by exact prefixLift 2742869
  have htrace : WordTrace (prefixWord ++ tailWord_2742869) baseStart_2742869 baseEnd_2742869 := by
    simpa [prefixWord, tailWord_2742869, baseEnd_2742869] using wordTrace_append hprefix tailTrace_2742869
  have hstable : (prefixWord ++ tailWord_2742869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742869).length < 2 ^ (prefixWord ++ tailWord_2742869).sum := by decide
  have hdescent : baseEnd_2742869 < baseStart_2742869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742872 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 5]
def baseStart_2742872 : Nat := 118140960795 + 2742872 * 2 ^ 59
def prefixEnd_2742872 : Nat := 4983230072969 + 3 ^ 40 * 2742872 * 2
def baseEnd_2742872 : Nat := 1408411709759097734385767

theorem tailTrace_2742872 : CollatzResearch.WordTrace tailWord_2742872 prefixEnd_2742872 1408411709759097734385767 := by
  unfold tailWord_2742872
  simp only [CollatzResearch.WordTrace]
  refine ⟨50020380259525332043939435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66693840346033776058585913 50020380259525332043939435)
  ·
    refine ⟨75030570389287998065909153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50020380259525332043939435 75030570389287998065909153)
    ·
      refine ⟨56272927791965998549431865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75030570389287998065909153 56272927791965998549431865)
      ·
        refine ⟨42204695843974498912073899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56272927791965998549431865 42204695843974498912073899)
        ·
          refine ⟨63307043765961748368110849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42204695843974498912073899 63307043765961748368110849)
          ·
            refine ⟨47480282824471311276083137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63307043765961748368110849 47480282824471311276083137)
            ·
              refine ⟨35610212118353483457062353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47480282824471311276083137 35610212118353483457062353)
              ·
                refine ⟨26707659088765112592796765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35610212118353483457062353 26707659088765112592796765)
                ·
                  refine ⟨10015372158286917222298787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26707659088765112592796765 10015372158286917222298787)
                  ·
                    refine ⟨15023058237430375833448181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10015372158286917222298787 15023058237430375833448181)
                    ·
                      refine ⟨1408411709759097734385767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15023058237430375833448181 1408411709759097734385767)
                      ·
                        rfl

theorem cell23_2742872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_2742872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742872 prefixEnd_2742872 := by exact prefixLift 2742872
  have htrace : WordTrace (prefixWord ++ tailWord_2742872) baseStart_2742872 baseEnd_2742872 := by
    simpa [prefixWord, tailWord_2742872, baseEnd_2742872] using wordTrace_append hprefix tailTrace_2742872
  have hstable : (prefixWord ++ tailWord_2742872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742872).length < 2 ^ (prefixWord ++ tailWord_2742872).sum := by decide
  have hdescent : baseEnd_2742872 < baseStart_2742872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742916 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_2742916 : Nat := 118140960795 + 2742916 * 2 ^ 59
def prefixEnd_2742916 : Nat := 4983230072969 + 3 ^ 40 * 2742916 * 2
def baseEnd_2742916 : Nat := 1408434302907895562235565

theorem tailTrace_2742916 : CollatzResearch.WordTrace tailWord_2742916 prefixEnd_2742916 1408434302907895562235565 := by
  unfold tailWord_2742916
  simp only [CollatzResearch.WordTrace]
  refine ⟨50021182665445629801240301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66694910220594173068320401 50021182665445629801240301)
  ·
    refine ⟨18757943499542111175465113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50021182665445629801240301 18757943499542111175465113)
    ·
      refine ⟨14068457624656583381598835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18757943499542111175465113 14068457624656583381598835)
      ·
        refine ⟨21102686436984875072398253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14068457624656583381598835 21102686436984875072398253)
        ·
          refine ⟨7913507413869328152149345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21102686436984875072398253 7913507413869328152149345)
          ·
            refine ⟨5935130560401996114112009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7913507413869328152149345 5935130560401996114112009)
            ·
              refine ⟨4451347920301497085584007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5935130560401996114112009 4451347920301497085584007)
              ·
                refine ⟨6677021880452245628376011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4451347920301497085584007 6677021880452245628376011)
                ·
                  refine ⟨10015532820678368442564017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6677021880452245628376011 10015532820678368442564017)
                  ·
                    refine ⟨7511649615508776331923013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10015532820678368442564017 7511649615508776331923013)
                    ·
                      refine ⟨1408434302907895562235565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7511649615508776331923013 1408434302907895562235565)
                      ·
                        rfl

theorem cell23_2742916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_2742916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742916 prefixEnd_2742916 := by exact prefixLift 2742916
  have htrace : WordTrace (prefixWord ++ tailWord_2742916) baseStart_2742916 baseEnd_2742916 := by
    simpa [prefixWord, tailWord_2742916, baseEnd_2742916] using wordTrace_append hprefix tailTrace_2742916
  have hstable : (prefixWord ++ tailWord_2742916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742916).length < 2 ^ (prefixWord ++ tailWord_2742916).sum := by decide
  have hdescent : baseEnd_2742916 < baseStart_2742916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742936 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 4, 1, 3]
def baseStart_2742936 : Nat := 118140960795 + 2742936 * 2 ^ 59
def prefixEnd_2742936 : Nat := 4983230072969 + 3 ^ 40 * 2742936 * 2
def baseEnd_2742936 : Nat := 1408444572520985483985473

theorem tailTrace_2742936 : CollatzResearch.WordTrace tailWord_2742936 prefixEnd_2742936 1408444572520985483985473 := by
  unfold tailWord_2742936
  simp only [CollatzResearch.WordTrace]
  refine ⟨50021547395409401509104331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66695396527212535345472441 50021547395409401509104331)
  ·
    refine ⟨75032321093114102263656497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50021547395409401509104331 75032321093114102263656497)
    ·
      refine ⟨56274240819835576697742373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75032321093114102263656497 56274240819835576697742373)
      ·
        refine ⟨10551420153719170630826695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56274240819835576697742373 10551420153719170630826695)
        ·
          refine ⟨15827130230578755946240043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10551420153719170630826695 15827130230578755946240043)
          ·
            refine ⟨23740695345868133919360065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15827130230578755946240043 23740695345868133919360065)
            ·
              refine ⟨17805521509401100439520049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23740695345868133919360065 17805521509401100439520049)
              ·
                refine ⟨13354141132050825329640037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17805521509401100439520049 13354141132050825329640037)
                ·
                  refine ⟨2503901462259529749307507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13354141132050825329640037 2503901462259529749307507)
                  ·
                    refine ⟨3755852193389294623961261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2503901462259529749307507 3755852193389294623961261)
                    ·
                      refine ⟨1408444572520985483985473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3755852193389294623961261 1408444572520985483985473)
                      ·
                        rfl

theorem cell23_2742936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_2742936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742936 prefixEnd_2742936 := by exact prefixLift 2742936
  have htrace : WordTrace (prefixWord ++ tailWord_2742936) baseStart_2742936 baseEnd_2742936 := by
    simpa [prefixWord, tailWord_2742936, baseEnd_2742936] using wordTrace_append hprefix tailTrace_2742936
  have hstable : (prefixWord ++ tailWord_2742936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742936).length < 2 ^ (prefixWord ++ tailWord_2742936).sum := by decide
  have hdescent : baseEnd_2742936 < baseStart_2742936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742940 : List Nat := [2, 2, 3, 2, 2, 3, 2, 1, 1, 2, 3]
def baseStart_2742940 : Nat := 118140960795 + 2742940 * 2 ^ 59
def prefixEnd_2742940 : Nat := 4983230072969 + 3 ^ 40 * 2742940 * 2
def baseEnd_2742940 : Nat := 1408446626443603468335455

theorem tailTrace_2742940 : CollatzResearch.WordTrace tailWord_2742940 prefixEnd_2742940 1408446626443603468335455 := by
  unfold tailWord_2742940
  simp only [CollatzResearch.WordTrace]
  refine ⟨50021620341402155850677137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66695493788536207800902849 50021620341402155850677137)
  ·
    refine ⟨37516215256051616888007853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50021620341402155850677137 37516215256051616888007853)
    ·
      refine ⟨14068580721019356333002945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37516215256051616888007853 14068580721019356333002945)
      ·
        refine ⟨10551435540764517249752209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14068580721019356333002945 10551435540764517249752209)
        ·
          refine ⟨7913576655573387937314157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10551435540764517249752209 7913576655573387937314157)
          ·
            refine ⟨2967591245840020476492809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7913576655573387937314157 2967591245840020476492809)
            ·
              refine ⟨2225693434380015357369607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2967591245840020476492809 2225693434380015357369607)
              ·
                refine ⟨3338540151570023036054411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2225693434380015357369607 3338540151570023036054411)
                ·
                  refine ⟨5007810227355034554081617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3338540151570023036054411 5007810227355034554081617)
                  ·
                    refine ⟨3755857670516275915561213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5007810227355034554081617 3755857670516275915561213)
                    ·
                      refine ⟨1408446626443603468335455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3755857670516275915561213 1408446626443603468335455)
                      ·
                        rfl

theorem cell23_2742940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_2742940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742940 prefixEnd_2742940 := by exact prefixLift 2742940
  have htrace : WordTrace (prefixWord ++ tailWord_2742940) baseStart_2742940 baseEnd_2742940 := by
    simpa [prefixWord, tailWord_2742940, baseEnd_2742940] using wordTrace_append hprefix tailTrace_2742940
  have hstable : (prefixWord ++ tailWord_2742940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742940).length < 2 ^ (prefixWord ++ tailWord_2742940).sum := by decide
  have hdescent : baseEnd_2742940 < baseStart_2742940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742980 : List Nat := [2, 3, 3, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_2742980 : Nat := 118140960795 + 2742980 * 2 ^ 59
def prefixEnd_2742980 : Nat := 4983230072969 + 3 ^ 40 * 2742980 * 2
def baseEnd_2742980 : Nat := 1408467165669783311835271

theorem tailTrace_2742980 : CollatzResearch.WordTrace tailWord_2742980 prefixEnd_2742980 1408467165669783311835271 := by
  unfold tailWord_2742980
  simp only [CollatzResearch.WordTrace]
  refine ⟨50022349801329699266405197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66696466401772932355206929 50022349801329699266405197)
  ·
    refine ⟨18758381175498637224901949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50022349801329699266405197 18758381175498637224901949)
    ·
      refine ⟨7034392940811988959338231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18758381175498637224901949 7034392940811988959338231)
      ·
        refine ⟨10551589411217983439007347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7034392940811988959338231 10551589411217983439007347)
        ·
          refine ⟨15827384116826975158511021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10551589411217983439007347 15827384116826975158511021)
          ·
            refine ⟨5935269043810115684441633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15827384116826975158511021 5935269043810115684441633)
            ·
              refine ⟨4451451782857586763331225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5935269043810115684441633 4451451782857586763331225)
              ·
                refine ⟨3338588837143190072498419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4451451782857586763331225 3338588837143190072498419)
                ·
                  refine ⟨5007883255714785108747629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3338588837143190072498419 5007883255714785108747629)
                  ·
                    refine ⟨1877956220893044415780361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5007883255714785108747629 1877956220893044415780361)
                    ·
                      refine ⟨1408467165669783311835271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1877956220893044415780361 1408467165669783311835271)
                      ·
                        rfl

theorem cell23_2742980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_2742980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2742980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2742980 prefixEnd_2742980 := by exact prefixLift 2742980
  have htrace : WordTrace (prefixWord ++ tailWord_2742980) baseStart_2742980 baseEnd_2742980 := by
    simpa [prefixWord, tailWord_2742980, baseEnd_2742980] using wordTrace_append hprefix tailTrace_2742980
  have hstable : (prefixWord ++ tailWord_2742980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742980).length < 2 ^ (prefixWord ++ tailWord_2742980).sum := by decide
  have hdescent : baseEnd_2742980 < baseStart_2742980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743049 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 1, 3, 4]
def baseStart_2743049 : Nat := 118140960795 + 2743049 * 2 ^ 59
def prefixEnd_2743049 : Nat := 4983230072969 + 3 ^ 40 * 2743049 * 2
def baseEnd_2743049 : Nat := 1408502595834943541872453

theorem tailTrace_2743049 : CollatzResearch.WordTrace tailWord_2743049 prefixEnd_2743049 1408502595834943541872453 := by
  unfold tailWord_2743049
  simp only [CollatzResearch.WordTrace]
  refine ⟨100047216239409423317072201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66698144159606282211381467 100047216239409423317072201)
  ·
    refine ⟨75035412179557067487804151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100047216239409423317072201 75035412179557067487804151)
    ·
      refine ⟨112553118269335601231706227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75035412179557067487804151 112553118269335601231706227)
      ·
        refine ⟨168829677404003401847559341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112553118269335601231706227 168829677404003401847559341)
        ·
          refine ⟨63311129026501275692834753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168829677404003401847559341 63311129026501275692834753)
          ·
            refine ⟨47483346769875956769626065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63311129026501275692834753 47483346769875956769626065)
            ·
              refine ⟨35612510077406967577219549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47483346769875956769626065 35612510077406967577219549)
              ·
                refine ⟨13354691279027612841457331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35612510077406967577219549 13354691279027612841457331)
                ·
                  refine ⟨20032036918541419262185997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13354691279027612841457331 20032036918541419262185997)
                  ·
                    refine ⟨7512013844453032223319749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20032036918541419262185997 7512013844453032223319749)
                    ·
                      refine ⟨1408502595834943541872453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7512013844453032223319749 1408502595834943541872453)
                      ·
                        rfl

theorem cell23_2743049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_2743049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743049 prefixEnd_2743049 := by exact prefixLift 2743049
  have htrace : WordTrace (prefixWord ++ tailWord_2743049) baseStart_2743049 baseEnd_2743049 := by
    simpa [prefixWord, tailWord_2743049, baseEnd_2743049] using wordTrace_append hprefix tailTrace_2743049
  have hstable : (prefixWord ++ tailWord_2743049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743049).length < 2 ^ (prefixWord ++ tailWord_2743049).sum := by decide
  have hdescent : baseEnd_2743049 < baseStart_2743049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743066 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4]
def baseStart_2743066 : Nat := 118140960795 + 2743066 * 2 ^ 59
def prefixEnd_2743066 : Nat := 4983230072969 + 3 ^ 40 * 2743066 * 2
def baseEnd_2743066 : Nat := 1408511325006069975359875

theorem tailTrace_2743066 : CollatzResearch.WordTrace tailWord_2743066 prefixEnd_2743066 1408511325006069975359875 := by
  unfold tailWord_2743066
  simp only [CollatzResearch.WordTrace]
  refine ⟨25011959070086958805110263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66698557520231890146960701 25011959070086958805110263)
  ·
    refine ⟨37517938605130438207665395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25011959070086958805110263 37517938605130438207665395)
    ·
      refine ⟨56276907907695657311498093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37517938605130438207665395 56276907907695657311498093)
      ·
        refine ⟨21103840465385871491811785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56276907907695657311498093 21103840465385871491811785)
        ·
          refine ⟨15827880349039403618858839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21103840465385871491811785 15827880349039403618858839)
          ·
            refine ⟨23741820523559105428288259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15827880349039403618858839 23741820523559105428288259)
            ·
              refine ⟨35612730785338658142432389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23741820523559105428288259 35612730785338658142432389)
              ·
                refine ⟨6677387022250998401706073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35612730785338658142432389 6677387022250998401706073)
                ·
                  refine ⟨5008040266688248801279555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6677387022250998401706073 5008040266688248801279555)
                  ·
                    refine ⟨7512060400032373201919333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5008040266688248801279555 7512060400032373201919333)
                    ·
                      refine ⟨1408511325006069975359875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7512060400032373201919333 1408511325006069975359875)
                      ·
                        rfl

theorem cell23_2743066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_2743066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743066 prefixEnd_2743066 := by exact prefixLift 2743066
  have htrace : WordTrace (prefixWord ++ tailWord_2743066) baseStart_2743066 baseEnd_2743066 := by
    simpa [prefixWord, tailWord_2743066, baseEnd_2743066] using wordTrace_append hprefix tailTrace_2743066
  have hstable : (prefixWord ++ tailWord_2743066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743066).length < 2 ^ (prefixWord ++ tailWord_2743066).sum := by decide
  have hdescent : baseEnd_2743066 < baseStart_2743066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743093 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 3, 4]
def baseStart_2743093 : Nat := 118140960795 + 2743093 * 2 ^ 59
def prefixEnd_2743093 : Nat := 4983230072969 + 3 ^ 40 * 2743093 * 2
def baseEnd_2743093 : Nat := 469508396327913789907417

theorem tailTrace_2743093 : CollatzResearch.WordTrace tailWord_2743093 prefixEnd_2743093 469508396327913789907417 := by
  unfold tailWord_2743093
  simp only [CollatzResearch.WordTrace]
  refine ⟨100048821051250018831673933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66699214034166679221115955 100048821051250018831673933)
  ·
    refine ⟨37518307894218757061877725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100048821051250018831673933 37518307894218757061877725)
    ·
      refine ⟨14069365460332033898204147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37518307894218757061877725 14069365460332033898204147)
      ·
        refine ⟨21104048190498050847306221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14069365460332033898204147 21104048190498050847306221)
        ·
          refine ⟨7914018071436769067739833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21104048190498050847306221 7914018071436769067739833)
          ·
            refine ⟨5935513553577576800804875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7914018071436769067739833 5935513553577576800804875)
            ·
              refine ⟨8903270330366365201207313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5935513553577576800804875 8903270330366365201207313)
              ·
                refine ⟨6677452747774773900905485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8903270330366365201207313 6677452747774773900905485)
                ·
                  refine ⟨2504044780415540212839557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6677452747774773900905485 2504044780415540212839557)
                  ·
                    refine ⟨469508396327913789907417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2504044780415540212839557 469508396327913789907417)
                    ·
                      rfl

theorem cell23_2743093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_2743093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743093 prefixEnd_2743093 := by exact prefixLift 2743093
  have htrace : WordTrace (prefixWord ++ tailWord_2743093) baseStart_2743093 baseEnd_2743093 := by
    simpa [prefixWord, tailWord_2743093, baseEnd_2743093] using wordTrace_append hprefix tailTrace_2743093
  have hstable : (prefixWord ++ tailWord_2743093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743093).length < 2 ^ (prefixWord ++ tailWord_2743093).sum := by decide
  have hdescent : baseEnd_2743093 < baseStart_2743093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743103 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 3]
def baseStart_2743103 : Nat := 118140960795 + 2743103 * 2 ^ 59
def prefixEnd_2743103 : Nat := 4983230072969 + 3 ^ 40 * 2743103 * 2
def baseEnd_2743103 : Nat := 1408530323790286330597205

theorem tailTrace_2743103 : CollatzResearch.WordTrace tailWord_2743103 prefixEnd_2743103 1408530323790286330597205 := by
  unfold tailWord_2743103
  simp only [CollatzResearch.WordTrace]
  refine ⟨100049185781213790539537963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66699457187475860359691975 100049185781213790539537963)
  ·
    refine ⟨150073778671820685809306945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100049185781213790539537963 150073778671820685809306945)
    ·
      refine ⟨112555334003865514356980209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150073778671820685809306945 112555334003865514356980209)
      ·
        refine ⟨84416500502899135767735157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112555334003865514356980209 84416500502899135767735157)
        ·
          refine ⟨7914046922146793978225171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84416500502899135767735157 7914046922146793978225171)
          ·
            refine ⟨11871070383220190967337757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7914046922146793978225171 11871070383220190967337757)
            ·
              refine ⟨4451651393707571612751659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11871070383220190967337757 4451651393707571612751659)
              ·
                refine ⟨6677477090561357419127489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4451651393707571612751659 6677477090561357419127489)
                ·
                  refine ⟨5008107817921018064345617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6677477090561357419127489 5008107817921018064345617)
                  ·
                    refine ⟨3756080863440763548259213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5008107817921018064345617 3756080863440763548259213)
                    ·
                      refine ⟨1408530323790286330597205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3756080863440763548259213 1408530323790286330597205)
                      ·
                        rfl

theorem cell23_2743103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_2743103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743103 prefixEnd_2743103 := by exact prefixLift 2743103
  have htrace : WordTrace (prefixWord ++ tailWord_2743103) baseStart_2743103 baseEnd_2743103 := by
    simpa [prefixWord, tailWord_2743103, baseEnd_2743103] using wordTrace_append hprefix tailTrace_2743103
  have hstable : (prefixWord ++ tailWord_2743103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743103).length < 2 ^ (prefixWord ++ tailWord_2743103).sum := by decide
  have hdescent : baseEnd_2743103 < baseStart_2743103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743143 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 1, 5, 2]
def baseStart_2743143 : Nat := 118140960795 + 2743143 * 2 ^ 59
def prefixEnd_2743143 : Nat := 4983230072969 + 3 ^ 40 * 2743143 * 2
def baseEnd_2743143 : Nat := 1408550863016466174097021

theorem tailTrace_2743143 : CollatzResearch.WordTrace tailWord_2743143 prefixEnd_2743143 1408550863016466174097021 := by
  unfold tailWord_2743143
  simp only [CollatzResearch.WordTrace]
  refine ⟨100050644701068877370994083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66700429800712584913996055 100050644701068877370994083)
  ·
    refine ⟨150075967051603316056491125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100050644701068877370994083 150075967051603316056491125)
    ·
      refine ⟨14069621911087810880296043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150075967051603316056491125 14069621911087810880296043)
      ·
        refine ⟨21104432866631716320444065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14069621911087810880296043 21104432866631716320444065)
        ·
          refine ⟨15828324649973787240333049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21104432866631716320444065 15828324649973787240333049)
          ·
            refine ⟨11871243487480340430249787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15828324649973787240333049 11871243487480340430249787)
            ·
              refine ⟨17806865231220510645374681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11871243487480340430249787 17806865231220510645374681)
              ·
                refine ⟨13355148923415382984031011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17806865231220510645374681 13355148923415382984031011)
                ·
                  refine ⟨20032723385123074476046517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13355148923415382984031011 20032723385123074476046517)
                  ·
                    refine ⟨1878067817355288232129361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20032723385123074476046517 1878067817355288232129361)
                    ·
                      refine ⟨1408550863016466174097021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1878067817355288232129361 1408550863016466174097021)
                      ·
                        rfl

theorem cell23_2743143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_2743143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743143 prefixEnd_2743143 := by exact prefixLift 2743143
  have htrace : WordTrace (prefixWord ++ tailWord_2743143) baseStart_2743143 baseEnd_2743143 := by
    simpa [prefixWord, tailWord_2743143, baseEnd_2743143] using wordTrace_append hprefix tailTrace_2743143
  have hstable : (prefixWord ++ tailWord_2743143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743143).length < 2 ^ (prefixWord ++ tailWord_2743143).sum := by decide
  have hdescent : baseEnd_2743143 < baseStart_2743143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743153 : List Nat := [1, 2, 2, 2, 1, 5, 2, 2, 1, 5]
def baseStart_2743153 : Nat := 118140960795 + 2743153 * 2 ^ 59
def prefixEnd_2743153 : Nat := 4983230072969 + 3 ^ 40 * 2743153 * 2
def baseEnd_2743153 : Nat := 469518665941003711657325

theorem tailTrace_2743153 : CollatzResearch.WordTrace tailWord_2743153 prefixEnd_2743153 469518665941003711657325 := by
  unfold tailWord_2743153
  simp only [CollatzResearch.WordTrace]
  refine ⟨100051009431032649078858113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66700672954021766052572075 100051009431032649078858113)
  ·
    refine ⟨75038257073274486809143585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100051009431032649078858113 75038257073274486809143585)
    ·
      refine ⟨56278692804955865106857689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75038257073274486809143585 56278692804955865106857689)
      ·
        refine ⟨42209019603716898830143267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56278692804955865106857689 42209019603716898830143267)
        ·
          refine ⟨63313529405575348245214901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42209019603716898830143267 63313529405575348245214901)
          ·
            refine ⟨5935643381772688897988897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63313529405575348245214901 5935643381772688897988897)
            ·
              refine ⟨4451732536329516673491673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5935643381772688897988897 4451732536329516673491673)
              ·
                refine ⟨3338799402247137505118755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4451732536329516673491673 3338799402247137505118755)
                ·
                  refine ⟨5008199103370706257678133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3338799402247137505118755 5008199103370706257678133)
                  ·
                    refine ⟨469518665941003711657325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5008199103370706257678133 469518665941003711657325)
                    ·
                      rfl

theorem cell23_2743153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_2743153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743153 prefixEnd_2743153 := by exact prefixLift 2743153
  have htrace : WordTrace (prefixWord ++ tailWord_2743153) baseStart_2743153 baseEnd_2743153 := by
    simpa [prefixWord, tailWord_2743153, baseEnd_2743153] using wordTrace_append hprefix tailTrace_2743153
  have hstable : (prefixWord ++ tailWord_2743153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743153).length < 2 ^ (prefixWord ++ tailWord_2743153).sum := by decide
  have hdescent : baseEnd_2743153 < baseStart_2743153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743173 : List Nat := [1, 3, 1, 1, 3, 3, 2, 3, 1, 1, 4]
def baseStart_2743173 : Nat := 118140960795 + 2743173 * 2 ^ 59
def prefixEnd_2743173 : Nat := 4983230072969 + 3 ^ 40 * 2743173 * 2
def baseEnd_2743173 : Nat := 1408566267436101056721883

theorem tailTrace_2743173 : CollatzResearch.WordTrace tailWord_2743173 prefixEnd_2743173 1408566267436101056721883 := by
  unfold tailWord_2743173
  simp only [CollatzResearch.WordTrace]
  refine ⟨100051738890960192494586173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66701159260640128329724115 100051738890960192494586173)
  ·
    refine ⟨37519402084110072185469815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100051738890960192494586173 37519402084110072185469815)
    ·
      refine ⟨56279103126165108278204723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37519402084110072185469815 56279103126165108278204723)
      ·
        refine ⟨84418654689247662417307085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56279103126165108278204723 84418654689247662417307085)
        ·
          refine ⟨31656995508467873406490157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84418654689247662417307085 31656995508467873406490157)
          ·
            refine ⟨11871373315675452527433809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31656995508467873406490157 11871373315675452527433809)
            ·
              refine ⟨8903529986756589395575357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11871373315675452527433809 8903529986756589395575357)
              ·
                refine ⟨3338823745033721023340759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8903529986756589395575357 3338823745033721023340759)
                ·
                  refine ⟨5008235617550581535011139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3338823745033721023340759 5008235617550581535011139)
                  ·
                    refine ⟨7512353426325872302516709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5008235617550581535011139 7512353426325872302516709)
                    ·
                      refine ⟨1408566267436101056721883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7512353426325872302516709 1408566267436101056721883)
                      ·
                        rfl

theorem cell23_2743173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_2743173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743173 prefixEnd_2743173 := by exact prefixLift 2743173
  have htrace : WordTrace (prefixWord ++ tailWord_2743173) baseStart_2743173 baseEnd_2743173 := by
    simpa [prefixWord, tailWord_2743173, baseEnd_2743173] using wordTrace_append hprefix tailTrace_2743173
  have hstable : (prefixWord ++ tailWord_2743173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743173).length < 2 ^ (prefixWord ++ tailWord_2743173).sum := by decide
  have hdescent : baseEnd_2743173 < baseStart_2743173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743179 : List Nat := [1, 1, 1, 1, 4, 2, 13]
def baseStart_2743179 : Nat := 118140960795 + 2743179 * 2 ^ 59
def prefixEnd_2743179 : Nat := 4983230072969 + 3 ^ 40 * 2743179 * 2
def baseEnd_2743179 : Nat := 17389745040988000410455

theorem tailTrace_2743179 : CollatzResearch.WordTrace tailWord_2743179 prefixEnd_2743179 17389745040988000410455 := by
  unfold tailWord_2743179
  simp only [CollatzResearch.WordTrace]
  refine ⟨100051957728938455519304591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66701305152625637012869727 100051957728938455519304591)
  ·
    refine ⟨150077936593407683278956887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100051957728938455519304591 150077936593407683278956887)
    ·
      refine ⟨225116904890111524918435331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150077936593407683278956887 225116904890111524918435331)
      ·
        refine ⟨337675357335167287377652997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225116904890111524918435331 337675357335167287377652997)
        ·
          refine ⟨63314129500343866383309937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 337675357335167287377652997 63314129500343866383309937)
          ·
            refine ⟨47485597125257899787482453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63314129500343866383309937 47485597125257899787482453)
            ·
              refine ⟨17389745040988000410455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 47485597125257899787482453 17389745040988000410455)
              ·
                rfl

theorem cell23_2743179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 13].length) (baseStart_2743179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743179 prefixEnd_2743179 := by exact prefixLift 2743179
  have htrace : WordTrace (prefixWord ++ tailWord_2743179) baseStart_2743179 baseEnd_2743179 := by
    simpa [prefixWord, tailWord_2743179, baseEnd_2743179] using wordTrace_append hprefix tailTrace_2743179
  have hstable : (prefixWord ++ tailWord_2743179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743179).length < 2 ^ (prefixWord ++ tailWord_2743179).sum := by decide
  have hdescent : baseEnd_2743179 < baseStart_2743179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743200 : List Nat := [2, 1, 1, 4, 1, 1, 6, 1, 2, 4]
def baseStart_2743200 : Nat := 118140960795 + 2743200 * 2 ^ 59
def prefixEnd_2743200 : Nat := 4983230072969 + 3 ^ 40 * 2743200 * 2
def baseEnd_2743200 : Nat := 469526710471257483694753

theorem tailTrace_2743200 : CollatzResearch.WordTrace tailWord_2743200 prefixEnd_2743200 469526710471257483694753 := by
  unfold tailWord_2743200
  simp only [CollatzResearch.WordTrace]
  refine ⟨50026361830931188052909527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66701815774574917403879369 50026361830931188052909527)
  ·
    refine ⟨75039542746396782079364291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50026361830931188052909527 75039542746396782079364291)
    ·
      refine ⟨112559314119595173119046437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75039542746396782079364291 112559314119595173119046437)
      ·
        refine ⟨21104871397424094959821207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112559314119595173119046437 21104871397424094959821207)
        ·
          refine ⟨31657307096136142439731811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21104871397424094959821207 31657307096136142439731811)
          ·
            refine ⟨47485960644204213659597717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31657307096136142439731811 47485960644204213659597717)
            ·
              refine ⟨2225904405197072515293643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47485960644204213659597717 2225904405197072515293643)
              ·
                refine ⟨3338856607795608772940465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2225904405197072515293643 3338856607795608772940465)
                ·
                  refine ⟨2504142455846706579705349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3338856607795608772940465 2504142455846706579705349)
                  ·
                    refine ⟨469526710471257483694753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2504142455846706579705349 469526710471257483694753)
                    ·
                      rfl

theorem cell23_2743200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 2, 4].length) (baseStart_2743200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743200 prefixEnd_2743200 := by exact prefixLift 2743200
  have htrace : WordTrace (prefixWord ++ tailWord_2743200) baseStart_2743200 baseEnd_2743200 := by
    simpa [prefixWord, tailWord_2743200, baseEnd_2743200] using wordTrace_append hprefix tailTrace_2743200
  have hstable : (prefixWord ++ tailWord_2743200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743200).length < 2 ^ (prefixWord ++ tailWord_2743200).sum := by decide
  have hdescent : baseEnd_2743200 < baseStart_2743200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743207 : List Nat := [1, 1, 6, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_2743207 : Nat := 118140960795 + 2743207 * 2 ^ 59
def prefixEnd_2743207 : Nat := 4983230072969 + 3 ^ 40 * 2743207 * 2
def baseEnd_2743207 : Nat := 1408583725778353923696727

theorem tailTrace_2743207 : CollatzResearch.WordTrace tailWord_2743207 prefixEnd_2743207 1408583725778353923696727 := by
  unfold tailWord_2743207
  simp only [CollatzResearch.WordTrace]
  refine ⟨100052978972837016301323875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66701985981891344200882583 100052978972837016301323875)
  ·
    refine ⟨150079468459255524451985813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100052978972837016301323875 150079468459255524451985813)
    ·
      refine ⟨7034975084027602708686835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 150079468459255524451985813 7034975084027602708686835)
      ·
        refine ⟨10552462626041404063030253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7034975084027602708686835 10552462626041404063030253)
        ·
          refine ⟨3957173484765526523636345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10552462626041404063030253 3957173484765526523636345)
          ·
            refine ⟨2967880113574144892727259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3957173484765526523636345 2967880113574144892727259)
            ·
              refine ⟨4451820170361217339090889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2967880113574144892727259 4451820170361217339090889)
              ·
                refine ⟨3338865127770913004318167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4451820170361217339090889 3338865127770913004318167)
                ·
                  refine ⟨5008297691656369506477251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3338865127770913004318167 5008297691656369506477251)
                  ·
                    refine ⟨7512446537484554259715877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5008297691656369506477251 7512446537484554259715877)
                    ·
                      refine ⟨1408583725778353923696727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7512446537484554259715877 1408583725778353923696727)
                      ·
                        rfl

theorem cell23_2743207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_2743207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743207 prefixEnd_2743207 := by exact prefixLift 2743207
  have htrace : WordTrace (prefixWord ++ tailWord_2743207) baseStart_2743207 baseEnd_2743207 := by
    simpa [prefixWord, tailWord_2743207, baseEnd_2743207] using wordTrace_append hprefix tailTrace_2743207
  have hstable : (prefixWord ++ tailWord_2743207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743207).length < 2 ^ (prefixWord ++ tailWord_2743207).sum := by decide
  have hdescent : baseEnd_2743207 < baseStart_2743207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743220 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2743220 : Nat := 118140960795 + 2743220 * 2 ^ 59
def prefixEnd_2743220 : Nat := 4983230072969 + 3 ^ 40 * 2743220 * 2
def baseEnd_2743220 : Nat := 1408590401026862372834167

theorem tailTrace_2743220 : CollatzResearch.WordTrace tailWord_2743220 prefixEnd_2743220 1408590401026862372834167 := by
  unfold tailWord_2743220
  simp only [CollatzResearch.WordTrace]
  refine ⟨50026726560894959760773557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66702302081193279681031409 50026726560894959760773557)
  ·
    refine ⟨4690005615083902477572521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50026726560894959760773557 4690005615083902477572521)
    ·
      refine ⟨3517504211312926858179391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4690005615083902477572521 3517504211312926858179391)
      ·
        refine ⟨5276256316969390287269087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3517504211312926858179391 5276256316969390287269087)
        ·
          refine ⟨7914384475454085430903631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5276256316969390287269087 7914384475454085430903631)
          ·
            refine ⟨11871576713181128146355447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7914384475454085430903631 11871576713181128146355447)
            ·
              refine ⟨17807365069771692219533171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11871576713181128146355447 17807365069771692219533171)
              ·
                refine ⟨26711047604657538329299757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17807365069771692219533171 26711047604657538329299757)
                ·
                  refine ⟨10016642851746576873487409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26711047604657538329299757 10016642851746576873487409)
                  ·
                    refine ⟨7512482138809932655115557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10016642851746576873487409 7512482138809932655115557)
                    ·
                      refine ⟨1408590401026862372834167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7512482138809932655115557 1408590401026862372834167)
                      ·
                        rfl

theorem cell23_2743220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2743220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743220 prefixEnd_2743220 := by exact prefixLift 2743220
  have htrace : WordTrace (prefixWord ++ tailWord_2743220) baseStart_2743220 baseEnd_2743220 := by
    simpa [prefixWord, tailWord_2743220, baseEnd_2743220] using wordTrace_append hprefix tailTrace_2743220
  have hstable : (prefixWord ++ tailWord_2743220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743220).length < 2 ^ (prefixWord ++ tailWord_2743220).sum := by decide
  have hdescent : baseEnd_2743220 < baseStart_2743220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743223 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 6, 1, 3]
def baseStart_2743223 : Nat := 118140960795 + 2743223 * 2 ^ 59
def prefixEnd_2743223 : Nat := 4983230072969 + 3 ^ 40 * 2743223 * 2
def baseEnd_2743223 : Nat := 1408591941468825861096653

theorem tailTrace_2743223 : CollatzResearch.WordTrace tailWord_2743223 prefixEnd_2743223 1408591941468825861096653 := by
  unfold tailWord_2743223
  simp only [CollatzResearch.WordTrace]
  refine ⟨100053562540779051033906323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66702375027186034022604215 100053562540779051033906323)
  ·
    refine ⟨150080343811168576550859485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100053562540779051033906323 150080343811168576550859485)
    ·
      refine ⟨56280128929188216206572307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150080343811168576550859485 56280128929188216206572307)
      ·
        refine ⟨84420193393782324309858461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56280128929188216206572307 84420193393782324309858461)
        ·
          refine ⟨31657572522668371616196923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84420193393782324309858461 31657572522668371616196923)
          ·
            refine ⟨47486358784002557424295385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31657572522668371616196923 47486358784002557424295385)
            ·
              refine ⟨35614769088001918068221539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47486358784002557424295385 35614769088001918068221539)
              ·
                refine ⟨53422153632002877102332309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35614769088001918068221539 53422153632002877102332309)
                ·
                  refine ⟨2504163451500134864171827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53422153632002877102332309 2504163451500134864171827)
                  ·
                    refine ⟨3756245177250202296257741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2504163451500134864171827 3756245177250202296257741)
                    ·
                      refine ⟨1408591941468825861096653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3756245177250202296257741 1408591941468825861096653)
                      ·
                        rfl

theorem cell23_2743223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 1, 3].length) (baseStart_2743223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743223 prefixEnd_2743223 := by exact prefixLift 2743223
  have htrace : WordTrace (prefixWord ++ tailWord_2743223) baseStart_2743223 baseEnd_2743223 := by
    simpa [prefixWord, tailWord_2743223, baseEnd_2743223] using wordTrace_append hprefix tailTrace_2743223
  have hstable : (prefixWord ++ tailWord_2743223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743223).length < 2 ^ (prefixWord ++ tailWord_2743223).sum := by decide
  have hdescent : baseEnd_2743223 < baseStart_2743223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743256 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 1, 8]
def baseStart_2743256 : Nat := 118140960795 + 2743256 * 2 ^ 59
def prefixEnd_2743256 : Nat := 4983230072969 + 3 ^ 40 * 2743256 * 2
def baseEnd_2743256 : Nat := 469536295443474743994667

theorem tailTrace_2743256 : CollatzResearch.WordTrace tailWord_2743256 prefixEnd_2743256 469536295443474743994667 := by
  unfold tailWord_2743256
  simp only [CollatzResearch.WordTrace]
  refine ⟨50027383074829748834928811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66703177433106331779905081 50027383074829748834928811)
  ·
    refine ⟨75041074612244623252393217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50027383074829748834928811 75041074612244623252393217)
    ·
      refine ⟨56280805959183467439294913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75041074612244623252393217 56280805959183467439294913)
      ·
        refine ⟨42210604469387600579471185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56280805959183467439294913 42210604469387600579471185)
        ·
          refine ⟨31657953352040700434603389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42210604469387600579471185 31657953352040700434603389)
          ·
            refine ⟨11871732507015262662976271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31657953352040700434603389 11871732507015262662976271)
            ·
              refine ⟨17807598760522893994464407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11871732507015262662976271 17807598760522893994464407)
              ·
                refine ⟨26711398140784340991696611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17807598760522893994464407 26711398140784340991696611)
                ·
                  refine ⟨40067097211176511487544917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26711398140784340991696611 40067097211176511487544917)
                  ·
                    refine ⟨469536295443474743994667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40067097211176511487544917 469536295443474743994667)
                    ·
                      rfl

theorem cell23_2743256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_2743256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743256 prefixEnd_2743256 := by exact prefixLift 2743256
  have htrace : WordTrace (prefixWord ++ tailWord_2743256) baseStart_2743256 baseEnd_2743256 := by
    simpa [prefixWord, tailWord_2743256, baseEnd_2743256] using wordTrace_append hprefix tailTrace_2743256
  have hstable : (prefixWord ++ tailWord_2743256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743256).length < 2 ^ (prefixWord ++ tailWord_2743256).sum := by decide
  have hdescent : baseEnd_2743256 < baseStart_2743256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743280 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 4, 2, 2]
def baseStart_2743280 : Nat := 118140960795 + 2743280 * 2 ^ 59
def prefixEnd_2743280 : Nat := 4983230072969 + 3 ^ 40 * 2743280 * 2
def baseEnd_2743280 : Nat := 1408621209866132138083891

theorem tailTrace_2743280 : CollatzResearch.WordTrace tailWord_2743280 prefixEnd_2743280 1408621209866132138083891 := by
  unfold tailWord_2743280
  simp only [CollatzResearch.WordTrace]
  refine ⟨50027820750786274884365647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66703761001048366512487529 50027820750786274884365647)
  ·
    refine ⟨75041731126179412326548471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50027820750786274884365647 75041731126179412326548471)
    ·
      refine ⟨112562596689269118489822707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75041731126179412326548471 112562596689269118489822707)
      ·
        refine ⟨168843895033903677734734061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112562596689269118489822707 168843895033903677734734061)
        ·
          refine ⟨63316460637713879150525273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168843895033903677734734061 63316460637713879150525273)
          ·
            refine ⟨47487345478285409362893955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63316460637713879150525273 47487345478285409362893955)
            ·
              refine ⟨71231018217428114044340933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47487345478285409362893955 71231018217428114044340933)
              ·
                refine ⟨13355815915767771383313925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71231018217428114044340933 13355815915767771383313925)
                ·
                  refine ⟨2504215484206457134371361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13355815915767771383313925 2504215484206457134371361)
                  ·
                    refine ⟨1878161613154842850778521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2504215484206457134371361 1878161613154842850778521)
                    ·
                      refine ⟨1408621209866132138083891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1878161613154842850778521 1408621209866132138083891)
                      ·
                        rfl

theorem cell23_2743280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 4, 2, 2].length) (baseStart_2743280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743280 prefixEnd_2743280 := by exact prefixLift 2743280
  have htrace : WordTrace (prefixWord ++ tailWord_2743280) baseStart_2743280 baseEnd_2743280 := by
    simpa [prefixWord, tailWord_2743280, baseEnd_2743280] using wordTrace_append hprefix tailTrace_2743280
  have hstable : (prefixWord ++ tailWord_2743280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743280).length < 2 ^ (prefixWord ++ tailWord_2743280).sum := by decide
  have hdescent : baseEnd_2743280 < baseStart_2743280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743297 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 4, 2, 2]
def baseStart_2743297 : Nat := 118140960795 + 2743297 * 2 ^ 59
def prefixEnd_2743297 : Nat := 4983230072969 + 3 ^ 40 * 2743297 * 2
def baseEnd_2743297 : Nat := 1408629939037258571571313

theorem tailTrace_2743297 : CollatzResearch.WordTrace tailWord_2743297 prefixEnd_2743297 1408629939037258571571313 := by
  unfold tailWord_2743297
  simp only [CollatzResearch.WordTrace]
  refine ⟨100056261542510961672100145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66704174361673974448066763 100056261542510961672100145)
  ·
    refine ⟨75042196156883221254075109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100056261542510961672100145 75042196156883221254075109)
    ·
      refine ⟨14070411779415603985139083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75042196156883221254075109 14070411779415603985139083)
      ·
        refine ⟨21105617669123405977708625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14070411779415603985139083 21105617669123405977708625)
        ·
          refine ⟨15829213251842554483281469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21105617669123405977708625 15829213251842554483281469)
          ·
            refine ⟨5935954969440957931230551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15829213251842554483281469 5935954969440957931230551)
            ·
              refine ⟨8903932454161436896845827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5935954969440957931230551 8903932454161436896845827)
              ·
                refine ⟨13355898681242155345268741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8903932454161436896845827 13355898681242155345268741)
                ·
                  refine ⟨2504231002732904127237889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13355898681242155345268741 2504231002732904127237889)
                  ·
                    refine ⟨1878173252049678095428417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2504231002732904127237889 1878173252049678095428417)
                    ·
                      refine ⟨1408629939037258571571313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1878173252049678095428417 1408629939037258571571313)
                      ·
                        rfl

theorem cell23_2743297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_2743297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743297 prefixEnd_2743297 := by exact prefixLift 2743297
  have htrace : WordTrace (prefixWord ++ tailWord_2743297) baseStart_2743297 baseEnd_2743297 := by
    simpa [prefixWord, tailWord_2743297, baseEnd_2743297] using wordTrace_append hprefix tailTrace_2743297
  have hstable : (prefixWord ++ tailWord_2743297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743297).length < 2 ^ (prefixWord ++ tailWord_2743297).sum := by decide
  have hdescent : baseEnd_2743297 < baseStart_2743297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743303 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 7]
def baseStart_2743303 : Nat := 118140960795 + 2743303 * 2 ^ 59
def prefixEnd_2743303 : Nat := 4983230072969 + 3 ^ 40 * 2743303 * 2
def baseEnd_2743303 : Nat := 156514779991242838677365

theorem tailTrace_2743303 : CollatzResearch.WordTrace tailWord_2743303 prefixEnd_2743303 156514779991242838677365 := by
  unfold tailWord_2743303
  simp only [CollatzResearch.WordTrace]
  refine ⟨100056480380489224696818563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66704320253659483131212375 100056480380489224696818563)
  ·
    refine ⟨150084720570733837045227845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100056480380489224696818563 150084720570733837045227845)
    ·
      refine ⟨28140885107012594445980221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150084720570733837045227845 28140885107012594445980221)
      ·
        refine ⟨10552831915129722917242583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28140885107012594445980221 10552831915129722917242583)
        ·
          refine ⟨15829247872694584375863875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10552831915129722917242583 15829247872694584375863875)
          ·
            refine ⟨23743871809041876563795813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15829247872694584375863875 23743871809041876563795813)
            ·
              refine ⟨4451975964195351855711715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23743871809041876563795813 4451975964195351855711715)
              ·
                refine ⟨6677963946293027783567573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4451975964195351855711715 6677963946293027783567573)
                ·
                  refine ⟨156514779991242838677365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6677963946293027783567573 156514779991242838677365)
                  ·
                    rfl

theorem cell23_2743303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 7].length) (baseStart_2743303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743303 prefixEnd_2743303 := by exact prefixLift 2743303
  have htrace : WordTrace (prefixWord ++ tailWord_2743303) baseStart_2743303 baseEnd_2743303 := by
    simpa [prefixWord, tailWord_2743303, baseEnd_2743303] using wordTrace_append hprefix tailTrace_2743303
  have hstable : (prefixWord ++ tailWord_2743303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743303).length < 2 ^ (prefixWord ++ tailWord_2743303).sum := by decide
  have hdescent : baseEnd_2743303 < baseStart_2743303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743323 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 3, 7, 2]
def baseStart_2743323 : Nat := 118140960795 + 2743323 * 2 ^ 59
def prefixEnd_2743323 : Nat := 4983230072969 + 3 ^ 40 * 2743323 * 2
def baseEnd_2743323 : Nat := 1408643289534275469846193

theorem tailTrace_2743323 : CollatzResearch.WordTrace tailWord_2743323 prefixEnd_2743323 1408643289534275469846193 := by
  unfold tailWord_2743323
  simp only [CollatzResearch.WordTrace]
  refine ⟨100057209840416768112546623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66704806560277845408364415 100057209840416768112546623)
  ·
    refine ⟨150085814760625152168819935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100057209840416768112546623 150085814760625152168819935)
    ·
      refine ⟨225128722140937728253229903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150085814760625152168819935 225128722140937728253229903)
      ·
        refine ⟨337693083211406592379844855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225128722140937728253229903 337693083211406592379844855)
        ·
          refine ⟨506539624817109888569767283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337693083211406592379844855 506539624817109888569767283)
          ·
            refine ⟨759809437225664832854650925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506539624817109888569767283 759809437225664832854650925)
            ·
              refine ⟨284928538959624312320494097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 759809437225664832854650925 284928538959624312320494097)
              ·
                refine ⟨213696404219718234240370573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284928538959624312320494097 213696404219718234240370573)
                ·
                  refine ⟨80136151582394337840138965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213696404219718234240370573 80136151582394337840138965)
                  ·
                    refine ⟨1878191052712367293128257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 80136151582394337840138965 1878191052712367293128257)
                    ·
                      refine ⟨1408643289534275469846193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1878191052712367293128257 1408643289534275469846193)
                      ·
                        rfl

theorem cell23_2743323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 7, 2].length) (baseStart_2743323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743323 prefixEnd_2743323 := by exact prefixLift 2743323
  have htrace : WordTrace (prefixWord ++ tailWord_2743323) baseStart_2743323 baseEnd_2743323 := by
    simpa [prefixWord, tailWord_2743323, baseEnd_2743323] using wordTrace_append hprefix tailTrace_2743323
  have hstable : (prefixWord ++ tailWord_2743323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743323).length < 2 ^ (prefixWord ++ tailWord_2743323).sum := by decide
  have hdescent : baseEnd_2743323 < baseStart_2743323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743333 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 2, 5]
def baseStart_2743333 : Nat := 118140960795 + 2743333 * 2 ^ 59
def prefixEnd_2743333 : Nat := 4983230072969 + 3 ^ 40 * 2743333 * 2
def baseEnd_2743333 : Nat := 469549474780273476907049

theorem tailTrace_2743333 : CollatzResearch.WordTrace tailWord_2743333 prefixEnd_2743333 469549474780273476907049 := by
  unfold tailWord_2743333
  simp only [CollatzResearch.WordTrace]
  refine ⟨100057574570380539820410653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66705049713587026546940435 100057574570380539820410653)
  ·
    refine ⟨37521590463892702432653995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100057574570380539820410653 37521590463892702432653995)
    ·
      refine ⟨56282385695839053648980993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37521590463892702432653995 56282385695839053648980993)
      ·
        refine ⟨42211789271879290236735745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56282385695839053648980993 42211789271879290236735745)
        ·
          refine ⟨31658841953909467677551809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42211789271879290236735745 31658841953909467677551809)
          ·
            refine ⟨23744131465432100758163857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31658841953909467677551809 23744131465432100758163857)
            ·
              refine ⟨17808098599074075568622893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23744131465432100758163857 17808098599074075568622893)
              ·
                refine ⟨6678036974652778338233585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17808098599074075568622893 6678036974652778338233585)
                ·
                  refine ⟨5008527730989583753675189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6678036974652778338233585 5008527730989583753675189)
                  ·
                    refine ⟨469549474780273476907049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5008527730989583753675189 469549474780273476907049)
                    ·
                      rfl

theorem cell23_2743333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_2743333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743333 prefixEnd_2743333 := by exact prefixLift 2743333
  have htrace : WordTrace (prefixWord ++ tailWord_2743333) baseStart_2743333 baseEnd_2743333 := by
    simpa [prefixWord, tailWord_2743333, baseEnd_2743333] using wordTrace_append hprefix tailTrace_2743333
  have hstable : (prefixWord ++ tailWord_2743333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743333).length < 2 ^ (prefixWord ++ tailWord_2743333).sum := by decide
  have hdescent : baseEnd_2743333 < baseStart_2743333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743350 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_2743350 : Nat := 118140960795 + 2743350 * 2 ^ 59
def prefixEnd_2743350 : Nat := 4983230072969 + 3 ^ 40 * 2743350 * 2
def baseEnd_2743350 : Nat := 469552384503982288069523

theorem tailTrace_2743350 : CollatzResearch.WordTrace tailWord_2743350 prefixEnd_2743350 469552384503982288069523 := by
  unfold tailWord_2743350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6253637163207434482736219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66705463074212634482519669 6253637163207434482736219)
  ·
    refine ⟨9380455744811151724104329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6253637163207434482736219 9380455744811151724104329)
    ·
      refine ⟨7035341808608363793078247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9380455744811151724104329 7035341808608363793078247)
      ·
        refine ⟨10553012712912545689617371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7035341808608363793078247 10553012712912545689617371)
        ·
          refine ⟨15829519069368818534426057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10553012712912545689617371 15829519069368818534426057)
          ·
            refine ⟨11872139302026613900819543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15829519069368818534426057 11872139302026613900819543)
            ·
              refine ⟨17808208953039920851229315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11872139302026613900819543 17808208953039920851229315)
              ·
                refine ⟨26712313429559881276843973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17808208953039920851229315 26712313429559881276843973)
                ·
                  refine ⟨5008558768042477739408245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26712313429559881276843973 5008558768042477739408245)
                  ·
                    refine ⟨469552384503982288069523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5008558768042477739408245 469552384503982288069523)
                    ·
                      rfl

theorem cell23_2743350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_2743350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743350 prefixEnd_2743350 := by exact prefixLift 2743350
  have htrace : WordTrace (prefixWord ++ tailWord_2743350) baseStart_2743350 baseEnd_2743350 := by
    simpa [prefixWord, tailWord_2743350, baseEnd_2743350] using wordTrace_append hprefix tailTrace_2743350
  have hstable : (prefixWord ++ tailWord_2743350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743350).length < 2 ^ (prefixWord ++ tailWord_2743350).sum := by decide
  have hdescent : baseEnd_2743350 < baseStart_2743350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743370 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 2, 4, 2]
def baseStart_2743370 : Nat := 118140960795 + 2743370 * 2 ^ 59
def prefixEnd_2743370 : Nat := 4983230072969 + 3 ^ 40 * 2743370 * 2
def baseEnd_2743370 : Nat := 1408667423125036785958477

theorem tailTrace_2743370 : CollatzResearch.WordTrace tailWord_2743370 prefixEnd_2743370 1408667423125036785958477 := by
  unfold tailWord_2743370
  simp only [CollatzResearch.WordTrace]
  refine ⟨25014731017811623784876891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66705949380830996759671709 25014731017811623784876891)
  ·
    refine ⟨37522096526717435677315337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25014731017811623784876891 37522096526717435677315337)
    ·
      refine ⟨28141572395038076757986503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37522096526717435677315337 28141572395038076757986503)
      ·
        refine ⟨42212358592557115136979755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28141572395038076757986503 42212358592557115136979755)
        ·
          refine ⟨63318537888835672705469633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42212358592557115136979755 63318537888835672705469633)
          ·
            refine ⟨47488903416626754529102225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63318537888835672705469633 47488903416626754529102225)
            ·
              refine ⟨35616677562470065896826669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47488903416626754529102225 35616677562470065896826669)
              ·
                refine ⟨13356254085926274711310001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35616677562470065896826669 13356254085926274711310001)
                ·
                  refine ⟨10017190564444706033482501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13356254085926274711310001 10017190564444706033482501)
                  ·
                    refine ⟨1878223230833382381277969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10017190564444706033482501 1878223230833382381277969)
                    ·
                      refine ⟨1408667423125036785958477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1878223230833382381277969 1408667423125036785958477)
                      ·
                        rfl

theorem cell23_2743370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_2743370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743370 prefixEnd_2743370 := by exact prefixLift 2743370
  have htrace : WordTrace (prefixWord ++ tailWord_2743370) baseStart_2743370 baseEnd_2743370 := by
    simpa [prefixWord, tailWord_2743370, baseEnd_2743370] using wordTrace_append hprefix tailTrace_2743370
  have hstable : (prefixWord ++ tailWord_2743370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743370).length < 2 ^ (prefixWord ++ tailWord_2743370).sum := by decide
  have hdescent : baseEnd_2743370 < baseStart_2743370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743380 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_2743380 : Nat := 118140960795 + 2743380 * 2 ^ 59
def prefixEnd_2743380 : Nat := 4983230072969 + 3 ^ 40 * 2743380 * 2
def baseEnd_2743380 : Nat := 469557519310527248944477

theorem tailTrace_2743380 : CollatzResearch.WordTrace tailWord_2743380 prefixEnd_2743380 469557519310527248944477 := by
  unfold tailWord_2743380
  simp only [CollatzResearch.WordTrace]
  refine ⟨50029644400605133423685797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66706192534140177898247729 50029644400605133423685797)
  ·
    refine ⟨9380558325113462516941087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50029644400605133423685797 9380558325113462516941087)
    ·
      refine ⟨14070837487670193775411631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9380558325113462516941087 14070837487670193775411631)
      ·
        refine ⟨21106256231505290663117447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14070837487670193775411631 21106256231505290663117447)
        ·
          refine ⟨31659384347257935994676171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21106256231505290663117447 31659384347257935994676171)
          ·
            refine ⟨47489076520886903992014257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31659384347257935994676171 47489076520886903992014257)
            ·
              refine ⟨35616807390665177994010693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47489076520886903992014257 35616807390665177994010693)
              ·
                refine ⟨6678151385749720873877005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35616807390665177994010693 6678151385749720873877005)
                ·
                  refine ⟨2504306769656145327703877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6678151385749720873877005 2504306769656145327703877)
                  ·
                    refine ⟨469557519310527248944477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2504306769656145327703877 469557519310527248944477)
                    ·
                      rfl

theorem cell23_2743380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_2743380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743380 prefixEnd_2743380 := by exact prefixLift 2743380
  have htrace : WordTrace (prefixWord ++ tailWord_2743380) baseStart_2743380 baseEnd_2743380 := by
    simpa [prefixWord, tailWord_2743380, baseEnd_2743380] using wordTrace_append hprefix tailTrace_2743380
  have hstable : (prefixWord ++ tailWord_2743380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743380).length < 2 ^ (prefixWord ++ tailWord_2743380).sum := by decide
  have hdescent : baseEnd_2743380 < baseStart_2743380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743397 : List Nat := [1, 3, 1, 3, 2, 1, 2, 5, 1, 4]
def baseStart_2743397 : Nat := 118140960795 + 2743397 * 2 ^ 59
def prefixEnd_2743397 : Nat := 4983230072969 + 3 ^ 40 * 2743397 * 2
def baseEnd_2743397 : Nat := 469560429034236060106951

theorem tailTrace_2743397 : CollatzResearch.WordTrace tailWord_2743397 prefixEnd_2743397 469560429034236060106951 := by
  unfold tailWord_2743397
  simp only [CollatzResearch.WordTrace]
  refine ⟨100059908842148678750740445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66706605894765785833826963 100059908842148678750740445)
  ·
    refine ⟨37522465815805754531527667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100059908842148678750740445 37522465815805754531527667)
    ·
      refine ⟨56283698723708631797291501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37522465815805754531527667 56283698723708631797291501)
      ·
        refine ⟨21106387021390736923984313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56283698723708631797291501 21106387021390736923984313)
        ·
          refine ⟨15829790266043052692988235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21106387021390736923984313 15829790266043052692988235)
          ·
            refine ⟨23744685399064579039482353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15829790266043052692988235 23744685399064579039482353)
            ·
              refine ⟨17808514049298434279611765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23744685399064579039482353 17808514049298434279611765)
              ·
                refine ⟨1669548192121728213713603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17808514049298434279611765 1669548192121728213713603)
                ·
                  refine ⟨2504322288182592320570405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669548192121728213713603 2504322288182592320570405)
                  ·
                    refine ⟨469560429034236060106951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2504322288182592320570405 469560429034236060106951)
                    ·
                      rfl

theorem cell23_2743397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 1, 4].length) (baseStart_2743397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743397 prefixEnd_2743397 := by exact prefixLift 2743397
  have htrace : WordTrace (prefixWord ++ tailWord_2743397) baseStart_2743397 baseEnd_2743397 := by
    simpa [prefixWord, tailWord_2743397, baseEnd_2743397] using wordTrace_append hprefix tailTrace_2743397
  have hstable : (prefixWord ++ tailWord_2743397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743397).length < 2 ^ (prefixWord ++ tailWord_2743397).sum := by decide
  have hdescent : baseEnd_2743397 < baseStart_2743397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743410 : List Nat := [3, 2, 1, 2, 2, 1, 4, 2, 6]
def baseStart_2743410 : Nat := 118140960795 + 2743410 * 2 ^ 59
def prefixEnd_2743410 : Nat := 4983230072969 + 3 ^ 40 * 2743410 * 2
def baseEnd_2743410 : Nat := 156520884705690736606477

theorem tailTrace_2743410 : CollatzResearch.WordTrace tailWord_2743410 prefixEnd_2743410 156520884705690736606477 := by
  unfold tailWord_2743410
  simp only [CollatzResearch.WordTrace]
  refine ⟨25015095747775395492740921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66706921994067721313975789 25015095747775395492740921)
  ·
    refine ⟨18761321810831546619555691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25015095747775395492740921 18761321810831546619555691)
    ·
      refine ⟨28141982716247319929333537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18761321810831546619555691 28141982716247319929333537)
      ·
        refine ⟨21106487037185489947000153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28141982716247319929333537 21106487037185489947000153)
        ·
          refine ⟨15829865277889117460250115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21106487037185489947000153 15829865277889117460250115)
          ·
            refine ⟨23744797916833676190375173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15829865277889117460250115 23744797916833676190375173)
            ·
              refine ⟨4452149609406314285695345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23744797916833676190375173 4452149609406314285695345)
              ·
                refine ⟨3339112207054735714271509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4452149609406314285695345 3339112207054735714271509)
                ·
                  refine ⟨156520884705690736606477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3339112207054735714271509 156520884705690736606477)
                  ·
                    rfl

theorem cell23_2743410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_2743410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743410 prefixEnd_2743410 := by exact prefixLift 2743410
  have htrace : WordTrace (prefixWord ++ tailWord_2743410) baseStart_2743410 baseEnd_2743410 := by
    simpa [prefixWord, tailWord_2743410, baseEnd_2743410] using wordTrace_append hprefix tailTrace_2743410
  have hstable : (prefixWord ++ tailWord_2743410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743410).length < 2 ^ (prefixWord ++ tailWord_2743410).sum := by decide
  have hdescent : baseEnd_2743410 < baseStart_2743410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743414 : List Nat := [5, 1, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_2743414 : Nat := 118140960795 + 2743414 * 2 ^ 59
def prefixEnd_2743414 : Nat := 4983230072969 + 3 ^ 40 * 2743414 * 2
def baseEnd_2743414 : Nat := 469563338757944871269425

theorem tailTrace_2743414 : CollatzResearch.WordTrace tailWord_2743414 prefixEnd_2743414 469563338757944871269425 := by
  unfold tailWord_2743414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6253783055192943165881831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66707019255391393769406197 6253783055192943165881831)
  ·
    refine ⟨9380674582789414748822747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6253783055192943165881831 9380674582789414748822747)
    ·
      refine ⟨14071011874184122123234121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9380674582789414748822747 14071011874184122123234121)
      ·
        refine ⟨10553258905638091592425591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14071011874184122123234121 10553258905638091592425591)
        ·
          refine ⟨15829888358457137388638387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10553258905638091592425591 15829888358457137388638387)
          ·
            refine ⟨23744832537685706082957581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15829888358457137388638387 23744832537685706082957581)
            ·
              refine ⟨8904312201632139781109093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23744832537685706082957581 8904312201632139781109093)
              ·
                refine ⟨1669558537806026208957955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8904312201632139781109093 1669558537806026208957955)
                ·
                  refine ⟨2504337806709039313436933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669558537806026208957955 2504337806709039313436933)
                  ·
                    refine ⟨469563338757944871269425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2504337806709039313436933 469563338757944871269425)
                    ·
                      rfl

theorem cell23_2743414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_2743414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743414 prefixEnd_2743414 := by exact prefixLift 2743414
  have htrace : WordTrace (prefixWord ++ tailWord_2743414) baseStart_2743414 baseEnd_2743414 := by
    simpa [prefixWord, tailWord_2743414, baseEnd_2743414] using wordTrace_append hprefix tailTrace_2743414
  have hstable : (prefixWord ++ tailWord_2743414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743414).length < 2 ^ (prefixWord ++ tailWord_2743414).sum := by decide
  have hdescent : baseEnd_2743414 < baseStart_2743414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743447 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 1, 5, 2]
def baseStart_2743447 : Nat := 118140960795 + 2743447 * 2 ^ 59
def prefixEnd_2743447 : Nat := 4983230072969 + 3 ^ 40 * 2743447 * 2
def baseEnd_2743447 : Nat := 1408706961135432984695623

theorem tailTrace_2743447 : CollatzResearch.WordTrace tailWord_2743447 prefixEnd_2743447 1408706961135432984695623 := by
  unfold tailWord_2743447
  simp only [CollatzResearch.WordTrace]
  refine ⟨100061732491967537290060595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66707821661311691526707063 100061732491967537290060595)
  ·
    refine ⟨150092598737951305935090893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100061732491967537290060595 150092598737951305935090893)
    ·
      refine ⟨56284724526731739725659085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150092598737951305935090893 56284724526731739725659085)
      ·
        refine ⟨21106771697524402397122157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56284724526731739725659085 21106771697524402397122157)
        ·
          refine ⟨7915039386571650898920809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21106771697524402397122157 7915039386571650898920809)
          ·
            refine ⟨5936279539928738174190607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7915039386571650898920809 5936279539928738174190607)
            ·
              refine ⟨8904419309893107261285911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5936279539928738174190607 8904419309893107261285911)
              ·
                refine ⟨13356628964839660891928867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8904419309893107261285911 13356628964839660891928867)
                ·
                  refine ⟨20034943447259491337893301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13356628964839660891928867 20034943447259491337893301)
                  ·
                    refine ⟨1878275948180577312927497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20034943447259491337893301 1878275948180577312927497)
                    ·
                      refine ⟨1408706961135432984695623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1878275948180577312927497 1408706961135432984695623)
                      ·
                        rfl

theorem cell23_2743447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_2743447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743447 prefixEnd_2743447 := by exact prefixLift 2743447
  have htrace : WordTrace (prefixWord ++ tailWord_2743447) baseStart_2743447 baseEnd_2743447 := by
    simpa [prefixWord, tailWord_2743447, baseEnd_2743447] using wordTrace_append hprefix tailTrace_2743447
  have hstable : (prefixWord ++ tailWord_2743447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743447).length < 2 ^ (prefixWord ++ tailWord_2743447).sum := by decide
  have hdescent : baseEnd_2743447 < baseStart_2743447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743480 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 3, 2, 3]
def baseStart_2743480 : Nat := 118140960795 + 2743480 * 2 ^ 59
def prefixEnd_2743480 : Nat := 4983230072969 + 3 ^ 40 * 2743480 * 2
def baseEnd_2743480 : Nat := 1408723905997031355582971

theorem tailTrace_2743480 : CollatzResearch.WordTrace tailWord_2743480 prefixEnd_2743480 1408723905997031355582971 := by
  unfold tailWord_2743480
  simp only [CollatzResearch.WordTrace]
  refine ⟨50031468050423991963005947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66708624067231989284007929 50031468050423991963005947)
  ·
    refine ⟨75047202075635987944508921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50031468050423991963005947 75047202075635987944508921)
    ·
      refine ⟨56285401556726990958381691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75047202075635987944508921 56285401556726990958381691)
      ·
        refine ⟨84428102335090486437572537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56285401556726990958381691 84428102335090486437572537)
        ·
          refine ⟨63321076751317864828179403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84428102335090486437572537 63321076751317864828179403)
          ·
            refine ⟨94981615126976797242269105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63321076751317864828179403 94981615126976797242269105)
            ·
              refine ⟨71236211345232597931701829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94981615126976797242269105 71236211345232597931701829)
              ·
                refine ⟨13356789627231112112194093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71236211345232597931701829 13356789627231112112194093)
                ·
                  refine ⟨5008796110211667042072785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13356789627231112112194093 5008796110211667042072785)
                  ·
                    refine ⟨3756597082658750281554589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5008796110211667042072785 3756597082658750281554589)
                    ·
                      refine ⟨1408723905997031355582971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3756597082658750281554589 1408723905997031355582971)
                      ·
                        rfl

theorem cell23_2743480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_2743480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743480 prefixEnd_2743480 := by exact prefixLift 2743480
  have htrace : WordTrace (prefixWord ++ tailWord_2743480) baseStart_2743480 baseEnd_2743480 := by
    simpa [prefixWord, tailWord_2743480, baseEnd_2743480] using wordTrace_append hprefix tailTrace_2743480
  have hstable : (prefixWord ++ tailWord_2743480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743480).length < 2 ^ (prefixWord ++ tailWord_2743480).sum := by decide
  have hdescent : baseEnd_2743480 < baseStart_2743480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743511 : List Nat := [1, 1, 3, 2, 1, 2, 5, 3, 1, 2, 2]
def baseStart_2743511 : Nat := 118140960795 + 2743511 * 2 ^ 59
def prefixEnd_2743511 : Nat := 4983230072969 + 3 ^ 40 * 2743511 * 2
def baseEnd_2743511 : Nat := 1408739823897320734295329

theorem tailTrace_2743511 : CollatzResearch.WordTrace tailWord_2743511 prefixEnd_2743511 1408739823897320734295329 := by
  unfold tailWord_2743511
  simp only [CollatzResearch.WordTrace]
  refine ⟨100064066763735676220390387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66709377842490450813593591 100064066763735676220390387)
  ·
    refine ⟨150096100145603514330585581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100064066763735676220390387 150096100145603514330585581)
    ·
      refine ⟨56286037554601317873969593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150096100145603514330585581 56286037554601317873969593)
      ·
        refine ⟨42214528165950988405477195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56286037554601317873969593 42214528165950988405477195)
        ·
          refine ⟨63321792248926482608215793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42214528165950988405477195 63321792248926482608215793)
          ·
            refine ⟨47491344186694861956161845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63321792248926482608215793 47491344186694861956161845)
            ·
              refine ⟨4452313517502643308390173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47491344186694861956161845 4452313517502643308390173)
              ·
                refine ⟨1669617569063491240646315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4452313517502643308390173 1669617569063491240646315)
                ·
                  refine ⟨2504426353595236860969473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669617569063491240646315 2504426353595236860969473)
                  ·
                    refine ⟨1878319765196427645727105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2504426353595236860969473 1878319765196427645727105)
                    ·
                      refine ⟨1408739823897320734295329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1878319765196427645727105 1408739823897320734295329)
                      ·
                        rfl

theorem cell23_2743511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_2743511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743511 prefixEnd_2743511 := by exact prefixLift 2743511
  have htrace : WordTrace (prefixWord ++ tailWord_2743511) baseStart_2743511 baseEnd_2743511 := by
    simpa [prefixWord, tailWord_2743511, baseEnd_2743511] using wordTrace_append hprefix tailTrace_2743511
  have hstable : (prefixWord ++ tailWord_2743511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743511).length < 2 ^ (prefixWord ++ tailWord_2743511).sum := by decide
  have hdescent : baseEnd_2743511 < baseStart_2743511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743513 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 1, 9]
def baseStart_2743513 : Nat := 118140960795 + 2743513 * 2 ^ 59
def prefixEnd_2743513 : Nat := 4983230072969 + 3 ^ 40 * 2743513 * 2
def baseEnd_2743513 : Nat := 469580283619543242156773

theorem tailTrace_2743513 : CollatzResearch.WordTrace tailWord_2743513 prefixEnd_2743513 469580283619543242156773 := by
  unfold tailWord_2743513
  simp only [CollatzResearch.WordTrace]
  refine ⟨100064139709728430561963193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66709426473152287041308795 100064139709728430561963193)
  ·
    refine ⟨75048104782296322921472395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100064139709728430561963193 75048104782296322921472395)
    ·
      refine ⟨112572157173444484382208593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75048104782296322921472395 112572157173444484382208593)
      ·
        refine ⟨84429117880083363286656445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112572157173444484382208593 84429117880083363286656445)
        ·
          refine ⟨31660919205031261232496167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84429117880083363286656445 31660919205031261232496167)
          ·
            refine ⟨47491378807546891848744251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31660919205031261232496167 47491378807546891848744251)
            ·
              refine ⟨71237068211320337773116377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47491378807546891848744251 71237068211320337773116377)
              ·
                refine ⟨53427801158490253329837283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71237068211320337773116377 53427801158490253329837283)
                ·
                  refine ⟨80141701737735379994755925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53427801158490253329837283 80141701737735379994755925)
                  ·
                    refine ⟨469580283619543242156773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 80141701737735379994755925 469580283619543242156773)
                    ·
                      rfl

theorem cell23_2743513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 9].length) (baseStart_2743513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743513 prefixEnd_2743513 := by exact prefixLift 2743513
  have htrace : WordTrace (prefixWord ++ tailWord_2743513) baseStart_2743513 baseEnd_2743513 := by
    simpa [prefixWord, tailWord_2743513, baseEnd_2743513] using wordTrace_append hprefix tailTrace_2743513
  have hstable : (prefixWord ++ tailWord_2743513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743513).length < 2 ^ (prefixWord ++ tailWord_2743513).sum := by decide
  have hdescent : baseEnd_2743513 < baseStart_2743513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743517 : List Nat := [1, 4, 3, 2, 2, 2, 9]
def baseStart_2743517 : Nat := 118140960795 + 2743517 * 2 ^ 59
def prefixEnd_2743517 : Nat := 4983230072969 + 3 ^ 40 * 2743517 * 2
def baseEnd_2743517 : Nat := 17391887713348737170621

theorem tailTrace_2743517 : CollatzResearch.WordTrace tailWord_2743517 prefixEnd_2743517 17391887713348737170621 := by
  unfold tailWord_2743517
  simp only [CollatzResearch.WordTrace]
  refine ⟨100064285601713939245108805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66709523734475959496739203 100064285601713939245108805)
  ·
    refine ⟨18762053550321363608457901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100064285601713939245108805 18762053550321363608457901)
    ·
      refine ⟨7035770081370511353171713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18762053550321363608457901 7035770081370511353171713)
      ·
        refine ⟨5276827561027883514878785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7035770081370511353171713 5276827561027883514878785)
        ·
          refine ⟨3957620670770912636159089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5276827561027883514878785 3957620670770912636159089)
          ·
            refine ⟨2968215503078184477119317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3957620670770912636159089 2968215503078184477119317)
            ·
              refine ⟨17391887713348737170621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2968215503078184477119317 17391887713348737170621)
              ·
                rfl

theorem cell23_2743517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 9].length) (baseStart_2743517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743517 prefixEnd_2743517 := by exact prefixLift 2743517
  have htrace : WordTrace (prefixWord ++ tailWord_2743517) baseStart_2743517 baseEnd_2743517 := by
    simpa [prefixWord, tailWord_2743517, baseEnd_2743517] using wordTrace_append hprefix tailTrace_2743517
  have hstable : (prefixWord ++ tailWord_2743517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743517).length < 2 ^ (prefixWord ++ tailWord_2743517).sum := by decide
  have hdescent : baseEnd_2743517 < baseStart_2743517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743528 : List Nat := [2, 1, 4, 1, 2, 1, 5, 2, 1, 2, 2]
def baseStart_2743528 : Nat := 118140960795 + 2743528 * 2 ^ 59
def prefixEnd_2743528 : Nat := 4983230072969 + 3 ^ 40 * 2743528 * 2
def baseEnd_2743528 : Nat := 1408748553068447167782751

theorem tailTrace_2743528 : CollatzResearch.WordTrace tailWord_2743528 prefixEnd_2743528 1408748553068447167782751 := by
  unfold tailWord_2743528
  simp only [CollatzResearch.WordTrace]
  refine ⟨50032343402337044061879619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66709791203116058749172825 50032343402337044061879619)
  ·
    refine ⟨75048515103505566092819429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50032343402337044061879619 75048515103505566092819429)
    ·
      refine ⟨14071596581907293642403643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75048515103505566092819429 14071596581907293642403643)
      ·
        refine ⟨21107394872860940463605465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14071596581907293642403643 21107394872860940463605465)
        ·
          refine ⟨15830546154645705347704099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21107394872860940463605465 15830546154645705347704099)
          ·
            refine ⟨23745819231968558021556149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15830546154645705347704099 23745819231968558021556149)
            ·
              refine ⟨2226170552997052314520889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23745819231968558021556149 2226170552997052314520889)
              ·
                refine ⟨1669627914747789235890667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2226170552997052314520889 1669627914747789235890667)
                ·
                  refine ⟨2504441872121683853836001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669627914747789235890667 2504441872121683853836001)
                  ·
                    refine ⟨1878331404091262890377001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2504441872121683853836001 1878331404091262890377001)
                    ·
                      refine ⟨1408748553068447167782751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1878331404091262890377001 1408748553068447167782751)
                      ·
                        rfl

theorem cell23_2743528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_2743528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743528 prefixEnd_2743528 := by exact prefixLift 2743528
  have htrace : WordTrace (prefixWord ++ tailWord_2743528) baseStart_2743528 baseEnd_2743528 := by
    simpa [prefixWord, tailWord_2743528, baseEnd_2743528] using wordTrace_append hprefix tailTrace_2743528
  have hstable : (prefixWord ++ tailWord_2743528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743528).length < 2 ^ (prefixWord ++ tailWord_2743528).sum := by decide
  have hdescent : baseEnd_2743528 < baseStart_2743528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743537 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 3, 3, 2]
def baseStart_2743537 : Nat := 118140960795 + 2743537 * 2 ^ 59
def prefixEnd_2743537 : Nat := 4983230072969 + 3 ^ 40 * 2743537 * 2
def baseEnd_2743537 : Nat := 1408753174394337632570209

theorem tailTrace_2743537 : CollatzResearch.WordTrace tailWord_2743537 prefixEnd_2743537 1408753174394337632570209 := by
  unfold tailWord_2743537
  simp only [CollatzResearch.WordTrace]
  refine ⟨100065015061641482660836865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66710010041094321773891243 100065015061641482660836865)
  ·
    refine ⟨75048761296231111995627649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100065015061641482660836865 75048761296231111995627649)
    ·
      refine ⟨56286570972173333996720737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75048761296231111995627649 56286570972173333996720737)
      ·
        refine ⟨42214928229130000497540553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56286570972173333996720737 42214928229130000497540553)
        ·
          refine ⟨31661196171847500373155415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42214928229130000497540553 31661196171847500373155415)
          ·
            refine ⟨47491794257771250559733123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31661196171847500373155415 47491794257771250559733123)
            ·
              refine ⟨71237691386656875839599685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47491794257771250559733123 71237691386656875839599685)
              ·
                refine ⟨13357067134998164219924941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71237691386656875839599685 13357067134998164219924941)
                ·
                  refine ⟨5008900175624311582471853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13357067134998164219924941 5008900175624311582471853)
                  ·
                    refine ⟨1878337565859116843426945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5008900175624311582471853 1878337565859116843426945)
                    ·
                      refine ⟨1408753174394337632570209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1878337565859116843426945 1408753174394337632570209)
                      ·
                        rfl

theorem cell23_2743537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_2743537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743537 prefixEnd_2743537 := by exact prefixLift 2743537
  have htrace : WordTrace (prefixWord ++ tailWord_2743537) baseStart_2743537 baseEnd_2743537 := by
    simpa [prefixWord, tailWord_2743537, baseEnd_2743537] using wordTrace_append hprefix tailTrace_2743537
  have hstable : (prefixWord ++ tailWord_2743537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743537).length < 2 ^ (prefixWord ++ tailWord_2743537).sum := by decide
  have hdescent : baseEnd_2743537 < baseStart_2743537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743538 : List Nat := [3, 2, 1, 3, 4, 1, 2, 1, 2, 4]
def baseStart_2743538 : Nat := 118140960795 + 2743538 * 2 ^ 59
def prefixEnd_2743538 : Nat := 4983230072969 + 3 ^ 40 * 2743538 * 2
def baseEnd_2743538 : Nat := 469584562624997376219235

theorem tailTrace_2743538 : CollatzResearch.WordTrace tailWord_2743538 prefixEnd_2743538 469584562624997376219235 := by
  unfold tailWord_2743538
  simp only [CollatzResearch.WordTrace]
  refine ⟨25016262883659464957905817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66710034356425239887748845 25016262883659464957905817)
  ·
    refine ⟨18762197162744598718429363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25016262883659464957905817 18762197162744598718429363)
    ·
      refine ⟨28143295744116898077644045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18762197162744598718429363 28143295744116898077644045)
      ·
        refine ⟨10553735904043836779116517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28143295744116898077644045 10553735904043836779116517)
        ·
          refine ⟨1978825482008219396084347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10553735904043836779116517 1978825482008219396084347)
          ·
            refine ⟨2968238223012329094126521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1978825482008219396084347 2968238223012329094126521)
            ·
              refine ⟨2226178667259246820594891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2968238223012329094126521 2226178667259246820594891)
              ·
                refine ⟨3339268000888870230892337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2226178667259246820594891 3339268000888870230892337)
                ·
                  refine ⟨2504451000666652673169253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3339268000888870230892337 2504451000666652673169253)
                  ·
                    refine ⟨469584562624997376219235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2504451000666652673169253 469584562624997376219235)
                    ·
                      rfl

theorem cell23_2743538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_2743538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743538 prefixEnd_2743538 := by exact prefixLift 2743538
  have htrace : WordTrace (prefixWord ++ tailWord_2743538) baseStart_2743538 baseEnd_2743538 := by
    simpa [prefixWord, tailWord_2743538, baseEnd_2743538] using wordTrace_append hprefix tailTrace_2743538
  have hstable : (prefixWord ++ tailWord_2743538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743538).length < 2 ^ (prefixWord ++ tailWord_2743538).sum := by decide
  have hdescent : baseEnd_2743538 < baseStart_2743538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743601 : List Nat := [1, 2, 2, 3, 3, 1, 2, 3, 2, 2, 2]
def baseStart_2743601 : Nat := 118140960795 + 2743601 * 2 ^ 59
def prefixEnd_2743601 : Nat := 4983230072969 + 3 ^ 40 * 2743601 * 2
def baseEnd_2743601 : Nat := 1408786037156225382169915

theorem tailTrace_2743601 : CollatzResearch.WordTrace tailWord_2743601 prefixEnd_2743601 1408786037156225382169915 := by
  unfold tailWord_2743601
  simp only [CollatzResearch.WordTrace]
  refine ⟨100067349333409621591166657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66711566222273081060777771 100067349333409621591166657)
  ·
    refine ⟨75050512000057216193374993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100067349333409621591166657 75050512000057216193374993)
    ·
      refine ⟨56287884000042912145031245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75050512000057216193374993 56287884000042912145031245)
      ·
        refine ⟨21107956500016092054386717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56287884000042912145031245 21107956500016092054386717)
        ·
          refine ⟨7915483687506034520395019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21107956500016092054386717 7915483687506034520395019)
          ·
            refine ⟨11873225531259051780592529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7915483687506034520395019 11873225531259051780592529)
            ·
              refine ⟨8904919148444288835444397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11873225531259051780592529 8904919148444288835444397)
              ·
                refine ⟨3339344680666608313291649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8904919148444288835444397 3339344680666608313291649)
                ·
                  refine ⟨2504508510499956234968737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3339344680666608313291649 2504508510499956234968737)
                  ·
                    refine ⟨1878381382874967176226553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2504508510499956234968737 1878381382874967176226553)
                    ·
                      refine ⟨1408786037156225382169915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1878381382874967176226553 1408786037156225382169915)
                      ·
                        rfl

theorem cell23_2743601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_2743601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743601 prefixEnd_2743601 := by exact prefixLift 2743601
  have htrace : WordTrace (prefixWord ++ tailWord_2743601) baseStart_2743601 baseEnd_2743601 := by
    simpa [prefixWord, tailWord_2743601, baseEnd_2743601] using wordTrace_append hprefix tailTrace_2743601
  have hstable : (prefixWord ++ tailWord_2743601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743601).length < 2 ^ (prefixWord ++ tailWord_2743601).sum := by decide
  have hdescent : baseEnd_2743601 < baseStart_2743601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743657 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 1, 6, 2]
def baseStart_2743657 : Nat := 118140960795 + 2743657 * 2 ^ 59
def prefixEnd_2743657 : Nat := 4983230072969 + 3 ^ 40 * 2743657 * 2
def baseEnd_2743657 : Nat := 1408814792072877163069657

theorem tailTrace_2743657 : CollatzResearch.WordTrace tailWord_2743657 prefixEnd_2743657 1408814792072877163069657 := by
  unfold tailWord_2743657
  simp only [CollatzResearch.WordTrace]
  refine ⟨100069391821206743155205225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66712927880804495436803483 100069391821206743155205225)
  ·
    refine ⟨75052043865905057366403919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100069391821206743155205225 75052043865905057366403919)
    ·
      refine ⟨112578065798857586049605879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75052043865905057366403919 112578065798857586049605879)
      ·
        refine ⟨168867098698286379074408819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112578065798857586049605879 168867098698286379074408819)
        ·
          refine ⟨253300648047429568611613229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168867098698286379074408819 253300648047429568611613229)
          ·
            refine ⟨94987743017786088229354961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253300648047429568611613229 94987743017786088229354961)
            ·
              refine ⟨71240807263339566172016221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94987743017786088229354961 71240807263339566172016221)
              ·
                refine ⟨26715302723752337314506083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71240807263339566172016221 26715302723752337314506083)
                ·
                  refine ⟨40072954085628505971759125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26715302723752337314506083 40072954085628505971759125)
                  ·
                    refine ⟨1878419722763836217426209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40072954085628505971759125 1878419722763836217426209)
                    ·
                      refine ⟨1408814792072877163069657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1878419722763836217426209 1408814792072877163069657)
                      ·
                        rfl

theorem cell23_2743657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 6, 2].length) (baseStart_2743657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743657 prefixEnd_2743657 := by exact prefixLift 2743657
  have htrace : WordTrace (prefixWord ++ tailWord_2743657) baseStart_2743657 baseEnd_2743657 := by
    simpa [prefixWord, tailWord_2743657, baseEnd_2743657] using wordTrace_append hprefix tailTrace_2743657
  have hstable : (prefixWord ++ tailWord_2743657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743657).length < 2 ^ (prefixWord ++ tailWord_2743657).sum := by decide
  have hdescent : baseEnd_2743657 < baseStart_2743657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743677 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 1, 4, 3]
def baseStart_2743677 : Nat := 118140960795 + 2743677 * 2 ^ 59
def prefixEnd_2743677 : Nat := 4983230072969 + 3 ^ 40 * 2743677 * 2
def baseEnd_2743677 : Nat := 1408825061685967084819565

theorem tailTrace_2743677 : CollatzResearch.WordTrace tailWord_2743677 prefixEnd_2743677 1408825061685967084819565 := by
  unfold tailWord_2743677
  simp only [CollatzResearch.WordTrace]
  refine ⟨100070121281134286570933285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66713414187422857713955523 100070121281134286570933285)
  ·
    refine ⟨18763147740212678732049991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100070121281134286570933285 18763147740212678732049991)
    ·
      refine ⟨28144721610319018098074987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18763147740212678732049991 28144721610319018098074987)
      ·
        refine ⟨42217082415478527147112481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28144721610319018098074987 42217082415478527147112481)
        ·
          refine ⟨31662811811608895360334361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42217082415478527147112481 31662811811608895360334361)
          ·
            refine ⟨23747108858706671520250771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31662811811608895360334361 23747108858706671520250771)
            ·
              refine ⟨35620663288060007280376157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23747108858706671520250771 35620663288060007280376157)
              ·
                refine ⟨13357748733022502730141059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35620663288060007280376157 13357748733022502730141059)
                ·
                  refine ⟨20036623099533754095211589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13357748733022502730141059 20036623099533754095211589)
                  ·
                    refine ⟨3756866831162578892852173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20036623099533754095211589 3756866831162578892852173)
                    ·
                      refine ⟨1408825061685967084819565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3756866831162578892852173 1408825061685967084819565)
                      ·
                        rfl

theorem cell23_2743677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_2743677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743677 prefixEnd_2743677 := by exact prefixLift 2743677
  have htrace : WordTrace (prefixWord ++ tailWord_2743677) baseStart_2743677 baseEnd_2743677 := by
    simpa [prefixWord, tailWord_2743677, baseEnd_2743677] using wordTrace_append hprefix tailTrace_2743677
  have hstable : (prefixWord ++ tailWord_2743677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743677).length < 2 ^ (prefixWord ++ tailWord_2743677).sum := by decide
  have hdescent : baseEnd_2743677 < baseStart_2743677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743714 : List Nat := [3, 3, 1, 2, 1, 3, 1, 3, 6]
def baseStart_2743714 : Nat := 118140960795 + 2743714 * 2 ^ 59
def prefixEnd_2743714 : Nat := 4983230072969 + 3 ^ 40 * 2743714 * 2
def baseEnd_2743714 : Nat := 156538228941131493339655

theorem tailTrace_2743714 : CollatzResearch.WordTrace tailWord_2743714 prefixEnd_2743714 156538228941131493339655 := by
  unfold tailWord_2743714
  simp only [CollatzResearch.WordTrace]
  refine ⟨25017867695500060472507549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66714313854666827926686797 25017867695500060472507549)
  ·
    refine ⟨9381700385812522677190331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25017867695500060472507549 9381700385812522677190331)
    ·
      refine ⟨14072550578718784015785497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9381700385812522677190331 14072550578718784015785497)
      ·
        refine ⟨10554412934039088011839123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14072550578718784015785497 10554412934039088011839123)
        ·
          refine ⟨15831619401058632017758685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10554412934039088011839123 15831619401058632017758685)
          ·
            refine ⟨5936857275396987006659507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15831619401058632017758685 5936857275396987006659507)
            ·
              refine ⟨8905285913095480509989261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5936857275396987006659507 8905285913095480509989261)
              ·
                refine ⟨3339482217410805191245973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8905285913095480509989261 3339482217410805191245973)
                ·
                  refine ⟨156538228941131493339655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3339482217410805191245973 156538228941131493339655)
                  ·
                    rfl

theorem cell23_2743714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_2743714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743714 prefixEnd_2743714 := by exact prefixLift 2743714
  have htrace : WordTrace (prefixWord ++ tailWord_2743714) baseStart_2743714 baseEnd_2743714 := by
    simpa [prefixWord, tailWord_2743714, baseEnd_2743714] using wordTrace_append hprefix tailTrace_2743714
  have hstable : (prefixWord ++ tailWord_2743714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743714).length < 2 ^ (prefixWord ++ tailWord_2743714).sum := by decide
  have hdescent : baseEnd_2743714 < baseStart_2743714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743724 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 3]
def baseStart_2743724 : Nat := 118140960795 + 2743724 * 2 ^ 59
def prefixEnd_2743724 : Nat := 4983230072969 + 3 ^ 40 * 2743724 * 2
def baseEnd_2743724 : Nat := 1408849195276728400931849

theorem tailTrace_2743724 : CollatzResearch.WordTrace tailWord_2743724 prefixEnd_2743724 1408849195276728400931849 := by
  unfold tailWord_2743724
  simp only [CollatzResearch.WordTrace]
  refine ⟨50035917755982006798947113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66714557007976009065262817 50035917755982006798947113)
  ·
    refine ⟨37526938316986505099210335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50035917755982006798947113 37526938316986505099210335)
    ·
      refine ⟨56290407475479757648815503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37526938316986505099210335 56290407475479757648815503)
      ·
        refine ⟨84435611213219636473223255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56290407475479757648815503 84435611213219636473223255)
        ·
          refine ⟨126653416819829454709834883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84435611213219636473223255 126653416819829454709834883)
          ·
            refine ⟨189980125229744182064752325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126653416819829454709834883 189980125229744182064752325)
            ·
              refine ⟨35621273480577034137141061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189980125229744182064752325 35621273480577034137141061)
              ·
                refine ⟨6678988777608193900713949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35621273480577034137141061 6678988777608193900713949)
                ·
                  refine ⟨2504620791603072712767731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6678988777608193900713949 2504620791603072712767731)
                  ·
                    refine ⟨3756931187404609069151597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2504620791603072712767731 3756931187404609069151597)
                    ·
                      refine ⟨1408849195276728400931849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3756931187404609069151597 1408849195276728400931849)
                      ·
                        rfl

theorem cell23_2743724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 3].length) (baseStart_2743724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743724 prefixEnd_2743724 := by exact prefixLift 2743724
  have htrace : WordTrace (prefixWord ++ tailWord_2743724) baseStart_2743724 baseEnd_2743724 := by
    simpa [prefixWord, tailWord_2743724, baseEnd_2743724] using wordTrace_append hprefix tailTrace_2743724
  have hstable : (prefixWord ++ tailWord_2743724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743724).length < 2 ^ (prefixWord ++ tailWord_2743724).sum := by decide
  have hdescent : baseEnd_2743724 < baseStart_2743724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743767 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 5]
def baseStart_2743767 : Nat := 118140960795 + 2743767 * 2 ^ 59
def prefixEnd_2743767 : Nat := 4983230072969 + 3 ^ 40 * 2743767 * 2
def baseEnd_2743767 : Nat := 1408871274944871732694151

theorem tailTrace_2743767 : CollatzResearch.WordTrace tailWord_2743767 prefixEnd_2743767 1408871274944871732694151 := by
  unfold tailWord_2743767
  simp only [CollatzResearch.WordTrace]
  refine ⟨100073403850808231941709555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66715602567205487961139703 100073403850808231941709555)
  ·
    refine ⟨150110105776212347912564333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100073403850808231941709555 150110105776212347912564333)
    ·
      refine ⟨56291289666079630467211625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150110105776212347912564333 56291289666079630467211625)
      ·
        refine ⟨42218467249559722850408719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56291289666079630467211625 42218467249559722850408719)
        ·
          refine ⟨63327700874339584275613079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42218467249559722850408719 63327700874339584275613079)
          ·
            refine ⟨94991551311509376413419619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63327700874339584275613079 94991551311509376413419619)
            ·
              refine ⟨142487326967264064620129429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94991551311509376413419619 142487326967264064620129429)
              ·
                refine ⟨6679093451590503029068567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142487326967264064620129429 6679093451590503029068567)
                ·
                  refine ⟨10018640177385754543602851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6679093451590503029068567 10018640177385754543602851)
                  ·
                    refine ⟨15027960266078631815404277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10018640177385754543602851 15027960266078631815404277)
                    ·
                      refine ⟨1408871274944871732694151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15027960266078631815404277 1408871274944871732694151)
                      ·
                        rfl

theorem cell23_2743767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_2743767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743767 prefixEnd_2743767 := by exact prefixLift 2743767
  have htrace : WordTrace (prefixWord ++ tailWord_2743767) baseStart_2743767 baseEnd_2743767 := by
    simpa [prefixWord, tailWord_2743767, baseEnd_2743767] using wordTrace_append hprefix tailTrace_2743767
  have hstable : (prefixWord ++ tailWord_2743767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743767).length < 2 ^ (prefixWord ++ tailWord_2743767).sum := by decide
  have hdescent : baseEnd_2743767 < baseStart_2743767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743784 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_2743784 : Nat := 118140960795 + 2743784 * 2 ^ 59
def prefixEnd_2743784 : Nat := 4983230072969 + 3 ^ 40 * 2743784 * 2
def baseEnd_2743784 : Nat := 1408880004115998166181573

theorem tailTrace_2743784 : CollatzResearch.WordTrace tailWord_2743784 prefixEnd_2743784 1408880004115998166181573 := by
  unfold tailWord_2743784
  simp only [CollatzResearch.WordTrace]
  refine ⟨50037011945873321922539203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66716015927831095896718937 50037011945873321922539203)
  ·
    refine ⟨75055517918809982883808805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50037011945873321922539203 75055517918809982883808805)
    ·
      refine ⟨14072909609776871790714151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75055517918809982883808805 14072909609776871790714151)
      ·
        refine ⟨21109364414665307686071227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14072909609776871790714151 21109364414665307686071227)
        ·
          refine ⟨31664046621997961529106841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21109364414665307686071227 31664046621997961529106841)
          ·
            refine ⟨23748034966498471146830131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31664046621997961529106841 23748034966498471146830131)
            ·
              refine ⟨35622052449747706720245197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23748034966498471146830131 35622052449747706720245197)
              ·
                refine ⟨13358269668655390020091949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35622052449747706720245197 13358269668655390020091949)
                ·
                  refine ⟨5009351125745771257534481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13358269668655390020091949 5009351125745771257534481)
                  ·
                    refine ⟨3757013344309328443150861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5009351125745771257534481 3757013344309328443150861)
                    ·
                      refine ⟨1408880004115998166181573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3757013344309328443150861 1408880004115998166181573)
                      ·
                        rfl

theorem cell23_2743784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_2743784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743784 prefixEnd_2743784 := by exact prefixLift 2743784
  have htrace : WordTrace (prefixWord ++ tailWord_2743784) baseStart_2743784 baseEnd_2743784 := by
    simpa [prefixWord, tailWord_2743784, baseEnd_2743784] using wordTrace_append hprefix tailTrace_2743784
  have hstable : (prefixWord ++ tailWord_2743784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743784).length < 2 ^ (prefixWord ++ tailWord_2743784).sum := by decide
  have hdescent : baseEnd_2743784 < baseStart_2743784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743798 : List Nat := [5, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4]
def baseStart_2743798 : Nat := 118140960795 + 2743798 * 2 ^ 59
def prefixEnd_2743798 : Nat := 4983230072969 + 3 ^ 40 * 2743798 * 2
def baseEnd_2743798 : Nat := 1408887192845161111406509

theorem tailTrace_2743798 : CollatzResearch.WordTrace tailWord_2743798 prefixEnd_2743798 1408887192845161111406509 := by
  unfold tailWord_2743798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6254658407105995264755503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66716356342463949490725365 6254658407105995264755503)
  ·
    refine ⟨9381987610658992897133255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6254658407105995264755503 9381987610658992897133255)
    ·
      refine ⟨14072981415988489345699883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9381987610658992897133255 14072981415988489345699883)
      ·
        refine ⟨21109472123982734018549825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14072981415988489345699883 21109472123982734018549825)
        ·
          refine ⟨15832104092987050513912369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21109472123982734018549825 15832104092987050513912369)
          ·
            refine ⟨11874078069740287885434277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15832104092987050513912369 11874078069740287885434277)
            ·
              refine ⟨2226389638076303978518927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11874078069740287885434277 2226389638076303978518927)
              ·
                refine ⟨3339584457114455967778391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2226389638076303978518927 3339584457114455967778391)
                ·
                  refine ⟨5009376685671683951667587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3339584457114455967778391 5009376685671683951667587)
                  ·
                    refine ⟨7514065028507525927501381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5009376685671683951667587 7514065028507525927501381)
                    ·
                      refine ⟨1408887192845161111406509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7514065028507525927501381 1408887192845161111406509)
                      ·
                        rfl

theorem cell23_2743798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_2743798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743798 prefixEnd_2743798 := by exact prefixLift 2743798
  have htrace : WordTrace (prefixWord ++ tailWord_2743798) baseStart_2743798 baseEnd_2743798 := by
    simpa [prefixWord, tailWord_2743798, baseEnd_2743798] using wordTrace_append hprefix tailTrace_2743798
  have hstable : (prefixWord ++ tailWord_2743798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743798).length < 2 ^ (prefixWord ++ tailWord_2743798).sum := by decide
  have hdescent : baseEnd_2743798 < baseStart_2743798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743815 : List Nat := [1, 1, 4, 3, 2, 1, 2, 4, 1, 2, 2]
def baseStart_2743815 : Nat := 118140960795 + 2743815 * 2 ^ 59
def prefixEnd_2743815 : Nat := 4983230072969 + 3 ^ 40 * 2743815 * 2
def baseEnd_2743815 : Nat := 1408895922016287544893931

theorem tailTrace_2743815 : CollatzResearch.WordTrace tailWord_2743815 prefixEnd_2743815 1408895922016287544893931 := by
  unfold tailWord_2743815
  simp only [CollatzResearch.WordTrace]
  refine ⟨100075154554634336139456899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66716769703089557426304599 100075154554634336139456899)
  ·
    refine ⟨150112731831951504209185349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100075154554634336139456899 150112731831951504209185349)
    ·
      refine ⟨28146137218490907039222253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150112731831951504209185349 28146137218490907039222253)
      ·
        refine ⟨10554801456934090139708345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28146137218490907039222253 10554801456934090139708345)
        ·
          refine ⟨7916101092700567604781259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10554801456934090139708345 7916101092700567604781259)
          ·
            refine ⟨11874151639050851407171889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7916101092700567604781259 11874151639050851407171889)
            ·
              refine ⟨8905613729288138555378917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11874151639050851407171889 8905613729288138555378917)
              ·
                refine ⟨1669802574241525979133547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8905613729288138555378917 1669802574241525979133547)
                ·
                  refine ⟨2504703861362288968700321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669802574241525979133547 2504703861362288968700321)
                  ·
                    refine ⟨1878527896021716726525241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2504703861362288968700321 1878527896021716726525241)
                    ·
                      refine ⟨1408895922016287544893931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1878527896021716726525241 1408895922016287544893931)
                      ·
                        rfl

theorem cell23_2743815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_2743815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743815 prefixEnd_2743815 := by exact prefixLift 2743815
  have htrace : WordTrace (prefixWord ++ tailWord_2743815) baseStart_2743815 baseEnd_2743815 := by
    simpa [prefixWord, tailWord_2743815, baseEnd_2743815] using wordTrace_append hprefix tailTrace_2743815
  have hstable : (prefixWord ++ tailWord_2743815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743815).length < 2 ^ (prefixWord ++ tailWord_2743815).sum := by decide
  have hdescent : baseEnd_2743815 < baseStart_2743815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743888 : List Nat := [2, 1, 1, 1, 1, 3, 5, 3, 2, 2, 2]
def baseStart_2743888 : Nat := 118140960795 + 2743888 * 2 ^ 59
def prefixEnd_2743888 : Nat := 4983230072969 + 3 ^ 40 * 2743888 * 2
def baseEnd_2743888 : Nat := 1408933406104065759281095

theorem tailTrace_2743888 : CollatzResearch.WordTrace tailWord_2743888 prefixEnd_2743888 1408933406104065759281095 := by
  unfold tailWord_2743888
  simp only [CollatzResearch.WordTrace]
  refine ⟨50038908541684934803432159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66718544722246579737909545 50038908541684934803432159)
  ·
    refine ⟨75058362812527402205148239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50038908541684934803432159 75058362812527402205148239)
    ·
      refine ⟨112587544218791103307722359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75058362812527402205148239 112587544218791103307722359)
      ·
        refine ⟨168881316328186654961583539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112587544218791103307722359 168881316328186654961583539)
        ·
          refine ⟨253321974492279982442375309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168881316328186654961583539 253321974492279982442375309)
          ·
            refine ⟨94995740434604993415890741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253321974492279982442375309 94995740434604993415890741)
            ·
              refine ⟨8905850665744218132739757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94995740434604993415890741 8905850665744218132739757)
              ·
                refine ⟨3339693999654081799777409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8905850665744218132739757 3339693999654081799777409)
                ·
                  refine ⟨2504770499740561349833057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3339693999654081799777409 2504770499740561349833057)
                  ·
                    refine ⟨1878577874805421012374793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2504770499740561349833057 1878577874805421012374793)
                    ·
                      refine ⟨1408933406104065759281095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1878577874805421012374793 1408933406104065759281095)
                      ·
                        rfl

theorem cell23_2743888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 2, 2, 2].length) (baseStart_2743888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743888 prefixEnd_2743888 := by exact prefixLift 2743888
  have htrace : WordTrace (prefixWord ++ tailWord_2743888) baseStart_2743888 baseEnd_2743888 := by
    simpa [prefixWord, tailWord_2743888, baseEnd_2743888] using wordTrace_append hprefix tailTrace_2743888
  have hstable : (prefixWord ++ tailWord_2743888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743888).length < 2 ^ (prefixWord ++ tailWord_2743888).sum := by decide
  have hdescent : baseEnd_2743888 < baseStart_2743888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743897 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 8]
def baseStart_2743897 : Nat := 118140960795 + 2743897 * 2 ^ 59
def prefixEnd_2743897 : Nat := 4983230072969 + 3 ^ 40 * 2743897 * 2
def baseEnd_2743897 : Nat := 1408938027429956224068553

theorem tailTrace_2743897 : CollatzResearch.WordTrace tailWord_2743897 prefixEnd_2743897 1408938027429956224068553 := by
  unfold tailWord_2743897
  simp only [CollatzResearch.WordTrace]
  refine ⟨100078145340337264143941945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66718763560224842762627963 100078145340337264143941945)
  ·
    refine ⟨75058609005252948107956459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100078145340337264143941945 75058609005252948107956459)
    ·
      refine ⟨112587913507879422161934689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75058609005252948107956459 112587913507879422161934689)
      ·
        refine ⟨84440935130909566621451017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112587913507879422161934689 84440935130909566621451017)
        ·
          refine ⟨63330701348182174966088263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84440935130909566621451017 63330701348182174966088263)
          ·
            refine ⟨94996052022273262449132395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63330701348182174966088263 94996052022273262449132395)
            ·
              refine ⟨142494078033409893673698593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94996052022273262449132395 142494078033409893673698593)
              ·
                refine ⟨106870558525057420255273945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142494078033409893673698593 106870558525057420255273945)
                ·
                  refine ⟨80152918893793065191455459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106870558525057420255273945 80152918893793065191455459)
                  ·
                    refine ⟨120229378340689597787183189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80152918893793065191455459 120229378340689597787183189)
                    ·
                      refine ⟨1408938027429956224068553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 120229378340689597787183189 1408938027429956224068553)
                      ·
                        rfl

theorem cell23_2743897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_2743897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743897 prefixEnd_2743897 := by exact prefixLift 2743897
  have htrace : WordTrace (prefixWord ++ tailWord_2743897) baseStart_2743897 baseEnd_2743897 := by
    simpa [prefixWord, tailWord_2743897, baseEnd_2743897] using wordTrace_append hprefix tailTrace_2743897
  have hstable : (prefixWord ++ tailWord_2743897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743897).length < 2 ^ (prefixWord ++ tailWord_2743897).sum := by decide
  have hdescent : baseEnd_2743897 < baseStart_2743897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743904 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 3]
def baseStart_2743904 : Nat := 118140960795 + 2743904 * 2 ^ 59
def prefixEnd_2743904 : Nat := 4983230072969 + 3 ^ 40 * 2743904 * 2
def baseEnd_2743904 : Nat := 1408941621794537696681021

theorem tailTrace_2743904 : CollatzResearch.WordTrace tailWord_2743904 prefixEnd_2743904 1408941621794537696681021 := by
  unfold tailWord_2743904
  simp only [CollatzResearch.WordTrace]
  refine ⟨50039200325655952169723383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66718933767541269559631177 50039200325655952169723383)
  ·
    refine ⟨75058800488483928254585075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50039200325655952169723383 75058800488483928254585075)
    ·
      refine ⟨112588200732725892381877613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75058800488483928254585075 112588200732725892381877613)
      ·
        refine ⟨42220575274772209643204105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112588200732725892381877613 42220575274772209643204105)
        ·
          refine ⟨31665431456079157232403079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42220575274772209643204105 31665431456079157232403079)
          ·
            refine ⟨47498147184118735848604619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31665431456079157232403079 47498147184118735848604619)
            ·
              refine ⟨71247220776178103772906929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47498147184118735848604619 71247220776178103772906929)
              ·
                refine ⟨53435415582133577829680197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71247220776178103772906929 53435415582133577829680197)
                ·
                  refine ⟨10019140421650045843065037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53435415582133577829680197 10019140421650045843065037)
                  ·
                    refine ⟨3757177658118767191149389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10019140421650045843065037 3757177658118767191149389)
                    ·
                      refine ⟨1408941621794537696681021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3757177658118767191149389 1408941621794537696681021)
                      ·
                        rfl

theorem cell23_2743904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_2743904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2743904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2743904 prefixEnd_2743904 := by exact prefixLift 2743904
  have htrace : WordTrace (prefixWord ++ tailWord_2743904) baseStart_2743904 baseEnd_2743904 := by
    simpa [prefixWord, tailWord_2743904, baseEnd_2743904] using wordTrace_append hprefix tailTrace_2743904
  have hstable : (prefixWord ++ tailWord_2743904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743904).length < 2 ^ (prefixWord ++ tailWord_2743904).sum := by decide
  have hdescent : baseEnd_2743904 < baseStart_2743904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744031 : List Nat := [1, 1, 2, 3, 2, 2, 1, 5, 1, 5]
def baseStart_2744031 : Nat := 118140960795 + 2744031 * 2 ^ 59
def prefixEnd_2744031 : Nat := 4983230072969 + 3 ^ 40 * 2744031 * 2
def baseEnd_2744031 : Nat := 469668944612552899930979

theorem tailTrace_2744031 : CollatzResearch.WordTrace tailWord_2744031 prefixEnd_2744031 469668944612552899930979 := by
  unfold tailWord_2744031
  simp only [CollatzResearch.WordTrace]
  refine ⟨100083032721851805029319947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66722021814567870019546631 100083032721851805029319947)
  ·
    refine ⟨150124549082777707543979921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100083032721851805029319947 150124549082777707543979921)
    ·
      refine ⟨112593411812083280657984941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150124549082777707543979921 112593411812083280657984941)
      ·
        refine ⟨42222529429531230246744353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112593411812083280657984941 42222529429531230246744353)
        ·
          refine ⟨31666897072148422685058265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42222529429531230246744353 31666897072148422685058265)
          ·
            refine ⟨23750172804111317013793699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31666897072148422685058265 23750172804111317013793699)
            ·
              refine ⟨35625259206166975520690549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23750172804111317013793699 35625259206166975520690549)
              ·
                refine ⟨3339868050578153955064739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35625259206166975520690549 3339868050578153955064739)
                ·
                  refine ⟨5009802075867230932597109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3339868050578153955064739 5009802075867230932597109)
                  ·
                    refine ⟨469668944612552899930979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5009802075867230932597109 469668944612552899930979)
                    ·
                      rfl

theorem cell23_2744031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 5].length) (baseStart_2744031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744031 prefixEnd_2744031 := by exact prefixLift 2744031
  have htrace : WordTrace (prefixWord ++ tailWord_2744031) baseStart_2744031 baseEnd_2744031 := by
    simpa [prefixWord, tailWord_2744031, baseEnd_2744031] using wordTrace_append hprefix tailTrace_2744031
  have hstable : (prefixWord ++ tailWord_2744031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744031).length < 2 ^ (prefixWord ++ tailWord_2744031).sum := by decide
  have hdescent : baseEnd_2744031 < baseStart_2744031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744039 : List Nat := [1, 1, 5, 4, 1, 1, 3, 2, 1, 4]
def baseStart_2744039 : Nat := 118140960795 + 2744039 * 2 ^ 59
def prefixEnd_2744039 : Nat := 4983230072969 + 3 ^ 40 * 2744039 * 2
def baseEnd_2744039 : Nat := 469670313894298222830967

theorem tailTrace_2744039 : CollatzResearch.WordTrace tailWord_2744039 prefixEnd_2744039 469670313894298222830967 := by
  unfold tailWord_2744039
  simp only [CollatzResearch.WordTrace]
  refine ⟨100083324505822822395611171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66722216337215214930407447 100083324505822822395611171)
  ·
    refine ⟨150124986758734233593416757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100083324505822822395611171 150124986758734233593416757)
    ·
      refine ⟨14074217508631334399382821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150124986758734233593416757 14074217508631334399382821)
      ·
        refine ⟨2638915782868375199884279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14074217508631334399382821 2638915782868375199884279)
        ·
          refine ⟨3958373674302562799826419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2638915782868375199884279 3958373674302562799826419)
          ·
            refine ⟨5937560511453844199739629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3958373674302562799826419 5937560511453844199739629)
            ·
              refine ⟨2226585191795191574902361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5937560511453844199739629 2226585191795191574902361)
              ·
                refine ⟨1669938893846393681176771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2226585191795191574902361 1669938893846393681176771)
                ·
                  refine ⟨2504908340769590521765157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669938893846393681176771 2504908340769590521765157)
                  ·
                    refine ⟨469670313894298222830967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2504908340769590521765157 469670313894298222830967)
                    ·
                      rfl

theorem cell23_2744039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_2744039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744039 prefixEnd_2744039 := by exact prefixLift 2744039
  have htrace : WordTrace (prefixWord ++ tailWord_2744039) baseStart_2744039 baseEnd_2744039 := by
    simpa [prefixWord, tailWord_2744039, baseEnd_2744039] using wordTrace_append hprefix tailTrace_2744039
  have hstable : (prefixWord ++ tailWord_2744039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744039).length < 2 ^ (prefixWord ++ tailWord_2744039).sum := by decide
  have hdescent : baseEnd_2744039 < baseStart_2744039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744045 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_2744045 : Nat := 118140960795 + 2744045 * 2 ^ 59
def prefixEnd_2744045 : Nat := 4983230072969 + 3 ^ 40 * 2744045 * 2
def baseEnd_2744045 : Nat := 1409014022566821645017873

theorem tailTrace_2744045 : CollatzResearch.WordTrace tailWord_2744045 prefixEnd_2744045 1409014022566821645017873 := by
  unfold tailWord_2744045
  simp only [CollatzResearch.WordTrace]
  refine ⟨100083543343801085420329589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66722362229200723613553059 100083543343801085420329589)
  ·
    refine ⟨9382832188481351758155899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100083543343801085420329589 9382832188481351758155899)
    ·
      refine ⟨14074248282722027637233849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9382832188481351758155899 14074248282722027637233849)
      ·
        refine ⟨10555686212041520727925387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14074248282722027637233849 10555686212041520727925387)
        ·
          refine ⟨15833529318062281091888081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10555686212041520727925387 15833529318062281091888081)
          ·
            refine ⟨11875146988546710818916061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15833529318062281091888081 11875146988546710818916061)
            ·
              refine ⟨4453180120705016557093523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11875146988546710818916061 4453180120705016557093523)
              ·
                refine ⟨6679770181057524835640285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4453180120705016557093523 6679770181057524835640285)
                ·
                  refine ⟨2504913817896571813365107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6679770181057524835640285 2504913817896571813365107)
                  ·
                    refine ⟨3757370726844857720047661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2504913817896571813365107 3757370726844857720047661)
                    ·
                      refine ⟨1409014022566821645017873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3757370726844857720047661 1409014022566821645017873)
                      ·
                        rfl

theorem cell23_2744045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_2744045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744045 prefixEnd_2744045 := by exact prefixLift 2744045
  have htrace : WordTrace (prefixWord ++ tailWord_2744045) baseStart_2744045 baseEnd_2744045 := by
    simpa [prefixWord, tailWord_2744045, baseEnd_2744045] using wordTrace_append hprefix tailTrace_2744045
  have hstable : (prefixWord ++ tailWord_2744045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744045).length < 2 ^ (prefixWord ++ tailWord_2744045).sum := by decide
  have hdescent : baseEnd_2744045 < baseStart_2744045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744052 : List Nat := [2, 6, 1, 1, 1, 1, 4, 1, 6]
def baseStart_2744052 : Nat := 118140960795 + 2744052 * 2 ^ 59
def prefixEnd_2744052 : Nat := 4983230072969 + 3 ^ 40 * 2744052 * 2
def baseEnd_2744052 : Nat := 156557512992378124181149

theorem tailTrace_2744052 : CollatzResearch.WordTrace tailWord_2744052 prefixEnd_2744052 156557512992378124181149 := by
  unfold tailWord_2744052
  simp only [CollatzResearch.WordTrace]
  refine ⟨50041899327387862807917205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66722532436517150410556273 50041899327387862807917205)
  ·
    refine ⟨2345714030971306069121119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50041899327387862807917205 2345714030971306069121119)
    ·
      refine ⟨3518571046456959103681679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2345714030971306069121119 3518571046456959103681679)
      ·
        refine ⟨5277856569685438655522519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3518571046456959103681679 5277856569685438655522519)
        ·
          refine ⟨7916784854528157983283779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5277856569685438655522519 7916784854528157983283779)
          ·
            refine ⟨11875177281792236974925669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7916784854528157983283779 11875177281792236974925669)
            ·
              refine ⟨2226595740336044432798563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11875177281792236974925669 2226595740336044432798563)
              ·
                refine ⟨3339893610504066649197845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2226595740336044432798563 3339893610504066649197845)
                ·
                  refine ⟨156557512992378124181149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3339893610504066649197845 156557512992378124181149)
                  ·
                    rfl

theorem cell23_2744052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_2744052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744052 prefixEnd_2744052 := by exact prefixLift 2744052
  have htrace : WordTrace (prefixWord ++ tailWord_2744052) baseStart_2744052 baseEnd_2744052 := by
    simpa [prefixWord, tailWord_2744052, baseEnd_2744052] using wordTrace_append hprefix tailTrace_2744052
  have hstable : (prefixWord ++ tailWord_2744052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744052).length < 2 ^ (prefixWord ++ tailWord_2744052).sum := by decide
  have hdescent : baseEnd_2744052 < baseStart_2744052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744061 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 6, 4]
def baseStart_2744061 : Nat := 118140960795 + 2744061 * 2 ^ 59
def prefixEnd_2744061 : Nat := 4983230072969 + 3 ^ 40 * 2744061 * 2
def baseEnd_2744061 : Nat := 469674079419097860805933

theorem tailTrace_2744061 : CollatzResearch.WordTrace tailWord_2744061 prefixEnd_2744061 469674079419097860805933 := by
  unfold tailWord_2744061
  simp only [CollatzResearch.WordTrace]
  refine ⟨100084126911743120152912037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66722751274495413435274691 100084126911743120152912037)
  ·
    refine ⟨18765773795951835028671007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100084126911743120152912037 18765773795951835028671007)
    ·
      refine ⟨28148660693927752543006511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18765773795951835028671007 28148660693927752543006511)
      ·
        refine ⟨42222991040891628814509767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28148660693927752543006511 42222991040891628814509767)
        ·
          refine ⟨63334486561337443221764651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42222991040891628814509767 63334486561337443221764651)
          ·
            refine ⟨95001729842006164832646977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63334486561337443221764651 95001729842006164832646977)
            ·
              refine ⟨71251297381504623624485233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95001729842006164832646977 71251297381504623624485233)
              ·
                refine ⟨53438473036128467718363925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71251297381504623624485233 53438473036128467718363925)
                ·
                  refine ⟨2504928423568521924298309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53438473036128467718363925 2504928423568521924298309)
                  ·
                    refine ⟨469674079419097860805933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2504928423568521924298309 469674079419097860805933)
                    ·
                      rfl

theorem cell23_2744061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_2744061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744061 prefixEnd_2744061 := by exact prefixLift 2744061
  have htrace : WordTrace (prefixWord ++ tailWord_2744061) baseStart_2744061 baseEnd_2744061 := by
    simpa [prefixWord, tailWord_2744061, baseEnd_2744061] using wordTrace_append hprefix tailTrace_2744061
  have hstable : (prefixWord ++ tailWord_2744061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744061).length < 2 ^ (prefixWord ++ tailWord_2744061).sum := by decide
  have hdescent : baseEnd_2744061 < baseStart_2744061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744068 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_2744068 : Nat := 118140960795 + 2744068 * 2 ^ 59
def prefixEnd_2744068 : Nat := 4983230072969 + 3 ^ 40 * 2744068 * 2
def baseEnd_2744068 : Nat := 1409025832621875055030267

theorem tailTrace_2744068 : CollatzResearch.WordTrace tailWord_2744068 prefixEnd_2744068 1409025832621875055030267 := by
  unfold tailWord_2744068
  simp only [CollatzResearch.WordTrace]
  refine ⟨50042191111358880174208429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66722921481811840232277905 50042191111358880174208429)
  ·
    refine ⟨18765821666759580065328161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50042191111358880174208429 18765821666759580065328161)
    ·
      refine ⟨14074366250069685048996121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18765821666759580065328161 14074366250069685048996121)
      ·
        refine ⟨10555774687552263786747091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14074366250069685048996121 10555774687552263786747091)
        ·
          refine ⟨15833662031328395680120637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10555774687552263786747091 15833662031328395680120637)
          ·
            refine ⟨5937623261748148380045239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15833662031328395680120637 5937623261748148380045239)
            ·
              refine ⟨8906434892622222570067859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5937623261748148380045239 8906434892622222570067859)
              ·
                refine ⟨13359652338933333855101789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8906434892622222570067859 13359652338933333855101789)
                ·
                  refine ⟨5009869627100000195663171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13359652338933333855101789 5009869627100000195663171)
                  ·
                    refine ⟨7514804440650000293494757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5009869627100000195663171 7514804440650000293494757)
                    ·
                      refine ⟨1409025832621875055030267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7514804440650000293494757 1409025832621875055030267)
                      ·
                        rfl

theorem cell23_2744068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_2744068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744068 prefixEnd_2744068 := by exact prefixLift 2744068
  have htrace : WordTrace (prefixWord ++ tailWord_2744068) baseStart_2744068 baseEnd_2744068 := by
    simpa [prefixWord, tailWord_2744068, baseEnd_2744068] using wordTrace_append hprefix tailTrace_2744068
  have hstable : (prefixWord ++ tailWord_2744068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744068).length < 2 ^ (prefixWord ++ tailWord_2744068).sum := by decide
  have hdescent : baseEnd_2744068 < baseStart_2744068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744082 : List Nat := [3, 2, 4, 1, 1, 2, 3, 1, 1, 5]
def baseStart_2744082 : Nat := 118140960795 + 2744082 * 2 ^ 59
def prefixEnd_2744082 : Nat := 4983230072969 + 3 ^ 40 * 2744082 * 2
def baseEnd_2744082 : Nat := 469677673783679333418401

theorem tailTrace_2744082 : CollatzResearch.WordTrace tailWord_2744082 prefixEnd_2744082 469677673783679333418401 := by
  unfold tailWord_2744082
  simp only [CollatzResearch.WordTrace]
  refine ⟨25021223211166760184856625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66723261896444693826284333 25021223211166760184856625)
  ·
    refine ⟨18765917408375070138642469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25021223211166760184856625 18765917408375070138642469)
    ·
      refine ⟨3518609514070325650995463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18765917408375070138642469 3518609514070325650995463)
      ·
        refine ⟨5277914271105488476493195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3518609514070325650995463 5277914271105488476493195)
        ·
          refine ⟨7916871406658232714739793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5277914271105488476493195 7916871406658232714739793)
          ·
            refine ⟨5937653554993674536054845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7916871406658232714739793 5937653554993674536054845)
            ·
              refine ⟨2226620083122627951020567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5937653554993674536054845 2226620083122627951020567)
              ·
                refine ⟨3339930124683941926530851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2226620083122627951020567 3339930124683941926530851)
                ·
                  refine ⟨5009895187025912889796277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3339930124683941926530851 5009895187025912889796277)
                  ·
                    refine ⟨469677673783679333418401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5009895187025912889796277 469677673783679333418401)
                    ·
                      rfl

theorem cell23_2744082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_2744082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744082 prefixEnd_2744082 := by exact prefixLift 2744082
  have htrace : WordTrace (prefixWord ++ tailWord_2744082) baseStart_2744082 baseEnd_2744082 := by
    simpa [prefixWord, tailWord_2744082, baseEnd_2744082] using wordTrace_append hprefix tailTrace_2744082
  have hstable : (prefixWord ++ tailWord_2744082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744082).length < 2 ^ (prefixWord ++ tailWord_2744082).sum := by decide
  have hdescent : baseEnd_2744082 < baseStart_2744082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744085 : List Nat := [1, 3, 2, 1, 2, 4, 3, 1, 1, 1, 4]
def baseStart_2744085 : Nat := 118140960795 + 2744085 * 2 ^ 59
def prefixEnd_2744085 : Nat := 4983230072969 + 3 ^ 40 * 2744085 * 2
def baseEnd_2744085 : Nat := 1409034561793001488517689

theorem tailTrace_2744085 : CollatzResearch.WordTrace tailWord_2744085 prefixEnd_2744085 1409034561793001488517689 := by
  unfold tailWord_2744085
  simp only [CollatzResearch.WordTrace]
  refine ⟨100085002263656172251785709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66723334842437448167857139 100085002263656172251785709)
  ·
    refine ⟨37531875848871064594419641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100085002263656172251785709 37531875848871064594419641)
    ·
      refine ⟨28148906886653298445814731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37531875848871064594419641 28148906886653298445814731)
      ·
        refine ⟨42223360329979947668722097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28148906886653298445814731 42223360329979947668722097)
        ·
          refine ⟨31667520247484960751541573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42223360329979947668722097 31667520247484960751541573)
          ·
            refine ⟨5937660046403430140914045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31667520247484960751541573 5937660046403430140914045)
            ·
              refine ⟨2226622517401286302842767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5937660046403430140914045 2226622517401286302842767)
              ·
                refine ⟨3339933776101929454264151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2226622517401286302842767 3339933776101929454264151)
                ·
                  refine ⟨5009900664152894181396227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3339933776101929454264151 5009900664152894181396227)
                  ·
                    refine ⟨7514850996229341272094341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5009900664152894181396227 7514850996229341272094341)
                    ·
                      refine ⟨1409034561793001488517689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7514850996229341272094341 1409034561793001488517689)
                      ·
                        rfl

theorem cell23_2744085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_2744085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744085 prefixEnd_2744085 := by exact prefixLift 2744085
  have htrace : WordTrace (prefixWord ++ tailWord_2744085) baseStart_2744085 baseEnd_2744085 := by
    simpa [prefixWord, tailWord_2744085, baseEnd_2744085] using wordTrace_append hprefix tailTrace_2744085
  have hstable : (prefixWord ++ tailWord_2744085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744085).length < 2 ^ (prefixWord ++ tailWord_2744085).sum := by decide
  have hdescent : baseEnd_2744085 < baseStart_2744085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744088 : List Nat := [2, 1, 2, 3, 1, 1, 2, 5, 1, 2, 3]
def baseStart_2744088 : Nat := 118140960795 + 2744088 * 2 ^ 59
def prefixEnd_2744088 : Nat := 4983230072969 + 3 ^ 40 * 2744088 * 2
def baseEnd_2744088 : Nat := 1409036102234964976780175

theorem tailTrace_2744088 : CollatzResearch.WordTrace tailWord_2744088 prefixEnd_2744088 1409036102234964976780175 := by
  unfold tailWord_2744088
  simp only [CollatzResearch.WordTrace]
  refine ⟨50042555841322651882072459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66723407788430202509429945 50042555841322651882072459)
  ·
    refine ⟨75063833761983977823108689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50042555841322651882072459 75063833761983977823108689)
    ·
      refine ⟨56297875321487983367331517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75063833761983977823108689 56297875321487983367331517)
      ·
        refine ⟨21111703245557993762749319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56297875321487983367331517 21111703245557993762749319)
        ·
          refine ⟨31667554868336990644123979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21111703245557993762749319 31667554868336990644123979)
          ·
            refine ⟨47501332302505485966185969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31667554868336990644123979 47501332302505485966185969)
            ·
              refine ⟨35625999226879114474639477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47501332302505485966185969 35625999226879114474639477)
              ·
                refine ⟨3339937427519916981997451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35625999226879114474639477 3339937427519916981997451)
                ·
                  refine ⟨5009906141279875472996177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3339937427519916981997451 5009906141279875472996177)
                  ·
                    refine ⟨3757429605959906604747133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5009906141279875472996177 3757429605959906604747133)
                    ·
                      refine ⟨1409036102234964976780175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3757429605959906604747133 1409036102234964976780175)
                      ·
                        rfl

theorem cell23_2744088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_2744088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744088 prefixEnd_2744088 := by exact prefixLift 2744088
  have htrace : WordTrace (prefixWord ++ tailWord_2744088) baseStart_2744088 baseEnd_2744088 := by
    simpa [prefixWord, tailWord_2744088, baseEnd_2744088] using wordTrace_append hprefix tailTrace_2744088
  have hstable : (prefixWord ++ tailWord_2744088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744088).length < 2 ^ (prefixWord ++ tailWord_2744088).sum := by decide
  have hdescent : baseEnd_2744088 < baseStart_2744088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744245 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 2, 5]
def baseStart_2744245 : Nat := 118140960795 + 2744245 * 2 ^ 59
def prefixEnd_2744245 : Nat := 4983230072969 + 3 ^ 40 * 2744245 * 2
def baseEnd_2744245 : Nat := 469705572899240287505651

theorem tailTrace_2744245 : CollatzResearch.WordTrace tailWord_2744245 prefixEnd_2744245 469705572899240287505651 := by
  unfold tailWord_2744245
  simp only [CollatzResearch.WordTrace]
  refine ⟨100090837943076519577610189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66727225295384346385073459 100090837943076519577610189)
  ·
    refine ⟨37534064228653694841603821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100090837943076519577610189 37534064228653694841603821)
    ·
      refine ⟨14075274085745135565601433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37534064228653694841603821 14075274085745135565601433)
      ·
        refine ⟨10556455564308851674201075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14075274085745135565601433 10556455564308851674201075)
        ·
          refine ⟨15834683346463277511301613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10556455564308851674201075 15834683346463277511301613)
          ·
            refine ⟨5938006254923729066738105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15834683346463277511301613 5938006254923729066738105)
            ·
              refine ⟨4453504691192796800053579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5938006254923729066738105 4453504691192796800053579)
              ·
                refine ⟨6680257036789195200080369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4453504691192796800053579 6680257036789195200080369)
                ·
                  refine ⟨5010192777591896400060277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6680257036789195200080369 5010192777591896400060277)
                  ·
                    refine ⟨469705572899240287505651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5010192777591896400060277 469705572899240287505651)
                    ·
                      rfl

theorem cell23_2744245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_2744245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744245 prefixEnd_2744245 := by exact prefixLift 2744245
  have htrace : WordTrace (prefixWord ++ tailWord_2744245) baseStart_2744245 baseEnd_2744245 := by
    simpa [prefixWord, tailWord_2744245, baseEnd_2744245] using wordTrace_append hprefix tailTrace_2744245
  have hstable : (prefixWord ++ tailWord_2744245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744245).length < 2 ^ (prefixWord ++ tailWord_2744245).sum := by decide
  have hdescent : baseEnd_2744245 < baseStart_2744245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744251 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 5]
def baseStart_2744251 : Nat := 118140960795 + 2744251 * 2 ^ 59
def prefixEnd_2744251 : Nat := 4983230072969 + 3 ^ 40 * 2744251 * 2
def baseEnd_2744251 : Nat := 1409119799581647839041925

theorem tailTrace_2744251 : CollatzResearch.WordTrace tailWord_2744251 prefixEnd_2744251 1409119799581647839041925 := by
  unfold tailWord_2744251
  simp only [CollatzResearch.WordTrace]
  refine ⟨100091056781054782602328607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66727371187369855068219071 100091056781054782602328607)
  ·
    refine ⟨150136585171582173903492911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100091056781054782602328607 150136585171582173903492911)
    ·
      refine ⟨225204877757373260855239367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150136585171582173903492911 225204877757373260855239367)
      ·
        refine ⟨337807316636059891282859051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225204877757373260855239367 337807316636059891282859051)
        ·
          refine ⟨506710974954089836924288577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337807316636059891282859051 506710974954089836924288577)
          ·
            refine ⟨380033231215567377693216433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 506710974954089836924288577 380033231215567377693216433)
            ·
              refine ⟨285024923411675533269912325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380033231215567377693216433 285024923411675533269912325)
              ·
                refine ⟨53442173139689162488108561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 285024923411675533269912325 53442173139689162488108561)
                ·
                  refine ⟨40081629854766871866081421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53442173139689162488108561 40081629854766871866081421)
                  ·
                    refine ⟨15030611195537576949780533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40081629854766871866081421 15030611195537576949780533)
                    ·
                      refine ⟨1409119799581647839041925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15030611195537576949780533 1409119799581647839041925)
                      ·
                        rfl

theorem cell23_2744251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 5].length) (baseStart_2744251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744251 prefixEnd_2744251 := by exact prefixLift 2744251
  have htrace : WordTrace (prefixWord ++ tailWord_2744251) baseStart_2744251 baseEnd_2744251 := by
    simpa [prefixWord, tailWord_2744251, baseEnd_2744251] using wordTrace_append hprefix tailTrace_2744251
  have hstable : (prefixWord ++ tailWord_2744251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744251).length < 2 ^ (prefixWord ++ tailWord_2744251).sum := by decide
  have hdescent : baseEnd_2744251 < baseStart_2744251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744282 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2]
def baseStart_2744282 : Nat := 118140960795 + 2744282 * 2 ^ 59
def prefixEnd_2744282 : Nat := 4983230072969 + 3 ^ 40 * 2744282 * 2
def baseEnd_2744282 : Nat := 1409135717481937217754283

theorem tailTrace_2744282 : CollatzResearch.WordTrace tailWord_2744282 prefixEnd_2744282 1409135717481937217754283 := by
  unfold tailWord_2744282
  simp only [CollatzResearch.WordTrace]
  refine ⟨25023046860985618724176775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66728124962628316597804733 25023046860985618724176775)
  ·
    refine ⟨37534570291478428086265163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25023046860985618724176775 37534570291478428086265163)
    ·
      refine ⟨56301855437217642129397745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37534570291478428086265163 56301855437217642129397745)
      ·
        refine ⟨42226391577913231597048309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56301855437217642129397745 42226391577913231597048309)
        ·
          refine ⟨3958724210429365462223279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42226391577913231597048309 3958724210429365462223279)
          ·
            refine ⟨5938086315644048193334919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3958724210429365462223279 5938086315644048193334919)
            ·
              refine ⟨8907129473466072290002379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5938086315644048193334919 8907129473466072290002379)
              ·
                refine ⟨13360694210199108435003569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8907129473466072290002379 13360694210199108435003569)
                ·
                  refine ⟨10020520657649331326252677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13360694210199108435003569 10020520657649331326252677)
                  ·
                    refine ⟨1878847623309249623672377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10020520657649331326252677 1878847623309249623672377)
                    ·
                      refine ⟨1409135717481937217754283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1878847623309249623672377 1409135717481937217754283)
                      ·
                        rfl

theorem cell23_2744282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_2744282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744282 prefixEnd_2744282 := by exact prefixLift 2744282
  have htrace : WordTrace (prefixWord ++ tailWord_2744282) baseStart_2744282 baseEnd_2744282 := by
    simpa [prefixWord, tailWord_2744282, baseEnd_2744282] using wordTrace_append hprefix tailTrace_2744282
  have hstable : (prefixWord ++ tailWord_2744282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744282).length < 2 ^ (prefixWord ++ tailWord_2744282).sum := by decide
  have hdescent : baseEnd_2744282 < baseStart_2744282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744302 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_2744302 : Nat := 118140960795 + 2744302 * 2 ^ 59
def prefixEnd_2744302 : Nat := 4983230072969 + 3 ^ 40 * 2744302 * 2
def baseEnd_2744302 : Nat := 1409145987095027139504191

theorem tailTrace_2744302 : CollatzResearch.WordTrace tailWord_2744302 prefixEnd_2744302 1409145987095027139504191 := by
  unfold tailWord_2744302
  simp only [CollatzResearch.WordTrace]
  refine ⟨12511614612983752289054395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66728611269246678874956773 12511614612983752289054395)
  ·
    refine ⟨18767421919475628433581593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12511614612983752289054395 18767421919475628433581593)
    ·
      refine ⟨14075566439606721325186195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18767421919475628433581593 14075566439606721325186195)
      ·
        refine ⟨21113349659410081987779293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14075566439606721325186195 21113349659410081987779293)
        ·
          refine ⟨7917506122278780745417235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21113349659410081987779293 7917506122278780745417235)
          ·
            refine ⟨11876259183418171118125853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7917506122278780745417235 11876259183418171118125853)
            ·
              refine ⟨4453597193781814169297195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11876259183418171118125853 4453597193781814169297195)
              ·
                refine ⟨6680395790672721253945793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4453597193781814169297195 6680395790672721253945793)
                ·
                  refine ⟨5010296843004540940459345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6680395790672721253945793 5010296843004540940459345)
                  ·
                    refine ⟨3757722632253405705344509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5010296843004540940459345 3757722632253405705344509)
                    ·
                      refine ⟨1409145987095027139504191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3757722632253405705344509 1409145987095027139504191)
                      ·
                        rfl

theorem cell23_2744302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_2744302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744302 prefixEnd_2744302 := by exact prefixLift 2744302
  have htrace : WordTrace (prefixWord ++ tailWord_2744302) baseStart_2744302 baseEnd_2744302 := by
    simpa [prefixWord, tailWord_2744302, baseEnd_2744302] using wordTrace_append hprefix tailTrace_2744302
  have hstable : (prefixWord ++ tailWord_2744302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744302).length < 2 ^ (prefixWord ++ tailWord_2744302).sum := by decide
  have hdescent : baseEnd_2744302 < baseStart_2744302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744332 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 3, 1, 3]
def baseStart_2744332 : Nat := 118140960795 + 2744332 * 2 ^ 59
def prefixEnd_2744332 : Nat := 4983230072969 + 3 ^ 40 * 2744332 * 2
def baseEnd_2744332 : Nat := 1409161391514662022129053

theorem tailTrace_2744332 : CollatzResearch.WordTrace tailWord_2744332 prefixEnd_2744332 1409161391514662022129053 := by
  unfold tailWord_2744332
  simp only [CollatzResearch.WordTrace]
  refine ⟨50047005546880666718013625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66729340729174222290684833 50047005546880666718013625)
  ·
    refine ⟨37535254160160500038510219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50047005546880666718013625 37535254160160500038510219)
    ·
      refine ⟨56302881240240750057765329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37535254160160500038510219 56302881240240750057765329)
      ·
        refine ⟨42227160930180562543323997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56302881240240750057765329 42227160930180562543323997)
        ·
          refine ⟨15835185348817710953746499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42227160930180562543323997 15835185348817710953746499)
          ·
            refine ⟨23752778023226566430619749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15835185348817710953746499 23752778023226566430619749)
            ·
              refine ⟨4453645879354981205741203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23752778023226566430619749 4453645879354981205741203)
              ·
                refine ⟨6680468819032471808611805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4453645879354981205741203 6680468819032471808611805)
                ·
                  refine ⟨2505175807137176928229427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6680468819032471808611805 2505175807137176928229427)
                  ·
                    refine ⟨3757763710705765392344141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2505175807137176928229427 3757763710705765392344141)
                    ·
                      refine ⟨1409161391514662022129053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3757763710705765392344141 1409161391514662022129053)
                      ·
                        rfl

theorem cell23_2744332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_2744332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744332 prefixEnd_2744332 := by exact prefixLift 2744332
  have htrace : WordTrace (prefixWord ++ tailWord_2744332) baseStart_2744332 baseEnd_2744332 := by
    simpa [prefixWord, tailWord_2744332, baseEnd_2744332] using wordTrace_append hprefix tailTrace_2744332
  have hstable : (prefixWord ++ tailWord_2744332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744332).length < 2 ^ (prefixWord ++ tailWord_2744332).sum := by decide
  have hdescent : baseEnd_2744332 < baseStart_2744332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744355 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 2, 6, 2]
def baseStart_2744355 : Nat := 118140960795 + 2744355 * 2 ^ 59
def prefixEnd_2744355 : Nat := 4983230072969 + 3 ^ 40 * 2744355 * 2
def baseEnd_2744355 : Nat := 1409173201569715432141447

theorem tailTrace_2744355 : CollatzResearch.WordTrace tailWord_2744355 prefixEnd_2744355 1409173201569715432141447 := by
  unfold tailWord_2744355
  simp only [CollatzResearch.WordTrace]
  refine ⟨100094849972678008364114519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66729899981785338909409679 100094849972678008364114519)
  ·
    refine ⟨150142274959017012546171779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100094849972678008364114519 150142274959017012546171779)
    ·
      refine ⟨225213412438525518819257669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150142274959017012546171779 225213412438525518819257669)
      ·
        refine ⟨42227514832223534778610813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225213412438525518819257669 42227514832223534778610813)
        ·
          refine ⟨15835318062083825541979055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42227514832223534778610813 15835318062083825541979055)
          ·
            refine ⟨23752977093125738312968583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15835318062083825541979055 23752977093125738312968583)
            ·
              refine ⟨35629465639688607469452875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23752977093125738312968583 35629465639688607469452875)
              ·
                refine ⟨53444198459532911204179313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35629465639688607469452875 53444198459532911204179313)
                ·
                  refine ⟨40083148844649683403134485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53444198459532911204179313 40083148844649683403134485)
                  ·
                    refine ⟨1878897602092953909521929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40083148844649683403134485 1878897602092953909521929)
                    ·
                      refine ⟨1409173201569715432141447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1878897602092953909521929 1409173201569715432141447)
                      ·
                        rfl

theorem cell23_2744355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_2744355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744355 prefixEnd_2744355 := by exact prefixLift 2744355
  have htrace : WordTrace (prefixWord ++ tailWord_2744355) baseStart_2744355 baseEnd_2744355 := by
    simpa [prefixWord, tailWord_2744355, baseEnd_2744355] using wordTrace_append hprefix tailTrace_2744355
  have hstable : (prefixWord ++ tailWord_2744355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744355).length < 2 ^ (prefixWord ++ tailWord_2744355).sum := by decide
  have hdescent : baseEnd_2744355 < baseStart_2744355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744366 : List Nat := [4, 1, 3, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_2744366 : Nat := 118140960795 + 2744366 * 2 ^ 59
def prefixEnd_2744366 : Nat := 4983230072969 + 3 ^ 40 * 2744366 * 2
def baseEnd_2744366 : Nat := 1409178849856914889103897

theorem tailTrace_2744366 : CollatzResearch.WordTrace tailWord_2744366 prefixEnd_2744366 1409178849856914889103897 := by
  unfold tailWord_2744366
  simp only [CollatzResearch.WordTrace]
  refine ⟨12511906396954769655345619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66730167450425438161843301 12511906396954769655345619)
  ·
    refine ⟨18767859595432154483018429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12511906396954769655345619 18767859595432154483018429)
    ·
      refine ⟨7037947348287057931131911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18767859595432154483018429 7037947348287057931131911)
      ·
        refine ⟨10556921022430586896697867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7037947348287057931131911 10556921022430586896697867)
        ·
          refine ⟨15835381533645880345046801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10556921022430586896697867 15835381533645880345046801)
          ·
            refine ⟨11876536150234410258785101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15835381533645880345046801 11876536150234410258785101)
            ·
              refine ⟨4453701056337903847044413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11876536150234410258785101 4453701056337903847044413)
              ·
                refine ⟨1670137896126713942641655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4453701056337903847044413 1670137896126713942641655)
                ·
                  refine ⟨2505206844190070913962483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1670137896126713942641655 2505206844190070913962483)
                  ·
                    refine ⟨3757810266285106370943725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2505206844190070913962483 3757810266285106370943725)
                    ·
                      refine ⟨1409178849856914889103897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3757810266285106370943725 1409178849856914889103897)
                      ·
                        rfl

theorem cell23_2744366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_2744366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744366 prefixEnd_2744366 := by exact prefixLift 2744366
  have htrace : WordTrace (prefixWord ++ tailWord_2744366) baseStart_2744366 baseEnd_2744366 := by
    simpa [prefixWord, tailWord_2744366, baseEnd_2744366] using wordTrace_append hprefix tailTrace_2744366
  have hstable : (prefixWord ++ tailWord_2744366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744366).length < 2 ^ (prefixWord ++ tailWord_2744366).sum := by decide
  have hdescent : baseEnd_2744366 < baseStart_2744366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744385 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2744385 : Nat := 118140960795 + 2744385 * 2 ^ 59
def prefixEnd_2744385 : Nat := 4983230072969 + 3 ^ 40 * 2744385 * 2
def baseEnd_2744385 : Nat := 1409188605989350314766309

theorem tailTrace_2744385 : CollatzResearch.WordTrace tailWord_2744385 prefixEnd_2744385 1409188605989350314766309 := by
  unfold tailWord_2744385
  simp only [CollatzResearch.WordTrace]
  refine ⟨100095944162569323487706609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66730629441712882325137739 100095944162569323487706609)
  ·
    refine ⟨75071958121926992615779957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100095944162569323487706609 75071958121926992615779957)
    ·
      refine ⟨7037996073930655557729371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75071958121926992615779957 7037996073930655557729371)
      ·
        refine ⟨10556994110895983336594057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7037996073930655557729371 10556994110895983336594057)
        ·
          refine ⟨7917745583171987502445543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10556994110895983336594057 7917745583171987502445543)
          ·
            refine ⟨11876618374757981253668315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7917745583171987502445543 11876618374757981253668315)
            ·
              refine ⟨17814927562136971880502473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11876618374757981253668315 17814927562136971880502473)
              ·
                refine ⟨13361195671602728910376855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17814927562136971880502473 13361195671602728910376855)
                ·
                  refine ⟨20041793507404093365565283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13361195671602728910376855 20041793507404093365565283)
                  ·
                    refine ⟨30062690261106140048347925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20041793507404093365565283 30062690261106140048347925)
                    ·
                      refine ⟨1409188605989350314766309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30062690261106140048347925 1409188605989350314766309)
                      ·
                        rfl

theorem cell23_2744385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2744385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744385 prefixEnd_2744385 := by exact prefixLift 2744385
  have htrace : WordTrace (prefixWord ++ tailWord_2744385) baseStart_2744385 baseEnd_2744385 := by
    simpa [prefixWord, tailWord_2744385, baseEnd_2744385] using wordTrace_append hprefix tailTrace_2744385
  have hstable : (prefixWord ++ tailWord_2744385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744385).length < 2 ^ (prefixWord ++ tailWord_2744385).sum := by decide
  have hdescent : baseEnd_2744385 < baseStart_2744385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744406 : List Nat := [5, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_2744406 : Nat := 118140960795 + 2744406 * 2 ^ 59
def prefixEnd_2744406 : Nat := 4983230072969 + 3 ^ 40 * 2744406 * 2
def baseEnd_2744406 : Nat := 1409199389083094732603713

theorem tailTrace_2744406 : CollatzResearch.WordTrace tailWord_2744406 prefixEnd_2744406 1409199389083094732603713 := by
  unfold tailWord_2744406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6256044380968327754638817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66731140063662162716147381 6256044380968327754638817)
  ·
    refine ⟨4692033285726245815979113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6256044380968327754638817 4692033285726245815979113)
    ·
      refine ⟨3519024964294684361984335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4692033285726245815979113 3519024964294684361984335)
      ·
        refine ⟨5278537446442026542976503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3519024964294684361984335 5278537446442026542976503)
        ·
          refine ⟨7917806169663039814464755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5278537446442026542976503 7917806169663039814464755)
          ·
            refine ⟨11876709254494559721697133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7917806169663039814464755 11876709254494559721697133)
            ·
              refine ⟨4453765970435459895636425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11876709254494559721697133 4453765970435459895636425)
              ·
                refine ⟨3340324477826594921727319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4453765970435459895636425 3340324477826594921727319)
                ·
                  refine ⟨5010486716739892382590979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340324477826594921727319 5010486716739892382590979)
                  ·
                    refine ⟨7515730075109838573886469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5010486716739892382590979 7515730075109838573886469)
                    ·
                      refine ⟨1409199389083094732603713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7515730075109838573886469 1409199389083094732603713)
                      ·
                        rfl

theorem cell23_2744406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_2744406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744406 prefixEnd_2744406 := by exact prefixLift 2744406
  have htrace : WordTrace (prefixWord ++ tailWord_2744406) baseStart_2744406 baseEnd_2744406 := by
    simpa [prefixWord, tailWord_2744406, baseEnd_2744406] using wordTrace_append hprefix tailTrace_2744406
  have hstable : (prefixWord ++ tailWord_2744406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744406).length < 2 ^ (prefixWord ++ tailWord_2744406).sum := by decide
  have hdescent : baseEnd_2744406 < baseStart_2744406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744426 : List Nat := [3, 1, 3, 2, 3, 1, 3, 1, 1, 2, 3]
def baseStart_2744426 : Nat := 118140960795 + 2744426 * 2 ^ 59
def prefixEnd_2744426 : Nat := 4983230072969 + 3 ^ 40 * 2744426 * 2
def baseEnd_2744426 : Nat := 1409209658696184654353621

theorem tailTrace_2744426 : CollatzResearch.WordTrace tailWord_2744426 prefixEnd_2744426 1409209658696184654353621 := by
  unfold tailWord_2744426
  simp only [CollatzResearch.WordTrace]
  refine ⟨25024359888855196872487283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66731626370280524993299421 25024359888855196872487283)
  ·
    refine ⟨37536539833282795308730925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25024359888855196872487283 37536539833282795308730925)
    ·
      refine ⟨14076202437481048240774097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37536539833282795308730925 14076202437481048240774097)
      ·
        refine ⟨10557151828110786180580573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14076202437481048240774097 10557151828110786180580573)
        ·
          refine ⟨3958931935541544817717715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10557151828110786180580573 3958931935541544817717715)
          ·
            refine ⟨5938397903312317226576573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3958931935541544817717715 5938397903312317226576573)
            ·
              refine ⟨2226899213742118959966215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5938397903312317226576573 2226899213742118959966215)
              ·
                refine ⟨3340348820613178439949323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2226899213742118959966215 3340348820613178439949323)
                ·
                  refine ⟨5010523230919767659923985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340348820613178439949323 5010523230919767659923985)
                  ·
                    refine ⟨3757892423189825744942989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5010523230919767659923985 3757892423189825744942989)
                    ·
                      refine ⟨1409209658696184654353621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3757892423189825744942989 1409209658696184654353621)
                      ·
                        rfl

theorem cell23_2744426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_2744426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744426 prefixEnd_2744426 := by exact prefixLift 2744426
  have htrace : WordTrace (prefixWord ++ tailWord_2744426) baseStart_2744426 baseEnd_2744426 := by
    simpa [prefixWord, tailWord_2744426, baseEnd_2744426] using wordTrace_append hprefix tailTrace_2744426
  have hstable : (prefixWord ++ tailWord_2744426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744426).length < 2 ^ (prefixWord ++ tailWord_2744426).sum := by decide
  have hdescent : baseEnd_2744426 < baseStart_2744426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744439 : List Nat := [1, 1, 3, 1, 1, 6, 2, 2, 2, 1, 3]
def baseStart_2744439 : Nat := 118140960795 + 2744439 * 2 ^ 59
def prefixEnd_2744439 : Nat := 4983230072969 + 3 ^ 40 * 2744439 * 2
def baseEnd_2744439 : Nat := 1409216333944693103491061

theorem tailTrace_2744439 : CollatzResearch.WordTrace tailWord_2744439 prefixEnd_2744439 1409216333944693103491061 := by
  unfold tailWord_2744439
  simp only [CollatzResearch.WordTrace]
  refine ⟨100097913704373690710172371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66731942469582460473448247 100097913704373690710172371)
  ·
    refine ⟨150146870556560536065258557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100097913704373690710172371 150146870556560536065258557)
    ·
      refine ⟨56305076458710201024471959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150146870556560536065258557 56305076458710201024471959)
      ·
        refine ⟨84457614688065301536707939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56305076458710201024471959 84457614688065301536707939)
        ·
          refine ⟨126686422032097952305061909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84457614688065301536707939 126686422032097952305061909)
          ·
            refine ⟨5938426032754591514299777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 126686422032097952305061909 5938426032754591514299777)
            ·
              refine ⟨4453819524565943635724833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5938426032754591514299777 4453819524565943635724833)
              ·
                refine ⟨3340364643424457726793625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4453819524565943635724833 3340364643424457726793625)
                ·
                  refine ⟨2505273482568343295095219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3340364643424457726793625 2505273482568343295095219)
                  ·
                    refine ⟨3757910223852514942642829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2505273482568343295095219 3757910223852514942642829)
                    ·
                      refine ⟨1409216333944693103491061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3757910223852514942642829 1409216333944693103491061)
                      ·
                        rfl

theorem cell23_2744439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 1, 3].length) (baseStart_2744439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744439 prefixEnd_2744439 := by exact prefixLift 2744439
  have htrace : WordTrace (prefixWord ++ tailWord_2744439) baseStart_2744439 baseEnd_2744439 := by
    simpa [prefixWord, tailWord_2744439, baseEnd_2744439] using wordTrace_append hprefix tailTrace_2744439
  have hstable : (prefixWord ++ tailWord_2744439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744439).length < 2 ^ (prefixWord ++ tailWord_2744439).sum := by decide
  have hdescent : baseEnd_2744439 < baseStart_2744439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744445 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_2744445 : Nat := 118140960795 + 2744445 * 2 ^ 59
def prefixEnd_2744445 : Nat := 4983230072969 + 3 ^ 40 * 2744445 * 2
def baseEnd_2744445 : Nat := 1409219414828620080016033

theorem tailTrace_2744445 : CollatzResearch.WordTrace tailWord_2744445 prefixEnd_2744445 1409219414828620080016033 := by
  unfold tailWord_2744445
  simp only [CollatzResearch.WordTrace]
  refine ⟨100098132542351953734890789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66732088361567969156593859 100098132542351953734890789)
  ·
    refine ⟨18768399851690991325292023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100098132542351953734890789 18768399851690991325292023)
    ·
      refine ⟨28152599777536486987938035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18768399851690991325292023 28152599777536486987938035)
      ·
        refine ⟨42228899666304730481907053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28152599777536486987938035 42228899666304730481907053)
        ·
          refine ⟨15835837374864273930715145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42228899666304730481907053 15835837374864273930715145)
          ·
            refine ⟨11876878031148205448036359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15835837374864273930715145 11876878031148205448036359)
            ·
              refine ⟨17815317046722308172054539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11876878031148205448036359 17815317046722308172054539)
              ·
                refine ⟨26722975570083462258081809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17815317046722308172054539 26722975570083462258081809)
                ·
                  refine ⟨20042231677562596693561357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26722975570083462258081809 20042231677562596693561357)
                  ·
                    refine ⟨7515836879085973760085509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20042231677562596693561357 7515836879085973760085509)
                    ·
                      refine ⟨1409219414828620080016033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7515836879085973760085509 1409219414828620080016033)
                      ·
                        rfl

theorem cell23_2744445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_2744445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744445 prefixEnd_2744445 := by exact prefixLift 2744445
  have htrace : WordTrace (prefixWord ++ tailWord_2744445) baseStart_2744445 baseEnd_2744445 := by
    simpa [prefixWord, tailWord_2744445, baseEnd_2744445] using wordTrace_append hprefix tailTrace_2744445
  have hstable : (prefixWord ++ tailWord_2744445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744445).length < 2 ^ (prefixWord ++ tailWord_2744445).sum := by decide
  have hdescent : baseEnd_2744445 < baseStart_2744445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744479 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 1, 4, 2]
def baseStart_2744479 : Nat := 118140960795 + 2744479 * 2 ^ 59
def prefixEnd_2744479 : Nat := 4983230072969 + 3 ^ 40 * 2744479 * 2
def baseEnd_2744479 : Nat := 1409236873170872946990877

theorem tailTrace_2744479 : CollatzResearch.WordTrace tailWord_2744479 prefixEnd_2744479 1409236873170872946990877 := by
  unfold tailWord_2744479
  simp only [CollatzResearch.WordTrace]
  refine ⟨100099372624228777541628491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66732915082819185027752327 100099372624228777541628491)
  ·
    refine ⟨150149058936343166312442737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100099372624228777541628491 150149058936343166312442737)
    ·
      refine ⟨112611794202257374734332053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150149058936343166312442737 112611794202257374734332053)
      ·
        refine ⟨5278677853230814440671815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 112611794202257374734332053 5278677853230814440671815)
        ·
          refine ⟨7918016779846221661007723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5278677853230814440671815 7918016779846221661007723)
          ·
            refine ⟨11877025169769332491511585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7918016779846221661007723 11877025169769332491511585)
            ·
              refine ⟨8907768877326999368633689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11877025169769332491511585 8907768877326999368633689)
              ·
                refine ⟨6680826657995249526475267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8907768877326999368633689 6680826657995249526475267)
                ·
                  refine ⟨10021239986992874289712901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6680826657995249526475267 10021239986992874289712901)
                  ·
                    refine ⟨1878982497561163929321169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10021239986992874289712901 1878982497561163929321169)
                    ·
                      refine ⟨1409236873170872946990877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1878982497561163929321169 1409236873170872946990877)
                      ·
                        rfl

theorem cell23_2744479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_2744479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744479 prefixEnd_2744479 := by exact prefixLift 2744479
  have htrace : WordTrace (prefixWord ++ tailWord_2744479) baseStart_2744479 baseEnd_2744479 := by
    simpa [prefixWord, tailWord_2744479, baseEnd_2744479] using wordTrace_append hprefix tailTrace_2744479
  have hstable : (prefixWord ++ tailWord_2744479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744479).length < 2 ^ (prefixWord ++ tailWord_2744479).sum := by decide
  have hdescent : baseEnd_2744479 < baseStart_2744479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744490 : List Nat := [3, 1, 5, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_2744490 : Nat := 118140960795 + 2744490 * 2 ^ 59
def prefixEnd_2744490 : Nat := 4983230072969 + 3 ^ 40 * 2744490 * 2
def baseEnd_2744490 : Nat := 1409242521458072403953327

theorem tailTrace_2744490 : CollatzResearch.WordTrace tailWord_2744490 prefixEnd_2744490 1409242521458072403953327 := by
  unfold tailWord_2744490
  simp only [CollatzResearch.WordTrace]
  refine ⟨25024943456797231605069731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66733182551459284280185949 25024943456797231605069731)
  ·
    refine ⟨37537415185195847407604597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25024943456797231605069731 37537415185195847407604597)
    ·
      refine ⟨3519132673612110694462931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37537415185195847407604597 3519132673612110694462931)
      ·
        refine ⟨5278699010418166041694397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3519132673612110694462931 5278699010418166041694397)
        ·
          refine ⟨1979512128906812265635399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5278699010418166041694397 1979512128906812265635399)
          ·
            refine ⟨2969268193360218398453099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1979512128906812265635399 2969268193360218398453099)
            ·
              refine ⟨4453902290040327597679649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2969268193360218398453099 4453902290040327597679649)
              ·
                refine ⟨3340426717530245698259737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4453902290040327597679649 3340426717530245698259737)
                ·
                  refine ⟨2505320038147684273694803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3340426717530245698259737 2505320038147684273694803)
                  ·
                    refine ⟨3757980057221526410542205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2505320038147684273694803 3757980057221526410542205)
                    ·
                      refine ⟨1409242521458072403953327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3757980057221526410542205 1409242521458072403953327)
                      ·
                        rfl

theorem cell23_2744490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_2744490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744490 prefixEnd_2744490 := by exact prefixLift 2744490
  have htrace : WordTrace (prefixWord ++ tailWord_2744490) baseStart_2744490 baseEnd_2744490 := by
    simpa [prefixWord, tailWord_2744490, baseEnd_2744490] using wordTrace_append hprefix tailTrace_2744490
  have hstable : (prefixWord ++ tailWord_2744490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744490).length < 2 ^ (prefixWord ++ tailWord_2744490).sum := by decide
  have hdescent : baseEnd_2744490 < baseStart_2744490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744512 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 3]
def baseStart_2744512 : Nat := 118140960795 + 2744512 * 2 ^ 59
def prefixEnd_2744512 : Nat := 4983230072969 + 3 ^ 40 * 2744512 * 2
def baseEnd_2744512 : Nat := 1409253818032471317878225

theorem tailTrace_2744512 : CollatzResearch.WordTrace tailWord_2744512 prefixEnd_2744512 1409253818032471317878225 := by
  unfold tailWord_2744512
  simp only [CollatzResearch.WordTrace]
  refine ⟨50050288116554612088789895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66733717488739482785053193 50050288116554612088789895)
  ·
    refine ⟨75075432174831918133184843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50050288116554612088789895 75075432174831918133184843)
    ·
      refine ⟨112613148262247877199777265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75075432174831918133184843 112613148262247877199777265)
      ·
        refine ⟨84459861196685907899832949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112613148262247877199777265 84459861196685907899832949)
        ·
          refine ⟨7918111987189303865609339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84459861196685907899832949 7918111987189303865609339)
          ·
            refine ⟨11877167980783955798414009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7918111987189303865609339 11877167980783955798414009)
            ·
              refine ⟨8907875985587966848810507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11877167980783955798414009 8907875985587966848810507)
              ·
                refine ⟨13361813978381950273215761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8907875985587966848810507 13361813978381950273215761)
                ·
                  refine ⟨10021360483786462704911821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13361813978381950273215761 10021360483786462704911821)
                  ·
                    refine ⟨3758010181419923514341933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10021360483786462704911821 3758010181419923514341933)
                    ·
                      refine ⟨1409253818032471317878225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3758010181419923514341933 1409253818032471317878225)
                      ·
                        rfl

theorem cell23_2744512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_2744512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744512 prefixEnd_2744512 := by exact prefixLift 2744512
  have htrace : WordTrace (prefixWord ++ tailWord_2744512) baseStart_2744512 baseEnd_2744512 := by
    simpa [prefixWord, tailWord_2744512, baseEnd_2744512] using wordTrace_append hprefix tailTrace_2744512
  have hstable : (prefixWord ++ tailWord_2744512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744512).length < 2 ^ (prefixWord ++ tailWord_2744512).sum := by decide
  have hdescent : baseEnd_2744512 < baseStart_2744512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744513 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_2744513 : Nat := 118140960795 + 2744513 * 2 ^ 59
def prefixEnd_2744513 : Nat := 4983230072969 + 3 ^ 40 * 2744513 * 2
def baseEnd_2744513 : Nat := 1409254331513125813965721

theorem tailTrace_2744513 : CollatzResearch.WordTrace tailWord_2744513 prefixEnd_2744513 1409254331513125813965721 := by
  unfold tailWord_2744513
  simp only [CollatzResearch.WordTrace]
  refine ⟨100100612706105601348366193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66733741804070400898910795 100100612706105601348366193)
  ·
    refine ⟨75075459529579201011274645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100100612706105601348366193 75075459529579201011274645)
    ·
      refine ⟨3519162165449025047403499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 75075459529579201011274645 3519162165449025047403499)
      ·
        refine ⟨5278743248173537571105249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3519162165449025047403499 5278743248173537571105249)
        ·
          refine ⟨3959057436130153178328937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5278743248173537571105249 3959057436130153178328937)
          ·
            refine ⟨2969293077097614883746703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3959057436130153178328937 2969293077097614883746703)
            ·
              refine ⟨4453939615646422325620055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2969293077097614883746703 4453939615646422325620055)
              ·
                refine ⟨6680909423469633488430083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4453939615646422325620055 6680909423469633488430083)
                ·
                  refine ⟨10021364135204450232645125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6680909423469633488430083 10021364135204450232645125)
                  ·
                    refine ⟨1879005775350834418620961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10021364135204450232645125 1879005775350834418620961)
                    ·
                      refine ⟨1409254331513125813965721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1879005775350834418620961 1409254331513125813965721)
                      ·
                        rfl

theorem cell23_2744513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_2744513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744513 prefixEnd_2744513 := by exact prefixLift 2744513
  have htrace : WordTrace (prefixWord ++ tailWord_2744513) baseStart_2744513 baseEnd_2744513 := by
    simpa [prefixWord, tailWord_2744513, baseEnd_2744513] using wordTrace_append hprefix tailTrace_2744513
  have hstable : (prefixWord ++ tailWord_2744513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744513).length < 2 ^ (prefixWord ++ tailWord_2744513).sum := by decide
  have hdescent : baseEnd_2744513 < baseStart_2744513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744552 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_2744552 : Nat := 118140960795 + 2744552 * 2 ^ 59
def prefixEnd_2744552 : Nat := 4983230072969 + 3 ^ 40 * 2744552 * 2
def baseEnd_2744552 : Nat := 1409274357258651161378041

theorem tailTrace_2744552 : CollatzResearch.WordTrace tailWord_2744552 prefixEnd_2744552 1409274357258651161378041 := by
  unfold tailWord_2744552
  simp only [CollatzResearch.WordTrace]
  refine ⟨50051017576482155504517955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66734690101976207339357273 50051017576482155504517955)
  ·
    refine ⟨75076526364723233256776933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50051017576482155504517955 75076526364723233256776933)
    ·
      refine ⟨14076848693385606235645675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75076526364723233256776933 14076848693385606235645675)
      ·
        refine ⟨21115273040078409353468513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14076848693385606235645675 21115273040078409353468513)
        ·
          refine ⟨15836454780058807015101385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21115273040078409353468513 15836454780058807015101385)
          ·
            refine ⟨11877341085044105261326039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15836454780058807015101385 11877341085044105261326039)
            ·
              refine ⟨17816011627566157891989059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11877341085044105261326039 17816011627566157891989059)
              ·
                refine ⟨26724017441349236837983589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17816011627566157891989059 26724017441349236837983589)
                ·
                  refine ⟨5010753270252981907121923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26724017441349236837983589 5010753270252981907121923)
                  ·
                    refine ⟨7516129905379472860682885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5010753270252981907121923 7516129905379472860682885)
                    ·
                      refine ⟨1409274357258651161378041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7516129905379472860682885 1409274357258651161378041)
                      ·
                        rfl

theorem cell23_2744552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_2744552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744552 prefixEnd_2744552 := by exact prefixLift 2744552
  have htrace : WordTrace (prefixWord ++ tailWord_2744552) baseStart_2744552 baseEnd_2744552 := by
    simpa [prefixWord, tailWord_2744552, baseEnd_2744552] using wordTrace_append hprefix tailTrace_2744552
  have hstable : (prefixWord ++ tailWord_2744552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744552).length < 2 ^ (prefixWord ++ tailWord_2744552).sum := by decide
  have hdescent : baseEnd_2744552 < baseStart_2744552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744629 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 1, 5, 2]
def baseStart_2744629 : Nat := 118140960795 + 2744629 * 2 ^ 59
def prefixEnd_2744629 : Nat := 4983230072969 + 3 ^ 40 * 2744629 * 2
def baseEnd_2744629 : Nat := 1409313895269047360115187

theorem tailTrace_2744629 : CollatzResearch.WordTrace tailWord_2744629 prefixEnd_2744629 1409313895269047360115187 := by
  unfold tailWord_2744629
  simp only [CollatzResearch.WordTrace]
  refine ⟨100104843573685353159588941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66736562382456902106392627 100104843573685353159588941)
  ·
    refine ⟨37539316340132007434845853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100104843573685353159588941 37539316340132007434845853)
    ·
      refine ⟨14077243627549502788067195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37539316340132007434845853 14077243627549502788067195)
      ·
        refine ⟨21115865441324254182100793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14077243627549502788067195 21115865441324254182100793)
        ·
          refine ⟨15836899080993190636575595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21115865441324254182100793 15836899080993190636575595)
          ·
            refine ⟨23755348621489785954863393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15836899080993190636575595 23755348621489785954863393)
            ·
              refine ⟨17816511466117339466147545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23755348621489785954863393 17816511466117339466147545)
              ·
                refine ⟨13362383599588004599610659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17816511466117339466147545 13362383599588004599610659)
                ·
                  refine ⟨20043575399382006899415989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13362383599588004599610659 20043575399382006899415989)
                  ·
                    refine ⟨1879085193692063146820249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20043575399382006899415989 1879085193692063146820249)
                    ·
                      refine ⟨1409313895269047360115187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1879085193692063146820249 1409313895269047360115187)
                      ·
                        rfl

theorem cell23_2744629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_2744629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744629 prefixEnd_2744629 := by exact prefixLift 2744629
  have htrace : WordTrace (prefixWord ++ tailWord_2744629) baseStart_2744629 baseEnd_2744629 := by
    simpa [prefixWord, tailWord_2744629, baseEnd_2744629] using wordTrace_append hprefix tailTrace_2744629
  have hstable : (prefixWord ++ tailWord_2744629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744629).length < 2 ^ (prefixWord ++ tailWord_2744629).sum := by decide
  have hdescent : baseEnd_2744629 < baseStart_2744629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744652 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 1, 6]
def baseStart_2744652 : Nat := 118140960795 + 2744652 * 2 ^ 59
def prefixEnd_2744652 : Nat := 4983230072969 + 3 ^ 40 * 2744652 * 2
def baseEnd_2744652 : Nat := 469775235108033590042527

theorem tailTrace_2744652 : CollatzResearch.WordTrace tailWord_2744652 prefixEnd_2744652 469775235108033590042527 := by
  unfold tailWord_2744652
  simp only [CollatzResearch.WordTrace]
  refine ⟨50052841226301014043838105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66737121635068018725117473 50052841226301014043838105)
  ·
    refine ⟨37539630919725760532878579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50052841226301014043838105 37539630919725760532878579)
    ·
      refine ⟨56309446379588640799317869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37539630919725760532878579 56309446379588640799317869)
      ·
        refine ⟨21116042392345740299744201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56309446379588640799317869 21116042392345740299744201)
        ·
          refine ⟨15837031794259305224808151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21116042392345740299744201 15837031794259305224808151)
          ·
            refine ⟨23755547691388957837212227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15837031794259305224808151 23755547691388957837212227)
            ·
              refine ⟨35633321537083436755818341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23755547691388957837212227 35633321537083436755818341)
              ·
                refine ⟨6681247788203144391715939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35633321537083436755818341 6681247788203144391715939)
                ·
                  refine ⟨10021871682304716587573909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6681247788203144391715939 10021871682304716587573909)
                  ·
                    refine ⟨469775235108033590042527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10021871682304716587573909 469775235108033590042527)
                    ·
                      rfl

theorem cell23_2744652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_2744652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744652 prefixEnd_2744652 := by exact prefixLift 2744652
  have htrace : WordTrace (prefixWord ++ tailWord_2744652) baseStart_2744652 baseEnd_2744652 := by
    simpa [prefixWord, tailWord_2744652, baseEnd_2744652] using wordTrace_append hprefix tailTrace_2744652
  have hstable : (prefixWord ++ tailWord_2744652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744652).length < 2 ^ (prefixWord ++ tailWord_2744652).sum := by decide
  have hdescent : baseEnd_2744652 < baseStart_2744652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744656 : List Nat := [2, 1, 1, 1, 1, 8, 2, 1, 1, 5]
def baseStart_2744656 : Nat := 118140960795 + 2744656 * 2 ^ 59
def prefixEnd_2744656 : Nat := 4983230072969 + 3 ^ 40 * 2744656 * 2
def baseEnd_2744656 : Nat := 469775919748906251492521

theorem tailTrace_2744656 : CollatzResearch.WordTrace tailWord_2744656 prefixEnd_2744656 469775919748906251492521 := by
  unfold tailWord_2744656
  simp only [CollatzResearch.WordTrace]
  refine ⟨50052914172293768385410911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66737218896391691180547881 50052914172293768385410911)
  ·
    refine ⟨75079371258440652578116367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50052914172293768385410911 75079371258440652578116367)
    ·
      refine ⟨112619056887660978867174551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75079371258440652578116367 112619056887660978867174551)
      ·
        refine ⟨168928585331491468300761827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112619056887660978867174551 168928585331491468300761827)
        ·
          refine ⟨253392877997237202451142741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168928585331491468300761827 253392877997237202451142741)
          ·
            refine ⟨2969447789030123466224329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 253392877997237202451142741 2969447789030123466224329)
            ·
              refine ⟨2227085841772592599668247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2969447789030123466224329 2227085841772592599668247)
              ·
                refine ⟨3340628762658888899502371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227085841772592599668247 3340628762658888899502371)
                ·
                  refine ⟨5010943143988333349253557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340628762658888899502371 5010943143988333349253557)
                  ·
                    refine ⟨469775919748906251492521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5010943143988333349253557 469775919748906251492521)
                    ·
                      rfl

theorem cell23_2744656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 1, 5].length) (baseStart_2744656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744656 prefixEnd_2744656 := by exact prefixLift 2744656
  have htrace : WordTrace (prefixWord ++ tailWord_2744656) baseStart_2744656 baseEnd_2744656 := by
    simpa [prefixWord, tailWord_2744656, baseEnd_2744656] using wordTrace_append hprefix tailTrace_2744656
  have hstable : (prefixWord ++ tailWord_2744656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744656).length < 2 ^ (prefixWord ++ tailWord_2744656).sum := by decide
  have hdescent : baseEnd_2744656 < baseStart_2744656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744679 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_2744679 : Nat := 118140960795 + 2744679 * 2 ^ 59
def prefixEnd_2744679 : Nat := 4983230072969 + 3 ^ 40 * 2744679 * 2
def baseEnd_2744679 : Nat := 1409339569301772164489957

theorem tailTrace_2744679 : CollatzResearch.WordTrace tailWord_2744679 prefixEnd_2744679 1409339569301772164489957 := by
  unfold tailWord_2744679
  simp only [CollatzResearch.WordTrace]
  refine ⟨100106667223504211698909091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66737778149002807799272727 100106667223504211698909091)
  ·
    refine ⟨150160000835256317548363637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100106667223504211698909091 150160000835256317548363637)
    ·
      refine ⟨14077500078305279770159091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150160000835256317548363637 14077500078305279770159091)
      ·
        refine ⟨21116250117457919655238637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14077500078305279770159091 21116250117457919655238637)
        ·
          refine ⟨7918593794046719870714489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21116250117457919655238637 7918593794046719870714489)
          ·
            refine ⟨5938945345535039903035867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7918593794046719870714489 5938945345535039903035867)
            ·
              refine ⟨8908418018302559854553801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5938945345535039903035867 8908418018302559854553801)
              ·
                refine ⟨6681313513726919890915351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8908418018302559854553801 6681313513726919890915351)
                ·
                  refine ⟨10021970270590379836373027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6681313513726919890915351 10021970270590379836373027)
                  ·
                    refine ⟨15032955405885569754559541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10021970270590379836373027 15032955405885569754559541)
                    ·
                      refine ⟨1409339569301772164489957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15032955405885569754559541 1409339569301772164489957)
                      ·
                        rfl

theorem cell23_2744679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_2744679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744679 prefixEnd_2744679 := by exact prefixLift 2744679
  have htrace : WordTrace (prefixWord ++ tailWord_2744679) baseStart_2744679 baseEnd_2744679 := by
    simpa [prefixWord, tailWord_2744679, baseEnd_2744679] using wordTrace_append hprefix tailTrace_2744679
  have hstable : (prefixWord ++ tailWord_2744679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744679).length < 2 ^ (prefixWord ++ tailWord_2744679).sum := by decide
  have hdescent : baseEnd_2744679 < baseStart_2744679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744693 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_2744693 : Nat := 118140960795 + 2744693 * 2 ^ 59
def prefixEnd_2744693 : Nat := 4983230072969 + 3 ^ 40 * 2744693 * 2
def baseEnd_2744693 : Nat := 1409346758030935109714893

theorem tailTrace_2744693 : CollatzResearch.WordTrace tailWord_2744693 prefixEnd_2744693 1409346758030935109714893 := by
  unfold tailWord_2744693
  simp only [CollatzResearch.WordTrace]
  refine ⟨100107177845453492089918733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66738118563635661393279155 100107177845453492089918733)
  ·
    refine ⟨37540191692045059533719525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100107177845453492089918733 37540191692045059533719525)
    ·
      refine ⟨7038785942258448662572411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37540191692045059533719525 7038785942258448662572411)
      ·
        refine ⟨10558178913387672993858617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7038785942258448662572411 10558178913387672993858617)
        ·
          refine ⟨7918634185040754745393963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10558178913387672993858617 7918634185040754745393963)
          ·
            refine ⟨11877951277561132118090945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7918634185040754745393963 11877951277561132118090945)
            ·
              refine ⟨8908463458170849088568209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11877951277561132118090945 8908463458170849088568209)
              ·
                refine ⟨6681347593628136816426157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8908463458170849088568209 6681347593628136816426157)
                ·
                  refine ⟨2505505347610551306159809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6681347593628136816426157 2505505347610551306159809)
                  ·
                    refine ⟨1879129010707913479619857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2505505347610551306159809 1879129010707913479619857)
                    ·
                      refine ⟨1409346758030935109714893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1879129010707913479619857 1409346758030935109714893)
                      ·
                        rfl

theorem cell23_2744693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_2744693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744693 prefixEnd_2744693 := by exact prefixLift 2744693
  have htrace : WordTrace (prefixWord ++ tailWord_2744693) baseStart_2744693 baseEnd_2744693 := by
    simpa [prefixWord, tailWord_2744693, baseEnd_2744693] using wordTrace_append hprefix tailTrace_2744693
  have hstable : (prefixWord ++ tailWord_2744693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744693).length < 2 ^ (prefixWord ++ tailWord_2744693).sum := by decide
  have hdescent : baseEnd_2744693 < baseStart_2744693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744699 : List Nat := [1, 1, 1, 1, 1, 9, 2, 7]
def baseStart_2744699 : Nat := 118140960795 + 2744699 * 2 ^ 59
def prefixEnd_2744699 : Nat := 4983230072969 + 3 ^ 40 * 2744699 * 2
def baseEnd_2744699 : Nat := 52198142182031929119995

theorem tailTrace_2744699 : CollatzResearch.WordTrace tailWord_2744699 prefixEnd_2744699 52198142182031929119995 := by
  unfold tailWord_2744699
  simp only [CollatzResearch.WordTrace]
  refine ⟨100107396683431755114637151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66738264455621170076424767 100107396683431755114637151)
  ·
    refine ⟨150161095025147632671955727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100107396683431755114637151 150161095025147632671955727)
    ·
      refine ⟨225241642537721449007933591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150161095025147632671955727 225241642537721449007933591)
      ·
        refine ⟨337862463806582173511900387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225241642537721449007933591 337862463806582173511900387)
        ·
          refine ⟨506793695709873260267850581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337862463806582173511900387 506793695709873260267850581)
          ·
            refine ⟨2969494310800038634381937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 506793695709873260267850581 2969494310800038634381937)
            ·
              refine ⟨2227120733100028975786453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2969494310800038634381937 2227120733100028975786453)
              ·
                refine ⟨52198142182031929119995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2227120733100028975786453 52198142182031929119995)
                ·
                  rfl

theorem cell23_2744699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 7].length) (baseStart_2744699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744699 prefixEnd_2744699 := by exact prefixLift 2744699
  have htrace : WordTrace (prefixWord ++ tailWord_2744699) baseStart_2744699 baseEnd_2744699 := by
    simpa [prefixWord, tailWord_2744699, baseEnd_2744699] using wordTrace_append hprefix tailTrace_2744699
  have hstable : (prefixWord ++ tailWord_2744699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744699).length < 2 ^ (prefixWord ++ tailWord_2744699).sum := by decide
  have hdescent : baseEnd_2744699 < baseStart_2744699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744737 : List Nat := [1, 2, 3, 5, 2, 1, 2, 1, 2, 4]
def baseStart_2744737 : Nat := 118140960795 + 2744737 * 2 ^ 59
def prefixEnd_2744737 : Nat := 4983230072969 + 3 ^ 40 * 2744737 * 2
def baseEnd_2744737 : Nat := 469789783726577645854897

theorem tailTrace_2744737 : CollatzResearch.WordTrace tailWord_2744737 prefixEnd_2744737 469789783726577645854897 := by
  unfold tailWord_2744737
  simp only [CollatzResearch.WordTrace]
  refine ⟨100108782657294087604520465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66739188438196058403013643 100108782657294087604520465)
  ·
    refine ⟨75081586992970565703390349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100108782657294087604520465 75081586992970565703390349)
    ·
      refine ⟨28155595122363962138771381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75081586992970565703390349 28155595122363962138771381)
      ·
        refine ⟨2639587042721621450509817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28155595122363962138771381 2639587042721621450509817)
        ·
          refine ⟨1979690282041216087882363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2639587042721621450509817 1979690282041216087882363)
          ·
            refine ⟨2969535423061824131823545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1979690282041216087882363 2969535423061824131823545)
            ·
              refine ⟨2227151567296368098867659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2969535423061824131823545 2227151567296368098867659)
              ·
                refine ⟨3340727350944552148301489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227151567296368098867659 3340727350944552148301489)
                ·
                  refine ⟨2505545513208414111226117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3340727350944552148301489 2505545513208414111226117)
                  ·
                    refine ⟨469789783726577645854897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2505545513208414111226117 469789783726577645854897)
                    ·
                      rfl

theorem cell23_2744737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_2744737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744737 prefixEnd_2744737 := by exact prefixLift 2744737
  have htrace : WordTrace (prefixWord ++ tailWord_2744737) baseStart_2744737 baseEnd_2744737 := by
    simpa [prefixWord, tailWord_2744737, baseEnd_2744737] using wordTrace_append hprefix tailTrace_2744737
  have hstable : (prefixWord ++ tailWord_2744737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744737).length < 2 ^ (prefixWord ++ tailWord_2744737).sum := by decide
  have hdescent : baseEnd_2744737 < baseStart_2744737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744743 : List Nat := [1, 1, 6, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_2744743 : Nat := 118140960795 + 2744743 * 2 ^ 59
def prefixEnd_2744743 : Nat := 4983230072969 + 3 ^ 40 * 2744743 * 2
def baseEnd_2744743 : Nat := 1409372432063659914089663

theorem tailTrace_2744743 : CollatzResearch.WordTrace tailWord_2744743 prefixEnd_2744743 1409372432063659914089663 := by
  unfold tailWord_2744743
  simp only [CollatzResearch.WordTrace]
  refine ⟨100109001495272350629238883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66739334330181567086159255 100109001495272350629238883)
  ·
    refine ⟨150163502242908525943858325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100109001495272350629238883 150163502242908525943858325)
    ·
      refine ⟨7038914167636337153618359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 150163502242908525943858325 7038914167636337153618359)
      ·
        refine ⟨10558371251454505730427539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7038914167636337153618359 10558371251454505730427539)
        ·
          refine ⟨15837556877181758595641309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10558371251454505730427539 15837556877181758595641309)
          ·
            refine ⟨5939083828943159473365491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15837556877181758595641309 5939083828943159473365491)
            ·
              refine ⟨8908625743414739210048237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5939083828943159473365491 8908625743414739210048237)
              ·
                refine ⟨3340734653780527203768089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8908625743414739210048237 3340734653780527203768089)
                ·
                  refine ⟨2505550990335395402826067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3340734653780527203768089 2505550990335395402826067)
                  ·
                    refine ⟨3758326485503093104239101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2505550990335395402826067 3758326485503093104239101)
                    ·
                      refine ⟨1409372432063659914089663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3758326485503093104239101 1409372432063659914089663)
                      ·
                        rfl

theorem cell23_2744743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_2744743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744743 prefixEnd_2744743 := by exact prefixLift 2744743
  have htrace : WordTrace (prefixWord ++ tailWord_2744743) baseStart_2744743 baseEnd_2744743 := by
    simpa [prefixWord, tailWord_2744743, baseEnd_2744743] using wordTrace_append hprefix tailTrace_2744743
  have hstable : (prefixWord ++ tailWord_2744743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744743).length < 2 ^ (prefixWord ++ tailWord_2744743).sum := by decide
  have hdescent : baseEnd_2744743 < baseStart_2744743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744753 : List Nat := [1, 2, 2, 4, 1, 2, 3, 2, 1, 3, 2]
def baseStart_2744753 : Nat := 118140960795 + 2744753 * 2 ^ 59
def prefixEnd_2744753 : Nat := 4983230072969 + 3 ^ 40 * 2744753 * 2
def baseEnd_2744753 : Nat := 1409377566870204874964617

theorem tailTrace_2744753 : CollatzResearch.WordTrace tailWord_2744753 prefixEnd_2744753 1409377566870204874964617 := by
  unfold tailWord_2744753
  simp only [CollatzResearch.WordTrace]
  refine ⟨100109366225236122337102913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66739577483490748224735275 100109366225236122337102913)
  ·
    refine ⟨75082024668927091752827185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100109366225236122337102913 75082024668927091752827185)
    ·
      refine ⟨56311518501695318814620389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75082024668927091752827185 56311518501695318814620389)
      ·
        refine ⟨10558409719067872277741323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56311518501695318814620389 10558409719067872277741323)
        ·
          refine ⟨15837614578601808416611985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10558409719067872277741323 15837614578601808416611985)
          ·
            refine ⟨11878210933951356312458989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15837614578601808416611985 11878210933951356312458989)
            ·
              refine ⟨4454329100231758617172121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11878210933951356312458989 4454329100231758617172121)
              ·
                refine ⟨3340746825173818962879091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4454329100231758617172121 3340746825173818962879091)
                ·
                  refine ⟨5011120237760728444318637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340746825173818962879091 5011120237760728444318637)
                  ·
                    refine ⟨1879170089160273166619489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5011120237760728444318637 1879170089160273166619489)
                    ·
                      refine ⟨1409377566870204874964617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1879170089160273166619489 1409377566870204874964617)
                      ·
                        rfl

theorem cell23_2744753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_2744753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744753 prefixEnd_2744753 := by exact prefixLift 2744753
  have htrace : WordTrace (prefixWord ++ tailWord_2744753) baseStart_2744753 baseEnd_2744753 := by
    simpa [prefixWord, tailWord_2744753, baseEnd_2744753] using wordTrace_append hprefix tailTrace_2744753
  have hstable : (prefixWord ++ tailWord_2744753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744753).length < 2 ^ (prefixWord ++ tailWord_2744753).sum := by decide
  have hdescent : baseEnd_2744753 < baseStart_2744753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744766 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2]
def baseStart_2744766 : Nat := 118140960795 + 2744766 * 2 ^ 59
def prefixEnd_2744766 : Nat := 4983230072969 + 3 ^ 40 * 2744766 * 2
def baseEnd_2744766 : Nat := 1409384242118713324102057

theorem tailTrace_2744766 : CollatzResearch.WordTrace tailWord_2744766 prefixEnd_2744766 1409384242118713324102057 := by
  unfold tailWord_2744766
  simp only [CollatzResearch.WordTrace]
  refine ⟨12513730046773628194665769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66739893582792683704884101 12513730046773628194665769)
  ·
    refine ⟨9385297535080221145999327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12513730046773628194665769 9385297535080221145999327)
    ·
      refine ⟨14077946302620331718998991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9385297535080221145999327 14077946302620331718998991)
      ·
        refine ⟨21116919453930497578498487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14077946302620331718998991 21116919453930497578498487)
        ·
          refine ⟨31675379180895746367747731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21116919453930497578498487 31675379180895746367747731)
          ·
            refine ⟨47513068771343619551621597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31675379180895746367747731 47513068771343619551621597)
            ·
              refine ⟨17817400789253857331858099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47513068771343619551621597 17817400789253857331858099)
              ·
                refine ⟨26726101183880785997787149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17817400789253857331858099 26726101183880785997787149)
                ·
                  refine ⟨10022287943955294749170181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26726101183880785997787149 10022287943955294749170181)
                  ·
                    refine ⟨1879178989491617765469409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10022287943955294749170181 1879178989491617765469409)
                    ·
                      refine ⟨1409384242118713324102057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1879178989491617765469409 1409384242118713324102057)
                      ·
                        rfl

theorem cell23_2744766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_2744766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744766 prefixEnd_2744766 := by exact prefixLift 2744766
  have htrace : WordTrace (prefixWord ++ tailWord_2744766) baseStart_2744766 baseEnd_2744766 := by
    simpa [prefixWord, tailWord_2744766, baseEnd_2744766] using wordTrace_append hprefix tailTrace_2744766
  have hstable : (prefixWord ++ tailWord_2744766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744766).length < 2 ^ (prefixWord ++ tailWord_2744766).sum := by decide
  have hdescent : baseEnd_2744766 < baseStart_2744766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744792 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 2, 1, 8]
def baseStart_2744792 : Nat := 118140960795 + 2744792 * 2 ^ 59
def prefixEnd_2744792 : Nat := 4983230072969 + 3 ^ 40 * 2744792 * 2
def baseEnd_2744792 : Nat := 1409397592615730222376937

theorem tailTrace_2744792 : CollatzResearch.WordTrace tailWord_2744792 prefixEnd_2744792 1409397592615730222376937 := by
  unfold tailWord_2744792
  simp only [CollatzResearch.WordTrace]
  refine ⟨50055394336047415998886315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66740525781396554665181753 50055394336047415998886315)
  ·
    refine ⟨75083091504071123998329473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50055394336047415998886315 75083091504071123998329473)
    ·
      refine ⟨56312318628053342998747105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75083091504071123998329473 56312318628053342998747105)
      ·
        refine ⟨42234238971040007249060329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56312318628053342998747105 42234238971040007249060329)
        ·
          refine ⟨31675679228280005436795247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42234238971040007249060329 31675679228280005436795247)
          ·
            refine ⟨47513518842420008155192871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31675679228280005436795247 47513518842420008155192871)
            ·
              refine ⟨71270278263630012232789307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47513518842420008155192871 71270278263630012232789307)
              ·
                refine ⟨106905417395445018349183961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71270278263630012232789307 106905417395445018349183961)
                ·
                  refine ⟨80179063046583763761887971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106905417395445018349183961 80179063046583763761887971)
                  ·
                    refine ⟨120268594569875645642831957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80179063046583763761887971 120268594569875645642831957)
                    ·
                      refine ⟨1409397592615730222376937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 120268594569875645642831957 1409397592615730222376937)
                      ·
                        rfl

theorem cell23_2744792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_2744792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744792 prefixEnd_2744792 := by exact prefixLift 2744792
  have htrace : WordTrace (prefixWord ++ tailWord_2744792) baseStart_2744792 baseEnd_2744792 := by
    simpa [prefixWord, tailWord_2744792, baseEnd_2744792] using wordTrace_append hprefix tailTrace_2744792
  have hstable : (prefixWord ++ tailWord_2744792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744792).length < 2 ^ (prefixWord ++ tailWord_2744792).sum := by decide
  have hdescent : baseEnd_2744792 < baseStart_2744792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744799 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 3]
def baseStart_2744799 : Nat := 118140960795 + 2744799 * 2 ^ 59
def prefixEnd_2744799 : Nat := 4983230072969 + 3 ^ 40 * 2744799 * 2
def baseEnd_2744799 : Nat := 1409401186980311694989405

theorem tailTrace_2744799 : CollatzResearch.WordTrace tailWord_2744799 prefixEnd_2744799 1409401186980311694989405 := by
  unfold tailWord_2744799
  simp only [CollatzResearch.WordTrace]
  refine ⟨100111043983069472193277451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66740695988712981462184967 100111043983069472193277451)
  ·
    refine ⟨150166565974604208289916177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100111043983069472193277451 150166565974604208289916177)
    ·
      refine ⟨112624924480953156217437133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150166565974604208289916177 112624924480953156217437133)
      ·
        refine ⟨42234346680357433581538925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112624924480953156217437133 42234346680357433581538925)
        ·
          refine ⟨15837880005134037593077097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42234346680357433581538925 15837880005134037593077097)
          ·
            refine ⟨11878410003850528194807823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15837880005134037593077097 11878410003850528194807823)
            ·
              refine ⟨17817615005775792292211735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11878410003850528194807823 17817615005775792292211735)
              ·
                refine ⟨26726422508663688438317603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17817615005775792292211735 26726422508663688438317603)
                ·
                  refine ⟨40089633762995532657476405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26726422508663688438317603 40089633762995532657476405)
                  ·
                    refine ⟨3758403165280831186638413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40089633762995532657476405 3758403165280831186638413)
                    ·
                      refine ⟨1409401186980311694989405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3758403165280831186638413 1409401186980311694989405)
                      ·
                        rfl

theorem cell23_2744799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_2744799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744799 prefixEnd_2744799 := by exact prefixLift 2744799
  have htrace : WordTrace (prefixWord ++ tailWord_2744799) baseStart_2744799 baseEnd_2744799 := by
    simpa [prefixWord, tailWord_2744799, baseEnd_2744799] using wordTrace_append hprefix tailTrace_2744799
  have hstable : (prefixWord ++ tailWord_2744799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744799).length < 2 ^ (prefixWord ++ tailWord_2744799).sum := by decide
  have hdescent : baseEnd_2744799 < baseStart_2744799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744832 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 3, 10]
def baseStart_2744832 : Nat := 118140960795 + 2744832 * 2 ^ 59
def prefixEnd_2744832 : Nat := 4983230072969 + 3 ^ 40 * 2744832 * 2
def baseEnd_2744832 : Nat := 469806043947303355292251

theorem tailTrace_2744832 : CollatzResearch.WordTrace tailWord_2744832 prefixEnd_2744832 469806043947303355292251 := by
  unfold tailWord_2744832
  simp only [CollatzResearch.WordTrace]
  refine ⟨50056123795974959414614375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66741498394633279219485833 50056123795974959414614375)
  ·
    refine ⟨75084185693962439121921563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50056123795974959414614375 75084185693962439121921563)
    ·
      refine ⟨112626278540943658682882345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75084185693962439121921563 112626278540943658682882345)
      ·
        refine ⟨84469708905707744012161759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112626278540943658682882345 84469708905707744012161759)
        ·
          refine ⟨126704563358561616018242639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84469708905707744012161759 126704563358561616018242639)
          ·
            refine ⟨190056845037842424027363959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126704563358561616018242639 190056845037842424027363959)
            ·
              refine ⟨285085267556763636041045939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190056845037842424027363959 285085267556763636041045939)
              ·
                refine ⟨427627901335145454061568909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285085267556763636041045939 427627901335145454061568909)
                ·
                  refine ⟨160360463000679545273088341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427627901335145454061568909 160360463000679545273088341)
                  ·
                    refine ⟨469806043947303355292251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 160360463000679545273088341 469806043947303355292251)
                    ·
                      rfl

theorem cell23_2744832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 10].length) (baseStart_2744832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744832 prefixEnd_2744832 := by exact prefixLift 2744832
  have htrace : WordTrace (prefixWord ++ tailWord_2744832) baseStart_2744832 baseEnd_2744832 := by
    simpa [prefixWord, tailWord_2744832, baseEnd_2744832] using wordTrace_append hprefix tailTrace_2744832
  have hstable : (prefixWord ++ tailWord_2744832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744832).length < 2 ^ (prefixWord ++ tailWord_2744832).sum := by decide
  have hdescent : baseEnd_2744832 < baseStart_2744832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744834 : List Nat := [3, 4, 1, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_2744834 : Nat := 118140960795 + 2744834 * 2 ^ 59
def prefixEnd_2744834 : Nat := 4983230072969 + 3 ^ 40 * 2744834 * 2
def baseEnd_2744834 : Nat := 1409419158803219058051745

theorem tailTrace_2744834 : CollatzResearch.WordTrace tailWord_2744834 prefixEnd_2744834 1409419158803219058051745 := by
  unfold tailWord_2744834
  simp only [CollatzResearch.WordTrace]
  refine ⟨25028080134485668292700389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66741547025295115447201037 25028080134485668292700389)
  ·
    refine ⟨4692765025216062804881323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25028080134485668292700389 4692765025216062804881323)
    ·
      refine ⟨7039147537824094207321985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4692765025216062804881323 7039147537824094207321985)
      ·
        refine ⟨5279360653368070655491489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7039147537824094207321985 5279360653368070655491489)
        ·
          refine ⟨3959520490026052991618617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5279360653368070655491489 3959520490026052991618617)
          ·
            refine ⟨2969640367519539743713963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3959520490026052991618617 2969640367519539743713963)
            ·
              refine ⟨4454460551279309615570945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2969640367519539743713963 4454460551279309615570945)
              ·
                refine ⟨3340845413459482211678209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4454460551279309615570945 3340845413459482211678209)
                ·
                  refine ⟨2505634060094611658758657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3340845413459482211678209 2505634060094611658758657)
                  ·
                    refine ⟨1879225545070958744068993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2505634060094611658758657 1879225545070958744068993)
                    ·
                      refine ⟨1409419158803219058051745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1879225545070958744068993 1409419158803219058051745)
                      ·
                        rfl

theorem cell23_2744834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_2744834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744834 prefixEnd_2744834 := by exact prefixLift 2744834
  have htrace : WordTrace (prefixWord ++ tailWord_2744834) baseStart_2744834 baseEnd_2744834 := by
    simpa [prefixWord, tailWord_2744834, baseEnd_2744834] using wordTrace_append hprefix tailTrace_2744834
  have hstable : (prefixWord ++ tailWord_2744834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744834).length < 2 ^ (prefixWord ++ tailWord_2744834).sum := by decide
  have hdescent : baseEnd_2744834 < baseStart_2744834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744893 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 2, 2, 3]
def baseStart_2744893 : Nat := 118140960795 + 2744893 * 2 ^ 59
def prefixEnd_2744893 : Nat := 4983230072969 + 3 ^ 40 * 2744893 * 2
def baseEnd_2744893 : Nat := 1409449454161834327213973

theorem tailTrace_2744893 : CollatzResearch.WordTrace tailWord_2744893 prefixEnd_2744893 1409449454161834327213973 := by
  unfold tailWord_2744893
  simp only [CollatzResearch.WordTrace]
  refine ⟨100114472444728926247199333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66742981629819284164799555 100114472444728926247199333)
  ·
    refine ⟨18771463583386673671349875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100114472444728926247199333 18771463583386673671349875)
    ·
      refine ⟨28157195375080010507024813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18771463583386673671349875 28157195375080010507024813)
      ·
        refine ⟨10558948265655003940134305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28157195375080010507024813 10558948265655003940134305)
        ·
          refine ⟨7919211199241252955100729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10558948265655003940134305 7919211199241252955100729)
          ·
            refine ⟨5939408399430939716325547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7919211199241252955100729 5939408399430939716325547)
            ·
              refine ⟨8909112599146409574488321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5939408399430939716325547 8909112599146409574488321)
              ·
                refine ⟨6681834449359807180866241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8909112599146409574488321 6681834449359807180866241)
                ·
                  refine ⟨5011375837019855385649681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6681834449359807180866241 5011375837019855385649681)
                  ·
                    refine ⟨3758531877764891539237261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5011375837019855385649681 3758531877764891539237261)
                    ·
                      refine ⟨1409449454161834327213973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3758531877764891539237261 1409449454161834327213973)
                      ·
                        rfl

theorem cell23_2744893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_2744893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744893 prefixEnd_2744893 := by exact prefixLift 2744893
  have htrace : WordTrace (prefixWord ++ tailWord_2744893) baseStart_2744893 baseEnd_2744893 := by
    simpa [prefixWord, tailWord_2744893, baseEnd_2744893] using wordTrace_append hprefix tailTrace_2744893
  have hstable : (prefixWord ++ tailWord_2744893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744893).length < 2 ^ (prefixWord ++ tailWord_2744893).sum := by decide
  have hdescent : baseEnd_2744893 < baseStart_2744893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744913 : List Nat := [1, 2, 2, 1, 3, 5, 2, 1, 6]
def baseStart_2744913 : Nat := 118140960795 + 2744913 * 2 ^ 59
def prefixEnd_2744913 : Nat := 4983230072969 + 3 ^ 40 * 2744913 * 2
def baseEnd_2744913 : Nat := 156606635974991583218209

theorem tailTrace_2744913 : CollatzResearch.WordTrace tailWord_2744913 prefixEnd_2744913 156606635974991583218209 := by
  unfold tailWord_2744913
  simp only [CollatzResearch.WordTrace]
  refine ⟨100115201904656469662927393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66743467936437646441951595 100115201904656469662927393)
  ·
    refine ⟨75086401428492352247195545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100115201904656469662927393 75086401428492352247195545)
    ·
      refine ⟨56314801071369264185396659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75086401428492352247195545 56314801071369264185396659)
      ·
        refine ⟨84472201607053896278094989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56314801071369264185396659 84472201607053896278094989)
        ·
          refine ⟨31677075602645211104285621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84472201607053896278094989 31677075602645211104285621)
          ·
            refine ⟨2969725837747988541026777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31677075602645211104285621 2969725837747988541026777)
            ·
              refine ⟨2227294378310991405770083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2969725837747988541026777 2227294378310991405770083)
              ·
                refine ⟨3340941567466487108655125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227294378310991405770083 3340941567466487108655125)
                ·
                  refine ⟨156606635974991583218209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3340941567466487108655125 156606635974991583218209)
                  ·
                    rfl

theorem cell23_2744913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 6].length) (baseStart_2744913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744913 prefixEnd_2744913 := by exact prefixLift 2744913
  have htrace : WordTrace (prefixWord ++ tailWord_2744913) baseStart_2744913 baseEnd_2744913 := by
    simpa [prefixWord, tailWord_2744913, baseEnd_2744913] using wordTrace_append hprefix tailTrace_2744913
  have hstable : (prefixWord ++ tailWord_2744913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744913).length < 2 ^ (prefixWord ++ tailWord_2744913).sum := by decide
  have hdescent : baseEnd_2744913 < baseStart_2744913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744956 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 4, 4]
def baseStart_2744956 : Nat := 118140960795 + 2744956 * 2 ^ 59
def prefixEnd_2744956 : Nat := 4983230072969 + 3 ^ 40 * 2744956 * 2
def baseEnd_2744956 : Nat := 469827267814355860242061

theorem tailTrace_2744956 : CollatzResearch.WordTrace tailWord_2744956 prefixEnd_2744956 469827267814355860242061 := by
  unfold tailWord_2744956
  simp only [CollatzResearch.WordTrace]
  refine ⟨50058385121750344003371361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66744513495667125337828481 50058385121750344003371361)
  ·
    refine ⟨37543788841312758002528521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50058385121750344003371361 37543788841312758002528521)
    ·
      refine ⟨28157841630984568501896391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37543788841312758002528521 28157841630984568501896391)
      ·
        refine ⟨42236762446476852752844587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28157841630984568501896391 42236762446476852752844587)
        ·
          refine ⟨63355143669715279129266881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42236762446476852752844587 63355143669715279129266881)
          ·
            refine ⟨47516357752286459346950161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63355143669715279129266881 47516357752286459346950161)
            ·
              refine ⟨35637268314214844510212621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47516357752286459346950161 35637268314214844510212621)
              ·
                refine ⟨13363975617830566691329733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35637268314214844510212621 13363975617830566691329733)
                ·
                  refine ⟨2505745428343231254624325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13363975617830566691329733 2505745428343231254624325)
                  ·
                    refine ⟨469827267814355860242061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2505745428343231254624325 469827267814355860242061)
                    ·
                      rfl

theorem cell23_2744956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_2744956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744956 prefixEnd_2744956 := by exact prefixLift 2744956
  have htrace : WordTrace (prefixWord ++ tailWord_2744956) baseStart_2744956 baseEnd_2744956 := by
    simpa [prefixWord, tailWord_2744956, baseEnd_2744956] using wordTrace_append hprefix tailTrace_2744956
  have hstable : (prefixWord ++ tailWord_2744956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744956).length < 2 ^ (prefixWord ++ tailWord_2744956).sum := by decide
  have hdescent : baseEnd_2744956 < baseStart_2744956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744957 : List Nat := [1, 4, 1, 1, 5, 1, 1, 4, 1, 1, 3]
def baseStart_2744957 : Nat := 118140960795 + 2744957 * 2 ^ 59
def prefixEnd_2744957 : Nat := 4983230072969 + 3 ^ 40 * 2744957 * 2
def baseEnd_2744957 : Nat := 1409482316923722076813679

theorem tailTrace_2744957 : CollatzResearch.WordTrace tailWord_2744957 prefixEnd_2744957 1409482316923722076813679 := by
  unfold tailWord_2744957
  simp only [CollatzResearch.WordTrace]
  refine ⟨100116806716497065177529125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66744537810998043451686083 100116806716497065177529125)
  ·
    refine ⟨18771901259343199720786711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100116806716497065177529125 18771901259343199720786711)
    ·
      refine ⟨28157851889014799581180067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18771901259343199720786711 28157851889014799581180067)
      ·
        refine ⟨42236777833522199371770101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28157851889014799581180067 42236777833522199371770101)
        ·
          refine ⟨3959697921892706191103447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42236777833522199371770101 3959697921892706191103447)
          ·
            refine ⟨5939546882839059286655171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3959697921892706191103447 5939546882839059286655171)
            ·
              refine ⟨8909320324258588929982757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5939546882839059286655171 8909320324258588929982757)
              ·
                refine ⟨1670497560798485424371767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8909320324258588929982757 1670497560798485424371767)
                ·
                  refine ⟨2505746341197728136557651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1670497560798485424371767 2505746341197728136557651)
                  ·
                    refine ⟨3758619511796592204836477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2505746341197728136557651 3758619511796592204836477)
                    ·
                      refine ⟨1409482316923722076813679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3758619511796592204836477 1409482316923722076813679)
                      ·
                        rfl

theorem cell23_2744957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_2744957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744957 prefixEnd_2744957 := by exact prefixLift 2744957
  have htrace : WordTrace (prefixWord ++ tailWord_2744957) baseStart_2744957 baseEnd_2744957 := by
    simpa [prefixWord, tailWord_2744957, baseEnd_2744957] using wordTrace_append hprefix tailTrace_2744957
  have hstable : (prefixWord ++ tailWord_2744957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744957).length < 2 ^ (prefixWord ++ tailWord_2744957).sum := by decide
  have hdescent : baseEnd_2744957 < baseStart_2744957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744959 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 6]
def baseStart_2744959 : Nat := 118140960795 + 2744959 * 2 ^ 59
def prefixEnd_2744959 : Nat := 4983230072969 + 3 ^ 40 * 2744959 * 2
def baseEnd_2744959 : Nat := 1409483343885031068988669

theorem tailTrace_2744959 : CollatzResearch.WordTrace tailWord_2744959 prefixEnd_2744959 1409483343885031068988669 := by
  unfold tailWord_2744959
  simp only [CollatzResearch.WordTrace]
  refine ⟨100116879662489819519101931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66744586441659879679401287 100116879662489819519101931)
  ·
    refine ⟨150175319493734729278652897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100116879662489819519101931 150175319493734729278652897)
    ·
      refine ⟨112631489620301046958989673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150175319493734729278652897 112631489620301046958989673)
      ·
        refine ⟨84473617215225785219242255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112631489620301046958989673 84473617215225785219242255)
        ·
          refine ⟨126710425822838677828863383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84473617215225785219242255 126710425822838677828863383)
          ·
            refine ⟨190065638734258016743295075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126710425822838677828863383 190065638734258016743295075)
            ·
              refine ⟨285098458101387025114942613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190065638734258016743295075 285098458101387025114942613)
              ·
                refine ⟨13363990223502516802262935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 285098458101387025114942613 13363990223502516802262935)
                ·
                  refine ⟨20045985335253775203394403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13363990223502516802262935 20045985335253775203394403)
                  ·
                    refine ⟨30068978002880662805091605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20045985335253775203394403 30068978002880662805091605)
                    ·
                      refine ⟨1409483343885031068988669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30068978002880662805091605 1409483343885031068988669)
                      ·
                        rfl

theorem cell23_2744959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_2744959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744959 prefixEnd_2744959 := by exact prefixLift 2744959
  have htrace : WordTrace (prefixWord ++ tailWord_2744959) baseStart_2744959 baseEnd_2744959 := by
    simpa [prefixWord, tailWord_2744959, baseEnd_2744959] using wordTrace_append hprefix tailTrace_2744959
  have hstable : (prefixWord ++ tailWord_2744959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744959).length < 2 ^ (prefixWord ++ tailWord_2744959).sum := by decide
  have hdescent : baseEnd_2744959 < baseStart_2744959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744983 : List Nat := [1, 1, 3, 3, 2, 1, 2, 4, 1, 2, 3]
def baseStart_2744983 : Nat := 118140960795 + 2744983 * 2 ^ 59
def prefixEnd_2744983 : Nat := 4983230072969 + 3 ^ 40 * 2744983 * 2
def baseEnd_2744983 : Nat := 1409495667420738975088559

theorem tailTrace_2744983 : CollatzResearch.WordTrace tailWord_2744983 prefixEnd_2744983 1409495667420738975088559 := by
  unfold tailWord_2744983
  simp only [CollatzResearch.WordTrace]
  refine ⟨100117755014402871617975603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66745170009601914411983735 100117755014402871617975603)
  ·
    refine ⟨150176632521604307426963405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100117755014402871617975603 150176632521604307426963405)
    ·
      refine ⟨56316237195601615285111277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150176632521604307426963405 56316237195601615285111277)
      ·
        refine ⟨21118588948350605731916729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56316237195601615285111277 21118588948350605731916729)
        ·
          refine ⟨15838941711262954298937547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21118588948350605731916729 15838941711262954298937547)
          ·
            refine ⟨23758412566894431448406321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15838941711262954298937547 23758412566894431448406321)
            ·
              refine ⟨17818809425170823586304741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23758412566894431448406321 17818809425170823586304741)
              ·
                refine ⟨3341026767219529422432139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17818809425170823586304741 3341026767219529422432139)
                ·
                  refine ⟨5011540150829294133648209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3341026767219529422432139 5011540150829294133648209)
                  ·
                    refine ⟨3758655113121970600236157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5011540150829294133648209 3758655113121970600236157)
                    ·
                      refine ⟨1409495667420738975088559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3758655113121970600236157 1409495667420738975088559)
                      ·
                        rfl

theorem cell23_2744983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_2744983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2744983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2744983 prefixEnd_2744983 := by exact prefixLift 2744983
  have htrace : WordTrace (prefixWord ++ tailWord_2744983) baseStart_2744983 baseEnd_2744983 := by
    simpa [prefixWord, tailWord_2744983, baseEnd_2744983] using wordTrace_append hprefix tailTrace_2744983
  have hstable : (prefixWord ++ tailWord_2744983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744983).length < 2 ^ (prefixWord ++ tailWord_2744983).sum := by decide
  have hdescent : baseEnd_2744983 < baseStart_2744983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745037 : List Nat := [1, 6, 2, 1, 2, 2, 2, 7]
def baseStart_2745037 : Nat := 118140960795 + 2745037 * 2 ^ 59
def prefixEnd_2745037 : Nat := 4983230072969 + 3 ^ 40 * 2745037 * 2
def baseEnd_2745037 : Nat := 52204570199114139400493

theorem tailTrace_2745037 : CollatzResearch.WordTrace tailWord_2745037 prefixEnd_2745037 52204570199114139400493 := by
  unfold tailWord_2745037
  simp only [CollatzResearch.WordTrace]
  refine ⟨100119724556207238840441365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66746483037471492560294243 100119724556207238840441365)
  ·
    refine ⟨4693112088572214320645689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 100119724556207238840441365 4693112088572214320645689)
    ·
      refine ⟨3519834066429160740484267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4693112088572214320645689 3519834066429160740484267)
      ·
        refine ⟨5279751099643741110726401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3519834066429160740484267 5279751099643741110726401)
        ·
          refine ⟨3959813324732805833044801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5279751099643741110726401 3959813324732805833044801)
          ·
            refine ⟨2969859993549604374783601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3959813324732805833044801 2969859993549604374783601)
            ·
              refine ⟨2227394995162203281087701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2969859993549604374783601 2227394995162203281087701)
              ·
                refine ⟨52204570199114139400493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2227394995162203281087701 52204570199114139400493)
                ·
                  rfl

theorem cell23_2745037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 7].length) (baseStart_2745037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745037 prefixEnd_2745037 := by exact prefixLift 2745037
  have htrace : WordTrace (prefixWord ++ tailWord_2745037) baseStart_2745037 baseEnd_2745037 := by
    simpa [prefixWord, tailWord_2745037, baseEnd_2745037] using wordTrace_append hprefix tailTrace_2745037
  have hstable : (prefixWord ++ tailWord_2745037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745037).length < 2 ^ (prefixWord ++ tailWord_2745037).sum := by decide
  have hdescent : baseEnd_2745037 < baseStart_2745037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745056 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 3]
def baseStart_2745056 : Nat := 118140960795 + 2745056 * 2 ^ 59
def prefixEnd_2745056 : Nat := 4983230072969 + 3 ^ 40 * 2745056 * 2
def baseEnd_2745056 : Nat := 1409533151508517189475723

theorem tailTrace_2745056 : CollatzResearch.WordTrace tailWord_2745056 prefixEnd_2745056 1409533151508517189475723 := by
  unfold tailWord_2745056
  simp only [CollatzResearch.WordTrace]
  refine ⟨50060208771569202542691511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66746945028758936723588681 50060208771569202542691511)
  ·
    refine ⟨75090313157353803814037267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50060208771569202542691511 75090313157353803814037267)
    ·
      refine ⟨112635469736030705721055901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75090313157353803814037267 112635469736030705721055901)
      ·
        refine ⟨42238301151011514645395963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112635469736030705721055901 42238301151011514645395963)
        ·
          refine ⟨63357451726517271968093945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42238301151011514645395963 63357451726517271968093945)
          ·
            refine ⟨47518088794887953976070459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63357451726517271968093945 47518088794887953976070459)
            ·
              refine ⟨71277133192331930964105689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47518088794887953976070459 71277133192331930964105689)
              ·
                refine ⟨53457849894248948223079267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71277133192331930964105689 53457849894248948223079267)
                ·
                  refine ⟨80186774841373422334618901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53457849894248948223079267 80186774841373422334618901)
                  ·
                    refine ⟨3758755070689379171935261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80186774841373422334618901 3758755070689379171935261)
                    ·
                      refine ⟨1409533151508517189475723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3758755070689379171935261 1409533151508517189475723)
                      ·
                        rfl

theorem cell23_2745056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_2745056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745056 prefixEnd_2745056 := by exact prefixLift 2745056
  have htrace : WordTrace (prefixWord ++ tailWord_2745056) baseStart_2745056 baseEnd_2745056 := by
    simpa [prefixWord, tailWord_2745056, baseEnd_2745056] using wordTrace_append hprefix tailTrace_2745056
  have hstable : (prefixWord ++ tailWord_2745056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745056).length < 2 ^ (prefixWord ++ tailWord_2745056).sum := by decide
  have hdescent : baseEnd_2745056 < baseStart_2745056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
