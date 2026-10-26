import V185TrunkScan21Chunk051

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_626660 : List Nat := [2, 3, 1, 1, 1, 1, 7, 2, 3]
def baseStart_626660 : Nat := 118140960795 + 626660 * 2 ^ 59
def prefixEnd_626660 : Nat := 4983230072969 + 3 ^ 40 * 626660 * 2
def baseEnd_626660 : Nat := 143012349754054854919133

theorem tailTrace_626660 : CollatzResearch.WordTrace tailWord_626660 prefixEnd_626660 143012349754054854919133 := by
  unfold tailWord_626660
  simp only [CollatzResearch.WordTrace]
  refine ⟨11428083954862659926206717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15237445273150213234942289 11428083954862659926206717)
  ·
    refine ⟨4285531483073497472327519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11428083954862659926206717 4285531483073497472327519)
    ·
      refine ⟨6428297224610246208491279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4285531483073497472327519 6428297224610246208491279)
      ·
        refine ⟨9642445836915369312736919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6428297224610246208491279 9642445836915369312736919)
        ·
          refine ⟨14463668755373053969105379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9642445836915369312736919 14463668755373053969105379)
          ·
            refine ⟨21695503133059580953658069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14463668755373053969105379 21695503133059580953658069)
            ·
              refine ⟨508488354681083928601361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21695503133059580953658069 508488354681083928601361)
              ·
                refine ⟨381366266010812946451021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508488354681083928601361 381366266010812946451021)
                ·
                  refine ⟨143012349754054854919133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381366266010812946451021 143012349754054854919133)
                  ·
                    rfl

theorem cell21_626660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_626660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626660 prefixEnd_626660 := by exact prefixLift 626660
  have htrace : WordTrace (prefixWord ++ tailWord_626660) baseStart_626660 baseEnd_626660 := by
    simpa [prefixWord, tailWord_626660, baseEnd_626660] using wordTrace_append hprefix tailTrace_626660
  have hstable : (prefixWord ++ tailWord_626660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626660).length < 2 ^ (prefixWord ++ tailWord_626660).sum := by decide
  have hdescent : baseEnd_626660 < baseStart_626660 := by decide
  rcases family_descends (prefixWord ++ tailWord_626660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626671 : List Nat := [1, 1, 2, 1, 4, 2, 4, 6]
def baseStart_626671 : Nat := 118140960795 + 626671 * 2 ^ 59
def prefixEnd_626671 : Nat := 4983230072969 + 3 ^ 40 * 626671 * 2
def baseEnd_626671 : Nat := 47671620034640426745259

theorem tailTrace_626671 : CollatzResearch.WordTrace tailWord_626671 prefixEnd_626671 47671620034640426745259 := by
  unfold tailWord_626671
  simp only [CollatzResearch.WordTrace]
  refine ⟨22856569112685468731063867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15237712741790312487375911 22856569112685468731063867)
  ·
    refine ⟨34284853669028203096595801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22856569112685468731063867 34284853669028203096595801)
    ·
      refine ⟨25713640251771152322446851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34284853669028203096595801 25713640251771152322446851)
      ·
        refine ⟨38570460377656728483670277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25713640251771152322446851 38570460377656728483670277)
        ·
          refine ⟨7231961320810636590688177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38570460377656728483670277 7231961320810636590688177)
          ·
            refine ⟨5423970990607977443016133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7231961320810636590688177 5423970990607977443016133)
            ·
              refine ⟨1016994560738995770565525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5423970990607977443016133 1016994560738995770565525)
              ·
                refine ⟨47671620034640426745259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1016994560738995770565525 47671620034640426745259)
                ·
                  rfl

theorem cell21_626671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 6].length) (baseStart_626671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626671 prefixEnd_626671 := by exact prefixLift 626671
  have htrace : WordTrace (prefixWord ++ tailWord_626671) baseStart_626671 baseEnd_626671 := by
    simpa [prefixWord, tailWord_626671, baseEnd_626671] using wordTrace_append hprefix tailTrace_626671
  have hstable : (prefixWord ++ tailWord_626671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626671).length < 2 ^ (prefixWord ++ tailWord_626671).sum := by decide
  have hdescent : baseEnd_626671 < baseStart_626671 := by decide
  rcases family_descends (prefixWord ++ tailWord_626671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626708 : List Nat := [2, 4, 3, 2, 1, 1, 2, 2, 4]
def baseStart_626708 : Nat := 118140960795 + 626708 * 2 ^ 59
def prefixEnd_626708 : Nat := 4983230072969 + 3 ^ 40 * 626708 * 2
def baseEnd_626708 : Nat := 143023304008017438119035

theorem tailTrace_626708 : CollatzResearch.WordTrace tailWord_626708 prefixEnd_626708 143023304008017438119035 := by
  unfold tailWord_626708
  simp only [CollatzResearch.WordTrace]
  refine ⟨11428959306775712025080389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15238612409034282700107185 11428959306775712025080389)
  ·
    refine ⟨2142929870020446004702573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11428959306775712025080389 2142929870020446004702573)
    ·
      refine ⟨803598701257667251763465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2142929870020446004702573 803598701257667251763465)
      ·
        refine ⟨602699025943250438822599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 803598701257667251763465 602699025943250438822599)
        ·
          refine ⟨904048538914875658233899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602699025943250438822599 904048538914875658233899)
          ·
            refine ⟨1356072808372313487350849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904048538914875658233899 1356072808372313487350849)
            ·
              refine ⟨1017054606279235115513137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1356072808372313487350849 1017054606279235115513137)
              ·
                refine ⟨762790954709426336634853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1017054606279235115513137 762790954709426336634853)
                ·
                  refine ⟨143023304008017438119035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 762790954709426336634853 143023304008017438119035)
                  ·
                    rfl

theorem cell21_626708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_626708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626708 prefixEnd_626708 := by exact prefixLift 626708
  have htrace : WordTrace (prefixWord ++ tailWord_626708) baseStart_626708 baseEnd_626708 := by
    simpa [prefixWord, tailWord_626708, baseEnd_626708] using wordTrace_append hprefix tailTrace_626708
  have hstable : (prefixWord ++ tailWord_626708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626708).length < 2 ^ (prefixWord ++ tailWord_626708).sum := by decide
  have hdescent : baseEnd_626708 < baseStart_626708 := by decide
  rcases family_descends (prefixWord ++ tailWord_626708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626719 : List Nat := [1, 1, 2, 4, 1, 2, 3, 4, 3]
def baseStart_626719 : Nat := 118140960795 + 626719 * 2 ^ 59
def prefixEnd_626719 : Nat := 4983230072969 + 3 ^ 40 * 626719 * 2
def baseEnd_626719 : Nat := 143025814357883863435679

theorem tailTrace_626719 : CollatzResearch.WordTrace tailWord_626719 prefixEnd_626719 143025814357883863435679 := by
  unfold tailWord_626719
  simp only [CollatzResearch.WordTrace]
  refine ⟨22858319816511572928811211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15238879877674381952540807 22858319816511572928811211)
  ·
    refine ⟨34287479724767359393216817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22858319816511572928811211 34287479724767359393216817)
    ·
      refine ⟨25715609793575519544912613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34287479724767359393216817 25715609793575519544912613)
      ·
        refine ⟨4821676836295409914671115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25715609793575519544912613 4821676836295409914671115)
        ·
          refine ⟨7232515254443114872006673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4821676836295409914671115 7232515254443114872006673)
          ·
            refine ⟨5424386440832336154005005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7232515254443114872006673 5424386440832336154005005)
            ·
              refine ⟨2034144915312126057751877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5424386440832336154005005 2034144915312126057751877)
              ·
                refine ⟨381402171621023635828477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2034144915312126057751877 381402171621023635828477)
                ·
                  refine ⟨143025814357883863435679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381402171621023635828477 143025814357883863435679)
                  ·
                    rfl

theorem cell21_626719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 3].length) (baseStart_626719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626719 prefixEnd_626719 := by exact prefixLift 626719
  have htrace : WordTrace (prefixWord ++ tailWord_626719) baseStart_626719 baseEnd_626719 := by
    simpa [prefixWord, tailWord_626719, baseEnd_626719] using wordTrace_append hprefix tailTrace_626719
  have hstable : (prefixWord ++ tailWord_626719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626719).length < 2 ^ (prefixWord ++ tailWord_626719).sum := by decide
  have hdescent : baseEnd_626719 < baseStart_626719 := by decide
  rcases family_descends (prefixWord ++ tailWord_626719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626761 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 7]
def baseStart_626761 : Nat := 118140960795 + 626761 * 2 ^ 59
def prefixEnd_626761 : Nat := 4983230072969 + 3 ^ 40 * 626761 * 2
def baseEnd_626761 : Nat := 143035399330101123735593

theorem tailTrace_626761 : CollatzResearch.WordTrace tailWord_626761 prefixEnd_626761 143035399330101123735593 := by
  unfold tailWord_626761
  simp only [CollatzResearch.WordTrace]
  refine ⟨22859851682359414101840137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15239901121572942734560091 22859851682359414101840137)
  ·
    refine ⟨17144888761769560576380103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22859851682359414101840137 17144888761769560576380103)
    ·
      refine ⟨25717333142654340864570155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17144888761769560576380103 25717333142654340864570155)
      ·
        refine ⟨38575999713981511296855233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25717333142654340864570155 38575999713981511296855233)
        ·
          refine ⟨28931999785486133472641425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38575999713981511296855233 28931999785486133472641425)
          ·
            refine ⟨21698999839114600104481069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28931999785486133472641425 21698999839114600104481069)
            ·
              refine ⟨8137124939667975039180401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21698999839114600104481069 8137124939667975039180401)
              ·
                refine ⟨6102843704750981279385301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8137124939667975039180401 6102843704750981279385301)
                ·
                  refine ⟨143035399330101123735593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6102843704750981279385301 143035399330101123735593)
                  ·
                    rfl

theorem cell21_626761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_626761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626761 prefixEnd_626761 := by exact prefixLift 626761
  have htrace : WordTrace (prefixWord ++ tailWord_626761) baseStart_626761 baseEnd_626761 := by
    simpa [prefixWord, tailWord_626761, baseEnd_626761] using wordTrace_append hprefix tailTrace_626761
  have hstable : (prefixWord ++ tailWord_626761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626761).length < 2 ^ (prefixWord ++ tailWord_626761).sum := by decide
  have hdescent : baseEnd_626761 < baseStart_626761 := by decide
  rcases family_descends (prefixWord ++ tailWord_626761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626778 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 5]
def baseStart_626778 : Nat := 118140960795 + 626778 * 2 ^ 59
def prefixEnd_626778 : Nat := 4983230072969 + 3 ^ 40 * 626778 * 2
def baseEnd_626778 : Nat := 143039278961712871952225

theorem tailTrace_626778 : CollatzResearch.WordTrace tailWord_626778 prefixEnd_626778 143039278961712871952225 := by
  unfold tailWord_626778
  simp only [CollatzResearch.WordTrace]
  refine ⟨5715117930824456501302247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15240314482198550670139325 5715117930824456501302247)
  ·
    refine ⟨8572676896236684751953371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5715117930824456501302247 8572676896236684751953371)
    ·
      refine ⟨12859015344355027127930057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8572676896236684751953371 12859015344355027127930057)
      ·
        refine ⟨9644261508266270345947543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12859015344355027127930057 9644261508266270345947543)
        ·
          refine ⟨14466392262399405518921315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9644261508266270345947543 14466392262399405518921315)
          ·
            refine ⟨21699588393599108278381973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14466392262399405518921315 21699588393599108278381973)
            ·
              refine ⟨1017168205949958200549155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21699588393599108278381973 1017168205949958200549155)
              ·
                refine ⟨1525752308924937300823733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1017168205949958200549155 1525752308924937300823733)
                ·
                  refine ⟨143039278961712871952225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1525752308924937300823733 143039278961712871952225)
                  ·
                    rfl

theorem cell21_626778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_626778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626778 prefixEnd_626778 := by exact prefixLift 626778
  have htrace : WordTrace (prefixWord ++ tailWord_626778) baseStart_626778 baseEnd_626778 := by
    simpa [prefixWord, tailWord_626778, baseEnd_626778] using wordTrace_append hprefix tailTrace_626778
  have hstable : (prefixWord ++ tailWord_626778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626778).length < 2 ^ (prefixWord ++ tailWord_626778).sum := by decide
  have hdescent : baseEnd_626778 < baseStart_626778 := by decide
  rcases family_descends (prefixWord ++ tailWord_626778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626812 : List Nat := [2, 2, 2, 1, 1, 6, 1, 3, 3]
def baseStart_626812 : Nat := 118140960795 + 626812 * 2 ^ 59
def prefixEnd_626812 : Nat := 4983230072969 + 3 ^ 40 * 626812 * 2
def baseEnd_626812 : Nat := 143047038224936368385489

theorem tailTrace_626812 : CollatzResearch.WordTrace tailWord_626812 prefixEnd_626812 143047038224936368385489 := by
  unfold tailWord_626812
  simp only [CollatzResearch.WordTrace]
  refine ⟨11430855902587324905973345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15241141203449766541297793 11430855902587324905973345)
  ·
    refine ⟨8573141926940493679480009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11430855902587324905973345 8573141926940493679480009)
    ·
      refine ⟨6429856445205370259610007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8573141926940493679480009 6429856445205370259610007)
      ·
        refine ⟨9644784667808055389415011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6429856445205370259610007 9644784667808055389415011)
        ·
          refine ⟨14467177001712083084122517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9644784667808055389415011 14467177001712083084122517)
          ·
            refine ⟨678148921955253894568243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14467177001712083084122517 678148921955253894568243)
            ·
              refine ⟨1017223382932880841852365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678148921955253894568243 1017223382932880841852365)
              ·
                refine ⟨381458768599830315694637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1017223382932880841852365 381458768599830315694637)
                ·
                  refine ⟨143047038224936368385489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381458768599830315694637 143047038224936368385489)
                  ·
                    rfl

theorem cell21_626812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_626812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626812 prefixEnd_626812 := by exact prefixLift 626812
  have htrace : WordTrace (prefixWord ++ tailWord_626812) baseStart_626812 baseEnd_626812 := by
    simpa [prefixWord, tailWord_626812, baseEnd_626812] using wordTrace_append hprefix tailTrace_626812
  have hstable : (prefixWord ++ tailWord_626812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626812).length < 2 ^ (prefixWord ++ tailWord_626812).sum := by decide
  have hdescent : baseEnd_626812 < baseStart_626812 := by decide
  rcases family_descends (prefixWord ++ tailWord_626812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626840 : List Nat := [2, 1, 2, 4, 3, 1, 2, 6]
def baseStart_626840 : Nat := 118140960795 + 626840 * 2 ^ 59
def prefixEnd_626840 : Nat := 4983230072969 + 3 ^ 40 * 626840 * 2
def baseEnd_626840 : Nat := 47684476068804847306255

theorem tailTrace_626840 : CollatzResearch.WordTrace tailWord_626840 prefixEnd_626840 47684476068804847306255 := by
  unfold tailWord_626840
  simp only [CollatzResearch.WordTrace]
  refine ⟨11431366524536605296982987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15241822032715473729310649 11431366524536605296982987)
  ·
    refine ⟨17147049786804907945474481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11431366524536605296982987 17147049786804907945474481)
    ·
      refine ⟨12860287340103680959105861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17147049786804907945474481 12860287340103680959105861)
      ·
        refine ⟨2411303876269440179832349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12860287340103680959105861 2411303876269440179832349)
        ·
          refine ⟨904238953601040067437131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2411303876269440179832349 904238953601040067437131)
          ·
            refine ⟨1356358430401560101155697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904238953601040067437131 1356358430401560101155697)
            ·
              refine ⟨1017268822801170075866773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1356358430401560101155697 1017268822801170075866773)
              ·
                refine ⟨47684476068804847306255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1017268822801170075866773 47684476068804847306255)
                ·
                  rfl

theorem cell21_626840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 6].length) (baseStart_626840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626840 prefixEnd_626840 := by exact prefixLift 626840
  have htrace : WordTrace (prefixWord ++ tailWord_626840) baseStart_626840 baseEnd_626840 := by
    simpa [prefixWord, tailWord_626840, baseEnd_626840] using wordTrace_append hprefix tailTrace_626840
  have hstable : (prefixWord ++ tailWord_626840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626840).length < 2 ^ (prefixWord ++ tailWord_626840).sum := by decide
  have hdescent : baseEnd_626840 < baseStart_626840 := by decide
  rcases family_descends (prefixWord ++ tailWord_626840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626975 : List Nat := [1, 1, 2, 4, 3, 2, 1, 7]
def baseStart_626975 : Nat := 118140960795 + 626975 * 2 ^ 59
def prefixEnd_626975 : Nat := 4983230072969 + 3 ^ 40 * 626975 * 2
def baseEnd_626975 : Nat := 47694745681894769056163

theorem tailTrace_626975 : CollatzResearch.WordTrace tailWord_626975 prefixEnd_626975 47694745681894769056163 := by
  unfold tailWord_626975
  simp only [CollatzResearch.WordTrace]
  refine ⟨22867656903584128650130379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15245104602389419100086919 22867656903584128650130379)
  ·
    refine ⟨34301485355376192975195569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22867656903584128650130379 34301485355376192975195569)
    ·
      refine ⟨25726114016532144731396677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34301485355376192975195569 25726114016532144731396677)
      ·
        refine ⟨4823646378099777137136877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25726114016532144731396677 4823646378099777137136877)
        ·
          refine ⟨1808867391787416426426329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4823646378099777137136877 1808867391787416426426329)
          ·
            refine ⟨1356650543840562319819747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1808867391787416426426329 1356650543840562319819747)
            ·
              refine ⟨2034975815760843479729621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356650543840562319819747 2034975815760843479729621)
              ·
                refine ⟨47694745681894769056163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2034975815760843479729621 47694745681894769056163)
                ·
                  rfl

theorem cell21_626975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 7].length) (baseStart_626975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626975 prefixEnd_626975 := by exact prefixLift 626975
  have htrace : WordTrace (prefixWord ++ tailWord_626975) baseStart_626975 baseEnd_626975 := by
    simpa [prefixWord, tailWord_626975, baseEnd_626975] using wordTrace_append hprefix tailTrace_626975
  have hstable : (prefixWord ++ tailWord_626975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626975).length < 2 ^ (prefixWord ++ tailWord_626975).sum := by decide
  have hdescent : baseEnd_626975 < baseStart_626975 := by decide
  rcases family_descends (prefixWord ++ tailWord_626975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626981 : List Nat := [1, 3, 1, 2, 6, 1, 1, 3, 3]
def baseStart_626981 : Nat := 118140960795 + 626981 * 2 ^ 59
def prefixEnd_626981 : Nat := 4983230072969 + 3 ^ 40 * 626981 * 2
def baseEnd_626981 : Nat := 143085606327429630068477

theorem tailTrace_626981 : CollatzResearch.WordTrace tailWord_626981 prefixEnd_626981 143085606327429630068477 := by
  unfold tailWord_626981
  simp only [CollatzResearch.WordTrace]
  refine ⟨22867875741562391674848797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15245250494374927783232531 22867875741562391674848797)
  ·
    refine ⟨8575453403085896878068299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22867875741562391674848797 8575453403085896878068299)
    ·
      refine ⟨12863180104628845317102449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8575453403085896878068299 12863180104628845317102449)
      ·
        refine ⟨9647385078471633987826837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12863180104628845317102449 9647385078471633987826837)
        ·
          refine ⟨452221175553357843179383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9647385078471633987826837 452221175553357843179383)
          ·
            refine ⟨678331763330036764769075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452221175553357843179383 678331763330036764769075)
            ·
              refine ⟨1017497644995055147153613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678331763330036764769075 1017497644995055147153613)
              ·
                refine ⟨381561616873145680182605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1017497644995055147153613 381561616873145680182605)
                ·
                  refine ⟨143085606327429630068477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381561616873145680182605 143085606327429630068477)
                  ·
                    rfl

theorem cell21_626981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_626981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626981 prefixEnd_626981 := by exact prefixLift 626981
  have htrace : WordTrace (prefixWord ++ tailWord_626981) baseStart_626981 baseEnd_626981 := by
    simpa [prefixWord, tailWord_626981, baseEnd_626981] using wordTrace_append hprefix tailTrace_626981
  have hstable : (prefixWord ++ tailWord_626981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626981).length < 2 ^ (prefixWord ++ tailWord_626981).sum := by decide
  have hdescent : baseEnd_626981 < baseStart_626981 := by decide
  rcases family_descends (prefixWord ++ tailWord_626981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627012 : List Nat := [2, 3, 4, 1, 2, 2, 2, 1, 4]
def baseStart_627012 : Nat := 118140960795 + 627012 * 2 ^ 59
def prefixEnd_627012 : Nat := 4983230072969 + 3 ^ 40 * 627012 * 2
def baseEnd_627012 : Nat := 143092680949780465051747

theorem tailTrace_627012 : CollatzResearch.WordTrace tailWord_627012 prefixEnd_627012 143092680949780465051747 := by
  unfold tailWord_627012
  simp only [CollatzResearch.WordTrace]
  refine ⟨11434503202225041984613645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15246004269633389312818193 11434503202225041984613645)
  ·
    refine ⟨4287938700834390744230117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11434503202225041984613645 4287938700834390744230117)
    ·
      refine ⟨803988506406448264543147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4287938700834390744230117 803988506406448264543147)
      ·
        refine ⟨1205982759609672396814721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803988506406448264543147 1205982759609672396814721)
        ·
          refine ⟨904487069707254297611041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1205982759609672396814721 904487069707254297611041)
          ·
            refine ⟨678365302280440723208281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 904487069707254297611041 678365302280440723208281)
            ·
              refine ⟨508773976710330542406211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 678365302280440723208281 508773976710330542406211)
              ·
                refine ⟨763160965065495813609317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508773976710330542406211 763160965065495813609317)
                ·
                  refine ⟨143092680949780465051747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 763160965065495813609317 143092680949780465051747)
                  ·
                    rfl

theorem cell21_627012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_627012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_627012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_627012 prefixEnd_627012 := by exact prefixLift 627012
  have htrace : WordTrace (prefixWord ++ tailWord_627012) baseStart_627012 baseEnd_627012 := by
    simpa [prefixWord, tailWord_627012, baseEnd_627012] using wordTrace_append hprefix tailTrace_627012
  have hstable : (prefixWord ++ tailWord_627012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627012).length < 2 ^ (prefixWord ++ tailWord_627012).sum := by decide
  have hdescent : baseEnd_627012 < baseStart_627012 := by decide
  rcases family_descends (prefixWord ++ tailWord_627012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627065 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 5]
def baseStart_627065 : Nat := 118140960795 + 627065 * 2 ^ 59
def prefixEnd_627065 : Nat := 4983230072969 + 3 ^ 40 * 627065 * 2
def baseEnd_627065 : Nat := 143104776271864150668305

theorem tailTrace_627065 : CollatzResearch.WordTrace tailWord_627065 prefixEnd_627065 143104776271864150668305 := by
  unfold tailWord_627065
  simp only [CollatzResearch.WordTrace]
  refine ⟨22870939473258074020906649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15247292982172049347271099 22870939473258074020906649)
  ·
    refine ⟨17153204604943555515679987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22870939473258074020906649 17153204604943555515679987)
    ·
      refine ⟨25729806907415333273519981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17153204604943555515679987 25729806907415333273519981)
      ·
        refine ⟨9648677590280749977569993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25729806907415333273519981 9648677590280749977569993)
        ·
          refine ⟨7236508192710562483177495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9648677590280749977569993 7236508192710562483177495)
          ·
            refine ⟨10854762289065843724766243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7236508192710562483177495 10854762289065843724766243)
            ·
              refine ⟨16282143433598765587149365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10854762289065843724766243 16282143433598765587149365)
              ·
                refine ⟨1526450946899884273795253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16282143433598765587149365 1526450946899884273795253)
                ·
                  refine ⟨143104776271864150668305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1526450946899884273795253 143104776271864150668305)
                  ·
                    rfl

theorem cell21_627065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_627065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_627065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_627065 prefixEnd_627065 := by exact prefixLift 627065
  have htrace : WordTrace (prefixWord ++ tailWord_627065) baseStart_627065 baseEnd_627065 := by
    simpa [prefixWord, tailWord_627065, baseEnd_627065] using wordTrace_append hprefix tailTrace_627065
  have hstable : (prefixWord ++ tailWord_627065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627065).length < 2 ^ (prefixWord ++ tailWord_627065).sum := by decide
  have hdescent : baseEnd_627065 < baseStart_627065 := by decide
  rcases family_descends (prefixWord ++ tailWord_627065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627144 : List Nat := [2, 1, 3, 1, 3, 4, 2, 5]
def baseStart_627144 : Nat := 118140960795 + 627144 * 2 ^ 59
def prefixEnd_627144 : Nat := 4983230072969 + 3 ^ 40 * 627144 * 2
def baseEnd_627144 : Nat := 47707601716059189617159

theorem tailTrace_627144 : CollatzResearch.WordTrace tailWord_627144 prefixEnd_627144 47707601716059189617159 := by
  unfold tailWord_627144
  simp only [CollatzResearch.WordTrace]
  refine ⟨11436910419985935256516243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15249213893314580342021657 11436910419985935256516243)
  ·
    refine ⟨17155365629978902884774365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11436910419985935256516243 17155365629978902884774365)
    ·
      refine ⟨6433262111242088581790387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17155365629978902884774365 6433262111242088581790387)
      ·
        refine ⟨9649893166863132872685581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6433262111242088581790387 9649893166863132872685581)
        ·
          refine ⟨3618709937573674827257093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9649893166863132872685581 3618709937573674827257093)
          ·
            refine ⟨678508113295064030110705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3618709937573674827257093 678508113295064030110705)
            ·
              refine ⟨508881084971298022583029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 678508113295064030110705 508881084971298022583029)
              ·
                refine ⟨47707601716059189617159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 508881084971298022583029 47707601716059189617159)
                ·
                  rfl

theorem cell21_627144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 5].length) (baseStart_627144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_627144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_627144 prefixEnd_627144 := by exact prefixLift 627144
  have htrace : WordTrace (prefixWord ++ tailWord_627144) baseStart_627144 baseEnd_627144 := by
    simpa [prefixWord, tailWord_627144, baseEnd_627144] using wordTrace_append hprefix tailTrace_627144
  have hstable : (prefixWord ++ tailWord_627144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627144).length < 2 ^ (prefixWord ++ tailWord_627144).sum := by decide
  have hdescent : baseEnd_627144 < baseStart_627144 := by decide
  rcases family_descends (prefixWord ++ tailWord_627144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627248 : List Nat := [2, 1, 1, 1, 2, 3, 4, 3, 4]
def baseStart_627248 : Nat := 118140960795 + 627248 * 2 ^ 59
def prefixEnd_627248 : Nat := 4983230072969 + 3 ^ 40 * 627248 * 2
def baseEnd_627248 : Nat := 143146539365096499117931

theorem tailTrace_627248 : CollatzResearch.WordTrace tailWord_627248 prefixEnd_627248 143146539365096499117931 := by
  unfold tailWord_627248
  simp only [CollatzResearch.WordTrace]
  refine ⟨11438807015797548137409199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15251742687730064183212265 11438807015797548137409199)
  ·
    refine ⟨17158210523696322206113799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11438807015797548137409199 17158210523696322206113799)
    ·
      refine ⟨25737315785544483309170699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17158210523696322206113799 25737315785544483309170699)
      ·
        refine ⟨38605973678316724963756049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25737315785544483309170699 38605973678316724963756049)
        ·
          refine ⟨28954480258737543722817037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38605973678316724963756049 28954480258737543722817037)
          ·
            refine ⟨10857930097026578896056389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28954480258737543722817037 10857930097026578896056389)
            ·
              refine ⟨2035861893192483543010573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10857930097026578896056389 2035861893192483543010573)
              ·
                refine ⟨763448209947181328628965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2035861893192483543010573 763448209947181328628965)
                ·
                  refine ⟨143146539365096499117931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 763448209947181328628965 143146539365096499117931)
                  ·
                    rfl

theorem cell21_627248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_627248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_627248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_627248 prefixEnd_627248 := by exact prefixLift 627248
  have htrace : WordTrace (prefixWord ++ tailWord_627248) baseStart_627248 baseEnd_627248 := by
    simpa [prefixWord, tailWord_627248, baseEnd_627248] using wordTrace_append hprefix tailTrace_627248
  have hstable : (prefixWord ++ tailWord_627248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627248).length < 2 ^ (prefixWord ++ tailWord_627248).sum := by decide
  have hdescent : baseEnd_627248 < baseStart_627248 := by decide
  rcases family_descends (prefixWord ++ tailWord_627248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627310 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_627310 : Nat := 118140960795 + 627310 * 2 ^ 59
def prefixEnd_627310 : Nat := 4983230072969 + 3 ^ 40 * 627310 * 2
def baseEnd_627310 : Nat := 143160688609798169084471

theorem tailTrace_627310 : CollatzResearch.WordTrace tailWord_627310 prefixEnd_627310 143160688609798169084471 := by
  unfold tailWord_627310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2859984419671310107946923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15253250238246987242383589 2859984419671310107946923)
  ·
    refine ⟨4289976629506965161920385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2859984419671310107946923 4289976629506965161920385)
    ·
      refine ⟨3217482472130223871440289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4289976629506965161920385 3217482472130223871440289)
      ·
        refine ⟨2413111854097667903580217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3217482472130223871440289 2413111854097667903580217)
        ·
          refine ⟨1809833890573250927685163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2413111854097667903580217 1809833890573250927685163)
          ·
            refine ⟨2714750835859876391527745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1809833890573250927685163 2714750835859876391527745)
            ·
              refine ⟨2036063126894907293645809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2714750835859876391527745 2036063126894907293645809)
              ·
                refine ⟨1527047345171180470234357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2036063126894907293645809 1527047345171180470234357)
                ·
                  refine ⟨143160688609798169084471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1527047345171180470234357 143160688609798169084471)
                  ·
                    rfl

theorem cell21_627310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_627310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_627310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_627310 prefixEnd_627310 := by exact prefixLift 627310
  have htrace : WordTrace (prefixWord ++ tailWord_627310) baseStart_627310 baseEnd_627310 := by
    simpa [prefixWord, tailWord_627310, baseEnd_627310] using wordTrace_append hprefix tailTrace_627310
  have hstable : (prefixWord ++ tailWord_627310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627310).length < 2 ^ (prefixWord ++ tailWord_627310).sum := by decide
  have hdescent : baseEnd_627310 < baseStart_627310 := by decide
  rcases family_descends (prefixWord ++ tailWord_627310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627330 : List Nat := [3, 4, 3, 1, 1, 2, 7]
def baseStart_627330 : Nat := 118140960795 + 627330 * 2 ^ 59
def prefixEnd_627330 : Nat := 4983230072969 + 3 ^ 40 * 627330 * 2
def baseEnd_627330 : Nat := 15907250320253619861233

theorem tailTrace_627330 : CollatzResearch.WordTrace tailWord_627330 prefixEnd_627330 15907250320253619861233 := by
  unfold tailWord_627330
  simp only [CollatzResearch.WordTrace]
  refine ⟨5720151204324506069825861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15253736544865349519535629 5720151204324506069825861)
  ·
    refine ⟨1072528350810844888092349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5720151204324506069825861 1072528350810844888092349)
    ·
      refine ⟨402198131554066833034631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1072528350810844888092349 402198131554066833034631)
      ·
        refine ⟨603297197331100249551947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402198131554066833034631 603297197331100249551947)
        ·
          refine ⟨904945795996650374327921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603297197331100249551947 904945795996650374327921)
          ·
            refine ⟨678709346997487780745941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 904945795996650374327921 678709346997487780745941)
            ·
              refine ⟨15907250320253619861233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 678709346997487780745941 15907250320253619861233)
              ·
                rfl

theorem cell21_627330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 7].length) (baseStart_627330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_627330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_627330 prefixEnd_627330 := by exact prefixLift 627330
  have htrace : WordTrace (prefixWord ++ tailWord_627330) baseStart_627330 baseEnd_627330 := by
    simpa [prefixWord, tailWord_627330, baseEnd_627330] using wordTrace_append hprefix tailTrace_627330
  have hstable : (prefixWord ++ tailWord_627330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627330).length < 2 ^ (prefixWord ++ tailWord_627330).sum := by decide
  have hdescent : baseEnd_627330 < baseStart_627330 := by decide
  rcases family_descends (prefixWord ++ tailWord_627330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627386 : List Nat := [3, 1, 1, 1, 2, 3, 2, 5, 3]
def baseStart_627386 : Nat := 118140960795 + 627386 * 2 ^ 59
def prefixEnd_627386 : Nat := 4983230072969 + 3 ^ 40 * 627386 * 2
def baseEnd_627386 : Nat := 143178032845238925817649

theorem tailTrace_627386 : CollatzResearch.WordTrace tailWord_627386 prefixEnd_627386 143178032845238925817649 := by
  unfold tailWord_627386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5720661826273786460835503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15255098203396763895561341 5720661826273786460835503)
  ·
    refine ⟨8580992739410679691253255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5720661826273786460835503 8580992739410679691253255)
    ·
      refine ⟨12871489109116019536879883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8580992739410679691253255 12871489109116019536879883)
      ·
        refine ⟨19307233663674029305319825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12871489109116019536879883 19307233663674029305319825)
        ·
          refine ⟨14480425247755521978989869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19307233663674029305319825 14480425247755521978989869)
          ·
            refine ⟨5430159467908320742121201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14480425247755521978989869 5430159467908320742121201)
            ·
              refine ⟨4072619600931240556590901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5430159467908320742121201 4072619600931240556590901)
              ·
                refine ⟨381808087587303802180397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4072619600931240556590901 381808087587303802180397)
                ·
                  refine ⟨143178032845238925817649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381808087587303802180397 143178032845238925817649)
                  ·
                    rfl

theorem cell21_627386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_627386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_627386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_627386 prefixEnd_627386 := by exact prefixLift 627386
  have htrace : WordTrace (prefixWord ++ tailWord_627386) baseStart_627386 baseEnd_627386 := by
    simpa [prefixWord, tailWord_627386, baseEnd_627386] using wordTrace_append hprefix tailTrace_627386
  have hstable : (prefixWord ++ tailWord_627386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627386).length < 2 ^ (prefixWord ++ tailWord_627386).sum := by decide
  have hdescent : baseEnd_627386 < baseStart_627386 := by decide
  rcases family_descends (prefixWord ++ tailWord_627386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627400 : List Nat := [2, 1, 3, 1, 2, 3, 1, 4, 4]
def baseStart_627400 : Nat := 118140960795 + 627400 * 2 ^ 59
def prefixEnd_627400 : Nat := 4983230072969 + 3 ^ 40 * 627400 * 2
def baseEnd_627400 : Nat := 143181227835978012584287

theorem tailTrace_627400 : CollatzResearch.WordTrace tailWord_627400 prefixEnd_627400 143181227835978012584287 := by
  unfold tailWord_627400
  simp only [CollatzResearch.WordTrace]
  refine ⟨11441578963522213117175827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15255438618029617489567769 11441578963522213117175827)
  ·
    refine ⟨17162368445283319675763741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11441578963522213117175827 17162368445283319675763741)
    ·
      refine ⟨6435888166981244878411403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17162368445283319675763741 6435888166981244878411403)
      ·
        refine ⟨9653832250471867317617105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6435888166981244878411403 9653832250471867317617105)
        ·
          refine ⟨7240374187853900488212829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9653832250471867317617105 7240374187853900488212829)
          ·
            refine ⟨2715140320445212683079811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7240374187853900488212829 2715140320445212683079811)
            ·
              refine ⟨4072710480667819024619717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2715140320445212683079811 4072710480667819024619717)
              ·
                refine ⟨763633215125216067116197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4072710480667819024619717 763633215125216067116197)
                ·
                  refine ⟨143181227835978012584287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 763633215125216067116197 143181227835978012584287)
                  ·
                    rfl

theorem cell21_627400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_627400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_627400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_627400 prefixEnd_627400 := by exact prefixLift 627400
  have htrace : WordTrace (prefixWord ++ tailWord_627400) baseStart_627400 baseEnd_627400 := by
    simpa [prefixWord, tailWord_627400, baseEnd_627400] using wordTrace_append hprefix tailTrace_627400
  have hstable : (prefixWord ++ tailWord_627400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627400).length < 2 ^ (prefixWord ++ tailWord_627400).sum := by decide
  have hdescent : baseEnd_627400 < baseStart_627400 := by decide
  rcases family_descends (prefixWord ++ tailWord_627400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627504 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 7]
def baseStart_627504 : Nat := 118140960795 + 627504 * 2 ^ 59
def prefixEnd_627504 : Nat := 4983230072969 + 3 ^ 40 * 627504 * 2
def baseEnd_627504 : Nat := 143204962052896942850741

theorem tailTrace_627504 : CollatzResearch.WordTrace tailWord_627504 prefixEnd_627504 143204962052896942850741 := by
  unfold tailWord_627504
  simp only [CollatzResearch.WordTrace]
  refine ⟨11443475559333825998068783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15257967412445101330758377 11443475559333825998068783)
  ·
    refine ⟨17165213339000738997103175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11443475559333825998068783 17165213339000738997103175)
    ·
      refine ⟨25747820008501108495654763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17165213339000738997103175 25747820008501108495654763)
      ·
        refine ⟨38621730012751662743482145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25747820008501108495654763 38621730012751662743482145)
        ·
          refine ⟨28966297509563747057611609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38621730012751662743482145 28966297509563747057611609)
          ·
            refine ⟨21724723132172810293208707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28966297509563747057611609 21724723132172810293208707)
            ·
              refine ⟨32587084698259215439813061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21724723132172810293208707 32587084698259215439813061)
              ·
                refine ⟨6110078380923602894964949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32587084698259215439813061 6110078380923602894964949)
                ·
                  refine ⟨143204962052896942850741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6110078380923602894964949 143204962052896942850741)
                  ·
                    rfl

theorem cell21_627504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_627504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_627504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_627504 prefixEnd_627504 := by exact prefixLift 627504
  have htrace : WordTrace (prefixWord ++ tailWord_627504) baseStart_627504 baseEnd_627504 := by
    simpa [prefixWord, tailWord_627504, baseEnd_627504] using wordTrace_append hprefix tailTrace_627504
  have hstable : (prefixWord ++ tailWord_627504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627504).length < 2 ^ (prefixWord ++ tailWord_627504).sum := by decide
  have hdescent : baseEnd_627504 < baseStart_627504 := by decide
  rcases family_descends (prefixWord ++ tailWord_627504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627566 : List Nat := [4, 1, 2, 3, 11]
def baseStart_627566 : Nat := 118140960795 + 627566 * 2 ^ 59
def prefixEnd_627566 : Nat := 4983230072969 + 3 ^ 40 * 627566 * 2
def baseEnd_627566 : Nat := 1768137176513563121201

theorem tailTrace_627566 : CollatzResearch.WordTrace tailWord_627566 prefixEnd_627566 1768137176513563121201 := by
  unfold tailWord_627566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2861151555555379573111819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15259474962962024389929701 2861151555555379573111819)
  ·
    refine ⟨4291727333333069359667729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2861151555555379573111819 4291727333333069359667729)
    ·
      refine ⟨3218795499999802019750797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4291727333333069359667729 3218795499999802019750797)
      ·
        refine ⟨1207048312499925757406549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3218795499999802019750797 1207048312499925757406549)
        ·
          refine ⟨1768137176513563121201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1207048312499925757406549 1768137176513563121201)
          ·
            rfl

theorem cell21_627566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 11].length) (baseStart_627566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_627566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_627566 prefixEnd_627566 := by exact prefixLift 627566
  have htrace : WordTrace (prefixWord ++ tailWord_627566) baseStart_627566 baseEnd_627566 := by
    simpa [prefixWord, tailWord_627566, baseEnd_627566] using wordTrace_append hprefix tailTrace_627566
  have hstable : (prefixWord ++ tailWord_627566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627566).length < 2 ^ (prefixWord ++ tailWord_627566).sum := by decide
  have hdescent : baseEnd_627566 < baseStart_627566 := by decide
  rcases family_descends (prefixWord ++ tailWord_627566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627580 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 9]
def baseStart_627580 : Nat := 118140960795 + 627580 * 2 ^ 59
def prefixEnd_627580 : Nat := 4983230072969 + 3 ^ 40 * 627580 * 2
def baseEnd_627580 : Nat := 143222306288337699583919

theorem tailTrace_627580 : CollatzResearch.WordTrace tailWord_627580 prefixEnd_627580 143222306288337699583919 := by
  unfold tailWord_627580
  simp only [CollatzResearch.WordTrace]
  refine ⟨11444861533196158487952097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15259815377594877983936129 11444861533196158487952097)
  ·
    refine ⟨8583646149897118865964073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11444861533196158487952097 8583646149897118865964073)
    ·
      refine ⟨6437734612422839149473055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8583646149897118865964073 6437734612422839149473055)
      ·
        refine ⟨9656601918634258724209583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6437734612422839149473055 9656601918634258724209583)
        ·
          refine ⟨14484902877951388086314375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9656601918634258724209583 14484902877951388086314375)
          ·
            refine ⟨21727354316927082129471563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14484902877951388086314375 21727354316927082129471563)
            ·
              refine ⟨32591031475390623194207345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21727354316927082129471563 32591031475390623194207345)
              ·
                refine ⟨24443273606542967395655509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32591031475390623194207345 24443273606542967395655509)
                ·
                  refine ⟨143222306288337699583919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24443273606542967395655509 143222306288337699583919)
                  ·
                    rfl

theorem cell21_627580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_627580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_627580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_627580 prefixEnd_627580 := by exact prefixLift 627580
  have htrace : WordTrace (prefixWord ++ tailWord_627580) baseStart_627580 baseEnd_627580 := by
    simpa [prefixWord, tailWord_627580, baseEnd_627580] using wordTrace_append hprefix tailTrace_627580
  have hstable : (prefixWord ++ tailWord_627580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627580).length < 2 ^ (prefixWord ++ tailWord_627580).sum := by decide
  have hdescent : baseEnd_627580 < baseStart_627580 := by decide
  rcases family_descends (prefixWord ++ tailWord_627580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627625 : List Nat := [1, 2, 1, 1, 1, 1, 14]
def baseStart_627625 : Nat := 118140960795 + 627625 * 2 ^ 59
def prefixEnd_627625 : Nat := 4983230072969 + 3 ^ 40 * 627625 * 2
def baseEnd_627625 : Nat := 15914730655714180148203

theorem tailTrace_627625 : CollatzResearch.WordTrace tailWord_627625 prefixEnd_627625 15914730655714180148203 := by
  unfold tailWord_627625
  simp only [CollatzResearch.WordTrace]
  refine ⟨22891364351229289661292329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15260909567486193107528219 22891364351229289661292329)
  ·
    refine ⟨17168523263421967245969247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22891364351229289661292329 17168523263421967245969247)
    ·
      refine ⟨25752784895132950868953871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17168523263421967245969247 25752784895132950868953871)
      ·
        refine ⟨38629177342699426303430807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25752784895132950868953871 38629177342699426303430807)
        ·
          refine ⟨57943766014049139455146211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38629177342699426303430807 57943766014049139455146211)
          ·
            refine ⟨86915649021073709182719317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57943766014049139455146211 86915649021073709182719317)
            ·
              refine ⟨15914730655714180148203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 86915649021073709182719317 15914730655714180148203)
              ·
                rfl

theorem cell21_627625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 14].length) (baseStart_627625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_627625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_627625 prefixEnd_627625 := by exact prefixLift 627625
  have htrace : WordTrace (prefixWord ++ tailWord_627625) baseStart_627625 baseEnd_627625 := by
    simpa [prefixWord, tailWord_627625, baseEnd_627625] using wordTrace_append hprefix tailTrace_627625
  have hstable : (prefixWord ++ tailWord_627625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627625).length < 2 ^ (prefixWord ++ tailWord_627625).sum := by decide
  have hdescent : baseEnd_627625 < baseStart_627625 := by decide
  rcases family_descends (prefixWord ++ tailWord_627625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627659 : List Nat := [1, 1, 1, 1, 3, 7, 2, 5]
def baseStart_627659 : Nat := 118140960795 + 627659 * 2 ^ 59
def prefixEnd_627659 : Nat := 4983230072969 + 3 ^ 40 * 627659 * 2
def baseEnd_627659 : Nat := 47746778388217039255697

theorem tailTrace_627659 : CollatzResearch.WordTrace tailWord_627659 prefixEnd_627659 47746778388217039255697 := by
  unfold tailWord_627659
  simp only [CollatzResearch.WordTrace]
  refine ⟨22892604433106113468030031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15261736288737408978686687 22892604433106113468030031)
  ·
    refine ⟨34338906649659170202045047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22892604433106113468030031 34338906649659170202045047)
    ·
      refine ⟨51508359974488755303067571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34338906649659170202045047 51508359974488755303067571)
      ·
        refine ⟨77262539961733132954601357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51508359974488755303067571 77262539961733132954601357)
        ·
          refine ⟨28973452485649924857975509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77262539961733132954601357 28973452485649924857975509)
          ·
            refine ⟨679065292632420113858801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 28973452485649924857975509 679065292632420113858801)
            ·
              refine ⟨509298969474315085394101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679065292632420113858801 509298969474315085394101)
              ·
                refine ⟨47746778388217039255697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 509298969474315085394101 47746778388217039255697)
                ·
                  rfl

theorem cell21_627659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 5].length) (baseStart_627659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_627659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_627659 prefixEnd_627659 := by exact prefixLift 627659
  have htrace : WordTrace (prefixWord ++ tailWord_627659) baseStart_627659 baseEnd_627659 := by
    simpa [prefixWord, tailWord_627659, baseEnd_627659] using wordTrace_append hprefix tailTrace_627659
  have hstable : (prefixWord ++ tailWord_627659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627659).length < 2 ^ (prefixWord ++ tailWord_627659).sum := by decide
  have hdescent : baseEnd_627659 < baseStart_627659 := by decide
  rcases family_descends (prefixWord ++ tailWord_627659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627690 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 5]
def baseStart_627690 : Nat := 118140960795 + 627690 * 2 ^ 59
def prefixEnd_627690 : Nat := 4983230072969 + 3 ^ 40 * 627690 * 2
def baseEnd_627690 : Nat := 143247409787001952750361

theorem tailTrace_627690 : CollatzResearch.WordTrace tailWord_627690 prefixEnd_627690 143247409787001952750361 := by
  unfold tailWord_627690
  simp only [CollatzResearch.WordTrace]
  refine ⟨5723433773998451440602131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15262490063995870508272349 5723433773998451440602131)
  ·
    refine ⟨8585150660997677160903197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5723433773998451440602131 8585150660997677160903197)
    ·
      refine ⟨3219431497874128935338699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8585150660997677160903197 3219431497874128935338699)
      ·
        refine ⟨4829147246811193403008049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219431497874128935338699 4829147246811193403008049)
        ·
          refine ⟨3621860435108395052256037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4829147246811193403008049 3621860435108395052256037)
          ·
            refine ⟨679098831582824072298007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3621860435108395052256037 679098831582824072298007)
            ·
              refine ⟨1018648247374236108447011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 679098831582824072298007 1018648247374236108447011)
              ·
                refine ⟨1527972371061354162670517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018648247374236108447011 1527972371061354162670517)
                ·
                  refine ⟨143247409787001952750361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1527972371061354162670517 143247409787001952750361)
                  ·
                    rfl

theorem cell21_627690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_627690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_627690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_627690 prefixEnd_627690 := by exact prefixLift 627690
  have htrace : WordTrace (prefixWord ++ tailWord_627690) baseStart_627690 baseEnd_627690 := by
    simpa [prefixWord, tailWord_627690, baseEnd_627690] using wordTrace_append hprefix tailTrace_627690
  have hstable : (prefixWord ++ tailWord_627690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627690).length < 2 ^ (prefixWord ++ tailWord_627690).sum := by decide
  have hdescent : baseEnd_627690 < baseStart_627690 := by decide
  rcases family_descends (prefixWord ++ tailWord_627690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627741 : List Nat := [1, 4, 2, 2, 4, 1, 2, 2, 3]
def baseStart_627741 : Nat := 118140960795 + 627741 * 2 ^ 59
def prefixEnd_627741 : Nat := 4983230072969 + 3 ^ 40 * 627741 * 2
def baseEnd_627741 : Nat := 143259048681837197400257

theorem tailTrace_627741 : CollatzResearch.WordTrace tailWord_627741 prefixEnd_627741 143259048681837197400257 := by
  unfold tailWord_627741
  simp only [CollatzResearch.WordTrace]
  refine ⟨22895595218809041472515077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15263730145872694315010051 22895595218809041472515077)
  ·
    refine ⟨4292924103526695276096577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22895595218809041472515077 4292924103526695276096577)
    ·
      refine ⟨3219693077645021457072433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4292924103526695276096577 3219693077645021457072433)
      ·
        refine ⟨2414769808233766092804325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3219693077645021457072433 2414769808233766092804325)
        ·
          refine ⟨452769339043831142400811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2414769808233766092804325 452769339043831142400811)
          ·
            refine ⟨679154008565746713601217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452769339043831142400811 679154008565746713601217)
            ·
              refine ⟨509365506424310035200913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679154008565746713601217 509365506424310035200913)
              ·
                refine ⟨382024129818232526400685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 509365506424310035200913 382024129818232526400685)
                ·
                  refine ⟨143259048681837197400257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 382024129818232526400685 143259048681837197400257)
                  ·
                    rfl

theorem cell21_627741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_627741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_627741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_627741 prefixEnd_627741 := by exact prefixLift 627741
  have htrace : WordTrace (prefixWord ++ tailWord_627741) baseStart_627741 baseEnd_627741 := by
    simpa [prefixWord, tailWord_627741, baseEnd_627741] using wordTrace_append hprefix tailTrace_627741
  have hstable : (prefixWord ++ tailWord_627741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627741).length < 2 ^ (prefixWord ++ tailWord_627741).sum := by decide
  have hdescent : baseEnd_627741 < baseStart_627741 := by decide
  rcases family_descends (prefixWord ++ tailWord_627741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627766 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_627766 : Nat := 118140960795 + 627766 * 2 ^ 59
def prefixEnd_627766 : Nat := 4983230072969 + 3 ^ 40 * 627766 * 2
def baseEnd_627766 : Nat := 143264754022442709483539

theorem tailTrace_627766 : CollatzResearch.WordTrace tailWord_627766 prefixEnd_627766 143264754022442709483539 := by
  unfold tailWord_627766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1431031690232404421385947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15264338029145647161450101 1431031690232404421385947)
  ·
    refine ⟨2146547535348606632078921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1431031690232404421385947 2146547535348606632078921)
    ·
      refine ⟨1609910651511454974059191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2146547535348606632078921 1609910651511454974059191)
      ·
        refine ⟨2414865977267182461088787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1609910651511454974059191 2414865977267182461088787)
        ·
          refine ⟨3622298965900773691633181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2414865977267182461088787 3622298965900773691633181)
          ·
            refine ⟨1358362112212790134362443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3622298965900773691633181 1358362112212790134362443)
            ·
              refine ⟨2037543168319185201543665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1358362112212790134362443 2037543168319185201543665)
              ·
                refine ⟨1528157376239388901157749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2037543168319185201543665 1528157376239388901157749)
                ·
                  refine ⟨143264754022442709483539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1528157376239388901157749 143264754022442709483539)
                  ·
                    rfl

theorem cell21_627766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_627766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_627766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_627766 prefixEnd_627766 := by exact prefixLift 627766
  have htrace : WordTrace (prefixWord ++ tailWord_627766) baseStart_627766 baseEnd_627766 := by
    simpa [prefixWord, tailWord_627766, baseEnd_627766] using wordTrace_append hprefix tailTrace_627766
  have hstable : (prefixWord ++ tailWord_627766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627766).length < 2 ^ (prefixWord ++ tailWord_627766).sum := by decide
  have hdescent : baseEnd_627766 < baseStart_627766 := by decide
  rcases family_descends (prefixWord ++ tailWord_627766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627794 : List Nat := [3, 2, 2, 1, 3, 2, 8]
def baseStart_627794 : Nat := 118140960795 + 627794 * 2 ^ 59
def prefixEnd_627794 : Nat := 4983230072969 + 3 ^ 40 * 627794 * 2
def baseEnd_627794 : Nat := 15919016000435653668535

theorem tailTrace_627794 : CollatzResearch.WordTrace tailWord_627794 prefixEnd_627794 15919016000435653668535 := by
  unfold tailWord_627794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5724382071904257881048609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15265018858411354349462957 5724382071904257881048609)
  ·
    refine ⟨4293286553928193410786457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5724382071904257881048609 4293286553928193410786457)
    ·
      refine ⟨3219964915446145058089843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4293286553928193410786457 3219964915446145058089843)
      ·
        refine ⟨4829947373169217587134765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219964915446145058089843 4829947373169217587134765)
        ·
          refine ⟨1811230264938456595175537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4829947373169217587134765 1811230264938456595175537)
          ·
            refine ⟨1358422698703842446381653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1811230264938456595175537 1358422698703842446381653)
            ·
              refine ⟨15919016000435653668535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1358422698703842446381653 15919016000435653668535)
              ·
                rfl

theorem cell21_627794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 8].length) (baseStart_627794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_627794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_627794 prefixEnd_627794 := by exact prefixLift 627794
  have htrace : WordTrace (prefixWord ++ tailWord_627794) baseStart_627794 baseEnd_627794 := by
    simpa [prefixWord, tailWord_627794, baseEnd_627794] using wordTrace_append hprefix tailTrace_627794
  have hstable : (prefixWord ++ tailWord_627794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627794).length < 2 ^ (prefixWord ++ tailWord_627794).sum := by decide
  have hdescent : baseEnd_627794 < baseStart_627794 := by decide
  rcases family_descends (prefixWord ++ tailWord_627794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627977 : List Nat := [1, 2, 1, 1, 3, 3, 1, 6, 3]
def baseStart_627977 : Nat := 118140960795 + 627977 * 2 ^ 59
def prefixEnd_627977 : Nat := 4983230072969 + 3 ^ 40 * 627977 * 2
def baseEnd_627977 : Nat := 143312907097153231466441

theorem tailTrace_627977 : CollatzResearch.WordTrace tailWord_627977 prefixEnd_627977 143312907097153231466441 := by
  unfold tailWord_627977
  simp only [CollatzResearch.WordTrace]
  refine ⟨22904202845954053778106185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15269468563969369185404123 22904202845954053778106185)
  ·
    refine ⟨17178152134465540333579639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22904202845954053778106185 17178152134465540333579639)
    ·
      refine ⟨25767228201698310500369459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17178152134465540333579639 25767228201698310500369459)
      ·
        refine ⟨38650842302547465750554189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25767228201698310500369459 38650842302547465750554189)
        ·
          refine ⟨14494065863455299656457821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38650842302547465750554189 14494065863455299656457821)
          ·
            refine ⟨5435274698795737371171683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14494065863455299656457821 5435274698795737371171683)
            ·
              refine ⟨8152912048193606056757525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5435274698795737371171683 8152912048193606056757525)
              ·
                refine ⟨382167752259075283910509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8152912048193606056757525 382167752259075283910509)
                ·
                  refine ⟨143312907097153231466441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 382167752259075283910509 143312907097153231466441)
                  ·
                    rfl

theorem cell21_627977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 3].length) (baseStart_627977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_627977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_627977 prefixEnd_627977 := by exact prefixLift 627977
  have htrace : WordTrace (prefixWord ++ tailWord_627977) baseStart_627977 baseEnd_627977 := by
    simpa [prefixWord, tailWord_627977, baseEnd_627977] using wordTrace_append hprefix tailTrace_627977
  have hstable : (prefixWord ++ tailWord_627977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627977).length < 2 ^ (prefixWord ++ tailWord_627977).sum := by decide
  have hdescent : baseEnd_627977 < baseStart_627977 := by decide
  rcases family_descends (prefixWord ++ tailWord_627977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628157 : List Nat := [1, 4, 1, 2, 2, 1, 2, 8]
def baseStart_628157 : Nat := 118140960795 + 628157 * 2 ^ 59
def prefixEnd_628157 : Nat := 4983230072969 + 3 ^ 40 * 628157 * 2
def baseEnd_628157 : Nat := 47784661849837639488691

theorem tailTrace_628157 : CollatzResearch.WordTrace tailWord_628157 prefixEnd_628157 47784661849837639488691 := by
  unfold tailWord_628157
  simp only [CollatzResearch.WordTrace]
  refine ⟨22910767985301944519658725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15273845323534629679772483 22910767985301944519658725)
  ·
    refine ⟨4295768997244114597436011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22910767985301944519658725 4295768997244114597436011)
    ·
      refine ⟨6443653495866171896154017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4295768997244114597436011 6443653495866171896154017)
      ·
        refine ⟨4832740121899628922115513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6443653495866171896154017 4832740121899628922115513)
        ·
          refine ⟨3624555091424721691586635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4832740121899628922115513 3624555091424721691586635)
          ·
            refine ⟨5436832637137082537379953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3624555091424721691586635 5436832637137082537379953)
            ·
              refine ⟨4077624477852811903034965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5436832637137082537379953 4077624477852811903034965)
              ·
                refine ⟨47784661849837639488691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4077624477852811903034965 47784661849837639488691)
                ·
                  rfl

theorem cell21_628157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 8].length) (baseStart_628157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628157 prefixEnd_628157 := by exact prefixLift 628157
  have htrace : WordTrace (prefixWord ++ tailWord_628157) baseStart_628157 baseEnd_628157 := by
    simpa [prefixWord, tailWord_628157, baseEnd_628157] using wordTrace_append hprefix tailTrace_628157
  have hstable : (prefixWord ++ tailWord_628157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628157).length < 2 ^ (prefixWord ++ tailWord_628157).sum := by decide
  have hdescent : baseEnd_628157 < baseStart_628157 := by decide
  rcases family_descends (prefixWord ++ tailWord_628157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628174 : List Nat := [4, 1, 1, 1, 2, 1, 6, 5]
def baseStart_628174 : Nat := 118140960795 + 628174 * 2 ^ 59
def prefixEnd_628174 : Nat := 4983230072969 + 3 ^ 40 * 628174 * 2
def baseEnd_628174 : Nat := 47785955060374888894235

theorem tailTrace_628174 : CollatzResearch.WordTrace tailWord_628174 prefixEnd_628174 47785955060374888894235 := by
  unfold tailWord_628174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2863923503280044552878447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15274258684160237615351717 2863923503280044552878447)
  ·
    refine ⟨4295885254920066829317671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2863923503280044552878447 4295885254920066829317671)
    ·
      refine ⟨6443827882380100243976507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4295885254920066829317671 6443827882380100243976507)
      ·
        refine ⟨9665741823570150365964761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6443827882380100243976507 9665741823570150365964761)
        ·
          refine ⟨7249306367677612774473571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9665741823570150365964761 7249306367677612774473571)
          ·
            refine ⟨10873959551516419161710357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7249306367677612774473571 10873959551516419161710357)
            ·
              refine ⟨509716853977332148205173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10873959551516419161710357 509716853977332148205173)
              ·
                refine ⟨47785955060374888894235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 509716853977332148205173 47785955060374888894235)
                ·
                  rfl

theorem cell21_628174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_628174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628174 prefixEnd_628174 := by exact prefixLift 628174
  have htrace : WordTrace (prefixWord ++ tailWord_628174) baseStart_628174 baseEnd_628174 := by
    simpa [prefixWord, tailWord_628174, baseEnd_628174] using wordTrace_append hprefix tailTrace_628174
  have hstable : (prefixWord ++ tailWord_628174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628174).length < 2 ^ (prefixWord ++ tailWord_628174).sum := by decide
  have hdescent : baseEnd_628174 < baseStart_628174 := by decide
  rcases family_descends (prefixWord ++ tailWord_628174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628180 : List Nat := [2, 4, 1, 2, 4, 1, 1, 3, 3]
def baseStart_628180 : Nat := 118140960795 + 628180 * 2 ^ 59
def prefixEnd_628180 : Nat := 4983230072969 + 3 ^ 40 * 628180 * 2
def baseEnd_628180 : Nat := 143359234462869989582693

theorem tailTrace_628180 : CollatzResearch.WordTrace tailWord_628180 prefixEnd_628180 143359234462869989582693 := by
  unfold tailWord_628180
  simp only [CollatzResearch.WordTrace]
  refine ⟨11455803432109309723872997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15274404576145746298497329 11455803432109309723872997)
  ·
    refine ⟨2147963143520495573226187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11455803432109309723872997 2147963143520495573226187)
    ·
      refine ⟨3221944715280743359839281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2147963143520495573226187 3221944715280743359839281)
      ·
        refine ⟨2416458536460557519879461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3221944715280743359839281 2416458536460557519879461)
        ·
          refine ⟨453085975586354534977399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2416458536460557519879461 453085975586354534977399)
          ·
            refine ⟨679628963379531802466099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453085975586354534977399 679628963379531802466099)
            ·
              refine ⟨1019443445069297703699149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 679628963379531802466099 1019443445069297703699149)
              ·
                refine ⟨382291291900986638887181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1019443445069297703699149 382291291900986638887181)
                ·
                  refine ⟨143359234462869989582693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 382291291900986638887181 143359234462869989582693)
                  ·
                    rfl

theorem cell21_628180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_628180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628180 prefixEnd_628180 := by exact prefixLift 628180
  have htrace : WordTrace (prefixWord ++ tailWord_628180) baseStart_628180 baseEnd_628180 := by
    simpa [prefixWord, tailWord_628180, baseEnd_628180] using wordTrace_append hprefix tailTrace_628180
  have hstable : (prefixWord ++ tailWord_628180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628180).length < 2 ^ (prefixWord ++ tailWord_628180).sum := by decide
  have hdescent : baseEnd_628180 < baseStart_628180 := by decide
  rcases family_descends (prefixWord ++ tailWord_628180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628385 : List Nat := [1, 2, 3, 3, 2, 1, 1, 8]
def baseStart_628385 : Nat := 118140960795 + 628385 * 2 ^ 59
def prefixEnd_628385 : Nat := 4983230072969 + 3 ^ 40 * 628385 * 2
def baseEnd_628385 : Nat := 47802006085278396221869

theorem tailTrace_628385 : CollatzResearch.WordTrace tailWord_628385 prefixEnd_628385 47802006085278396221869 := by
  unfold tailWord_628385
  simp only [CollatzResearch.WordTrace]
  refine ⟨22919083828475939458958609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15279389218983959639305739 22919083828475939458958609)
  ·
    refine ⟨17189312871356954594218957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22919083828475939458958609 17189312871356954594218957)
    ·
      refine ⟨6445992326758857972832109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17189312871356954594218957 6445992326758857972832109)
      ·
        refine ⟨2417247122534571739812041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6445992326758857972832109 2417247122534571739812041)
        ·
          refine ⟨1812935341900928804859031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2417247122534571739812041 1812935341900928804859031)
          ·
            refine ⟨2719403012851393207288547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1812935341900928804859031 2719403012851393207288547)
            ·
              refine ⟨4079104519277089810932821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2719403012851393207288547 4079104519277089810932821)
              ·
                refine ⟨47802006085278396221869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4079104519277089810932821 47802006085278396221869)
                ·
                  rfl

theorem cell21_628385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 8].length) (baseStart_628385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628385 prefixEnd_628385 := by exact prefixLift 628385
  have htrace : WordTrace (prefixWord ++ tailWord_628385) baseStart_628385 baseEnd_628385 := by
    simpa [prefixWord, tailWord_628385, baseEnd_628385] using wordTrace_append hprefix tailTrace_628385
  have hstable : (prefixWord ++ tailWord_628385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628385).length < 2 ^ (prefixWord ++ tailWord_628385).sum := by decide
  have hdescent : baseEnd_628385 < baseStart_628385 := by decide
  rcases family_descends (prefixWord ++ tailWord_628385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628388 : List Nat := [2, 3, 1, 2, 2, 2, 4, 1, 4]
def baseStart_628388 : Nat := 118140960795 + 628388 * 2 ^ 59
def prefixEnd_628388 : Nat := 4983230072969 + 3 ^ 40 * 628388 * 2
def baseEnd_628388 : Nat := 143406702896707850115601

theorem tailTrace_628388 : CollatzResearch.WordTrace tailWord_628388 prefixEnd_628388 143406702896707850115601 := by
  unfold tailWord_628388
  simp only [CollatzResearch.WordTrace]
  refine ⟨11459596623732535485658909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15279462164976713980878545 11459596623732535485658909)
  ·
    refine ⟨4297348733899700807122091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11459596623732535485658909 4297348733899700807122091)
    ·
      refine ⟨6446023100849551210683137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4297348733899700807122091 6446023100849551210683137)
      ·
        refine ⟨4834517325637163408012353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6446023100849551210683137 4834517325637163408012353)
        ·
          refine ⟨3625887994227872556009265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4834517325637163408012353 3625887994227872556009265)
          ·
            refine ⟨2719415995670904417006949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3625887994227872556009265 2719415995670904417006949)
            ·
              refine ⟨509890499188294578188803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2719415995670904417006949 509890499188294578188803)
              ·
                refine ⟨764835748782441867283205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509890499188294578188803 764835748782441867283205)
                ·
                  refine ⟨143406702896707850115601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 764835748782441867283205 143406702896707850115601)
                  ·
                    rfl

theorem cell21_628388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_628388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628388 prefixEnd_628388 := by exact prefixLift 628388
  have htrace : WordTrace (prefixWord ++ tailWord_628388) baseStart_628388 baseEnd_628388 := by
    simpa [prefixWord, tailWord_628388, baseEnd_628388] using wordTrace_append hprefix tailTrace_628388
  have hstable : (prefixWord ++ tailWord_628388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628388).length < 2 ^ (prefixWord ++ tailWord_628388).sum := by decide
  have hdescent : baseEnd_628388 < baseStart_628388 := by decide
  rcases family_descends (prefixWord ++ tailWord_628388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628399 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 7]
def baseStart_628399 : Nat := 118140960795 + 628399 * 2 ^ 59
def prefixEnd_628399 : Nat := 4983230072969 + 3 ^ 40 * 628399 * 2
def baseEnd_628399 : Nat := 143409213246574275432245

theorem tailTrace_628399 : CollatzResearch.WordTrace tailWord_628399 prefixEnd_628399 143409213246574275432245 := by
  unfold tailWord_628399
  simp only [CollatzResearch.WordTrace]
  refine ⟨22919594450425219849968251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15279729633616813233312167 22919594450425219849968251)
  ·
    refine ⟨34379391675637829774952377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22919594450425219849968251 34379391675637829774952377)
    ·
      refine ⟨25784543756728372331214283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34379391675637829774952377 25784543756728372331214283)
      ·
        refine ⟨38676815635092558496821425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25784543756728372331214283 38676815635092558496821425)
        ·
          refine ⟨29007611726319418872616069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38676815635092558496821425 29007611726319418872616069)
          ·
            refine ⟨5438927198684891038615513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29007611726319418872616069 5438927198684891038615513)
            ·
              refine ⟨4079195399013668278961635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5438927198684891038615513 4079195399013668278961635)
              ·
                refine ⟨6118793098520502418442453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4079195399013668278961635 6118793098520502418442453)
                ·
                  refine ⟨143409213246574275432245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6118793098520502418442453 143409213246574275432245)
                  ·
                    rfl

theorem cell21_628399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 7].length) (baseStart_628399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628399 prefixEnd_628399 := by exact prefixLift 628399
  have htrace : WordTrace (prefixWord ++ tailWord_628399) baseStart_628399 baseEnd_628399 := by
    simpa [prefixWord, tailWord_628399, baseEnd_628399] using wordTrace_append hprefix tailTrace_628399
  have hstable : (prefixWord ++ tailWord_628399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628399).length < 2 ^ (prefixWord ++ tailWord_628399).sum := by decide
  have hdescent : baseEnd_628399 < baseStart_628399 := by decide
  rcases family_descends (prefixWord ++ tailWord_628399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628422 : List Nat := [6, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_628422 : Nat := 118140960795 + 628422 * 2 ^ 59
def prefixEnd_628422 : Nat := 4983230072969 + 3 ^ 40 * 628422 * 2
def baseEnd_628422 : Nat := 143414462159931346548865

theorem tailTrace_628422 : CollatzResearch.WordTrace tailWord_628422 prefixEnd_628422 143414462159931346548865 := by
  unfold tailWord_628422
  simp only [CollatzResearch.WordTrace]
  refine ⟨716263541541934211814235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15280288886227929852037013 716263541541934211814235)
  ·
    refine ⟨1074395312312901317721353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 716263541541934211814235 1074395312312901317721353)
    ·
      refine ⟨805796484234675988291015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1074395312312901317721353 805796484234675988291015)
      ·
        refine ⟨1208694726352013982436523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 805796484234675988291015 1208694726352013982436523)
        ·
          refine ⟨1813042089528020973654785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1208694726352013982436523 1813042089528020973654785)
          ·
            refine ⟨1359781567146015730241089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1813042089528020973654785 1359781567146015730241089)
            ·
              refine ⟨1019836175359511797680817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1359781567146015730241089 1019836175359511797680817)
              ·
                refine ⟨764877131519633848260613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1019836175359511797680817 764877131519633848260613)
                ·
                  refine ⟨143414462159931346548865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 764877131519633848260613 143414462159931346548865)
                  ·
                    rfl

theorem cell21_628422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_628422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628422 prefixEnd_628422 := by exact prefixLift 628422
  have htrace : WordTrace (prefixWord ++ tailWord_628422) baseStart_628422 baseEnd_628422 := by
    simpa [prefixWord, tailWord_628422, baseEnd_628422] using wordTrace_append hprefix tailTrace_628422
  have hstable : (prefixWord ++ tailWord_628422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628422).length < 2 ^ (prefixWord ++ tailWord_628422).sum := by decide
  have hdescent : baseEnd_628422 < baseStart_628422 := by decide
  rcases family_descends (prefixWord ++ tailWord_628422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628433 : List Nat := [1, 2, 2, 1, 2, 5, 1, 4, 3]
def baseStart_628433 : Nat := 118140960795 + 628433 * 2 ^ 59
def prefixEnd_628433 : Nat := 4983230072969 + 3 ^ 40 * 628433 * 2
def baseEnd_628433 : Nat := 143416972509797771865509

theorem tailTrace_628433 : CollatzResearch.WordTrace tailWord_628433 prefixEnd_628433 143416972509797771865509 := by
  unfold tailWord_628433
  simp only [CollatzResearch.WordTrace]
  refine ⟨22920834532302043656705953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15280556354868029104470635 22920834532302043656705953)
  ·
    refine ⟨17190625899226532742529465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22920834532302043656705953 17190625899226532742529465)
    ·
      refine ⟨12892969424419899556897099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17190625899226532742529465 12892969424419899556897099)
      ·
        refine ⟨19339454136629849335345649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12892969424419899556897099 19339454136629849335345649)
        ·
          refine ⟨14504590602472387001509237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19339454136629849335345649 14504590602472387001509237)
          ·
            refine ⟨1359805368981786281391491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14504590602472387001509237 1359805368981786281391491)
            ·
              refine ⟨2039708053472679422087237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1359805368981786281391491 2039708053472679422087237)
              ·
                refine ⟨382445260026127391641357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2039708053472679422087237 382445260026127391641357)
                ·
                  refine ⟨143416972509797771865509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 382445260026127391641357 143416972509797771865509)
                  ·
                    rfl

theorem cell21_628433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 3].length) (baseStart_628433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628433 prefixEnd_628433 := by exact prefixLift 628433
  have htrace : WordTrace (prefixWord ++ tailWord_628433) baseStart_628433 baseEnd_628433 := by
    simpa [prefixWord, tailWord_628433, baseEnd_628433] using wordTrace_append hprefix tailTrace_628433
  have hstable : (prefixWord ++ tailWord_628433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628433).length < 2 ^ (prefixWord ++ tailWord_628433).sum := by decide
  have hdescent : baseEnd_628433 < baseStart_628433 := by decide
  rcases family_descends (prefixWord ++ tailWord_628433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628478 : List Nat := [4, 2, 2, 1, 3, 1, 8]
def baseStart_628478 : Nat := 118140960795 + 628478 * 2 ^ 59
def prefixEnd_628478 : Nat := 4983230072969 + 3 ^ 40 * 628478 * 2
def baseEnd_628478 : Nat := 15936360235876410401713

theorem tailTrace_628478 : CollatzResearch.WordTrace tailWord_628478 prefixEnd_628478 15936360235876410401713 := by
  unfold tailWord_628478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2865309477142377042761761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15281650544759344228062725 2865309477142377042761761)
  ·
    refine ⟨2148982107856782782071321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2865309477142377042761761 2148982107856782782071321)
    ·
      refine ⟨1611736580892587086553491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2148982107856782782071321 1611736580892587086553491)
      ·
        refine ⟨2417604871338880629830237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1611736580892587086553491 2417604871338880629830237)
        ·
          refine ⟨906601826752080236186339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2417604871338880629830237 906601826752080236186339)
          ·
            refine ⟨1359902740128120354279509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 906601826752080236186339 1359902740128120354279509)
            ·
              refine ⟨15936360235876410401713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1359902740128120354279509 15936360235876410401713)
              ·
                rfl

theorem cell21_628478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 8].length) (baseStart_628478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628478 prefixEnd_628478 := by exact prefixLift 628478
  have htrace : WordTrace (prefixWord ++ tailWord_628478) baseStart_628478 baseEnd_628478 := by
    simpa [prefixWord, tailWord_628478, baseEnd_628478] using wordTrace_append hprefix tailTrace_628478
  have hstable : (prefixWord ++ tailWord_628478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628478).length < 2 ^ (prefixWord ++ tailWord_628478).sum := by decide
  have hdescent : baseEnd_628478 < baseStart_628478 := by decide
  rcases family_descends (prefixWord ++ tailWord_628478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628557 : List Nat := [1, 6, 1, 2, 1, 1, 4, 1, 4]
def baseStart_628557 : Nat := 118140960795 + 628557 * 2 ^ 59
def prefixEnd_628557 : Nat := 4983230072969 + 3 ^ 40 * 628557 * 2
def baseEnd_628557 : Nat := 143445270999201111798589

theorem tailTrace_628557 : CollatzResearch.WordTrace tailWord_628557 prefixEnd_628557 143445270999201111798589 := by
  unfold tailWord_628557
  simp only [CollatzResearch.WordTrace]
  refine ⟨22925357183852812834219925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15283571455901875222813283 22925357183852812834219925)
  ·
    refine ⟨1074626117993100601604059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22925357183852812834219925 1074626117993100601604059)
    ·
      refine ⟨1611939176989650902406089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1074626117993100601604059 1611939176989650902406089)
      ·
        refine ⟨1208954382742238176804567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1611939176989650902406089 1208954382742238176804567)
        ·
          refine ⟨1813431574113357265206851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1208954382742238176804567 1813431574113357265206851)
          ·
            refine ⟨2720147361170035897810277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813431574113357265206851 2720147361170035897810277)
            ·
              refine ⟨510027630219381730839427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2720147361170035897810277 510027630219381730839427)
              ·
                refine ⟨765041445329072596259141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510027630219381730839427 765041445329072596259141)
                ·
                  refine ⟨143445270999201111798589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 765041445329072596259141 143445270999201111798589)
                  ·
                    rfl

theorem cell21_628557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_628557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628557 prefixEnd_628557 := by exact prefixLift 628557
  have htrace : WordTrace (prefixWord ++ tailWord_628557) baseStart_628557 baseEnd_628557 := by
    simpa [prefixWord, tailWord_628557, baseEnd_628557] using wordTrace_append hprefix tailTrace_628557
  have hstable : (prefixWord ++ tailWord_628557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628557).length < 2 ^ (prefixWord ++ tailWord_628557).sum := by decide
  have hdescent : baseEnd_628557 < baseStart_628557 := by decide
  rcases family_descends (prefixWord ++ tailWord_628557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628661 : List Nat := [1, 3, 3, 2, 1, 2, 2, 4, 3]
def baseStart_628661 : Nat := 118140960795 + 628661 * 2 ^ 59
def prefixEnd_628661 : Nat := 4983230072969 + 3 ^ 40 * 628661 * 2
def baseEnd_628661 : Nat := 143469005216120042065043

theorem tailTrace_628661 : CollatzResearch.WordTrace tailWord_628661 prefixEnd_628661 143469005216120042065043 := by
  unfold tailWord_628661
  simp only [CollatzResearch.WordTrace]
  refine ⟨22929150375476038596005837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15286100250317359064003891 22929150375476038596005837)
  ·
    refine ⟨8598431390803514473502189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22929150375476038596005837 8598431390803514473502189)
    ·
      refine ⟨3224411771551317927563321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8598431390803514473502189 3224411771551317927563321)
      ·
        refine ⟨2418308828663488445672491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3224411771551317927563321 2418308828663488445672491)
        ·
          refine ⟨3627463242995232668508737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2418308828663488445672491 3627463242995232668508737)
          ·
            refine ⟨2720597432246424501381553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3627463242995232668508737 2720597432246424501381553)
            ·
              refine ⟨2040448074184818376036165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2720597432246424501381553 2040448074184818376036165)
              ·
                refine ⟨382584013909653445506781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2040448074184818376036165 382584013909653445506781)
                ·
                  refine ⟨143469005216120042065043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 382584013909653445506781 143469005216120042065043)
                  ·
                    rfl

theorem cell21_628661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_628661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628661 prefixEnd_628661 := by exact prefixLift 628661
  have htrace : WordTrace (prefixWord ++ tailWord_628661) baseStart_628661 baseEnd_628661 := by
    simpa [prefixWord, tailWord_628661, baseEnd_628661] using wordTrace_append hprefix tailTrace_628661
  have hstable : (prefixWord ++ tailWord_628661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628661).length < 2 ^ (prefixWord ++ tailWord_628661).sum := by decide
  have hdescent : baseEnd_628661 < baseStart_628661 := by decide
  rcases family_descends (prefixWord ++ tailWord_628661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628672 : List Nat := [2, 1, 1, 2, 3, 2, 2, 8]
def baseStart_628672 : Nat := 118140960795 + 628672 * 2 ^ 59
def prefixEnd_628672 : Nat := 4983230072969 + 3 ^ 40 * 628672 * 2
def baseEnd_628672 : Nat := 47823838521995489127229

theorem tailTrace_628672 : CollatzResearch.WordTrace tailWord_628672 prefixEnd_628672 47823838521995489127229 := by
  unfold tailWord_628672
  simp only [CollatzResearch.WordTrace]
  refine ⟨11464775789218093737328135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15286367718957458316437513 11464775789218093737328135)
  ·
    refine ⟨17197163683827140605992203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11464775789218093737328135 17197163683827140605992203)
    ·
      refine ⟨25795745525740710908988305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17197163683827140605992203 25795745525740710908988305)
      ·
        refine ⟨19346809144305533181741229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25795745525740710908988305 19346809144305533181741229)
        ·
          refine ⟨7255053429114574943152961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19346809144305533181741229 7255053429114574943152961)
          ·
            refine ⟨5441290071835931207364721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7255053429114574943152961 5441290071835931207364721)
            ·
              refine ⟨4080967553876948405523541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5441290071835931207364721 4080967553876948405523541)
              ·
                refine ⟨47823838521995489127229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4080967553876948405523541 47823838521995489127229)
                ·
                  rfl

theorem cell21_628672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 8].length) (baseStart_628672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628672 prefixEnd_628672 := by exact prefixLift 628672
  have htrace : WordTrace (prefixWord ++ tailWord_628672) baseStart_628672 baseEnd_628672 := by
    simpa [prefixWord, tailWord_628672, baseEnd_628672] using wordTrace_append hprefix tailTrace_628672
  have hstable : (prefixWord ++ tailWord_628672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628672).length < 2 ^ (prefixWord ++ tailWord_628672).sum := by decide
  have hdescent : baseEnd_628672 < baseStart_628672 := by decide
  rcases family_descends (prefixWord ++ tailWord_628672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628720 : List Nat := [2, 1, 1, 1, 3, 2, 2, 6, 3]
def baseStart_628720 : Nat := 118140960795 + 628720 * 2 ^ 59
def prefixEnd_628720 : Nat := 4983230072969 + 3 ^ 40 * 628720 * 2
def baseEnd_628720 : Nat := 143482469819949050581589

theorem tailTrace_628720 : CollatzResearch.WordTrace tailWord_628720 prefixEnd_628720 143482469819949050581589 := by
  unfold tailWord_628720
  simp only [CollatzResearch.WordTrace]
  refine ⟨11465651141131145836201807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15287534854841527781602409 11465651141131145836201807)
  ·
    refine ⟨17198476711696718754302711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11465651141131145836201807 17198476711696718754302711)
    ·
      refine ⟨25797715067545078131454067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17198476711696718754302711 25797715067545078131454067)
      ·
        refine ⟨38696572601317617197181101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25797715067545078131454067 38696572601317617197181101)
        ·
          refine ⟨14511214725494106448942913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38696572601317617197181101 14511214725494106448942913)
          ·
            refine ⟨10883411044120579836707185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14511214725494106448942913 10883411044120579836707185)
            ·
              refine ⟨8162558283090434877530389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10883411044120579836707185 8162558283090434877530389)
              ·
                refine ⟨382619919519864134884237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8162558283090434877530389 382619919519864134884237)
                ·
                  refine ⟨143482469819949050581589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 382619919519864134884237 143482469819949050581589)
                  ·
                    rfl

theorem cell21_628720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 3].length) (baseStart_628720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628720 prefixEnd_628720 := by exact prefixLift 628720
  have htrace : WordTrace (prefixWord ++ tailWord_628720) baseStart_628720 baseEnd_628720 := by
    simpa [prefixWord, tailWord_628720, baseEnd_628720] using wordTrace_append hprefix tailTrace_628720
  have hstable : (prefixWord ++ tailWord_628720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628720).length < 2 ^ (prefixWord ++ tailWord_628720).sum := by decide
  have hdescent : baseEnd_628720 < baseStart_628720 := by decide
  rcases family_descends (prefixWord ++ tailWord_628720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628726 : List Nat := [5, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_628726 : Nat := 118140960795 + 628726 * 2 ^ 59
def prefixEnd_628726 : Nat := 4983230072969 + 3 ^ 40 * 628726 * 2
def baseEnd_628726 : Nat := 143483839101694373481577

theorem tailTrace_628726 : CollatzResearch.WordTrace tailWord_628726 prefixEnd_628726 143483839101694373481577 := by
  unfold tailWord_628726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1433220070015034668570127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15287680746827036464748021 1433220070015034668570127)
  ·
    refine ⟨2149830105022552002855191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1433220070015034668570127 2149830105022552002855191)
    ·
      refine ⟨3224745157533828004282787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2149830105022552002855191 3224745157533828004282787)
      ·
        refine ⟨4837117736300742006424181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3224745157533828004282787 4837117736300742006424181)
        ·
          refine ⟨453479787778194563102267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4837117736300742006424181 453479787778194563102267)
          ·
            refine ⟨680219681667291844653401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453479787778194563102267 680219681667291844653401)
            ·
              refine ⟨510164761250468883490051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 680219681667291844653401 510164761250468883490051)
              ·
                refine ⟨765247141875703325235077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510164761250468883490051 765247141875703325235077)
                ·
                  refine ⟨143483839101694373481577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 765247141875703325235077 143483839101694373481577)
                  ·
                    rfl

theorem cell21_628726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_628726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628726 prefixEnd_628726 := by exact prefixLift 628726
  have htrace : WordTrace (prefixWord ++ tailWord_628726) baseStart_628726 baseEnd_628726 := by
    simpa [prefixWord, tailWord_628726, baseEnd_628726] using wordTrace_append hprefix tailTrace_628726
  have hstable : (prefixWord ++ tailWord_628726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628726).length < 2 ^ (prefixWord ++ tailWord_628726).sum := by decide
  have hdescent : baseEnd_628726 < baseStart_628726 := by decide
  rcases family_descends (prefixWord ++ tailWord_628726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628748 : List Nat := [2, 2, 1, 2, 3, 1, 1, 9]
def baseStart_628748 : Nat := 118140960795 + 628748 * 2 ^ 59
def prefixEnd_628748 : Nat := 4983230072969 + 3 ^ 40 * 628748 * 2
def baseEnd_628748 : Nat := 47829619933809074704955

theorem tailTrace_628748 : CollatzResearch.WordTrace tailWord_628748 prefixEnd_628748 47829619933809074704955 := by
  unfold tailWord_628748
  simp only [CollatzResearch.WordTrace]
  refine ⟨11466161763080426227211449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15288215684107234969615265 11466161763080426227211449)
  ·
    refine ⟨8599621322310319670408587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11466161763080426227211449 8599621322310319670408587)
    ·
      refine ⟨12899431983465479505612881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8599621322310319670408587 12899431983465479505612881)
      ·
        refine ⟨9674573987599109629209661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12899431983465479505612881 9674573987599109629209661)
        ·
          refine ⟨3627965245349666110953623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9674573987599109629209661 3627965245349666110953623)
          ·
            refine ⟨5441947868024499166430435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3627965245349666110953623 5441947868024499166430435)
            ·
              refine ⟨8162921802036748749645653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5441947868024499166430435 8162921802036748749645653)
              ·
                refine ⟨47829619933809074704955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8162921802036748749645653 47829619933809074704955)
                ·
                  rfl

theorem cell21_628748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 9].length) (baseStart_628748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628748 prefixEnd_628748 := by exact prefixLift 628748
  have htrace : WordTrace (prefixWord ++ tailWord_628748) baseStart_628748 baseEnd_628748 := by
    simpa [prefixWord, tailWord_628748, baseEnd_628748] using wordTrace_append hprefix tailTrace_628748
  have hstable : (prefixWord ++ tailWord_628748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628748).length < 2 ^ (prefixWord ++ tailWord_628748).sum := by decide
  have hdescent : baseEnd_628748 < baseStart_628748 := by decide
  rcases family_descends (prefixWord ++ tailWord_628748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628782 : List Nat := [4, 1, 3, 1, 1, 4, 1, 6]
def baseStart_628782 : Nat := 118140960795 + 628782 * 2 ^ 59
def prefixEnd_628782 : Nat := 4983230072969 + 3 ^ 40 * 628782 * 2
def baseEnd_628782 : Nat := 47832206354883573516043

theorem tailTrace_628782 : CollatzResearch.WordTrace tailWord_628782 prefixEnd_628782 47832206354883573516043 := by
  unfold tailWord_628782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2866695451004709532645075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15289042405358450840773733 2866695451004709532645075)
  ·
    refine ⟨4300043176507064298967613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2866695451004709532645075 4300043176507064298967613)
    ·
      refine ⟨1612516191190149112112855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4300043176507064298967613 1612516191190149112112855)
      ·
        refine ⟨2418774286785223668169283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1612516191190149112112855 2418774286785223668169283)
        ·
          refine ⟨3628161430177835502253925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2418774286785223668169283 3628161430177835502253925)
          ·
            refine ⟨680280268158344156672611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3628161430177835502253925 680280268158344156672611)
            ·
              refine ⟨1020420402237516235008917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680280268158344156672611 1020420402237516235008917)
              ·
                refine ⟨47832206354883573516043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1020420402237516235008917 47832206354883573516043)
                ·
                  rfl

theorem cell21_628782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_628782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628782 prefixEnd_628782 := by exact prefixLift 628782
  have htrace : WordTrace (prefixWord ++ tailWord_628782) baseStart_628782 baseEnd_628782 := by
    simpa [prefixWord, tailWord_628782, baseEnd_628782] using wordTrace_append hprefix tailTrace_628782
  have hstable : (prefixWord ++ tailWord_628782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628782).length < 2 ^ (prefixWord ++ tailWord_628782).sum := by decide
  have hdescent : baseEnd_628782 < baseStart_628782 := by decide
  rcases family_descends (prefixWord ++ tailWord_628782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628824 : List Nat := [2, 1, 2, 2, 1, 5, 8]
def baseStart_628824 : Nat := 118140960795 + 628824 * 2 ^ 59
def prefixEnd_628824 : Nat := 4983230072969 + 3 ^ 40 * 628824 * 2
def baseEnd_628824 : Nat := 15945133781874220094227

theorem tailTrace_628824 : CollatzResearch.WordTrace tailWord_628824 prefixEnd_628824 15945133781874220094227 := by
  unfold tailWord_628824
  simp only [CollatzResearch.WordTrace]
  refine ⟨11467547736942758717094763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15290063649257011622793017 11467547736942758717094763)
  ·
    refine ⟨17201321605414138075642145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11467547736942758717094763 17201321605414138075642145)
    ·
      refine ⟨12900991204060603556731609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17201321605414138075642145 12900991204060603556731609)
      ·
        refine ⟨9675743403045452667548707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12900991204060603556731609 9675743403045452667548707)
        ·
          refine ⟨14513615104568179001323061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9675743403045452667548707 14513615104568179001323061)
          ·
            refine ⟨1360651416053266781374037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14513615104568179001323061 1360651416053266781374037)
            ·
              refine ⟨15945133781874220094227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1360651416053266781374037 15945133781874220094227)
              ·
                rfl

theorem cell21_628824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 8].length) (baseStart_628824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628824 prefixEnd_628824 := by exact prefixLift 628824
  have htrace : WordTrace (prefixWord ++ tailWord_628824) baseStart_628824 baseEnd_628824 := by
    simpa [prefixWord, tailWord_628824, baseEnd_628824] using wordTrace_append hprefix tailTrace_628824
  have hstable : (prefixWord ++ tailWord_628824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628824).length < 2 ^ (prefixWord ++ tailWord_628824).sum := by decide
  have hdescent : baseEnd_628824 < baseStart_628824 := by decide
  rcases family_descends (prefixWord ++ tailWord_628824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628855 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 5]
def baseStart_628855 : Nat := 118140960795 + 628855 * 2 ^ 59
def prefixEnd_628855 : Nat := 4983230072969 + 3 ^ 40 * 628855 * 2
def baseEnd_628855 : Nat := 143513278659218815831313

theorem tailTrace_628855 : CollatzResearch.WordTrace tailWord_628855 prefixEnd_628855 143513278659218815831313 := by
  unfold tailWord_628855
  simp only [CollatzResearch.WordTrace]
  refine ⟨22936226136773209728568019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15290817424515473152378679 22936226136773209728568019)
  ·
    refine ⟨34404339205159814592852029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22936226136773209728568019 34404339205159814592852029)
    ·
      refine ⟨12901627201934930472319511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34404339205159814592852029 12901627201934930472319511)
      ·
        refine ⟨19352440802902395708479267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12901627201934930472319511 19352440802902395708479267)
        ·
          refine ⟨29028661204353593562718901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19352440802902395708479267 29028661204353593562718901)
          ·
            refine ⟨2721436987908149396504897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29028661204353593562718901 2721436987908149396504897)
            ·
              refine ⟨2041077740931112047378673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2721436987908149396504897 2041077740931112047378673)
              ·
                refine ⟨1530808305698334035534005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2041077740931112047378673 1530808305698334035534005)
                ·
                  refine ⟨143513278659218815831313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1530808305698334035534005 143513278659218815831313)
                  ·
                    rfl

theorem cell21_628855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 5].length) (baseStart_628855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628855 prefixEnd_628855 := by exact prefixLift 628855
  have htrace : WordTrace (prefixWord ++ tailWord_628855) baseStart_628855 baseEnd_628855 := by
    simpa [prefixWord, tailWord_628855, baseEnd_628855] using wordTrace_append hprefix tailTrace_628855
  have hstable : (prefixWord ++ tailWord_628855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628855).length < 2 ^ (prefixWord ++ tailWord_628855).sum := by decide
  have hdescent : baseEnd_628855 < baseStart_628855 := by decide
  rcases family_descends (prefixWord ++ tailWord_628855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628940 : List Nat := [2, 2, 1, 6, 2, 1, 2, 2, 3]
def baseStart_628940 : Nat := 118140960795 + 628940 * 2 ^ 59
def prefixEnd_628940 : Nat := 4983230072969 + 3 ^ 40 * 628940 * 2
def baseEnd_628940 : Nat := 143532676817277556914473

theorem tailTrace_628940 : CollatzResearch.WordTrace tailWord_628940 prefixEnd_628940 143532676817277556914473 := by
  unfold tailWord_628940
  simp only [CollatzResearch.WordTrace]
  refine ⟨11469663170732634622706137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15292884227643512830274849 11469663170732634622706137)
  ·
    refine ⟨8602247378049475967029603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11469663170732634622706137 8602247378049475967029603)
    ·
      refine ⟨12903371067074213950544405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8602247378049475967029603 12903371067074213950544405)
      ·
        refine ⟨604845518769103778931769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12903371067074213950544405 604845518769103778931769)
        ·
          refine ⟨453634139076827834198827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 604845518769103778931769 453634139076827834198827)
          ·
            refine ⟨680451208615241751298241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453634139076827834198827 680451208615241751298241)
            ·
              refine ⟨510338406461431313473681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 680451208615241751298241 510338406461431313473681)
              ·
                refine ⟨382753804846073485105261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 510338406461431313473681 382753804846073485105261)
                ·
                  refine ⟨143532676817277556914473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 382753804846073485105261 143532676817277556914473)
                  ·
                    rfl

theorem cell21_628940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_628940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628940 prefixEnd_628940 := by exact prefixLift 628940
  have htrace : WordTrace (prefixWord ++ tailWord_628940) baseStart_628940 baseEnd_628940 := by
    simpa [prefixWord, tailWord_628940, baseEnd_628940] using wordTrace_append hprefix tailTrace_628940
  have hstable : (prefixWord ++ tailWord_628940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628940).length < 2 ^ (prefixWord ++ tailWord_628940).sum := by decide
  have hdescent : baseEnd_628940 < baseStart_628940 := by decide
  rcases family_descends (prefixWord ++ tailWord_628940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628945 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 6]
def baseStart_628945 : Nat := 118140960795 + 628945 * 2 ^ 59
def prefixEnd_628945 : Nat := 4983230072969 + 3 ^ 40 * 628945 * 2
def baseEnd_628945 : Nat := 143533817885398659331129

theorem tailTrace_628945 : CollatzResearch.WordTrace tailWord_628945 prefixEnd_628945 143533817885398659331129 := by
  unfold tailWord_628945
  simp only [CollatzResearch.WordTrace]
  refine ⟨22939508706447155099344289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15293005804298103399562859 22939508706447155099344289)
  ·
    refine ⟨17204631529835366324508217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22939508706447155099344289 17204631529835366324508217)
    ·
      refine ⟨12903473647376524743381163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17204631529835366324508217 12903473647376524743381163)
      ·
        refine ⟨19355210471064787115071745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12903473647376524743381163 19355210471064787115071745)
        ·
          refine ⟨14516407853298590336303809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19355210471064787115071745 14516407853298590336303809)
          ·
            refine ⟨10887305889973942752227857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14516407853298590336303809 10887305889973942752227857)
            ·
              refine ⟨8165479417480457064170893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10887305889973942752227857 8165479417480457064170893)
              ·
                refine ⟨3062054781555171399064085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8165479417480457064170893 3062054781555171399064085)
                ·
                  refine ⟨143533817885398659331129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3062054781555171399064085 143533817885398659331129)
                  ·
                    rfl

theorem cell21_628945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_628945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628945 prefixEnd_628945 := by exact prefixLift 628945
  have htrace : WordTrace (prefixWord ++ tailWord_628945) baseStart_628945 baseEnd_628945 := by
    simpa [prefixWord, tailWord_628945, baseEnd_628945] using wordTrace_append hprefix tailTrace_628945
  have hstable : (prefixWord ++ tailWord_628945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628945).length < 2 ^ (prefixWord ++ tailWord_628945).sum := by decide
  have hdescent : baseEnd_628945 < baseStart_628945 := by decide
  rcases family_descends (prefixWord ++ tailWord_628945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628996 : List Nat := [2, 3, 2, 2, 3, 2, 1, 2, 4]
def baseStart_628996 : Nat := 118140960795 + 628996 * 2 ^ 59
def prefixEnd_628996 : Nat := 4983230072969 + 3 ^ 40 * 628996 * 2
def baseEnd_628996 : Nat := 143545456780233903981025

theorem tailTrace_628996 : CollatzResearch.WordTrace tailWord_628996 prefixEnd_628996 143545456780233903981025 := by
  unfold tailWord_628996
  simp only [CollatzResearch.WordTrace]
  refine ⟨11470684414631195404725421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15294245886174927206300561 11470684414631195404725421)
  ·
    refine ⟨4301506655486698276772033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11470684414631195404725421 4301506655486698276772033)
    ·
      refine ⟨3226129991615023707579025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4301506655486698276772033 3226129991615023707579025)
      ·
        refine ⟨2419597493711267780684269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3226129991615023707579025 2419597493711267780684269)
        ·
          refine ⟨907349060141725417756601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2419597493711267780684269 907349060141725417756601)
          ·
            refine ⟨680511795106294063317451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 907349060141725417756601 680511795106294063317451)
            ·
              refine ⟨1020767692659441094976177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680511795106294063317451 1020767692659441094976177)
              ·
                refine ⟨765575769494580821232133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1020767692659441094976177 765575769494580821232133)
                ·
                  refine ⟨143545456780233903981025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 765575769494580821232133 143545456780233903981025)
                  ·
                    rfl

theorem cell21_628996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_628996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_628996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_628996 prefixEnd_628996 := by exact prefixLift 628996
  have htrace : WordTrace (prefixWord ++ tailWord_628996) baseStart_628996 baseEnd_628996 := by
    simpa [prefixWord, tailWord_628996, baseEnd_628996] using wordTrace_append hprefix tailTrace_628996
  have hstable : (prefixWord ++ tailWord_628996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628996).length < 2 ^ (prefixWord ++ tailWord_628996).sum := by decide
  have hdescent : baseEnd_628996 < baseStart_628996 := by decide
  rcases family_descends (prefixWord ++ tailWord_628996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629117 : List Nat := [1, 4, 1, 1, 2, 3, 4, 2, 3]
def baseStart_629117 : Nat := 118140960795 + 629117 * 2 ^ 59
def prefixEnd_629117 : Nat := 4983230072969 + 3 ^ 40 * 629117 * 2
def baseEnd_629117 : Nat := 143573070628764582464111

theorem tailTrace_629117 : CollatzResearch.WordTrace tailWord_629117 prefixEnd_629117 143573070628764582464111 := by
  unfold tailWord_629117
  simp only [CollatzResearch.WordTrace]
  refine ⟨22945782061824028474605605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15297188041216018983070403 22945782061824028474605605)
  ·
    refine ⟨4302334136592005338988551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22945782061824028474605605 4302334136592005338988551)
    ·
      refine ⟨6453501204888008008482827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4302334136592005338988551 6453501204888008008482827)
      ·
        refine ⟨9680251807332012012724241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6453501204888008008482827 9680251807332012012724241)
        ·
          refine ⟨7260188855499009009543181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9680251807332012012724241 7260188855499009009543181)
          ·
            refine ⟨2722570820812128378578693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7260188855499009009543181 2722570820812128378578693)
            ·
              refine ⟨510482028902274070983505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2722570820812128378578693 510482028902274070983505)
              ·
                refine ⟨382861521676705553237629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 510482028902274070983505 382861521676705553237629)
                ·
                  refine ⟨143573070628764582464111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 382861521676705553237629 143573070628764582464111)
                  ·
                    rfl

theorem cell21_629117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_629117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_629117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_629117 prefixEnd_629117 := by exact prefixLift 629117
  have htrace : WordTrace (prefixWord ++ tailWord_629117) baseStart_629117 baseEnd_629117 := by
    simpa [prefixWord, tailWord_629117, baseEnd_629117] using wordTrace_append hprefix tailTrace_629117
  have hstable : (prefixWord ++ tailWord_629117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629117).length < 2 ^ (prefixWord ++ tailWord_629117).sum := by decide
  have hdescent : baseEnd_629117 < baseStart_629117 := by decide
  rcases family_descends (prefixWord ++ tailWord_629117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629165 : List Nat := [1, 5, 2, 2, 3, 1, 1, 2, 4]
def baseStart_629165 : Nat := 118140960795 + 629165 * 2 ^ 59
def prefixEnd_629165 : Nat := 4983230072969 + 3 ^ 40 * 629165 * 2
def baseEnd_629165 : Nat := 143584024882727165664013

theorem tailTrace_629165 : CollatzResearch.WordTrace tailWord_629165 prefixEnd_629165 143584024882727165664013 := by
  unfold tailWord_629165
  simp only [CollatzResearch.WordTrace]
  refine ⟨22947532765650132672352949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15298355177100088448235299 22947532765650132672352949)
  ·
    refine ⟨2151331196779699938033089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22947532765650132672352949 2151331196779699938033089)
    ·
      refine ⟨1613498397584774953524817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2151331196779699938033089 1613498397584774953524817)
      ·
        refine ⟨1210123798188581215143613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1613498397584774953524817 1210123798188581215143613)
        ·
          refine ⟨453796424320717955678855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1210123798188581215143613 453796424320717955678855)
          ·
            refine ⟨680694636481076933518283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453796424320717955678855 680694636481076933518283)
            ·
              refine ⟨1021041954721615400277425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680694636481076933518283 1021041954721615400277425)
              ·
                refine ⟨765781466041211550208069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1021041954721615400277425 765781466041211550208069)
                ·
                  refine ⟨143584024882727165664013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 765781466041211550208069 143584024882727165664013)
                  ·
                    rfl

theorem cell21_629165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_629165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_629165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_629165 prefixEnd_629165 := by exact prefixLift 629165
  have htrace : WordTrace (prefixWord ++ tailWord_629165) baseStart_629165 baseEnd_629165 := by
    simpa [prefixWord, tailWord_629165, baseEnd_629165] using wordTrace_append hprefix tailTrace_629165
  have hstable : (prefixWord ++ tailWord_629165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629165).length < 2 ^ (prefixWord ++ tailWord_629165).sum := by decide
  have hdescent : baseEnd_629165 < baseStart_629165 := by decide
  rcases family_descends (prefixWord ++ tailWord_629165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629187 : List Nat := [1, 1, 1, 3, 1, 1, 3, 10]
def baseStart_629187 : Nat := 118140960795 + 629187 * 2 ^ 59
def prefixEnd_629187 : Nat := 4983230072969 + 3 ^ 40 * 629187 * 2
def baseEnd_629187 : Nat := 47863015194153338765767

theorem tailTrace_629187 : CollatzResearch.WordTrace tailWord_629187 prefixEnd_629187 47863015194153338765767 := by
  unfold tailWord_629187
  simp only [CollatzResearch.WordTrace]
  refine ⟨22948335171570430429653815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15298890114380286953102543 22948335171570430429653815)
  ·
    refine ⟨34422502757355645644480723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22948335171570430429653815 34422502757355645644480723)
    ·
      refine ⟨51633754136033468466721085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34422502757355645644480723 51633754136033468466721085)
      ·
        refine ⟨19362657801012550675020407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51633754136033468466721085 19362657801012550675020407)
        ·
          refine ⟨29043986701518826012530611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19362657801012550675020407 29043986701518826012530611)
          ·
            refine ⟨43565980052278239018795917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29043986701518826012530611 43565980052278239018795917)
            ·
              refine ⟨16337242519604339632048469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43565980052278239018795917 16337242519604339632048469)
              ·
                refine ⟨47863015194153338765767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16337242519604339632048469 47863015194153338765767)
                ·
                  rfl

theorem cell21_629187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 10].length) (baseStart_629187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_629187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_629187 prefixEnd_629187 := by exact prefixLift 629187
  have htrace : WordTrace (prefixWord ++ tailWord_629187) baseStart_629187 baseEnd_629187 := by
    simpa [prefixWord, tailWord_629187, baseEnd_629187] using wordTrace_append hprefix tailTrace_629187
  have hstable : (prefixWord ++ tailWord_629187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629187).length < 2 ^ (prefixWord ++ tailWord_629187).sum := by decide
  have hdescent : baseEnd_629187 < baseStart_629187 := by decide
  rcases family_descends (prefixWord ++ tailWord_629187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629221 : List Nat := [1, 3, 1, 5, 2, 2, 7]
def baseStart_629221 : Nat := 118140960795 + 629221 * 2 ^ 59
def prefixEnd_629221 : Nat := 4983230072969 + 3 ^ 40 * 629221 * 2
def baseEnd_629221 : Nat := 15955200538409279192285

theorem tailTrace_629221 : CollatzResearch.WordTrace tailWord_629221 prefixEnd_629221 15955200538409279192285 := by
  unfold tailWord_629221
  simp only [CollatzResearch.WordTrace]
  refine ⟨22949575253447254236391517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15299716835631502824261011 22949575253447254236391517)
  ·
    refine ⟨8606090720042720338646819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22949575253447254236391517 8606090720042720338646819)
    ·
      refine ⟨12909136080064080507970229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8606090720042720338646819 12909136080064080507970229)
      ·
        refine ⟨1210231507506007547622209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12909136080064080507970229 1210231507506007547622209)
        ·
          refine ⟨907673630629505660716657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1210231507506007547622209 907673630629505660716657)
          ·
            refine ⟨680755222972129245537493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 907673630629505660716657 680755222972129245537493)
            ·
              refine ⟨15955200538409279192285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 680755222972129245537493 15955200538409279192285)
              ·
                rfl

theorem cell21_629221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 7].length) (baseStart_629221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_629221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_629221 prefixEnd_629221 := by exact prefixLift 629221
  have htrace : WordTrace (prefixWord ++ tailWord_629221) baseStart_629221 baseEnd_629221 := by
    simpa [prefixWord, tailWord_629221, baseEnd_629221] using wordTrace_append hprefix tailTrace_629221
  have hstable : (prefixWord ++ tailWord_629221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629221).length < 2 ^ (prefixWord ++ tailWord_629221).sum := by decide
  have hdescent : baseEnd_629221 < baseStart_629221 := by decide
  rcases family_descends (prefixWord ++ tailWord_629221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629280 : List Nat := [2, 1, 1, 6, 2, 9]
def baseStart_629280 : Nat := 118140960795 + 629280 * 2 ^ 59
def prefixEnd_629280 : Nat := 4983230072969 + 3 ^ 40 * 629280 * 2
def baseEnd_629280 : Nat := 5318898868500463749893

theorem tailTrace_629280 : CollatzResearch.WordTrace tailWord_629280 prefixEnd_629280 5318898868500463749893 := by
  unfold tailWord_629280
  simp only [CollatzResearch.WordTrace]
  refine ⟨11475863580116753656394647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15301151440155671541859529 11475863580116753656394647)
  ·
    refine ⟨17213795370175130484591971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11475863580116753656394647 17213795370175130484591971)
    ·
      refine ⟨25820693055262695726887957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17213795370175130484591971 25820693055262695726887957)
      ·
        refine ⟨1210344986965438862197873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25820693055262695726887957 1210344986965438862197873)
        ·
          refine ⟨907758740224079146648405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1210344986965438862197873 907758740224079146648405)
          ·
            refine ⟨5318898868500463749893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 907758740224079146648405 5318898868500463749893)
            ·
              rfl

theorem cell21_629280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 9].length) (baseStart_629280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_629280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_629280 prefixEnd_629280 := by exact prefixLift 629280
  have htrace : WordTrace (prefixWord ++ tailWord_629280) baseStart_629280 baseEnd_629280 := by
    simpa [prefixWord, tailWord_629280, baseEnd_629280] using wordTrace_append hprefix tailTrace_629280
  have hstable : (prefixWord ++ tailWord_629280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629280).length < 2 ^ (prefixWord ++ tailWord_629280).sum := by decide
  have hdescent : baseEnd_629280 < baseStart_629280 := by decide
  rcases family_descends (prefixWord ++ tailWord_629280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629387 : List Nat := [1, 1, 1, 1, 4, 1, 2, 7, 3]
def baseStart_629387 : Nat := 118140960795 + 629387 * 2 ^ 59
def prefixEnd_629387 : Nat := 4983230072969 + 3 ^ 40 * 629387 * 2
def baseEnd_629387 : Nat := 143634688307304112963559

theorem tailTrace_629387 : CollatzResearch.WordTrace tailWord_629387 prefixEnd_629387 143634688307304112963559 := by
  unfold tailWord_629387
  simp only [CollatzResearch.WordTrace]
  refine ⟨22955629770845864586934415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15303753180563909724622943 22955629770845864586934415)
  ·
    refine ⟨34433444656268796880401623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22955629770845864586934415 34433444656268796880401623)
    ·
      refine ⟨51650166984403195320602435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34433444656268796880401623 51650166984403195320602435)
      ·
        refine ⟨77475250476604792980903653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51650166984403195320602435 77475250476604792980903653)
        ·
          refine ⟨14526609464363398683919435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77475250476604792980903653 14526609464363398683919435)
          ·
            refine ⟨21789914196545098025879153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14526609464363398683919435 21789914196545098025879153)
            ·
              refine ⟨16342435647408823519409365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21789914196545098025879153 16342435647408823519409365)
              ·
                refine ⟨383025835486144301236157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16342435647408823519409365 383025835486144301236157)
                ·
                  refine ⟨143634688307304112963559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 383025835486144301236157 143634688307304112963559)
                  ·
                    rfl

theorem cell21_629387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 3].length) (baseStart_629387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_629387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_629387 prefixEnd_629387 := by exact prefixLift 629387
  have htrace : WordTrace (prefixWord ++ tailWord_629387) baseStart_629387 baseEnd_629387 := by
    simpa [prefixWord, tailWord_629387, baseEnd_629387] using wordTrace_append hprefix tailTrace_629387
  have hstable : (prefixWord ++ tailWord_629387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629387).length < 2 ^ (prefixWord ++ tailWord_629387).sum := by decide
  have hdescent : baseEnd_629387 < baseStart_629387 := by decide
  rcases family_descends (prefixWord ++ tailWord_629387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629401 : List Nat := [1, 2, 1, 2, 1, 2, 4, 4, 4]
def baseStart_629401 : Nat := 118140960795 + 629401 * 2 ^ 59
def prefixEnd_629401 : Nat := 4983230072969 + 3 ^ 40 * 629401 * 2
def baseEnd_629401 : Nat := 143637883298043199730197

theorem tailTrace_629401 : CollatzResearch.WordTrace tailWord_629401 prefixEnd_629401 143637883298043199730197 := by
  unfold tailWord_629401
  simp only [CollatzResearch.WordTrace]
  refine ⟨22956140392795144977944057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15304093595196763318629371 22956140392795144977944057)
  ·
    refine ⟨17217105294596358733458043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22956140392795144977944057 17217105294596358733458043)
    ·
      refine ⟨25825657941894538100187065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17217105294596358733458043 25825657941894538100187065)
      ·
        refine ⟨19369243456420903575140299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25825657941894538100187065 19369243456420903575140299)
        ·
          refine ⟨29053865184631355362710449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19369243456420903575140299 29053865184631355362710449)
          ·
            refine ⟨21790398888473516522032837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29053865184631355362710449 21790398888473516522032837)
            ·
              refine ⟨4085699791588784347881157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21790398888473516522032837 4085699791588784347881157)
              ·
                refine ⟨766068710922897065227717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4085699791588784347881157 766068710922897065227717)
                ·
                  refine ⟨143637883298043199730197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 766068710922897065227717 143637883298043199730197)
                  ·
                    rfl

theorem cell21_629401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_629401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_629401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_629401 prefixEnd_629401 := by exact prefixLift 629401
  have htrace : WordTrace (prefixWord ++ tailWord_629401) baseStart_629401 baseEnd_629401 := by
    simpa [prefixWord, tailWord_629401, baseEnd_629401] using wordTrace_append hprefix tailTrace_629401
  have hstable : (prefixWord ++ tailWord_629401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629401).length < 2 ^ (prefixWord ++ tailWord_629401).sum := by decide
  have hdescent : baseEnd_629401 < baseStart_629401 := by decide
  rcases family_descends (prefixWord ++ tailWord_629401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629404 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 5]
def baseStart_629404 : Nat := 118140960795 + 629404 * 2 ^ 59
def prefixEnd_629404 : Nat := 4983230072969 + 3 ^ 40 * 629404 * 2
def baseEnd_629404 : Nat := 143638567938915861180191

theorem tailTrace_629404 : CollatzResearch.WordTrace tailWord_629404 prefixEnd_629404 143638567938915861180191 := by
  unfold tailWord_629404
  simp only [CollatzResearch.WordTrace]
  refine ⟨11478124905892138245151633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15304166541189517660202177 11478124905892138245151633)
  ·
    refine ⟨8608593679419103683863725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11478124905892138245151633 8608593679419103683863725)
    ·
      refine ⟨3228222629782163881448897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8608593679419103683863725 3228222629782163881448897)
      ·
        refine ⟨2421166972336622911086673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3228222629782163881448897 2421166972336622911086673)
        ·
          refine ⟨1815875229252467183315005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2421166972336622911086673 1815875229252467183315005)
          ·
            refine ⟨680953210969675193743127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1815875229252467183315005 680953210969675193743127)
            ·
              refine ⟨1021429816454512790614691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680953210969675193743127 1021429816454512790614691)
              ·
                refine ⟨1532144724681769185922037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021429816454512790614691 1532144724681769185922037)
                ·
                  refine ⟨143638567938915861180191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1532144724681769185922037 143638567938915861180191)
                  ·
                    rfl

theorem cell21_629404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_629404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_629404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_629404 prefixEnd_629404 := by exact prefixLift 629404
  have htrace : WordTrace (prefixWord ++ tailWord_629404) baseStart_629404 baseEnd_629404 := by
    simpa [prefixWord, tailWord_629404, baseEnd_629404] using wordTrace_append hprefix tailTrace_629404
  have hstable : (prefixWord ++ tailWord_629404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629404).length < 2 ^ (prefixWord ++ tailWord_629404).sum := by decide
  have hdescent : baseEnd_629404 < baseStart_629404 := by decide
  rcases family_descends (prefixWord ++ tailWord_629404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629511 : List Nat := [1, 1, 4, 4, 1, 3, 1, 2, 4]
def baseStart_629511 : Nat := 118140960795 + 629511 * 2 ^ 59
def prefixEnd_629511 : Nat := 4983230072969 + 3 ^ 40 * 629511 * 2
def baseEnd_629511 : Nat := 143662986796707452896639

theorem tailTrace_629511 : CollatzResearch.WordTrace tailWord_629511 prefixEnd_629511 143662986796707452896639 := by
  unfold tailWord_629511
  simp only [CollatzResearch.WordTrace]
  refine ⟨22960152422396633764448387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15306768281597755842965591 22960152422396633764448387)
  ·
    refine ⟨34440228633594950646672581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22960152422396633764448387 34440228633594950646672581)
    ·
      refine ⟨6457542868799053246251109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34440228633594950646672581 6457542868799053246251109)
      ·
        refine ⟨1210789287899822483672083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6457542868799053246251109 1210789287899822483672083)
        ·
          refine ⟨1816183931849733725508125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1210789287899822483672083 1816183931849733725508125)
          ·
            refine ⟨681068974443650147065547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1816183931849733725508125 681068974443650147065547)
            ·
              refine ⟨1021603461665475220598321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681068974443650147065547 1021603461665475220598321)
              ·
                refine ⟨766202596249106415448741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1021603461665475220598321 766202596249106415448741)
                ·
                  refine ⟨143662986796707452896639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 766202596249106415448741 143662986796707452896639)
                  ·
                    rfl

theorem cell21_629511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 4].length) (baseStart_629511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_629511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_629511 prefixEnd_629511 := by exact prefixLift 629511
  have htrace : WordTrace (prefixWord ++ tailWord_629511) baseStart_629511 baseEnd_629511 := by
    simpa [prefixWord, tailWord_629511, baseEnd_629511] using wordTrace_append hprefix tailTrace_629511
  have hstable : (prefixWord ++ tailWord_629511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629511).length < 2 ^ (prefixWord ++ tailWord_629511).sum := by decide
  have hdescent : baseEnd_629511 < baseStart_629511 := by decide
  rcases family_descends (prefixWord ++ tailWord_629511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629567 : List Nat := [1, 1, 2, 2, 5, 1, 9]
def baseStart_629567 : Nat := 118140960795 + 629567 * 2 ^ 59
def prefixEnd_629567 : Nat := 4983230072969 + 3 ^ 40 * 629567 * 2
def baseEnd_629567 : Nat := 15963974084407088884799

theorem tailTrace_629567 : CollatzResearch.WordTrace tailWord_629567 prefixEnd_629567 15963974084407088884799 := by
  unfold tailWord_629567
  simp only [CollatzResearch.WordTrace]
  refine ⟨22962194910193755328486955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15308129940129170218991303 22962194910193755328486955)
  ·
    refine ⟨34443292365290632992730433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22962194910193755328486955 34443292365290632992730433)
    ·
      refine ⟨25832469273967974744547825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34443292365290632992730433 25832469273967974744547825)
      ·
        refine ⟨19374351955475981058410869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25832469273967974744547825 19374351955475981058410869)
        ·
          refine ⟨1816345495825873224226019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19374351955475981058410869 1816345495825873224226019)
          ·
            refine ⟨2724518243738809836339029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1816345495825873224226019 2724518243738809836339029)
            ·
              refine ⟨15963974084407088884799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2724518243738809836339029 15963974084407088884799)
              ·
                rfl

theorem cell21_629567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 9].length) (baseStart_629567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_629567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_629567 prefixEnd_629567 := by exact prefixLift 629567
  have htrace : WordTrace (prefixWord ++ tailWord_629567) baseStart_629567 baseEnd_629567 := by
    simpa [prefixWord, tailWord_629567, baseEnd_629567] using wordTrace_append hprefix tailTrace_629567
  have hstable : (prefixWord ++ tailWord_629567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629567).length < 2 ^ (prefixWord ++ tailWord_629567).sum := by decide
  have hdescent : baseEnd_629567 < baseStart_629567 := by decide
  rcases family_descends (prefixWord ++ tailWord_629567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629629 : List Nat := [1, 4, 1, 1, 2, 1, 3, 4, 4]
def baseStart_629629 : Nat := 118140960795 + 629629 * 2 ^ 59
def prefixEnd_629629 : Nat := 4983230072969 + 3 ^ 40 * 629629 * 2
def baseEnd_629629 : Nat := 143689916004365469929731

theorem tailTrace_629629 : CollatzResearch.WordTrace tailWord_629629 prefixEnd_629629 143689916004365469929731 := by
  unfold tailWord_629629
  simp only [CollatzResearch.WordTrace]
  refine ⟨22964456235969139917243941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15309637490646093278162627 22964456235969139917243941)
  ·
    refine ⟨4305835544244213734483239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22964456235969139917243941 4305835544244213734483239)
    ·
      refine ⟨6458753316366320601724859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4305835544244213734483239 6458753316366320601724859)
      ·
        refine ⟨9688129974549480902587289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6458753316366320601724859 9688129974549480902587289)
        ·
          refine ⟨7266097480912110676940467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9688129974549480902587289 7266097480912110676940467)
          ·
            refine ⟨10899146221368166015410701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7266097480912110676940467 10899146221368166015410701)
            ·
              refine ⟨4087179833013062255779013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10899146221368166015410701 4087179833013062255779013)
              ·
                refine ⟨766346218689949172958565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4087179833013062255779013 766346218689949172958565)
                ·
                  refine ⟨143689916004365469929731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 766346218689949172958565 143689916004365469929731)
                  ·
                    rfl

theorem cell21_629629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_629629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_629629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_629629 prefixEnd_629629 := by exact prefixLift 629629
  have htrace : WordTrace (prefixWord ++ tailWord_629629) baseStart_629629 baseEnd_629629 := by
    simpa [prefixWord, tailWord_629629, baseEnd_629629] using wordTrace_append hprefix tailTrace_629629
  have hstable : (prefixWord ++ tailWord_629629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629629).length < 2 ^ (prefixWord ++ tailWord_629629).sum := by decide
  have hdescent : baseEnd_629629 < baseStart_629629 := by decide
  rcases family_descends (prefixWord ++ tailWord_629629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629643 : List Nat := [1, 1, 1, 1, 4, 2, 5, 6]
def baseStart_629643 : Nat := 118140960795 + 629643 * 2 ^ 59
def prefixEnd_629643 : Nat := 4983230072969 + 3 ^ 40 * 629643 * 2
def baseEnd_629643 : Nat := 47897703665034852232123

theorem tailTrace_629643 : CollatzResearch.WordTrace tailWord_629643 prefixEnd_629643 47897703665034852232123 := by
  unfold tailWord_629643
  simp only [CollatzResearch.WordTrace]
  refine ⟨22964966857918420308253583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15309977905278946872169055 22964966857918420308253583)
  ·
    refine ⟨34447450286877630462380375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22964966857918420308253583 34447450286877630462380375)
    ·
      refine ⟨51671175430316445693570563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34447450286877630462380375 51671175430316445693570563)
      ·
        refine ⟨77506763145474668540355845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51671175430316445693570563 77506763145474668540355845)
        ·
          refine ⟨14532518089776500351316721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77506763145474668540355845 14532518089776500351316721)
          ·
            refine ⟨10899388567332375263487541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14532518089776500351316721 10899388567332375263487541)
            ·
              refine ⟨1021817678187410180951957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10899388567332375263487541 1021817678187410180951957)
              ·
                refine ⟨47897703665034852232123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1021817678187410180951957 47897703665034852232123)
                ·
                  rfl

theorem cell21_629643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 6].length) (baseStart_629643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_629643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_629643 prefixEnd_629643 := by exact prefixLift 629643
  have htrace : WordTrace (prefixWord ++ tailWord_629643) baseStart_629643 baseEnd_629643 := by
    simpa [prefixWord, tailWord_629643, baseEnd_629643] using wordTrace_append hprefix tailTrace_629643
  have hstable : (prefixWord ++ tailWord_629643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629643).length < 2 ^ (prefixWord ++ tailWord_629643).sum := by decide
  have hdescent : baseEnd_629643 < baseStart_629643 := by decide
  rcases family_descends (prefixWord ++ tailWord_629643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629677 : List Nat := [1, 5, 2, 3, 1, 1, 8]
def baseStart_629677 : Nat := 118140960795 + 629677 * 2 ^ 59
def prefixEnd_629677 : Nat := 4983230072969 + 3 ^ 40 * 629677 * 2
def baseEnd_629677 : Nat := 15966763362036450347737

theorem tailTrace_629677 : CollatzResearch.WordTrace tailWord_629677 prefixEnd_629677 15966763362036450347737 := by
  unfold tailWord_629677
  simp only [CollatzResearch.WordTrace]
  refine ⟨22966206939795244114991285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15310804626530162743327523 22966206939795244114991285)
  ·
    refine ⟨2153081900605804135780433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22966206939795244114991285 2153081900605804135780433)
    ·
      refine ⟨1614811425454353101835325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2153081900605804135780433 1614811425454353101835325)
      ·
        refine ⟨605554284545382413188247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1614811425454353101835325 605554284545382413188247)
        ·
          refine ⟨908331426818073619782371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605554284545382413188247 908331426818073619782371)
          ·
            refine ⟨1362497140227110429673557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908331426818073619782371 1362497140227110429673557)
            ·
              refine ⟨15966763362036450347737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1362497140227110429673557 15966763362036450347737)
              ·
                rfl

theorem cell21_629677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 8].length) (baseStart_629677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_629677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_629677 prefixEnd_629677 := by exact prefixLift 629677
  have htrace : WordTrace (prefixWord ++ tailWord_629677) baseStart_629677 baseEnd_629677 := by
    simpa [prefixWord, tailWord_629677, baseEnd_629677] using wordTrace_append hprefix tailTrace_629677
  have hstable : (prefixWord ++ tailWord_629677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629677).length < 2 ^ (prefixWord ++ tailWord_629677).sum := by decide
  have hdescent : baseEnd_629677 < baseStart_629677 := by decide
  rcases family_descends (prefixWord ++ tailWord_629677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629725 : List Nat := [1, 4, 3, 1, 2, 3, 1, 3, 3]
def baseStart_629725 : Nat := 118140960795 + 629725 * 2 ^ 59
def prefixEnd_629725 : Nat := 4983230072969 + 3 ^ 40 * 629725 * 2
def baseEnd_629725 : Nat := 143711824512290636329535

theorem tailTrace_629725 : CollatzResearch.WordTrace tailWord_629725 prefixEnd_629725 143711824512290636329535 := by
  unfold tailWord_629725
  simp only [CollatzResearch.WordTrace]
  refine ⟨22967957643621348312738629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15311971762414232208492419 22967957643621348312738629)
  ·
    refine ⟨4306492058179002808638493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22967957643621348312738629 4306492058179002808638493)
    ·
      refine ⟨1614934521817126053239435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4306492058179002808638493 1614934521817126053239435)
      ·
        refine ⟨2422401782725689079859153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1614934521817126053239435 2422401782725689079859153)
        ·
          refine ⟨1816801337044266809894365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2422401782725689079859153 1816801337044266809894365)
          ·
            refine ⟨681300501391600053710387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1816801337044266809894365 681300501391600053710387)
            ·
              refine ⟨1021950752087400080565581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681300501391600053710387 1021950752087400080565581)
              ·
                refine ⟨383231532032775030212093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1021950752087400080565581 383231532032775030212093)
                ·
                  refine ⟨143711824512290636329535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 383231532032775030212093 143711824512290636329535)
                  ·
                    rfl

theorem cell21_629725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_629725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_629725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_629725 prefixEnd_629725 := by exact prefixLift 629725
  have htrace : WordTrace (prefixWord ++ tailWord_629725) baseStart_629725 baseEnd_629725 := by
    simpa [prefixWord, tailWord_629725, baseEnd_629725] using wordTrace_append hprefix tailTrace_629725
  have hstable : (prefixWord ++ tailWord_629725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629725).length < 2 ^ (prefixWord ++ tailWord_629725).sum := by decide
  have hdescent : baseEnd_629725 < baseStart_629725 := by decide
  rcases family_descends (prefixWord ++ tailWord_629725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629857 : List Nat := [1, 2, 3, 1, 1, 2, 5, 2, 4]
def baseStart_629857 : Nat := 118140960795 + 629857 * 2 ^ 59
def prefixEnd_629857 : Nat := 4983230072969 + 3 ^ 40 * 629857 * 2
def baseEnd_629857 : Nat := 143741948710687740129265

theorem tailTrace_629857 : CollatzResearch.WordTrace tailWord_629857 prefixEnd_629857 143741948710687740129265 := by
  unfold tailWord_629857
  simp only [CollatzResearch.WordTrace]
  refine ⟨22972772079143134856543825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15315181386095423237695883 22972772079143134856543825)
  ·
    refine ⟨17229579059357351142407869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22972772079143134856543825 17229579059357351142407869)
    ·
      refine ⟨6461092147259006678402951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17229579059357351142407869 6461092147259006678402951)
      ·
        refine ⟨9691638220888510017604427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6461092147259006678402951 9691638220888510017604427)
        ·
          refine ⟨14537457331332765026406641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9691638220888510017604427 14537457331332765026406641)
          ·
            refine ⟨10903092998499573769804981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14537457331332765026406641 10903092998499573769804981)
            ·
              refine ⟨1022164968609335040919217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10903092998499573769804981 1022164968609335040919217)
              ·
                refine ⟨766623726457001280689413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022164968609335040919217 766623726457001280689413)
                ·
                  refine ⟨143741948710687740129265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 766623726457001280689413 143741948710687740129265)
                  ·
                    rfl

theorem cell21_629857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_629857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_629857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_629857 prefixEnd_629857 := by exact prefixLift 629857
  have htrace : WordTrace (prefixWord ++ tailWord_629857) baseStart_629857 baseEnd_629857 := by
    simpa [prefixWord, tailWord_629857, baseEnd_629857] using wordTrace_append hprefix tailTrace_629857
  have hstable : (prefixWord ++ tailWord_629857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629857).length < 2 ^ (prefixWord ++ tailWord_629857).sum := by decide
  have hdescent : baseEnd_629857 < baseStart_629857 := by decide
  rcases family_descends (prefixWord ++ tailWord_629857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629874 : List Nat := [3, 2, 1, 2, 2, 1, 5, 1, 4]
def baseStart_629874 : Nat := 118140960795 + 629874 * 2 ^ 59
def prefixEnd_629874 : Nat := 4983230072969 + 3 ^ 40 * 629874 * 2
def baseEnd_629874 : Nat := 143745828342299488345897

theorem tailTrace_629874 : CollatzResearch.WordTrace tailWord_629874 prefixEnd_629874 143745828342299488345897 := by
  unfold tailWord_629874
  simp only [CollatzResearch.WordTrace]
  refine ⟨5743348030020386689978169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15315594746721031173275117 5743348030020386689978169)
  ·
    refine ⟨4307511022515290017483627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5743348030020386689978169 4307511022515290017483627)
    ·
      refine ⟨6461266533772935026225441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4307511022515290017483627 6461266533772935026225441)
      ·
        refine ⟨4845949900329701269669081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6461266533772935026225441 4845949900329701269669081)
        ·
          refine ⟨3634462425247275952251811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4845949900329701269669081 3634462425247275952251811)
          ·
            refine ⟨5451693637870913928377717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3634462425247275952251811 5451693637870913928377717)
            ·
              refine ⟨511096278550398180785411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5451693637870913928377717 511096278550398180785411)
              ·
                refine ⟨766644417825597271178117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 511096278550398180785411 766644417825597271178117)
                ·
                  refine ⟨143745828342299488345897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 766644417825597271178117 143745828342299488345897)
                  ·
                    rfl

theorem cell21_629874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_629874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_629874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_629874 prefixEnd_629874 := by exact prefixLift 629874
  have htrace : WordTrace (prefixWord ++ tailWord_629874) baseStart_629874 baseEnd_629874 := by
    simpa [prefixWord, tailWord_629874, baseEnd_629874] using wordTrace_append hprefix tailTrace_629874
  have hstable : (prefixWord ++ tailWord_629874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629874).length < 2 ^ (prefixWord ++ tailWord_629874).sum := by decide
  have hdescent : baseEnd_629874 < baseStart_629874 := by decide
  rcases family_descends (prefixWord ++ tailWord_629874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629981 : List Nat := [1, 4, 3, 2, 2, 2, 1, 6]
def baseStart_629981 : Nat := 118140960795 + 629981 * 2 ^ 59
def prefixEnd_629981 : Nat := 4983230072969 + 3 ^ 40 * 629981 * 2
def baseEnd_629981 : Nat := 47923415733363693354115

theorem tailTrace_629981 : CollatzResearch.WordTrace tailWord_629981 prefixEnd_629981 47923415733363693354115 := by
  unfold tailWord_629981
  simp only [CollatzResearch.WordTrace]
  refine ⟨22977294730693904034057797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15318196487129269356038531 22977294730693904034057797)
  ·
    refine ⟨4308242762005107006385837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22977294730693904034057797 4308242762005107006385837)
    ·
      refine ⟨1615591035751915127394689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4308242762005107006385837 1615591035751915127394689)
      ·
        refine ⟨1211693276813936345546017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1615591035751915127394689 1211693276813936345546017)
        ·
          refine ⟨908769957610452259159513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1211693276813936345546017 908769957610452259159513)
          ·
            refine ⟨681577468207839194369635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 908769957610452259159513 681577468207839194369635)
            ·
              refine ⟨1022366202311758791554453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681577468207839194369635 1022366202311758791554453)
              ·
                refine ⟨47923415733363693354115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1022366202311758791554453 47923415733363693354115)
                ·
                  rfl

theorem cell21_629981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 6].length) (baseStart_629981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_629981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_629981 prefixEnd_629981 := by exact prefixLift 629981
  have htrace : WordTrace (prefixWord ++ tailWord_629981) baseStart_629981 baseEnd_629981 := by
    simpa [prefixWord, tailWord_629981, baseEnd_629981] using wordTrace_append hprefix tailTrace_629981
  have hstable : (prefixWord ++ tailWord_629981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629981).length < 2 ^ (prefixWord ++ tailWord_629981).sum := by decide
  have hdescent : baseEnd_629981 < baseStart_629981 := by decide
  rcases family_descends (prefixWord ++ tailWord_629981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630012 : List Nat := [2, 2, 2, 1, 5, 1, 2, 3, 3]
def baseStart_630012 : Nat := 118140960795 + 630012 * 2 ^ 59
def prefixEnd_630012 : Nat := 4983230072969 + 3 ^ 40 * 630012 * 2
def baseEnd_630012 : Nat := 143777321822441915045615

theorem tailTrace_630012 : CollatzResearch.WordTrace tailWord_630012 prefixEnd_630012 143777321822441915045615 := by
  unfold tailWord_630012
  simp only [CollatzResearch.WordTrace]
  refine ⟨11489212696790798164218145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15318950262387730885624193 11489212696790798164218145)
  ·
    refine ⟨8616909522593098623163609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11489212696790798164218145 8616909522593098623163609)
    ·
      refine ⟨6462682141944823967372707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8616909522593098623163609 6462682141944823967372707)
      ·
        refine ⟨9694023212917235951059061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6462682141944823967372707 9694023212917235951059061)
        ·
          refine ⟨908814676210990870411787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9694023212917235951059061 908814676210990870411787)
          ·
            refine ⟨1363222014316486305617681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908814676210990870411787 1363222014316486305617681)
            ·
              refine ⟨1022416510737364729213261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1363222014316486305617681 1022416510737364729213261)
              ·
                refine ⟨383406191526511773454973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1022416510737364729213261 383406191526511773454973)
                ·
                  refine ⟨143777321822441915045615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 383406191526511773454973 143777321822441915045615)
                  ·
                    rfl

theorem cell21_630012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_630012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_630012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_630012 prefixEnd_630012 := by exact prefixLift 630012
  have htrace : WordTrace (prefixWord ++ tailWord_630012) baseStart_630012 baseEnd_630012 := by
    simpa [prefixWord, tailWord_630012, baseEnd_630012] using wordTrace_append hprefix tailTrace_630012
  have hstable : (prefixWord ++ tailWord_630012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630012).length < 2 ^ (prefixWord ++ tailWord_630012).sum := by decide
  have hdescent : baseEnd_630012 < baseStart_630012 := by decide
  rcases family_descends (prefixWord ++ tailWord_630012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630113 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 5]
def baseStart_630113 : Nat := 118140960795 + 630113 * 2 ^ 59
def prefixEnd_630113 : Nat := 4983230072969 + 3 ^ 40 * 630113 * 2
def baseEnd_630113 : Nat := 143800371398488183862075

theorem tailTrace_630113 : CollatzResearch.WordTrace tailWord_630113 prefixEnd_630113 143800371398488183862075 := by
  unfold tailWord_630113
  simp only [CollatzResearch.WordTrace]
  refine ⟨22982109166215690577862993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15321406110810460385241995 22982109166215690577862993)
  ·
    refine ⟨17236581874661767933397245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22982109166215690577862993 17236581874661767933397245)
    ·
      refine ⟨6463718202998162975023967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17236581874661767933397245 6463718202998162975023967)
      ·
        refine ⟨9695577304497244462535951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6463718202998162975023967 9695577304497244462535951)
        ·
          refine ⟨14543365956745866693803927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9695577304497244462535951 14543365956745866693803927)
          ·
            refine ⟨21815048935118800040705891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14543365956745866693803927 21815048935118800040705891)
            ·
              refine ⟨32722573402678200061058837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21815048935118800040705891 32722573402678200061058837)
              ·
                refine ⟨1533870628250540627862133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32722573402678200061058837 1533870628250540627862133)
                ·
                  refine ⟨143800371398488183862075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1533870628250540627862133 143800371398488183862075)
                  ·
                    rfl

theorem cell21_630113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_630113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_630113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_630113 prefixEnd_630113 := by exact prefixLift 630113
  have htrace : WordTrace (prefixWord ++ tailWord_630113) baseStart_630113 baseEnd_630113 := by
    simpa [prefixWord, tailWord_630113, baseEnd_630113] using wordTrace_append hprefix tailTrace_630113
  have hstable : (prefixWord ++ tailWord_630113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630113).length < 2 ^ (prefixWord ++ tailWord_630113).sum := by decide
  have hdescent : baseEnd_630113 < baseStart_630113 := by decide
  rcases family_descends (prefixWord ++ tailWord_630113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630147 : List Nat := [1, 1, 1, 3, 5, 2, 1, 4, 3]
def baseStart_630147 : Nat := 118140960795 + 630147 * 2 ^ 59
def prefixEnd_630147 : Nat := 4983230072969 + 3 ^ 40 * 630147 * 2
def baseEnd_630147 : Nat := 143808130661711680295339

theorem tailTrace_630147 : CollatzResearch.WordTrace tailWord_630147 prefixEnd_630147 143808130661711680295339 := by
  unfold tailWord_630147
  simp only [CollatzResearch.WordTrace]
  refine ⟨22983349248092514384600695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15322232832061676256400463 22983349248092514384600695)
  ·
    refine ⟨34475023872138771576901043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22983349248092514384600695 34475023872138771576901043)
    ·
      refine ⟨51712535808208157365351565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34475023872138771576901043 51712535808208157365351565)
      ·
        refine ⟨19392200928078059012006837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51712535808208157365351565 19392200928078059012006837)
        ·
          refine ⟨1818018837007318032375641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19392200928078059012006837 1818018837007318032375641)
          ·
            refine ⟨1363514127755488524281731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1818018837007318032375641 1363514127755488524281731)
            ·
              refine ⟨2045271191633232786422597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363514127755488524281731 2045271191633232786422597)
              ·
                refine ⟨383488348431231147454237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2045271191633232786422597 383488348431231147454237)
                ·
                  refine ⟨143808130661711680295339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 383488348431231147454237 143808130661711680295339)
                  ·
                    rfl

theorem cell21_630147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 3].length) (baseStart_630147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_630147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_630147 prefixEnd_630147 := by exact prefixLift 630147
  have htrace : WordTrace (prefixWord ++ tailWord_630147) baseStart_630147 baseEnd_630147 := by
    simpa [prefixWord, tailWord_630147, baseEnd_630147] using wordTrace_append hprefix tailTrace_630147
  have hstable : (prefixWord ++ tailWord_630147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630147).length < 2 ^ (prefixWord ++ tailWord_630147).sum := by decide
  have hdescent : baseEnd_630147 < baseStart_630147 := by decide
  rcases family_descends (prefixWord ++ tailWord_630147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630302 : List Nat := [4, 3, 3, 1, 2, 8]
def baseStart_630302 : Nat := 118140960795 + 630302 * 2 ^ 59
def prefixEnd_630302 : Nat := 4983230072969 + 3 ^ 40 * 630302 * 2
def baseEnd_630302 : Nat := 5327537176795031674507

theorem tailTrace_630302 : CollatzResearch.WordTrace tailWord_630302 prefixEnd_630302 5327537176795031674507 := by
  unfold tailWord_630302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2873625320316371982061645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15326001708353983904328773 2873625320316371982061645)
  ·
    refine ⟨1077609495118639493273117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2873625320316371982061645 1077609495118639493273117)
    ·
      refine ⟨404103560669489809977419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1077609495118639493273117 404103560669489809977419)
      ·
        refine ⟨606155341004234714966129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404103560669489809977419 606155341004234714966129)
        ·
          refine ⟨454616505753176036224597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 606155341004234714966129 454616505753176036224597)
          ·
            refine ⟨5327537176795031674507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 454616505753176036224597 5327537176795031674507)
            ·
              rfl

theorem cell21_630302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 8].length) (baseStart_630302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_630302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_630302 prefixEnd_630302 := by exact prefixLift 630302
  have htrace : WordTrace (prefixWord ++ tailWord_630302) baseStart_630302 baseEnd_630302 := by
    simpa [prefixWord, tailWord_630302, baseEnd_630302] using wordTrace_append hprefix tailTrace_630302
  have hstable : (prefixWord ++ tailWord_630302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630302).length < 2 ^ (prefixWord ++ tailWord_630302).sum := by decide
  have hdescent : baseEnd_630302 < baseStart_630302 := by decide
  rcases family_descends (prefixWord ++ tailWord_630302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630327 : List Nat := [1, 1, 3, 1, 2, 6, 1, 6]
def baseStart_630327 : Nat := 118140960795 + 630327 * 2 ^ 59
def prefixEnd_630327 : Nat := 4983230072969 + 3 ^ 40 * 630327 * 2
def baseEnd_630327 : Nat := 47949736371357122431657

theorem tailTrace_630327 : CollatzResearch.WordTrace tailWord_630327 prefixEnd_630327 47949736371357122431657 := by
  unfold tailWord_630327
  simp only [CollatzResearch.WordTrace]
  refine ⟨22989914387440405126153235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15326609591626936750768823 22989914387440405126153235)
  ·
    refine ⟨34484871581160607689229853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22989914387440405126153235 34484871581160607689229853)
    ·
      refine ⟨12931826842935227883461195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34484871581160607689229853 12931826842935227883461195)
      ·
        refine ⟨19397740264402841825191793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12931826842935227883461195 19397740264402841825191793)
        ·
          refine ⟨14548305198302131368893845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19397740264402841825191793 14548305198302131368893845)
          ·
            refine ⟨681951806170412407916899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14548305198302131368893845 681951806170412407916899)
            ·
              refine ⟨1022927709255618611875349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681951806170412407916899 1022927709255618611875349)
              ·
                refine ⟨47949736371357122431657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1022927709255618611875349 47949736371357122431657)
                ·
                  rfl

theorem cell21_630327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 6].length) (baseStart_630327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_630327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_630327 prefixEnd_630327 := by exact prefixLift 630327
  have htrace : WordTrace (prefixWord ++ tailWord_630327) baseStart_630327 baseEnd_630327 := by
    simpa [prefixWord, tailWord_630327, baseEnd_630327] using wordTrace_append hprefix tailTrace_630327
  have hstable : (prefixWord ++ tailWord_630327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630327).length < 2 ^ (prefixWord ++ tailWord_630327).sum := by decide
  have hdescent : baseEnd_630327 < baseStart_630327 := by decide
  rcases family_descends (prefixWord ++ tailWord_630327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630341 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 5]
def baseStart_630341 : Nat := 118140960795 + 630341 * 2 ^ 59
def prefixEnd_630341 : Nat := 4983230072969 + 3 ^ 40 * 630341 * 2
def baseEnd_630341 : Nat := 143852404104810454061609

theorem tailTrace_630341 : CollatzResearch.WordTrace tailWord_630341 prefixEnd_630341 143852404104810454061609 := by
  unfold tailWord_630341
  simp only [CollatzResearch.WordTrace]
  refine ⟨22990425009389685517162877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15326950006259790344775251 22990425009389685517162877)
  ·
    refine ⟨8621409378521132068936079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22990425009389685517162877 8621409378521132068936079)
    ·
      refine ⟨12932114067781698103404119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8621409378521132068936079 12932114067781698103404119)
      ·
        refine ⟨19398171101672547155106179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12932114067781698103404119 19398171101672547155106179)
        ·
          refine ⟨29097256652508820732659269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19398171101672547155106179 29097256652508820732659269)
          ·
            refine ⟨5455735622345403887373613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29097256652508820732659269 5455735622345403887373613)
            ·
              refine ⟨2045900858379526457765105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5455735622345403887373613 2045900858379526457765105)
              ·
                refine ⟨1534425643784644843323829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2045900858379526457765105 1534425643784644843323829)
                ·
                  refine ⟨143852404104810454061609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1534425643784644843323829 143852404104810454061609)
                  ·
                    rfl

theorem cell21_630341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_630341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_630341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_630341 prefixEnd_630341 := by exact prefixLift 630341
  have htrace : WordTrace (prefixWord ++ tailWord_630341) baseStart_630341 baseEnd_630341 := by
    simpa [prefixWord, tailWord_630341, baseEnd_630341] using wordTrace_append hprefix tailTrace_630341
  have hstable : (prefixWord ++ tailWord_630341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630341).length < 2 ^ (prefixWord ++ tailWord_630341).sum := by decide
  have hdescent : baseEnd_630341 < baseStart_630341 := by decide
  rcases family_descends (prefixWord ++ tailWord_630341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630372 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 6]
def baseStart_630372 : Nat := 118140960795 + 630372 * 2 ^ 59
def prefixEnd_630372 : Nat := 4983230072969 + 3 ^ 40 * 630372 * 2
def baseEnd_630372 : Nat := 143859478727161289044879

theorem tailTrace_630372 : CollatzResearch.WordTrace tailWord_630372 prefixEnd_630372 143859478727161289044879 := by
  unfold tailWord_630372
  simp only [CollatzResearch.WordTrace]
  refine ⟨11495777836138688905770685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15327703781518251874360913 11495777836138688905770685)
  ·
    refine ⟨4310916688552008339664007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11495777836138688905770685 4310916688552008339664007)
    ·
      refine ⟨6466375032828012509496011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4310916688552008339664007 6466375032828012509496011)
      ·
        refine ⟨9699562549242018764244017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6466375032828012509496011 9699562549242018764244017)
        ·
          refine ⟨7274671911931514073183013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9699562549242018764244017 7274671911931514073183013)
          ·
            refine ⟨1364000983487158888721815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7274671911931514073183013 1364000983487158888721815)
            ·
              refine ⟨2046001475230738333082723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1364000983487158888721815 2046001475230738333082723)
              ·
                refine ⟨3069002212846107499624085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2046001475230738333082723 3069002212846107499624085)
                ·
                  refine ⟨143859478727161289044879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3069002212846107499624085 143859478727161289044879)
                  ·
                    rfl

theorem cell21_630372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_630372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_630372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_630372 prefixEnd_630372 := by exact prefixLift 630372
  have htrace : WordTrace (prefixWord ++ tailWord_630372) baseStart_630372 baseEnd_630372 := by
    simpa [prefixWord, tailWord_630372, baseEnd_630372] using wordTrace_append hprefix tailTrace_630372
  have hstable : (prefixWord ++ tailWord_630372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630372).length < 2 ^ (prefixWord ++ tailWord_630372).sum := by decide
  have hdescent : baseEnd_630372 < baseStart_630372 := by decide
  rcases family_descends (prefixWord ++ tailWord_630372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630420 : List Nat := [2, 4, 2, 2, 2, 2, 7]
def baseStart_630420 : Nat := 118140960795 + 630420 * 2 ^ 59
def prefixEnd_630420 : Nat := 4983230072969 + 3 ^ 40 * 630420 * 2
def baseEnd_630420 : Nat := 15985603664569319138309

theorem tailTrace_630420 : CollatzResearch.WordTrace tailWord_630420 prefixEnd_630420 15985603664569319138309 := by
  unfold tailWord_630420
  simp only [CollatzResearch.WordTrace]
  refine ⟨11496653188051741004644357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15328870917402321339525809 11496653188051741004644357)
  ·
    refine ⟨2155622472759701438370817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11496653188051741004644357 2155622472759701438370817)
    ·
      refine ⟨1616716854569776078778113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2155622472759701438370817 1616716854569776078778113)
      ·
        refine ⟨1212537640927332059083585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1616716854569776078778113 1212537640927332059083585)
        ·
          refine ⟨909403230695499044312689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1212537640927332059083585 909403230695499044312689)
          ·
            refine ⟨682052423021624283234517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 909403230695499044312689 682052423021624283234517)
            ·
              refine ⟨15985603664569319138309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 682052423021624283234517 15985603664569319138309)
              ·
                rfl

theorem cell21_630420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 7].length) (baseStart_630420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_630420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_630420 prefixEnd_630420 := by exact prefixLift 630420
  have htrace : WordTrace (prefixWord ++ tailWord_630420) baseStart_630420 baseEnd_630420 := by
    simpa [prefixWord, tailWord_630420, baseEnd_630420] using wordTrace_append hprefix tailTrace_630420
  have hstable : (prefixWord ++ tailWord_630420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630420).length < 2 ^ (prefixWord ++ tailWord_630420).sum := by decide
  have hdescent : baseEnd_630420 < baseStart_630420 := by decide
  rcases family_descends (prefixWord ++ tailWord_630420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630538 : List Nat := [3, 1, 2, 2, 1, 4, 8]
def baseStart_630538 : Nat := 118140960795 + 630538 * 2 ^ 59
def prefixEnd_630538 : Nat := 4983230072969 + 3 ^ 40 * 630538 * 2
def baseEnd_630538 : Nat := 15988595798753543253097

theorem tailTrace_630538 : CollatzResearch.WordTrace tailWord_630538 prefixEnd_630538 15988595798753543253097 := by
  unfold tailWord_630538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5749402547418997040521067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15331740126450658774722845 5749402547418997040521067)
  ·
    refine ⟨8624103821128495560781601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5749402547418997040521067 8624103821128495560781601)
    ·
      refine ⟨6468077865846371670586201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8624103821128495560781601 6468077865846371670586201)
      ·
        refine ⟨4851058399384778752939651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6468077865846371670586201 4851058399384778752939651)
        ·
          refine ⟨7276587599077168129409477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4851058399384778752939651 7276587599077168129409477)
          ·
            refine ⟨1364360174826969024264277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7276587599077168129409477 1364360174826969024264277)
            ·
              refine ⟨15988595798753543253097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1364360174826969024264277 15988595798753543253097)
              ·
                rfl

theorem cell21_630538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 8].length) (baseStart_630538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_630538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_630538 prefixEnd_630538 := by exact prefixLift 630538
  have htrace : WordTrace (prefixWord ++ tailWord_630538) baseStart_630538 baseEnd_630538 := by
    simpa [prefixWord, tailWord_630538, baseEnd_630538] using wordTrace_append hprefix tailTrace_630538
  have hstable : (prefixWord ++ tailWord_630538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630538).length < 2 ^ (prefixWord ++ tailWord_630538).sum := by decide
  have hdescent : baseEnd_630538 < baseStart_630538 := by decide
  rcases family_descends (prefixWord ++ tailWord_630538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630755 : List Nat := [1, 1, 1, 6, 1, 4, 1, 3, 3]
def baseStart_630755 : Nat := 118140960795 + 630755 * 2 ^ 59
def prefixEnd_630755 : Nat := 4983230072969 + 3 ^ 40 * 630755 * 2
def baseEnd_630755 : Nat := 143946884545237734160763

theorem tailTrace_630755 : CollatzResearch.WordTrace tailWord_630755 prefixEnd_630755 143946884545237734160763 := by
  unfold tailWord_630755
  simp only [CollatzResearch.WordTrace]
  refine ⟨23005524829889834222733719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15337016553259889481822479 23005524829889834222733719)
  ·
    refine ⟨34508287244834751334100579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23005524829889834222733719 34508287244834751334100579)
    ·
      refine ⟨51762430867252127001150869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34508287244834751334100579 51762430867252127001150869)
      ·
        refine ⟨2426363946902443453178947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51762430867252127001150869 2426363946902443453178947)
        ·
          refine ⟨3639545920353665179768421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2426363946902443453178947 3639545920353665179768421)
          ·
            refine ⟨682414860066312221206579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3639545920353665179768421 682414860066312221206579)
            ·
              refine ⟨1023622290099468331809869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682414860066312221206579 1023622290099468331809869)
              ·
                refine ⟨383858358787300624428701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1023622290099468331809869 383858358787300624428701)
                ·
                  refine ⟨143946884545237734160763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 383858358787300624428701 143946884545237734160763)
                  ·
                    rfl

theorem cell21_630755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 3].length) (baseStart_630755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_630755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_630755 prefixEnd_630755 := by exact prefixLift 630755
  have htrace : WordTrace (prefixWord ++ tailWord_630755) baseStart_630755 baseEnd_630755 := by
    simpa [prefixWord, tailWord_630755, baseEnd_630755] using wordTrace_append hprefix tailTrace_630755
  have hstable : (prefixWord ++ tailWord_630755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630755).length < 2 ^ (prefixWord ++ tailWord_630755).sum := by decide
  have hdescent : baseEnd_630755 < baseStart_630755 := by decide
  rcases family_descends (prefixWord ++ tailWord_630755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630766 : List Nat := [4, 1, 2, 1, 3, 1, 9]
def baseStart_630766 : Nat := 118140960795 + 630766 * 2 ^ 59
def prefixEnd_630766 : Nat := 4983230072969 + 3 ^ 40 * 630766 * 2
def baseEnd_630766 : Nat := 15994377210567128830823

theorem tailTrace_630766 : CollatzResearch.WordTrace tailWord_630766 prefixEnd_630766 15994377210567128830823 := by
  unfold tailWord_630766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2875740754106247887673019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15337284021899988734256101 2875740754106247887673019)
  ·
    refine ⟨4313611131159371831509529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2875740754106247887673019 4313611131159371831509529)
    ·
      refine ⟨3235208348369528873632147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4313611131159371831509529 3235208348369528873632147)
      ·
        refine ⟨4852812522554293310448221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3235208348369528873632147 4852812522554293310448221)
        ·
          refine ⟨1819804695957859991418083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4852812522554293310448221 1819804695957859991418083)
          ·
            refine ⟨2729707043936789987127125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819804695957859991418083 2729707043936789987127125)
            ·
              refine ⟨15994377210567128830823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2729707043936789987127125 15994377210567128830823)
              ·
                rfl

theorem cell21_630766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 9].length) (baseStart_630766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_630766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_630766 prefixEnd_630766 := by exact prefixLift 630766
  have htrace : WordTrace (prefixWord ++ tailWord_630766) baseStart_630766 baseEnd_630766 := by
    simpa [prefixWord, tailWord_630766, baseEnd_630766] using wordTrace_append hprefix tailTrace_630766
  have hstable : (prefixWord ++ tailWord_630766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630766).length < 2 ^ (prefixWord ++ tailWord_630766).sum := by decide
  have hdescent : baseEnd_630766 < baseStart_630766 := by decide
  rcases family_descends (prefixWord ++ tailWord_630766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630887 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 6]
def baseStart_630887 : Nat := 118140960795 + 630887 * 2 ^ 59
def prefixEnd_630887 : Nat := 4983230072969 + 3 ^ 40 * 630887 * 2
def baseEnd_630887 : Nat := 143977008743634837960493

theorem tailTrace_630887 : CollatzResearch.WordTrace tailWord_630887 prefixEnd_630887 143977008743634837960493 := by
  unfold tailWord_630887
  simp only [CollatzResearch.WordTrace]
  refine ⟨23010339265411620766538915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15340226176941080511025943 23010339265411620766538915)
  ·
    refine ⟨34515508898117431149808373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23010339265411620766538915 34515508898117431149808373)
    ·
      refine ⟨3235828959198509170294535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34515508898117431149808373 3235828959198509170294535)
      ·
        refine ⟨4853743438797763755441803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3235828959198509170294535 4853743438797763755441803)
        ·
          refine ⟨7280615158196645633162705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4853743438797763755441803 7280615158196645633162705)
          ·
            refine ⟨5460461368647484224872029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7280615158196645633162705 5460461368647484224872029)
            ·
              refine ⟨2047673013242806584327011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5460461368647484224872029 2047673013242806584327011)
              ·
                refine ⟨3071509519864209876490517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2047673013242806584327011 3071509519864209876490517)
                ·
                  refine ⟨143977008743634837960493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3071509519864209876490517 143977008743634837960493)
                  ·
                    rfl

theorem cell21_630887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 6].length) (baseStart_630887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_630887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_630887 prefixEnd_630887 := by exact prefixLift 630887
  have htrace : WordTrace (prefixWord ++ tailWord_630887) baseStart_630887 baseEnd_630887 := by
    simpa [prefixWord, tailWord_630887, baseEnd_630887] using wordTrace_append hprefix tailTrace_630887
  have hstable : (prefixWord ++ tailWord_630887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630887).length < 2 ^ (prefixWord ++ tailWord_630887).sum := by decide
  have hdescent : baseEnd_630887 < baseStart_630887 := by decide
  rcases family_descends (prefixWord ++ tailWord_630887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630890 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 5]
def baseStart_630890 : Nat := 118140960795 + 630890 * 2 ^ 59
def prefixEnd_630890 : Nat := 4983230072969 + 3 ^ 40 * 630890 * 2
def baseEnd_630890 : Nat := 143977693384507499410487

theorem tailTrace_630890 : CollatzResearch.WordTrace tailWord_630890 prefixEnd_630890 143977693384507499410487 := by
  unfold tailWord_630890
  simp only [CollatzResearch.WordTrace]
  refine ⟨5752612171100188069724531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15340299122933834852598749 5752612171100188069724531)
  ·
    refine ⟨8628918256650282104586797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5752612171100188069724531 8628918256650282104586797)
    ·
      refine ⟨3235844346243855789220049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8628918256650282104586797 3235844346243855789220049)
      ·
        refine ⟨2426883259682891841915037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3235844346243855789220049 2426883259682891841915037)
        ·
          refine ⟨910081222381084440718139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2426883259682891841915037 910081222381084440718139)
          ·
            refine ⟨1365121833571626661077209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910081222381084440718139 1365121833571626661077209)
            ·
              refine ⟨1023841375178719995807907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1365121833571626661077209 1023841375178719995807907)
              ·
                refine ⟨1535762062768079993711861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023841375178719995807907 1535762062768079993711861)
                ·
                  refine ⟨143977693384507499410487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1535762062768079993711861 143977693384507499410487)
                  ·
                    rfl

theorem cell21_630890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_630890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_630890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_630890 prefixEnd_630890 := by exact prefixLift 630890
  have htrace : WordTrace (prefixWord ++ tailWord_630890) baseStart_630890 baseEnd_630890 := by
    simpa [prefixWord, tailWord_630890, baseEnd_630890] using wordTrace_append hprefix tailTrace_630890
  have hstable : (prefixWord ++ tailWord_630890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630890).length < 2 ^ (prefixWord ++ tailWord_630890).sum := by decide
  have hdescent : baseEnd_630890 < baseStart_630890 := by decide
  rcases family_descends (prefixWord ++ tailWord_630890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630935 : List Nat := [1, 1, 3, 3, 5, 1, 7]
def baseStart_630935 : Nat := 118140960795 + 630935 * 2 ^ 59
def prefixEnd_630935 : Nat := 4983230072969 + 3 ^ 40 * 630935 * 2
def baseEnd_630935 : Nat := 15998662555288602351155

theorem tailTrace_630935 : CollatzResearch.WordTrace tailWord_630935 prefixEnd_630935 15998662555288602351155 := by
  unfold tailWord_630935
  simp only [CollatzResearch.WordTrace]
  refine ⟨23012089969237724964286259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15341393312825149976190839 23012089969237724964286259)
  ·
    refine ⟨34518134953856587446429389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23012089969237724964286259 34518134953856587446429389)
    ·
      refine ⟨12944300607696220292411021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34518134953856587446429389 12944300607696220292411021)
      ·
        refine ⟨4854112727886082609654133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12944300607696220292411021 4854112727886082609654133)
        ·
          refine ⟨455073068239320244655075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4854112727886082609654133 455073068239320244655075)
          ·
            refine ⟨682609602358980366982613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455073068239320244655075 682609602358980366982613)
            ·
              refine ⟨15998662555288602351155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 682609602358980366982613 15998662555288602351155)
              ·
                rfl

theorem cell21_630935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 7].length) (baseStart_630935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_630935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_630935 prefixEnd_630935 := by exact prefixLift 630935
  have htrace : WordTrace (prefixWord ++ tailWord_630935) baseStart_630935 baseEnd_630935 := by
    simpa [prefixWord, tailWord_630935, baseEnd_630935] using wordTrace_append hprefix tailTrace_630935
  have hstable : (prefixWord ++ tailWord_630935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630935).length < 2 ^ (prefixWord ++ tailWord_630935).sum := by decide
  have hdescent : baseEnd_630935 < baseStart_630935 := by decide
  rcases family_descends (prefixWord ++ tailWord_630935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630997 : List Nat := [1, 3, 2, 4, 2, 1, 2, 2, 4]
def baseStart_630997 : Nat := 118140960795 + 630997 * 2 ^ 59
def prefixEnd_630997 : Nat := 4983230072969 + 3 ^ 40 * 630997 * 2
def baseEnd_630997 : Nat := 144002112242299091126935

theorem tailTrace_630997 : CollatzResearch.WordTrace tailWord_630997 prefixEnd_630997 144002112242299091126935 := by
  unfold tailWord_630997
  simp only [CollatzResearch.WordTrace]
  refine ⟨23014351295013109553043245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15342900863342073035362163 23014351295013109553043245)
  ·
    refine ⟨8630381735629916082391217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23014351295013109553043245 8630381735629916082391217)
    ·
      refine ⟨6472786301722437061793413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8630381735629916082391217 6472786301722437061793413)
      ·
        refine ⟨1213647431572956949086265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6472786301722437061793413 1213647431572956949086265)
        ·
          refine ⟨910235573679717711814699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1213647431572956949086265 910235573679717711814699)
          ·
            refine ⟨1365353360519576567722049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910235573679717711814699 1365353360519576567722049)
            ·
              refine ⟨1024015020389682425791537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1365353360519576567722049 1024015020389682425791537)
              ·
                refine ⟨768011265292261819343653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1024015020389682425791537 768011265292261819343653)
                ·
                  refine ⟨144002112242299091126935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 768011265292261819343653 144002112242299091126935)
                  ·
                    rfl

theorem cell21_630997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_630997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_630997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_630997 prefixEnd_630997 := by exact prefixLift 630997
  have htrace : WordTrace (prefixWord ++ tailWord_630997) baseStart_630997 baseEnd_630997 := by
    simpa [prefixWord, tailWord_630997, baseEnd_630997] using wordTrace_append hprefix tailTrace_630997
  have hstable : (prefixWord ++ tailWord_630997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630997).length < 2 ^ (prefixWord ++ tailWord_630997).sum := by decide
  have hdescent : baseEnd_630997 < baseStart_630997 := by decide
  rcases family_descends (prefixWord ++ tailWord_630997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631008 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 5]
def baseStart_631008 : Nat := 118140960795 + 631008 * 2 ^ 59
def prefixEnd_631008 : Nat := 4983230072969 + 3 ^ 40 * 631008 * 2
def baseEnd_631008 : Nat := 144004622592165516443579

theorem tailTrace_631008 : CollatzResearch.WordTrace tailWord_631008 prefixEnd_631008 144004622592165516443579 := by
  unfold tailWord_631008
  simp only [CollatzResearch.WordTrace]
  refine ⟨11507376248986629215846839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15343168331982172287795785 11507376248986629215846839)
  ·
    refine ⟨17261064373479943823770259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11507376248986629215846839 17261064373479943823770259)
    ·
      refine ⟨25891596560219915735655389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17261064373479943823770259 25891596560219915735655389)
      ·
        refine ⟨9709348710082468400870771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25891596560219915735655389 9709348710082468400870771)
        ·
          refine ⟨14564023065123702601306157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9709348710082468400870771 14564023065123702601306157)
          ·
            refine ⟨5461508649421388475489809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14564023065123702601306157 5461508649421388475489809)
            ·
              refine ⟨4096131487066041356617357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5461508649421388475489809 4096131487066041356617357)
              ·
                refine ⟨1536049307649765508731509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4096131487066041356617357 1536049307649765508731509)
                ·
                  refine ⟨144004622592165516443579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1536049307649765508731509 144004622592165516443579)
                  ·
                    rfl

theorem cell21_631008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_631008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_631008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_631008 prefixEnd_631008 := by exact prefixLift 631008
  have htrace : WordTrace (prefixWord ++ tailWord_631008) baseStart_631008 baseEnd_631008 := by
    simpa [prefixWord, tailWord_631008, baseEnd_631008] using wordTrace_append hprefix tailTrace_631008
  have hstable : (prefixWord ++ tailWord_631008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631008).length < 2 ^ (prefixWord ++ tailWord_631008).sum := by decide
  have hdescent : baseEnd_631008 < baseStart_631008 := by decide
  rcases family_descends (prefixWord ++ tailWord_631008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631084 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 5]
def baseStart_631084 : Nat := 118140960795 + 631084 * 2 ^ 59
def prefixEnd_631084 : Nat := 4983230072969 + 3 ^ 40 * 631084 * 2
def baseEnd_631084 : Nat := 144021966827606273176757

theorem tailTrace_631084 : CollatzResearch.WordTrace tailWord_631084 prefixEnd_631084 144021966827606273176757 := by
  unfold tailWord_631084
  simp only [CollatzResearch.WordTrace]
  refine ⟨11508762222848961705730153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15345016297131948940973537 11508762222848961705730153)
  ·
    refine ⟨8631571667136721279297615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11508762222848961705730153 8631571667136721279297615)
    ·
      refine ⟨12947357500705081918946423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8631571667136721279297615 12947357500705081918946423)
      ·
        refine ⟨19421036251057622878419635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12947357500705081918946423 19421036251057622878419635)
        ·
          refine ⟨29131554376586434317629453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19421036251057622878419635 29131554376586434317629453)
          ·
            refine ⟨10924332891219912869111045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29131554376586434317629453 10924332891219912869111045)
            ·
              refine ⟨2048312417103733662958321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10924332891219912869111045 2048312417103733662958321)
              ·
                refine ⟨1536234312827800247218741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2048312417103733662958321 1536234312827800247218741)
                ·
                  refine ⟨144021966827606273176757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1536234312827800247218741 144021966827606273176757)
                  ·
                    rfl

theorem cell21_631084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_631084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_631084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_631084 prefixEnd_631084 := by exact prefixLift 631084
  have htrace : WordTrace (prefixWord ++ tailWord_631084) baseStart_631084 baseEnd_631084 := by
    simpa [prefixWord, tailWord_631084, baseEnd_631084] using wordTrace_append hprefix tailTrace_631084
  have hstable : (prefixWord ++ tailWord_631084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631084).length < 2 ^ (prefixWord ++ tailWord_631084).sum := by decide
  have hdescent : baseEnd_631084 < baseStart_631084 := by decide
  rcases family_descends (prefixWord ++ tailWord_631084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631146 : List Nat := [3, 1, 3, 3, 1, 1, 2, 7]
def baseStart_631146 : Nat := 118140960795 + 631146 * 2 ^ 59
def prefixEnd_631146 : Nat := 4983230072969 + 3 ^ 40 * 631146 * 2
def baseEnd_631146 : Nat := 48012038690769314381099

theorem tailTrace_631146 : CollatzResearch.WordTrace tailWord_631146 prefixEnd_631146 48012038690769314381099 := by
  unfold tailWord_631146
  simp only [CollatzResearch.WordTrace]
  refine ⟨5754946442868327000054323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15346523847648872000144861 5754946442868327000054323)
  ·
    refine ⟨8632419664302490500081485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5754946442868327000054323 8632419664302490500081485)
    ·
      refine ⟨3237157374113433937530557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8632419664302490500081485 3237157374113433937530557)
      ·
        refine ⟨1213934015292537726573959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3237157374113433937530557 1213934015292537726573959)
        ·
          refine ⟨1820901022938806589860939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213934015292537726573959 1820901022938806589860939)
          ·
            refine ⟨2731351534408209884791409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1820901022938806589860939 2731351534408209884791409)
            ·
              refine ⟨2048513650806157413593557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2731351534408209884791409 2048513650806157413593557)
              ·
                refine ⟨48012038690769314381099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2048513650806157413593557 48012038690769314381099)
                ·
                  rfl

theorem cell21_631146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_631146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_631146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_631146 prefixEnd_631146 := by exact prefixLift 631146
  have htrace : WordTrace (prefixWord ++ tailWord_631146) baseStart_631146 baseEnd_631146 := by
    simpa [prefixWord, tailWord_631146, baseEnd_631146] using wordTrace_append hprefix tailTrace_631146
  have hstable : (prefixWord ++ tailWord_631146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631146).length < 2 ^ (prefixWord ++ tailWord_631146).sum := by decide
  have hdescent : baseEnd_631146 < baseStart_631146 := by decide
  rcases family_descends (prefixWord ++ tailWord_631146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631191 : List Nat := [1, 1, 3, 3, 1, 1, 4, 3, 4]
def baseStart_631191 : Nat := 118140960795 + 631191 * 2 ^ 59
def prefixEnd_631191 : Nat := 4983230072969 + 3 ^ 40 * 631191 * 2
def baseEnd_631191 : Nat := 144046385685397864893205

theorem tailTrace_631191 : CollatzResearch.WordTrace tailWord_631191 prefixEnd_631191 144046385685397864893205 := by
  unfold tailWord_631191
  simp only [CollatzResearch.WordTrace]
  refine ⟨23021427056310280685605427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15347618037540187123736951 23021427056310280685605427)
  ·
    refine ⟨34532140584465421028408141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23021427056310280685605427 34532140584465421028408141)
    ·
      refine ⟨12949552719174532885653053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34532140584465421028408141 12949552719174532885653053)
      ·
        refine ⟨4856082269690449832119895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12949552719174532885653053 4856082269690449832119895)
        ·
          refine ⟨7284123404535674748179843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4856082269690449832119895 7284123404535674748179843)
          ·
            refine ⟨10926185106803512122269765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7284123404535674748179843 10926185106803512122269765)
            ·
              refine ⟨2048659707525658522925581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10926185106803512122269765 2048659707525658522925581)
              ·
                refine ⟨768247390322121946097093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2048659707525658522925581 768247390322121946097093)
                ·
                  refine ⟨144046385685397864893205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 768247390322121946097093 144046385685397864893205)
                  ·
                    rfl

theorem cell21_631191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 4].length) (baseStart_631191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_631191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_631191 prefixEnd_631191 := by exact prefixLift 631191
  have htrace : WordTrace (prefixWord ++ tailWord_631191) baseStart_631191 baseEnd_631191 := by
    simpa [prefixWord, tailWord_631191, baseEnd_631191] using wordTrace_append hprefix tailTrace_631191
  have hstable : (prefixWord ++ tailWord_631191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631191).length < 2 ^ (prefixWord ++ tailWord_631191).sum := by decide
  have hdescent : baseEnd_631191 < baseStart_631191 := by decide
  rcases family_descends (prefixWord ++ tailWord_631191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631329 : List Nat := [1, 2, 3, 2, 2, 1, 2, 5, 3]
def baseStart_631329 : Nat := 118140960795 + 631329 * 2 ^ 59
def prefixEnd_631329 : Nat := 4983230072969 + 3 ^ 40 * 631329 * 2
def baseEnd_631329 : Nat := 144077879165540291592923

theorem tailTrace_631329 : CollatzResearch.WordTrace tailWord_631329 prefixEnd_631329 144077879165540291592923 := by
  unfold tailWord_631329
  simp only [CollatzResearch.WordTrace]
  refine ⟨23026460329810330254129041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15350973553206886836086027 23026460329810330254129041)
  ·
    refine ⟨17269845247357747690596781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23026460329810330254129041 17269845247357747690596781)
    ·
      refine ⟨6476191967759155383973793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17269845247357747690596781 6476191967759155383973793)
      ·
        refine ⟨4857143975819366537980345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6476191967759155383973793 4857143975819366537980345)
        ·
          refine ⟨3642857981864524903485259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4857143975819366537980345 3642857981864524903485259)
          ·
            refine ⟨5464286972796787355227889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3642857981864524903485259 5464286972796787355227889)
            ·
              refine ⟨4098215229597590516420917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5464286972796787355227889 4098215229597590516420917)
              ·
                refine ⟨384207677774774110914461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4098215229597590516420917 384207677774774110914461)
                ·
                  refine ⟨144077879165540291592923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 384207677774774110914461 144077879165540291592923)
                  ·
                    rfl

theorem cell21_631329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 3].length) (baseStart_631329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_631329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_631329 prefixEnd_631329 := by exact prefixLift 631329
  have htrace : WordTrace (prefixWord ++ tailWord_631329) baseStart_631329 baseEnd_631329 := by
    simpa [prefixWord, tailWord_631329, baseEnd_631329] using wordTrace_append hprefix tailTrace_631329
  have hstable : (prefixWord ++ tailWord_631329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631329).length < 2 ^ (prefixWord ++ tailWord_631329).sum := by decide
  have hdescent : baseEnd_631329 < baseStart_631329 := by decide
  rcases family_descends (prefixWord ++ tailWord_631329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631346 : List Nat := [3, 2, 1, 1, 2, 1, 6, 2, 3]
def baseStart_631346 : Nat := 118140960795 + 631346 * 2 ^ 59
def prefixEnd_631346 : Nat := 4983230072969 + 3 ^ 40 * 631346 * 2
def baseEnd_631346 : Nat := 144081758797152039809555

theorem tailTrace_631346 : CollatzResearch.WordTrace tailWord_631346 prefixEnd_631346 144081758797152039809555 := by
  unfold tailWord_631346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5756770092687185539374473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15351386913832494771665261 5756770092687185539374473)
  ·
    refine ⟨4317577569515389154530855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5756770092687185539374473 4317577569515389154530855)
    ·
      refine ⟨6476366354273083731796283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4317577569515389154530855 6476366354273083731796283)
      ·
        refine ⟨9714549531409625597694425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6476366354273083731796283 9714549531409625597694425)
        ·
          refine ⟨7285912148557219198270819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9714549531409625597694425 7285912148557219198270819)
          ·
            refine ⟨10928868222835828797406229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7285912148557219198270819 10928868222835828797406229)
            ·
              refine ⟨512290697945429474878417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10928868222835828797406229 512290697945429474878417)
              ·
                refine ⟨384218023459072106158813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 512290697945429474878417 384218023459072106158813)
                ·
                  refine ⟨144081758797152039809555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 384218023459072106158813 144081758797152039809555)
                  ·
                    rfl

theorem cell21_631346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_631346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_631346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_631346 prefixEnd_631346 := by exact prefixLift 631346
  have htrace : WordTrace (prefixWord ++ tailWord_631346) baseStart_631346 baseEnd_631346 := by
    simpa [prefixWord, tailWord_631346, baseEnd_631346] using wordTrace_append hprefix tailTrace_631346
  have hstable : (prefixWord ++ tailWord_631346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631346).length < 2 ^ (prefixWord ++ tailWord_631346).sum := by decide
  have hdescent : baseEnd_631346 < baseStart_631346 := by decide
  rcases family_descends (prefixWord ++ tailWord_631346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631371 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 7]
def baseStart_631371 : Nat := 118140960795 + 631371 * 2 ^ 59
def prefixEnd_631371 : Nat := 4983230072969 + 3 ^ 40 * 631371 * 2
def baseEnd_631371 : Nat := 144087464137757551892837

theorem tailTrace_631371 : CollatzResearch.WordTrace tailWord_631371 prefixEnd_631371 144087464137757551892837 := by
  unfold tailWord_631371
  simp only [CollatzResearch.WordTrace]
  refine ⟨23027992195658171427157967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15351994797105447618105311 23027992195658171427157967)
  ·
    refine ⟨34541988293487257140736951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23027992195658171427157967 34541988293487257140736951)
    ·
      refine ⟨51812982440230885711105427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34541988293487257140736951 51812982440230885711105427)
      ·
        refine ⟨77719473660346328566658141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51812982440230885711105427 77719473660346328566658141)
        ·
          refine ⟨29144802622629873212496803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77719473660346328566658141 29144802622629873212496803)
          ·
            refine ⟨43717203933944809818745205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29144802622629873212496803 43717203933944809818745205)
            ·
              refine ⟨4098487868807325920507363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43717203933944809818745205 4098487868807325920507363)
              ·
                refine ⟨6147731803210988880761045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4098487868807325920507363 6147731803210988880761045)
                ·
                  refine ⟨144087464137757551892837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6147731803210988880761045 144087464137757551892837)
                  ·
                    rfl

theorem cell21_631371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 7].length) (baseStart_631371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_631371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_631371 prefixEnd_631371 := by exact prefixLift 631371
  have htrace : WordTrace (prefixWord ++ tailWord_631371) baseStart_631371 baseEnd_631371 := by
    simpa [prefixWord, tailWord_631371, baseEnd_631371] using wordTrace_append hprefix tailTrace_631371
  have hstable : (prefixWord ++ tailWord_631371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631371).length < 2 ^ (prefixWord ++ tailWord_631371).sum := by decide
  have hdescent : baseEnd_631371 < baseStart_631371 := by decide
  rcases family_descends (prefixWord ++ tailWord_631371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631394 : List Nat := [3, 3, 2, 3, 1, 2, 1, 2, 4]
def baseStart_631394 : Nat := 118140960795 + 631394 * 2 ^ 59
def prefixEnd_631394 : Nat := 4983230072969 + 3 ^ 40 * 631394 * 2
def baseEnd_631394 : Nat := 144092713051114623009457

theorem tailTrace_631394 : CollatzResearch.WordTrace tailWord_631394 prefixEnd_631394 144092713051114623009457 := by
  unfold tailWord_631394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5757207768643711588811309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15352554049716564236830157 5757207768643711588811309)
  ·
    refine ⟨2158952913241391845804241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5757207768643711588811309 2158952913241391845804241)
    ·
      refine ⟨1619214684931043884353181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2158952913241391845804241 1619214684931043884353181)
      ·
        refine ⟨607205506849141456632443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1619214684931043884353181 607205506849141456632443)
        ·
          refine ⟨910808260273712184948665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607205506849141456632443 910808260273712184948665)
          ·
            refine ⟨683106195205284138711499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 910808260273712184948665 683106195205284138711499)
            ·
              refine ⟨1024659292807926208067249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683106195205284138711499 1024659292807926208067249)
              ·
                refine ⟨768494469605944656050437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1024659292807926208067249 768494469605944656050437)
                ·
                  refine ⟨144092713051114623009457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 768494469605944656050437 144092713051114623009457)
                  ·
                    rfl

theorem cell21_631394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_631394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_631394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_631394 prefixEnd_631394 := by exact prefixLift 631394
  have htrace : WordTrace (prefixWord ++ tailWord_631394) baseStart_631394 baseEnd_631394 := by
    simpa [prefixWord, tailWord_631394, baseEnd_631394] using wordTrace_append hprefix tailTrace_631394
  have hstable : (prefixWord ++ tailWord_631394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631394).length < 2 ^ (prefixWord ++ tailWord_631394).sum := by decide
  have hdescent : baseEnd_631394 < baseStart_631394 := by decide
  rcases family_descends (prefixWord ++ tailWord_631394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631405 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 5]
def baseStart_631405 : Nat := 118140960795 + 631405 * 2 ^ 59
def prefixEnd_631405 : Nat := 4983230072969 + 3 ^ 40 * 631405 * 2
def baseEnd_631405 : Nat := 144095223400981048326101

theorem tailTrace_631405 : CollatzResearch.WordTrace tailWord_631405 prefixEnd_631405 144095223400981048326101 := by
  unfold tailWord_631405
  simp only [CollatzResearch.WordTrace]
  refine ⟨23029232277534995233895669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15352821518356663489263779 23029232277534995233895669)
  ·
    refine ⟨2158990526018905803177719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23029232277534995233895669 2158990526018905803177719)
    ·
      refine ⟨3238485789028358704766579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2158990526018905803177719 3238485789028358704766579)
      ·
        refine ⟨4857728683542538057149869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3238485789028358704766579 4857728683542538057149869)
        ·
          refine ⟨1821648256328451771431201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4857728683542538057149869 1821648256328451771431201)
          ·
            refine ⟨1366236192246338828573401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1821648256328451771431201 1366236192246338828573401)
            ·
              refine ⟨1024677144184754121430051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1366236192246338828573401 1024677144184754121430051)
              ·
                refine ⟨1537015716277131182145077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024677144184754121430051 1537015716277131182145077)
                ·
                  refine ⟨144095223400981048326101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1537015716277131182145077 144095223400981048326101)
                  ·
                    rfl

theorem cell21_631405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_631405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_631405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_631405 prefixEnd_631405 := by exact prefixLift 631405
  have htrace : WordTrace (prefixWord ++ tailWord_631405) baseStart_631405 baseEnd_631405 := by
    simpa [prefixWord, tailWord_631405, baseEnd_631405] using wordTrace_append hprefix tailTrace_631405
  have hstable : (prefixWord ++ tailWord_631405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631405).length < 2 ^ (prefixWord ++ tailWord_631405).sum := by decide
  have hdescent : baseEnd_631405 < baseStart_631405 := by decide
  rcases family_descends (prefixWord ++ tailWord_631405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631470 : List Nat := [4, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_631470 : Nat := 118140960795 + 631470 * 2 ^ 59
def prefixEnd_631470 : Nat := 4983230072969 + 3 ^ 40 * 631470 * 2
def baseEnd_631470 : Nat := 144110057286555379742635

theorem tailTrace_631470 : CollatzResearch.WordTrace tailWord_631470 prefixEnd_631470 144110057286555379742635 := by
  unfold tailWord_631470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2878950377787438916876483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15354402014866340890007909 2878950377787438916876483)
  ·
    refine ⟨4318425566681158375314725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2878950377787438916876483 4318425566681158375314725)
    ·
      refine ⟨809704793752717195371511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4318425566681158375314725 809704793752717195371511)
      ·
        refine ⟨1214557190629075793057267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 809704793752717195371511 1214557190629075793057267)
        ·
          refine ⟨1821835785943613689585901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1214557190629075793057267 1821835785943613689585901)
          ·
            refine ⟨683188419728855133594713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1821835785943613689585901 683188419728855133594713)
            ·
              refine ⟨512391314796641350196035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 683188419728855133594713 512391314796641350196035)
              ·
                refine ⟨768586972194962025294053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512391314796641350196035 768586972194962025294053)
                ·
                  refine ⟨144110057286555379742635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 768586972194962025294053 144110057286555379742635)
                  ·
                    rfl

theorem cell21_631470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_631470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_631470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_631470 prefixEnd_631470 := by exact prefixLift 631470
  have htrace : WordTrace (prefixWord ++ tailWord_631470) baseStart_631470 baseEnd_631470 := by
    simpa [prefixWord, tailWord_631470, baseEnd_631470] using wordTrace_append hprefix tailTrace_631470
  have hstable : (prefixWord ++ tailWord_631470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631470).length < 2 ^ (prefixWord ++ tailWord_631470).sum := by decide
  have hdescent : baseEnd_631470 < baseStart_631470 := by decide
  rcases family_descends (prefixWord ++ tailWord_631470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631509 : List Nat := [1, 3, 2, 5, 10]
def baseStart_631509 : Nat := 118140960795 + 631509 * 2 ^ 59
def prefixEnd_631509 : Nat := 4983230072969 + 3 ^ 40 * 631509 * 2
def baseEnd_631509 : Nat := 1779246390344444180155

theorem tailTrace_631509 : CollatzResearch.WordTrace tailWord_631509 prefixEnd_631509 1779246390344444180155 := by
  unfold tailWord_631509
  simp only [CollatzResearch.WordTrace]
  refine ⟨23033025469158220995681581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15355350312772147330454387 23033025469158220995681581)
  ·
    refine ⟨8637384550934332873380593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23033025469158220995681581 8637384550934332873380593)
    ·
      refine ⟨6478038413200749655035445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8637384550934332873380593 6478038413200749655035445)
      ·
        refine ⟨607316101237570280159573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6478038413200749655035445 607316101237570280159573)
        ·
          refine ⟨1779246390344444180155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 607316101237570280159573 1779246390344444180155)
          ·
            rfl

theorem cell21_631509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 10].length) (baseStart_631509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_631509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_631509 prefixEnd_631509 := by exact prefixLift 631509
  have htrace : WordTrace (prefixWord ++ tailWord_631509) baseStart_631509 baseEnd_631509 := by
    simpa [prefixWord, tailWord_631509, baseEnd_631509] using wordTrace_append hprefix tailTrace_631509
  have hstable : (prefixWord ++ tailWord_631509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631509).length < 2 ^ (prefixWord ++ tailWord_631509).sum := by decide
  have hdescent : baseEnd_631509 < baseStart_631509 := by decide
  rcases family_descends (prefixWord ++ tailWord_631509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631633 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 5]
def baseStart_631633 : Nat := 118140960795 + 631633 * 2 ^ 59
def prefixEnd_631633 : Nat := 4983230072969 + 3 ^ 40 * 631633 * 2
def baseEnd_631633 : Nat := 144147256107303318525635

theorem tailTrace_631633 : CollatzResearch.WordTrace tailWord_631633 prefixEnd_631633 144147256107303318525635 := by
  unfold tailWord_631633
  simp only [CollatzResearch.WordTrace]
  refine ⟨23037548120708990173195553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15358365413805993448797035 23037548120708990173195553)
  ·
    refine ⟨17278161090531742629896665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23037548120708990173195553 17278161090531742629896665)
    ·
      refine ⟨12958620817898806972422499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17278161090531742629896665 12958620817898806972422499)
      ·
        refine ⟨19437931226848210458633749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12958620817898806972422499 19437931226848210458633749)
        ·
          refine ⟨911153026258509865248457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19437931226848210458633749 911153026258509865248457)
          ·
            refine ⟨683364769693882398936343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 911153026258509865248457 683364769693882398936343)
            ·
              refine ⟨1025047154540823598404515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683364769693882398936343 1025047154540823598404515)
              ·
                refine ⟨1537570731811235397606773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025047154540823598404515 1537570731811235397606773)
                ·
                  refine ⟨144147256107303318525635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1537570731811235397606773 144147256107303318525635)
                  ·
                    rfl

theorem cell21_631633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 5].length) (baseStart_631633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_631633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_631633 prefixEnd_631633 := by exact prefixLift 631633
  have htrace : WordTrace (prefixWord ++ tailWord_631633) baseStart_631633 baseEnd_631633 := by
    simpa [prefixWord, tailWord_631633, baseEnd_631633] using wordTrace_append hprefix tailTrace_631633
  have hstable : (prefixWord ++ tailWord_631633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631633).length < 2 ^ (prefixWord ++ tailWord_631633).sum := by decide
  have hdescent : baseEnd_631633 < baseStart_631633 := by decide
  rcases family_descends (prefixWord ++ tailWord_631633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631678 : List Nat := [4, 2, 3, 1, 2, 9]
def baseStart_631678 : Nat := 118140960795 + 631678 * 2 ^ 59
def prefixEnd_631678 : Nat := 4983230072969 + 3 ^ 40 * 631678 * 2
def baseEnd_631678 : Nat := 5339167619273823713909

theorem tailTrace_631678 : CollatzResearch.WordTrace tailWord_631678 prefixEnd_631678 5339167619273823713909 := by
  unfold tailWord_631678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2879898675693245357322961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15359459603697308572389125 2879898675693245357322961)
  ·
    refine ⟨2159924006769934017992221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2879898675693245357322961 2159924006769934017992221)
    ·
      refine ⟨809971502538725256747083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2159924006769934017992221 809971502538725256747083)
      ·
        refine ⟨1214957253808087885120625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 809971502538725256747083 1214957253808087885120625)
        ·
          refine ⟨911217940356065913840469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1214957253808087885120625 911217940356065913840469)
          ·
            refine ⟨5339167619273823713909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 911217940356065913840469 5339167619273823713909)
            ·
              rfl

theorem cell21_631678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 9].length) (baseStart_631678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_631678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_631678 prefixEnd_631678 := by exact prefixLift 631678
  have htrace : WordTrace (prefixWord ++ tailWord_631678) baseStart_631678 baseEnd_631678 := by
    simpa [prefixWord, tailWord_631678, baseEnd_631678] using wordTrace_append hprefix tailTrace_631678
  have hstable : (prefixWord ++ tailWord_631678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631678).length < 2 ^ (prefixWord ++ tailWord_631678).sum := by decide
  have hdescent : baseEnd_631678 < baseStart_631678 := by decide
  rcases family_descends (prefixWord ++ tailWord_631678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631751 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 5]
def baseStart_631751 : Nat := 118140960795 + 631751 * 2 ^ 59
def prefixEnd_631751 : Nat := 4983230072969 + 3 ^ 40 * 631751 * 2
def baseEnd_631751 : Nat := 144174185314961335558727

theorem tailTrace_631751 : CollatzResearch.WordTrace tailWord_631751 prefixEnd_631751 144174185314961335558727 := by
  unfold tailWord_631751
  simp only [CollatzResearch.WordTrace]
  refine ⟨23041851934281496325991107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15361234622854330883994071 23041851934281496325991107)
  ·
    refine ⟨34562777901422244488986661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23041851934281496325991107 34562777901422244488986661)
    ·
      refine ⟨6480520856516670841684999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34562777901422244488986661 6480520856516670841684999)
      ·
        refine ⟨9720781284775006262527499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6480520856516670841684999 9720781284775006262527499)
        ·
          refine ⟨14581171927162509393791249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9720781284775006262527499 14581171927162509393791249)
          ·
            refine ⟨10935878945371882045343437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14581171927162509393791249 10935878945371882045343437)
            ·
              refine ⟨4100954604514455767003789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10935878945371882045343437 4100954604514455767003789)
              ·
                refine ⟨1537857976692920912626421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4100954604514455767003789 1537857976692920912626421)
                ·
                  refine ⟨144174185314961335558727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1537857976692920912626421 144174185314961335558727)
                  ·
                    rfl

theorem cell21_631751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 5].length) (baseStart_631751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_631751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_631751 prefixEnd_631751 := by exact prefixLift 631751
  have htrace : WordTrace (prefixWord ++ tailWord_631751) baseStart_631751 baseEnd_631751 := by
    simpa [prefixWord, tailWord_631751, baseEnd_631751] using wordTrace_append hprefix tailTrace_631751
  have hstable : (prefixWord ++ tailWord_631751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631751).length < 2 ^ (prefixWord ++ tailWord_631751).sum := by decide
  have hdescent : baseEnd_631751 < baseStart_631751 := by decide
  rcases family_descends (prefixWord ++ tailWord_631751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631816 : List Nat := [2, 1, 3, 2, 1, 5, 2, 1, 4]
def baseStart_631816 : Nat := 118140960795 + 631816 * 2 ^ 59
def prefixEnd_631816 : Nat := 4983230072969 + 3 ^ 40 * 631816 * 2
def baseEnd_631816 : Nat := 144189019200535666975261

theorem tailTrace_631816 : CollatzResearch.WordTrace tailWord_631816 prefixEnd_631816 144189019200535666975261 := by
  unfold tailWord_631816
  simp only [CollatzResearch.WordTrace]
  refine ⟨11522111339523006213553651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15362815119364008284738201 11522111339523006213553651)
  ·
    refine ⟨17283167009284509320330477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11522111339523006213553651 17283167009284509320330477)
    ·
      refine ⟨6481187628481690995123929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17283167009284509320330477 6481187628481690995123929)
      ·
        refine ⟨4860890721361268246342947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6481187628481690995123929 4860890721361268246342947)
        ·
          refine ⟨7291336082041902369514421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4860890721361268246342947 7291336082041902369514421)
          ·
            refine ⟨683562757691428347141977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7291336082041902369514421 683562757691428347141977)
            ·
              refine ⟨512672068268571260356483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 683562757691428347141977 512672068268571260356483)
              ·
                refine ⟨769008102402856890534725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512672068268571260356483 769008102402856890534725)
                ·
                  refine ⟨144189019200535666975261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 769008102402856890534725 144189019200535666975261)
                  ·
                    rfl

theorem cell21_631816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 4].length) (baseStart_631816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_631816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_631816 prefixEnd_631816 := by exact prefixLift 631816
  have htrace : WordTrace (prefixWord ++ tailWord_631816) baseStart_631816 baseEnd_631816 := by
    simpa [prefixWord, tailWord_631816, baseEnd_631816] using wordTrace_append hprefix tailTrace_631816
  have hstable : (prefixWord ++ tailWord_631816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631816).length < 2 ^ (prefixWord ++ tailWord_631816).sum := by decide
  have hdescent : baseEnd_631816 < baseStart_631816 := by decide
  rcases family_descends (prefixWord ++ tailWord_631816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631920 : List Nat := [2, 1, 1, 1, 5, 1, 1, 6, 3]
def baseStart_631920 : Nat := 118140960795 + 631920 * 2 ^ 59
def prefixEnd_631920 : Nat := 4983230072969 + 3 ^ 40 * 631920 * 2
def baseEnd_631920 : Nat := 144212753417454597241715

theorem tailTrace_631920 : CollatzResearch.WordTrace tailWord_631920 prefixEnd_631920 144212753417454597241715 := by
  unfold tailWord_631920
  simp only [CollatzResearch.WordTrace]
  refine ⟨11524007935334619094446607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15365343913779492125928809 11524007935334619094446607)
  ·
    refine ⟨17286011903001928641669911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11524007935334619094446607 17286011903001928641669911)
    ·
      refine ⟨25929017854502892962504867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17286011903001928641669911 25929017854502892962504867)
      ·
        refine ⟨38893526781754339443757301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25929017854502892962504867 38893526781754339443757301)
        ·
          refine ⟨3646268135789469322852247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38893526781754339443757301 3646268135789469322852247)
          ·
            refine ⟨5469402203684203984278371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646268135789469322852247 5469402203684203984278371)
            ·
              refine ⟨8204103305526305976417557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5469402203684203984278371 8204103305526305976417557)
              ·
                refine ⟨384567342446545592644573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8204103305526305976417557 384567342446545592644573)
                ·
                  refine ⟨144212753417454597241715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 384567342446545592644573 144212753417454597241715)
                  ·
                    rfl

theorem cell21_631920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 3].length) (baseStart_631920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_631920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_631920 prefixEnd_631920 := by exact prefixLift 631920
  have htrace : WordTrace (prefixWord ++ tailWord_631920) baseStart_631920 baseEnd_631920 := by
    simpa [prefixWord, tailWord_631920, baseEnd_631920] using wordTrace_append hprefix tailTrace_631920
  have hstable : (prefixWord ++ tailWord_631920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631920).length < 2 ^ (prefixWord ++ tailWord_631920).sum := by decide
  have hdescent : baseEnd_631920 < baseStart_631920 := by decide
  rcases family_descends (prefixWord ++ tailWord_631920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631954 : List Nat := [3, 2, 3, 1, 1, 4, 1, 3, 3]
def baseStart_631954 : Nat := 118140960795 + 631954 * 2 ^ 59
def prefixEnd_631954 : Nat := 4983230072969 + 3 ^ 40 * 631954 * 2
def baseEnd_631954 : Nat := 144220512680678093674979

theorem tailTrace_631954 : CollatzResearch.WordTrace tailWord_631954 prefixEnd_631954 144220512680678093674979 := by
  unfold tailWord_631954
  simp only [CollatzResearch.WordTrace]
  refine ⟨5762313988136515498907729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15366170635030707997087277 5762313988136515498907729)
  ·
    refine ⟨4321735491102386624180797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5762313988136515498907729 4321735491102386624180797)
    ·
      refine ⟨1620650809163394984067799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4321735491102386624180797 1620650809163394984067799)
      ·
        refine ⟨2430976213745092476101699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1620650809163394984067799 2430976213745092476101699)
        ·
          refine ⟨3646464320617638714152549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2430976213745092476101699 3646464320617638714152549)
          ·
            refine ⟨683712060115807258903603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3646464320617638714152549 683712060115807258903603)
            ·
              refine ⟨1025568090173710888355405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683712060115807258903603 1025568090173710888355405)
              ·
                refine ⟨384588033815141583133277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1025568090173710888355405 384588033815141583133277)
                ·
                  refine ⟨144220512680678093674979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 384588033815141583133277 144220512680678093674979)
                  ·
                    rfl

theorem cell21_631954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_631954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_631954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_631954 prefixEnd_631954 := by exact prefixLift 631954
  have htrace : WordTrace (prefixWord ++ tailWord_631954) baseStart_631954 baseEnd_631954 := by
    simpa [prefixWord, tailWord_631954, baseEnd_631954] using wordTrace_append hprefix tailTrace_631954
  have hstable : (prefixWord ++ tailWord_631954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631954).length < 2 ^ (prefixWord ++ tailWord_631954).sum := by decide
  have hdescent : baseEnd_631954 < baseStart_631954 := by decide
  rcases family_descends (prefixWord ++ tailWord_631954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632024 : List Nat := [2, 1, 2, 2, 5, 9]
def baseStart_632024 : Nat := 118140960795 + 632024 * 2 ^ 59
def prefixEnd_632024 : Nat := 4983230072969 + 3 ^ 40 * 632024 * 2
def baseEnd_632024 : Nat := 5342092134606426944747

theorem tailTrace_632024 : CollatzResearch.WordTrace tailWord_632024 prefixEnd_632024 5342092134606426944747 := by
  unfold tailWord_632024
  simp only [CollatzResearch.WordTrace]
  refine ⟨11525904531146231975339563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15367872708194975967119417 11525904531146231975339563)
  ·
    refine ⟨17288856796719347963009345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11525904531146231975339563 17288856796719347963009345)
    ·
      refine ⟨12966642597539510972257009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17288856796719347963009345 12966642597539510972257009)
      ·
        refine ⟨9724981948154633229192757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12966642597539510972257009 9724981948154633229192757)
        ·
          refine ⟨911717057639496865236821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9724981948154633229192757 911717057639496865236821)
          ·
            refine ⟨5342092134606426944747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 911717057639496865236821 5342092134606426944747)
            ·
              rfl

theorem cell21_632024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 9].length) (baseStart_632024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_632024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_632024 prefixEnd_632024 := by exact prefixLift 632024
  have htrace : WordTrace (prefixWord ++ tailWord_632024) baseStart_632024 baseEnd_632024 := by
    simpa [prefixWord, tailWord_632024, baseEnd_632024] using wordTrace_append hprefix tailTrace_632024
  have hstable : (prefixWord ++ tailWord_632024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632024).length < 2 ^ (prefixWord ++ tailWord_632024).sum := by decide
  have hdescent : baseEnd_632024 < baseStart_632024 := by decide
  rcases family_descends (prefixWord ++ tailWord_632024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632069 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 6]
def baseStart_632069 : Nat := 118140960795 + 632069 * 2 ^ 59
def prefixEnd_632069 : Nat := 4983230072969 + 3 ^ 40 * 632069 * 2
def baseEnd_632069 : Nat := 144246757247463449258077

theorem tailTrace_632069 : CollatzResearch.WordTrace tailWord_632069 prefixEnd_632069 144246757247463449258077 := by
  unfold tailWord_632069
  simp only [CollatzResearch.WordTrace]
  refine ⟨23053450347129436636067261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15368966898086291090711507 23053450347129436636067261)
  ·
    refine ⟨8645043880173538738525223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23053450347129436636067261 8645043880173538738525223)
    ·
      refine ⟨12967565820260308107787835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8645043880173538738525223 12967565820260308107787835)
      ·
        refine ⟨19451348730390462161681753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12967565820260308107787835 19451348730390462161681753)
        ·
          refine ⟨14588511547792846621261315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19451348730390462161681753 14588511547792846621261315)
          ·
            refine ⟨21882767321689269931891973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14588511547792846621261315 21882767321689269931891973)
            ·
              refine ⟨4103018872816738112229745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21882767321689269931891973 4103018872816738112229745)
              ·
                refine ⟨3077264154612553584172309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4103018872816738112229745 3077264154612553584172309)
                ·
                  refine ⟨144246757247463449258077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3077264154612553584172309 144246757247463449258077)
                  ·
                    rfl

theorem cell21_632069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_632069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_632069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_632069 prefixEnd_632069 := by exact prefixLift 632069
  have htrace : WordTrace (prefixWord ++ tailWord_632069) baseStart_632069 baseEnd_632069 := by
    simpa [prefixWord, tailWord_632069, baseEnd_632069] using wordTrace_append hprefix tailTrace_632069
  have hstable : (prefixWord ++ tailWord_632069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632069).length < 2 ^ (prefixWord ++ tailWord_632069).sum := by decide
  have hdescent : baseEnd_632069 < baseStart_632069 := by decide
  rcases family_descends (prefixWord ++ tailWord_632069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632100 : List Nat := [2, 3, 1, 3, 1, 1, 2, 8]
def baseStart_632100 : Nat := 118140960795 + 632100 * 2 ^ 59
def prefixEnd_632100 : Nat := 4983230072969 + 3 ^ 40 * 632100 * 2
def baseEnd_632100 : Nat := 48084610623271428080449

theorem tailTrace_632100 : CollatzResearch.WordTrace tailWord_632100 prefixEnd_632100 48084610623271428080449 := by
  unfold tailWord_632100
  simp only [CollatzResearch.WordTrace]
  refine ⟨11527290505008564465222877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15369720673344752620297169 11527290505008564465222877)
  ·
    refine ⟨4322733939378211674458579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11527290505008564465222877 4322733939378211674458579)
    ·
      refine ⟨6484100909067317511687869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4322733939378211674458579 6484100909067317511687869)
      ·
        refine ⟨2431537840900244066882951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6484100909067317511687869 2431537840900244066882951)
        ·
          refine ⟨3647306761350366100324427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2431537840900244066882951 3647306761350366100324427)
          ·
            refine ⟨5470960142025549150486641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3647306761350366100324427 5470960142025549150486641)
            ·
              refine ⟨4103220106519161862864981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5470960142025549150486641 4103220106519161862864981)
              ·
                refine ⟨48084610623271428080449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4103220106519161862864981 48084610623271428080449)
                ·
                  rfl

theorem cell21_632100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 8].length) (baseStart_632100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_632100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_632100 prefixEnd_632100 := by exact prefixLift 632100
  have htrace : WordTrace (prefixWord ++ tailWord_632100) baseStart_632100 baseEnd_632100 := by
    simpa [prefixWord, tailWord_632100, baseEnd_632100] using wordTrace_append hprefix tailTrace_632100
  have hstable : (prefixWord ++ tailWord_632100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632100).length < 2 ^ (prefixWord ++ tailWord_632100).sum := by decide
  have hdescent : baseEnd_632100 < baseStart_632100 := by decide
  rcases family_descends (prefixWord ++ tailWord_632100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632117 : List Nat := [1, 3, 3, 1, 2, 2, 4, 5]
def baseStart_632117 : Nat := 118140960795 + 632117 * 2 ^ 59
def prefixEnd_632117 : Nat := 4983230072969 + 3 ^ 40 * 632117 * 2
def baseEnd_632117 : Nat := 48085903833808677485993

theorem tailTrace_632117 : CollatzResearch.WordTrace tailWord_632117 prefixEnd_632117 48085903833808677485993 := by
  unfold tailWord_632117
  simp only [CollatzResearch.WordTrace]
  refine ⟨23055201050955540833814605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15370134033970360555876403 23055201050955540833814605)
  ·
    refine ⟨8645700394108327812680477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23055201050955540833814605 8645700394108327812680477)
    ·
      refine ⟨3242137647790622929755179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8645700394108327812680477 3242137647790622929755179)
      ·
        refine ⟨4863206471685934394632769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3242137647790622929755179 4863206471685934394632769)
        ·
          refine ⟨3647404853764450795974577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4863206471685934394632769 3647404853764450795974577)
          ·
            refine ⟨2735553640323338096980933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3647404853764450795974577 2735553640323338096980933)
            ·
              refine ⟨512916307560625893183925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2735553640323338096980933 512916307560625893183925)
              ·
                refine ⟨48085903833808677485993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 512916307560625893183925 48085903833808677485993)
                ·
                  rfl

theorem cell21_632117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 5].length) (baseStart_632117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_632117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_632117 prefixEnd_632117 := by exact prefixLift 632117
  have htrace : WordTrace (prefixWord ++ tailWord_632117) baseStart_632117 baseEnd_632117 := by
    simpa [prefixWord, tailWord_632117, baseEnd_632117] using wordTrace_append hprefix tailTrace_632117
  have hstable : (prefixWord ++ tailWord_632117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632117).length < 2 ^ (prefixWord ++ tailWord_632117).sum := by decide
  have hdescent : baseEnd_632117 < baseStart_632117 := by decide
  rcases family_descends (prefixWord ++ tailWord_632117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632145 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 6]
def baseStart_632145 : Nat := 118140960795 + 632145 * 2 ^ 59
def prefixEnd_632145 : Nat := 4983230072969 + 3 ^ 40 * 632145 * 2
def baseEnd_632145 : Nat := 144264101482904205991255

theorem tailTrace_632145 : CollatzResearch.WordTrace tailWord_632145 prefixEnd_632145 144264101482904205991255 := by
  unfold tailWord_632145
  simp only [CollatzResearch.WordTrace]
  refine ⟨23056222294854101615833889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15370814863236067743889259 23056222294854101615833889)
  ·
    refine ⟨17292166721140576211875417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23056222294854101615833889 17292166721140576211875417)
    ·
      refine ⟨12969125040855432158906563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17292166721140576211875417 12969125040855432158906563)
      ·
        refine ⟨19453687561283148238359845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12969125040855432158906563 19453687561283148238359845)
        ·
          refine ⟨3647566417740590294692471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19453687561283148238359845 3647566417740590294692471)
          ·
            refine ⟨5471349626610885442038707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3647566417740590294692471 5471349626610885442038707)
            ·
              refine ⟨8207024439916328163058061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5471349626610885442038707 8207024439916328163058061)
              ·
                refine ⟨3077634164968623061146773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8207024439916328163058061 3077634164968623061146773)
                ·
                  refine ⟨144264101482904205991255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3077634164968623061146773 144264101482904205991255)
                  ·
                    rfl

theorem cell21_632145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_632145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_632145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_632145 prefixEnd_632145 := by exact prefixLift 632145
  have htrace : WordTrace (prefixWord ++ tailWord_632145) baseStart_632145 baseEnd_632145 := by
    simpa [prefixWord, tailWord_632145, baseEnd_632145] using wordTrace_append hprefix tailTrace_632145
  have hstable : (prefixWord ++ tailWord_632145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632145).length < 2 ^ (prefixWord ++ tailWord_632145).sum := by decide
  have hdescent : baseEnd_632145 < baseStart_632145 := by decide
  rcases family_descends (prefixWord ++ tailWord_632145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632193 : List Nat := [1, 2, 4, 3, 3, 8]
def baseStart_632193 : Nat := 118140960795 + 632193 * 2 ^ 59
def prefixEnd_632193 : Nat := 4983230072969 + 3 ^ 40 * 632193 * 2
def baseEnd_632193 : Nat := 5343520582846918118191

theorem tailTrace_632193 : CollatzResearch.WordTrace tailWord_632193 prefixEnd_632193 5343520582846918118191 := by
  unfold tailWord_632193
  simp only [CollatzResearch.WordTrace]
  refine ⟨23057972998680205813581233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15371981999120137209054155 23057972998680205813581233)
  ·
    refine ⟨17293479749010154360185925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23057972998680205813581233 17293479749010154360185925)
    ·
      refine ⟨3242527452939403942534861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17293479749010154360185925 3242527452939403942534861)
      ·
        refine ⟨1215947794852276478450573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3242527452939403942534861 1215947794852276478450573)
        ·
          refine ⟨455980423069603679418965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1215947794852276478450573 455980423069603679418965)
          ·
            refine ⟨5343520582846918118191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 455980423069603679418965 5343520582846918118191)
            ·
              rfl

theorem cell21_632193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 8].length) (baseStart_632193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_632193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_632193 prefixEnd_632193 := by exact prefixLift 632193
  have htrace : WordTrace (prefixWord ++ tailWord_632193) baseStart_632193 baseEnd_632193 := by
    simpa [prefixWord, tailWord_632193, baseEnd_632193] using wordTrace_append hprefix tailTrace_632193
  have hstable : (prefixWord ++ tailWord_632193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632193).length < 2 ^ (prefixWord ++ tailWord_632193).sum := by decide
  have hdescent : baseEnd_632193 < baseStart_632193 := by decide
  rcases family_descends (prefixWord ++ tailWord_632193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632317 : List Nat := [1, 4, 1, 1, 1, 5, 3, 2, 3]
def baseStart_632317 : Nat := 118140960795 + 632317 * 2 ^ 59
def prefixEnd_632317 : Nat := 4983230072969 + 3 ^ 40 * 632317 * 2
def baseEnd_632317 : Nat := 144303354226270129124237

theorem tailTrace_632317 : CollatzResearch.WordTrace tailWord_632317 prefixEnd_632317 144303354226270129124237 := by
  unfold tailWord_632317
  simp only [CollatzResearch.WordTrace]
  refine ⟨23062495650230974991095205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15374997100153983327396803 23062495650230974991095205)
  ·
    refine ⟨4324217934418307810830351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23062495650230974991095205 4324217934418307810830351)
    ·
      refine ⟨6486326901627461716245527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4324217934418307810830351 6486326901627461716245527)
      ·
        refine ⟨9729490352441192574368291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6486326901627461716245527 9729490352441192574368291)
        ·
          refine ⟨14594235528661788861552437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9729490352441192574368291 14594235528661788861552437)
          ·
            refine ⟨1368209580812042705770541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14594235528661788861552437 1368209580812042705770541)
            ·
              refine ⟨513078592804516014663953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1368209580812042705770541 513078592804516014663953)
              ·
                refine ⟨384808944603387010997965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513078592804516014663953 384808944603387010997965)
                ·
                  refine ⟨144303354226270129124237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 384808944603387010997965 144303354226270129124237)
                  ·
                    rfl

theorem cell21_632317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_632317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_632317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_632317 prefixEnd_632317 := by exact prefixLift 632317
  have htrace : WordTrace (prefixWord ++ tailWord_632317) baseStart_632317 baseEnd_632317 := by
    simpa [prefixWord, tailWord_632317, baseEnd_632317] using wordTrace_append hprefix tailTrace_632317
  have hstable : (prefixWord ++ tailWord_632317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632317).length < 2 ^ (prefixWord ++ tailWord_632317).sum := by decide
  have hdescent : baseEnd_632317 < baseStart_632317 := by decide
  rcases family_descends (prefixWord ++ tailWord_632317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632376 : List Nat := [2, 1, 2, 1, 4, 3, 1, 4, 3]
def baseStart_632376 : Nat := 118140960795 + 632376 * 2 ^ 59
def prefixEnd_632376 : Nat := 4983230072969 + 3 ^ 40 * 632376 * 2
def baseEnd_632376 : Nat := 144316818830099137640783

theorem tailTrace_632376 : CollatzResearch.WordTrace tailWord_632376 prefixEnd_632376 144316818830099137640783 := by
  unfold tailWord_632376
  simp only [CollatzResearch.WordTrace]
  refine ⟨11532323778508614033746491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15376431704678152044995321 11532323778508614033746491)
  ·
    refine ⟨17298485667762921050619737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11532323778508614033746491 17298485667762921050619737)
    ·
      refine ⟨12973864250822190787964803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17298485667762921050619737 12973864250822190787964803)
      ·
        refine ⟨19460796376233286181947205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12973864250822190787964803 19460796376233286181947205)
        ·
          refine ⟨3648899320543741159115101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19460796376233286181947205 3648899320543741159115101)
          ·
            refine ⟨1368337245203902934668163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3648899320543741159115101 1368337245203902934668163)
            ·
              refine ⟨2052505867805854402002245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1368337245203902934668163 2052505867805854402002245)
              ·
                refine ⟨384844850213597700375421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2052505867805854402002245 384844850213597700375421)
                ·
                  refine ⟨144316818830099137640783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 384844850213597700375421 144316818830099137640783)
                  ·
                    rfl

theorem cell21_632376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 3].length) (baseStart_632376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_632376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_632376 prefixEnd_632376 := by exact prefixLift 632376
  have htrace : WordTrace (prefixWord ++ tailWord_632376) baseStart_632376 baseEnd_632376 := by
    simpa [prefixWord, tailWord_632376, baseEnd_632376] using wordTrace_append hprefix tailTrace_632376
  have hstable : (prefixWord ++ tailWord_632376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632376).length < 2 ^ (prefixWord ++ tailWord_632376).sum := by decide
  have hdescent : baseEnd_632376 < baseStart_632376 := by decide
  rcases family_descends (prefixWord ++ tailWord_632376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632480 : List Nat := [2, 1, 1, 4, 3, 3, 7]
def baseStart_632480 : Nat := 118140960795 + 632480 * 2 ^ 59
def prefixEnd_632480 : Nat := 4983230072969 + 3 ^ 40 * 632480 * 2
def baseEnd_632480 : Nat := 16037839227446451989693

theorem tailTrace_632480 : CollatzResearch.WordTrace tailWord_632480 prefixEnd_632480 16037839227446451989693 := by
  unfold tailWord_632480
  simp only [CollatzResearch.WordTrace]
  refine ⟨11534220374320226914639447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15378960499093635886185929 11534220374320226914639447)
  ·
    refine ⟨17301330561480340371959171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11534220374320226914639447 17301330561480340371959171)
    ·
      refine ⟨25951995842220510557938757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17301330561480340371959171 25951995842220510557938757)
      ·
        refine ⟨4865999220416345729613517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25951995842220510557938757 4865999220416345729613517)
        ·
          refine ⟨1824749707656129648605069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4865999220416345729613517 1824749707656129648605069)
          ·
            refine ⟨684281140371048618226901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1824749707656129648605069 684281140371048618226901)
            ·
              refine ⟨16037839227446451989693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 684281140371048618226901 16037839227446451989693)
              ·
                rfl

theorem cell21_632480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 7].length) (baseStart_632480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_632480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_632480 prefixEnd_632480 := by exact prefixLift 632480
  have htrace : WordTrace (prefixWord ++ tailWord_632480) baseStart_632480 baseEnd_632480 := by
    simpa [prefixWord, tailWord_632480, baseEnd_632480] using wordTrace_append hprefix tailTrace_632480
  have hstable : (prefixWord ++ tailWord_632480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632480).length < 2 ^ (prefixWord ++ tailWord_632480).sum := by decide
  have hdescent : baseEnd_632480 < baseStart_632480 := by decide
  rcases family_descends (prefixWord ++ tailWord_632480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632587 : List Nat := [1, 1, 1, 1, 5, 1, 3, 5, 3]
def baseStart_632587 : Nat := 118140960795 + 632587 * 2 ^ 59
def prefixEnd_632587 : Nat := 4983230072969 + 3 ^ 40 * 632587 * 2
def baseEnd_632587 : Nat := 144364971904809659623685

theorem tailTrace_632587 : CollatzResearch.WordTrace tailWord_632587 prefixEnd_632587 144364971904809659623685 := by
  unfold tailWord_632587
  simp only [CollatzResearch.WordTrace]
  refine ⟨23072343359252811103424015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15381562239501874068949343 23072343359252811103424015)
  ·
    refine ⟨34608515038879216655136023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23072343359252811103424015 34608515038879216655136023)
    ·
      refine ⟨51912772558318824982704035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34608515038879216655136023 51912772558318824982704035)
      ·
        refine ⟨77869158837478237474056053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51912772558318824982704035 77869158837478237474056053)
        ·
          refine ⟨7300233641013584763192755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77869158837478237474056053 7300233641013584763192755)
          ·
            refine ⟨10950350461520377144789133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7300233641013584763192755 10950350461520377144789133)
            ·
              refine ⟨4106381423070141429295925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10950350461520377144789133 4106381423070141429295925)
              ·
                refine ⟨384973258412825758996493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4106381423070141429295925 384973258412825758996493)
                ·
                  refine ⟨144364971904809659623685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 384973258412825758996493 144364971904809659623685)
                  ·
                    rfl

theorem cell21_632587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 3].length) (baseStart_632587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_632587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_632587 prefixEnd_632587 := by exact prefixLift 632587
  have htrace : WordTrace (prefixWord ++ tailWord_632587) baseStart_632587 baseEnd_632587 := by
    simpa [prefixWord, tailWord_632587, baseEnd_632587] using wordTrace_append hprefix tailTrace_632587
  have hstable : (prefixWord ++ tailWord_632587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632587).length < 2 ^ (prefixWord ++ tailWord_632587).sum := by decide
  have hdescent : baseEnd_632587 < baseStart_632587 := by decide
  rcases family_descends (prefixWord ++ tailWord_632587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632632 : List Nat := [2, 1, 2, 1, 3, 3, 4, 5]
def baseStart_632632 : Nat := 118140960795 + 632632 * 2 ^ 59
def prefixEnd_632632 : Nat := 4983230072969 + 3 ^ 40 * 632632 * 2
def baseEnd_632632 : Nat := 48125080505966527124531

theorem tailTrace_632632 : CollatzResearch.WordTrace tailWord_632632 prefixEnd_632632 48125080505966527124531 := by
  unfold tailWord_632632
  simp only [CollatzResearch.WordTrace]
  refine ⟨11536992322044891894406075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15382656429393189192541433 11536992322044891894406075)
  ·
    refine ⟨17305488483067337841609113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11536992322044891894406075 17305488483067337841609113)
    ·
      refine ⟨12979116362300503381206835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17305488483067337841609113 12979116362300503381206835)
      ·
        refine ⟨19468674543450755071810253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12979116362300503381206835 19468674543450755071810253)
        ·
          refine ⟨7300752953794033151928845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19468674543450755071810253 7300752953794033151928845)
          ·
            refine ⟨2737782357672762431973317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7300752953794033151928845 2737782357672762431973317)
            ·
              refine ⟨513334192063642955994997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2737782357672762431973317 513334192063642955994997)
              ·
                refine ⟨48125080505966527124531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 513334192063642955994997 48125080505966527124531)
                ·
                  rfl

theorem cell21_632632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 5].length) (baseStart_632632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_632632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_632632 prefixEnd_632632 := by exact prefixLift 632632
  have htrace : WordTrace (prefixWord ++ tailWord_632632) baseStart_632632 baseEnd_632632 := by
    simpa [prefixWord, tailWord_632632, baseEnd_632632] using wordTrace_append hprefix tailTrace_632632
  have hstable : (prefixWord ++ tailWord_632632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632632).length < 2 ^ (prefixWord ++ tailWord_632632).sum := by decide
  have hdescent : baseEnd_632632 < baseStart_632632 := by decide
  rcases family_descends (prefixWord ++ tailWord_632632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632714 : List Nat := [3, 1, 2, 4, 2, 2, 2, 2, 3]
def baseStart_632714 : Nat := 118140960795 + 632714 * 2 ^ 59
def prefixEnd_632714 : Nat := 4983230072969 + 3 ^ 40 * 632714 * 2
def baseEnd_632714 : Nat := 144393955035085661006759

theorem tailTrace_632714 : CollatzResearch.WordTrace tailWord_632714 prefixEnd_632714 144393955035085661006759 := by
  unfold tailWord_632714
  simp only [CollatzResearch.WordTrace]
  refine ⟨5769243857448177948324299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15384650286528474528864797 5769243857448177948324299)
  ·
    refine ⟨8653865786172266922486449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5769243857448177948324299 8653865786172266922486449)
    ·
      refine ⟨6490399339629200191864837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8653865786172266922486449 6490399339629200191864837)
      ·
        refine ⟨1216949876180475035974657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6490399339629200191864837 1216949876180475035974657)
        ·
          refine ⟨912712407135356276980993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1216949876180475035974657 912712407135356276980993)
          ·
            refine ⟨684534305351517207735745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 912712407135356276980993 684534305351517207735745)
            ·
              refine ⟨513400729013637905801809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 684534305351517207735745 513400729013637905801809)
              ·
                refine ⟨385050546760228429351357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513400729013637905801809 385050546760228429351357)
                ·
                  refine ⟨144393955035085661006759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385050546760228429351357 144393955035085661006759)
                  ·
                    rfl

theorem cell21_632714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_632714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_632714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_632714 prefixEnd_632714 := by exact prefixLift 632714
  have htrace : WordTrace (prefixWord ++ tailWord_632714) baseStart_632714 baseEnd_632714 := by
    simpa [prefixWord, tailWord_632714, baseEnd_632714] using wordTrace_append hprefix tailTrace_632714
  have hstable : (prefixWord ++ tailWord_632714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632714).length < 2 ^ (prefixWord ++ tailWord_632714).sum := by decide
  have hdescent : baseEnd_632714 < baseStart_632714 := by decide
  rcases family_descends (prefixWord ++ tailWord_632714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632736 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 8]
def baseStart_632736 : Nat := 118140960795 + 632736 * 2 ^ 59
def prefixEnd_632736 : Nat := 4983230072969 + 3 ^ 40 * 632736 * 2
def baseEnd_632736 : Nat := 144398975734818511640047

theorem tailTrace_632736 : CollatzResearch.WordTrace tailWord_632736 prefixEnd_632736 144398975734818511640047 := by
  unfold tailWord_632736
  simp only [CollatzResearch.WordTrace]
  refine ⟨11538888917856504775299031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15385185223808673033732041 11538888917856504775299031)
  ·
    refine ⟨17308333376784757162948547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11538888917856504775299031 17308333376784757162948547)
    ·
      refine ⟨25962500065177135744422821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17308333376784757162948547 25962500065177135744422821)
      ·
        refine ⟨4867968762220712952079279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25962500065177135744422821 4867968762220712952079279)
        ·
          refine ⟨7301953143331069428118919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4867968762220712952079279 7301953143331069428118919)
          ·
            refine ⟨10952929714996604142178379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7301953143331069428118919 10952929714996604142178379)
            ·
              refine ⟨16429394572494906213267569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10952929714996604142178379 16429394572494906213267569)
              ·
                refine ⟨12322045929371179659950677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16429394572494906213267569 12322045929371179659950677)
                ·
                  refine ⟨144398975734818511640047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12322045929371179659950677 144398975734818511640047)
                  ·
                    rfl

theorem cell21_632736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_632736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_632736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_632736 prefixEnd_632736 := by exact prefixLift 632736
  have htrace : WordTrace (prefixWord ++ tailWord_632736) baseStart_632736 baseEnd_632736 := by
    simpa [prefixWord, tailWord_632736, baseEnd_632736] using wordTrace_append hprefix tailTrace_632736
  have hstable : (prefixWord ++ tailWord_632736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632736).length < 2 ^ (prefixWord ++ tailWord_632736).sum := by decide
  have hdescent : baseEnd_632736 < baseStart_632736 := by decide
  rcases family_descends (prefixWord ++ tailWord_632736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632843 : List Nat := [1, 1, 1, 1, 6, 1, 4, 6]
def baseStart_632843 : Nat := 118140960795 + 632843 * 2 ^ 59
def prefixEnd_632843 : Nat := 4983230072969 + 3 ^ 40 * 632843 * 2
def baseEnd_632843 : Nat := 48141131530870034452165

theorem tailTrace_632843 : CollatzResearch.WordTrace tailWord_632843 prefixEnd_632843 48141131530870034452165 := by
  unfold tailWord_632843
  simp only [CollatzResearch.WordTrace]
  refine ⟨23081680446325366824743183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15387786964216911216495455 23081680446325366824743183)
  ·
    refine ⟨34622520669488050237114775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23081680446325366824743183 34622520669488050237114775)
    ·
      refine ⟨51933781004232075355672163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34622520669488050237114775 51933781004232075355672163)
      ·
        refine ⟨77900671506348113033508245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51933781004232075355672163 77900671506348113033508245)
        ·
          refine ⟨3651593976860067798445699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 77900671506348113033508245 3651593976860067798445699)
          ·
            refine ⟨5477390965290101697668549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3651593976860067798445699 5477390965290101697668549)
            ·
              refine ⟨1027010805991894068312853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5477390965290101697668549 1027010805991894068312853)
              ·
                refine ⟨48141131530870034452165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1027010805991894068312853 48141131530870034452165)
                ·
                  rfl

theorem cell21_632843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 6].length) (baseStart_632843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_632843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_632843 prefixEnd_632843 := by exact prefixLift 632843
  have htrace : WordTrace (prefixWord ++ tailWord_632843) baseStart_632843 baseEnd_632843 := by
    simpa [prefixWord, tailWord_632843, baseEnd_632843] using wordTrace_append hprefix tailTrace_632843
  have hstable : (prefixWord ++ tailWord_632843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632843).length < 2 ^ (prefixWord ++ tailWord_632843).sum := by decide
  have hdescent : baseEnd_632843 < baseStart_632843 := by decide
  rcases family_descends (prefixWord ++ tailWord_632843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632857 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 7]
def baseStart_632857 : Nat := 118140960795 + 632857 * 2 ^ 59
def prefixEnd_632857 : Nat := 4983230072969 + 3 ^ 40 * 632857 * 2
def baseEnd_632857 : Nat := 144426589583349190123133

theorem tailTrace_632857 : CollatzResearch.WordTrace tailWord_632857 prefixEnd_632857 144426589583349190123133 := by
  unfold tailWord_632857
  simp only [CollatzResearch.WordTrace]
  refine ⟨23082191068274647215752825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15388127378849764810501883 23082191068274647215752825)
  ·
    refine ⟨17311643301205985411814619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23082191068274647215752825 17311643301205985411814619)
    ·
      refine ⟨25967464951808978117721929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17311643301205985411814619 25967464951808978117721929)
      ·
        refine ⟨19475598713856733588291447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25967464951808978117721929 19475598713856733588291447)
        ·
          refine ⟨29213398070785100382437171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19475598713856733588291447 29213398070785100382437171)
          ·
            refine ⟨43820097106177650573655757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29213398070785100382437171 43820097106177650573655757)
            ·
              refine ⟨16432536414816618965120909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43820097106177650573655757 16432536414816618965120909)
              ·
                refine ⟨6162201155556232111920341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16432536414816618965120909 6162201155556232111920341)
                ·
                  refine ⟨144426589583349190123133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6162201155556232111920341 144426589583349190123133)
                  ·
                    rfl

theorem cell21_632857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_632857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_632857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_632857 prefixEnd_632857 := by exact prefixLift 632857
  have htrace : WordTrace (prefixWord ++ tailWord_632857) baseStart_632857 baseEnd_632857 := by
    simpa [prefixWord, tailWord_632857, baseEnd_632857] using wordTrace_append hprefix tailTrace_632857
  have hstable : (prefixWord ++ tailWord_632857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632857).length < 2 ^ (prefixWord ++ tailWord_632857).sum := by decide
  have hdescent : baseEnd_632857 < baseStart_632857 := by decide
  rcases family_descends (prefixWord ++ tailWord_632857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632894 : List Nat := [4, 2, 1, 3, 3, 1, 1, 6]
def baseStart_632894 : Nat := 118140960795 + 632894 * 2 ^ 59
def prefixEnd_632894 : Nat := 4983230072969 + 3 ^ 40 * 632894 * 2
def baseEnd_632894 : Nat := 48145011162481782668797

theorem tailTrace_632894 : CollatzResearch.WordTrace tailWord_632894 prefixEnd_632894 48145011162481782668797 := by
  unfold tailWord_632894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2885442571142575316856217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15389027046093735023233157 2885442571142575316856217)
  ·
    refine ⟨2164081928356931487642163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2885442571142575316856217 2164081928356931487642163)
    ·
      refine ⟨3246122892535397231463245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2164081928356931487642163 3246122892535397231463245)
      ·
        refine ⟨1217296084700773961798717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3246122892535397231463245 1217296084700773961798717)
        ·
          refine ⟨456486031762790235674519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1217296084700773961798717 456486031762790235674519)
          ·
            refine ⟨684729047644185353511779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456486031762790235674519 684729047644185353511779)
            ·
              refine ⟨1027093571466278030267669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684729047644185353511779 1027093571466278030267669)
              ·
                refine ⟨48145011162481782668797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1027093571466278030267669 48145011162481782668797)
                ·
                  rfl

theorem cell21_632894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_632894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_632894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_632894 prefixEnd_632894 := by exact prefixLift 632894
  have htrace : WordTrace (prefixWord ++ tailWord_632894) baseStart_632894 baseEnd_632894 := by
    simpa [prefixWord, tailWord_632894, baseEnd_632894] using wordTrace_append hprefix tailTrace_632894
  have hstable : (prefixWord ++ tailWord_632894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632894).length < 2 ^ (prefixWord ++ tailWord_632894).sum := by decide
  have hdescent : baseEnd_632894 < baseStart_632894 := by decide
  rcases family_descends (prefixWord ++ tailWord_632894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632925 : List Nat := [1, 4, 4, 1, 1, 2, 2, 3, 3]
def baseStart_632925 : Nat := 118140960795 + 632925 * 2 ^ 59
def prefixEnd_632925 : Nat := 4983230072969 + 3 ^ 40 * 632925 * 2
def baseEnd_632925 : Nat := 144442108109796182989661

theorem tailTrace_632925 : CollatzResearch.WordTrace tailWord_632925 prefixEnd_632925 144442108109796182989661 := by
  unfold tailWord_632925
  simp only [CollatzResearch.WordTrace]
  refine ⟨23084671232028294829228229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15389780821352196552818819 23084671232028294829228229)
  ·
    refine ⟨4328375856005305280480293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23084671232028294829228229 4328375856005305280480293)
    ·
      refine ⟨811570473000994740090055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4328375856005305280480293 811570473000994740090055)
      ·
        refine ⟨1217355709501492110135083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 811570473000994740090055 1217355709501492110135083)
        ·
          refine ⟨1826033564252238165202625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217355709501492110135083 1826033564252238165202625)
          ·
            refine ⟨1369525173189178623901969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1826033564252238165202625 1369525173189178623901969)
            ·
              refine ⟨1027143879891883967926477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1369525173189178623901969 1027143879891883967926477)
              ·
                refine ⟨385178954959456487972429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1027143879891883967926477 385178954959456487972429)
                ·
                  refine ⟨144442108109796182989661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385178954959456487972429 144442108109796182989661)
                  ·
                    rfl

theorem cell21_632925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_632925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_632925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_632925 prefixEnd_632925 := by exact prefixLift 632925
  have htrace : WordTrace (prefixWord ++ tailWord_632925) baseStart_632925 baseEnd_632925 := by
    simpa [prefixWord, tailWord_632925, baseEnd_632925] using wordTrace_append hprefix tailTrace_632925
  have hstable : (prefixWord ++ tailWord_632925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632925).length < 2 ^ (prefixWord ++ tailWord_632925).sum := by decide
  have hdescent : baseEnd_632925 < baseStart_632925 := by decide
  rcases family_descends (prefixWord ++ tailWord_632925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633054 : List Nat := [4, 17]
def baseStart_633054 : Nat := 118140960795 + 633054 * 2 ^ 59
def prefixEnd_633054 : Nat := 4983230072969 + 3 ^ 40 * 633054 * 2
def baseEnd_633054 : Nat := 66059235330279206831

theorem tailTrace_633054 : CollatzResearch.WordTrace tailWord_633054 prefixEnd_633054 66059235330279206831 := by
  unfold tailWord_633054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2886172031070118732584277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15392917499040633240449477 2886172031070118732584277)
  ·
    refine ⟨66059235330279206831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 17 2886172031070118732584277 66059235330279206831)
    ·
      rfl

theorem cell21_633054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 17].length) (baseStart_633054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633054 prefixEnd_633054 := by exact prefixLift 633054
  have htrace : WordTrace (prefixWord ++ tailWord_633054) baseStart_633054 baseEnd_633054 := by
    simpa [prefixWord, tailWord_633054, baseEnd_633054] using wordTrace_append hprefix tailTrace_633054
  have hstable : (prefixWord ++ tailWord_633054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633054).length < 2 ^ (prefixWord ++ tailWord_633054).sum := by decide
  have hdescent : baseEnd_633054 < baseStart_633054 := by decide
  rcases family_descends (prefixWord ++ tailWord_633054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633057 : List Nat := [1, 2, 3, 1, 3, 1, 4, 2, 4]
def baseStart_633057 : Nat := 118140960795 + 633057 * 2 ^ 59
def prefixEnd_633057 : Nat := 4983230072969 + 3 ^ 40 * 633057 * 2
def baseEnd_633057 : Nat := 144472232308193286789391

theorem tailTrace_633057 : CollatzResearch.WordTrace tailWord_633057 prefixEnd_633057 144472232308193286789391 := by
  unfold tailWord_633057
  simp only [CollatzResearch.WordTrace]
  refine ⟨23089485667550081373033425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15392990445033387582022283 23089485667550081373033425)
  ·
    refine ⟨17317114250662561029775069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23089485667550081373033425 17317114250662561029775069)
    ·
      refine ⟨6493917843998460386165651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17317114250662561029775069 6493917843998460386165651)
      ·
        refine ⟨9740876765997690579248477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6493917843998460386165651 9740876765997690579248477)
        ·
          refine ⟨3652828787249133967218179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9740876765997690579248477 3652828787249133967218179)
          ·
            refine ⟨5479243180873700950827269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3652828787249133967218179 5479243180873700950827269)
            ·
              refine ⟨1027358096413818928280113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5479243180873700950827269 1027358096413818928280113)
              ·
                refine ⟨770518572310364196210085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1027358096413818928280113 770518572310364196210085)
                ·
                  refine ⟨144472232308193286789391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 770518572310364196210085 144472232308193286789391)
                  ·
                    rfl

theorem cell21_633057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_633057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633057 prefixEnd_633057 := by exact prefixLift 633057
  have htrace : WordTrace (prefixWord ++ tailWord_633057) baseStart_633057 baseEnd_633057 := by
    simpa [prefixWord, tailWord_633057, baseEnd_633057] using wordTrace_append hprefix tailTrace_633057
  have hstable : (prefixWord ++ tailWord_633057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633057).length < 2 ^ (prefixWord ++ tailWord_633057).sum := by decide
  have hdescent : baseEnd_633057 < baseStart_633057 := by decide
  rcases family_descends (prefixWord ++ tailWord_633057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633071 : List Nat := [1, 1, 2, 1, 6, 1, 3, 6]
def baseStart_633071 : Nat := 118140960795 + 633071 * 2 ^ 59
def prefixEnd_633071 : Nat := 4983230072969 + 3 ^ 40 * 633071 * 2
def baseEnd_633071 : Nat := 48158475766310791185343

theorem tailTrace_633071 : CollatzResearch.WordTrace tailWord_633071 prefixEnd_633071 48158475766310791185343 := by
  unfold tailWord_633071
  simp only [CollatzResearch.WordTrace]
  refine ⟨23089996289499361764043067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15393330859666241176028711 23089996289499361764043067)
  ·
    refine ⟨34634994434249042646064601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23089996289499361764043067 34634994434249042646064601)
    ·
      refine ⟨25976245825686781984548451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34634994434249042646064601 25976245825686781984548451)
      ·
        refine ⟨38964368738530172976822677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25976245825686781984548451 38964368738530172976822677)
        ·
          refine ⟨1826454784618601858288563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38964368738530172976822677 1826454784618601858288563)
          ·
            refine ⟨2739682176927902787432845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1826454784618601858288563 2739682176927902787432845)
            ·
              refine ⟨1027380816347963545287317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2739682176927902787432845 1027380816347963545287317)
              ·
                refine ⟨48158475766310791185343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1027380816347963545287317 48158475766310791185343)
                ·
                  rfl

theorem cell21_633071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 6].length) (baseStart_633071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633071 prefixEnd_633071 := by exact prefixLift 633071
  have htrace : WordTrace (prefixWord ++ tailWord_633071) baseStart_633071 baseEnd_633071 := by
    simpa [prefixWord, tailWord_633071, baseEnd_633071] using wordTrace_append hprefix tailTrace_633071
  have hstable : (prefixWord ++ tailWord_633071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633071).length < 2 ^ (prefixWord ++ tailWord_633071).sum := by decide
  have hdescent : baseEnd_633071 < baseStart_633071 := by decide
  rcases family_descends (prefixWord ++ tailWord_633071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633119 : List Nat := [1, 1, 2, 4, 3, 1, 2, 4, 3]
def baseStart_633119 : Nat := 118140960795 + 633119 * 2 ^ 59
def prefixEnd_633119 : Nat := 4983230072969 + 3 ^ 40 * 633119 * 2
def baseEnd_633119 : Nat := 144486381552894956755931

theorem tailTrace_633119 : CollatzResearch.WordTrace tailWord_633119 prefixEnd_633119 144486381552894956755931 := by
  unfold tailWord_633119
  simp only [CollatzResearch.WordTrace]
  refine ⟨23091746993325465961790411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15394497995550310641193607 23091746993325465961790411)
  ·
    refine ⟨34637620489988198942685617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23091746993325465961790411 34637620489988198942685617)
    ·
      refine ⟨25978215367491149207014213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34637620489988198942685617 25978215367491149207014213)
      ·
        refine ⟨4870915381404590476315165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25978215367491149207014213 4870915381404590476315165)
        ·
          refine ⟨1826593268026721428618187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4870915381404590476315165 1826593268026721428618187)
          ·
            refine ⟨2739889902040082142927281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1826593268026721428618187 2739889902040082142927281)
            ·
              refine ⟨2054917426530061607195461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2739889902040082142927281 2054917426530061607195461)
              ·
                refine ⟨385297017474386551349149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2054917426530061607195461 385297017474386551349149)
                ·
                  refine ⟨144486381552894956755931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385297017474386551349149 144486381552894956755931)
                  ·
                    rfl

theorem cell21_633119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 3].length) (baseStart_633119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633119 prefixEnd_633119 := by exact prefixLift 633119
  have htrace : WordTrace (prefixWord ++ tailWord_633119) baseStart_633119 baseEnd_633119 := by
    simpa [prefixWord, tailWord_633119, baseEnd_633119] using wordTrace_append hprefix tailTrace_633119
  have hstable : (prefixWord ++ tailWord_633119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633119).length < 2 ^ (prefixWord ++ tailWord_633119).sum := by decide
  have hdescent : baseEnd_633119 < baseStart_633119 := by decide
  rcases family_descends (prefixWord ++ tailWord_633119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633153 : List Nat := [1, 2, 5, 2, 2, 2, 1, 3, 3]
def baseStart_633153 : Nat := 118140960795 + 633153 * 2 ^ 59
def prefixEnd_633153 : Nat := 4983230072969 + 3 ^ 40 * 633153 * 2
def baseEnd_633153 : Nat := 144494140816118453189195

theorem tailTrace_633153 : CollatzResearch.WordTrace tailWord_633153 prefixEnd_633153 144494140816118453189195 := by
  unfold tailWord_633153
  simp only [CollatzResearch.WordTrace]
  refine ⟨23092987075202289768528113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15395324716801526512352075 23092987075202289768528113)
  ·
    refine ⟨17319740306401717326396085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23092987075202289768528113 17319740306401717326396085)
    ·
      refine ⟨1623725653725160999349633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17319740306401717326396085 1623725653725160999349633)
      ·
        refine ⟨1217794240293870749512225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1623725653725160999349633 1217794240293870749512225)
        ·
          refine ⟨913345680220403062134169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1217794240293870749512225 913345680220403062134169)
          ·
            refine ⟨685009260165302296600627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 913345680220403062134169 685009260165302296600627)
            ·
              refine ⟨1027513890247953444900941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685009260165302296600627 1027513890247953444900941)
              ·
                refine ⟨385317708842982541837853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1027513890247953444900941 385317708842982541837853)
                ·
                  refine ⟨144494140816118453189195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385317708842982541837853 144494140816118453189195)
                  ·
                    rfl

theorem cell21_633153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 3].length) (baseStart_633153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633153 prefixEnd_633153 := by exact prefixLift 633153
  have htrace : WordTrace (prefixWord ++ tailWord_633153) baseStart_633153 baseEnd_633153 := by
    simpa [prefixWord, tailWord_633153, baseEnd_633153] using wordTrace_append hprefix tailTrace_633153
  have hstable : (prefixWord ++ tailWord_633153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633153).length < 2 ^ (prefixWord ++ tailWord_633153).sum := by decide
  have hdescent : baseEnd_633153 < baseStart_633153 := by decide
  rcases family_descends (prefixWord ++ tailWord_633153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633237 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 5]
def baseStart_633237 : Nat := 118140960795 + 633237 * 2 ^ 59
def prefixEnd_633237 : Nat := 4983230072969 + 3 ^ 40 * 633237 * 2
def baseEnd_633237 : Nat := 144513310760552973789023

theorem tailTrace_633237 : CollatzResearch.WordTrace tailWord_633237 prefixEnd_633237 144513310760552973789023 := by
  unfold tailWord_633237
  simp only [CollatzResearch.WordTrace]
  refine ⟨23096050806897972114585965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15397367204598648076390643 23096050806897972114585965)
  ·
    refine ⟨8661019052586739542969737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23096050806897972114585965 8661019052586739542969737)
    ·
      refine ⟨6495764289440054657227303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8661019052586739542969737 6495764289440054657227303)
      ·
        refine ⟨9743646434160081985840955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6495764289440054657227303 9743646434160081985840955)
        ·
          refine ⟨14615469651240122978761433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9743646434160081985840955 14615469651240122978761433)
          ·
            refine ⟨10961602238430092234071075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14615469651240122978761433 10961602238430092234071075)
            ·
              refine ⟨16442403357645138351106613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10961602238430092234071075 16442403357645138351106613)
              ·
                refine ⟨1541475314779231720416245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16442403357645138351106613 1541475314779231720416245)
                ·
                  refine ⟨144513310760552973789023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1541475314779231720416245 144513310760552973789023)
                  ·
                    rfl

theorem cell21_633237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_633237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633237 prefixEnd_633237 := by exact prefixLift 633237
  have htrace : WordTrace (prefixWord ++ tailWord_633237) baseStart_633237 baseEnd_633237 := by
    simpa [prefixWord, tailWord_633237, baseEnd_633237] using wordTrace_append hprefix tailTrace_633237
  have hstable : (prefixWord ++ tailWord_633237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633237).length < 2 ^ (prefixWord ++ tailWord_633237).sum := by decide
  have hdescent : baseEnd_633237 < baseStart_633237 := by decide
  rcases family_descends (prefixWord ++ tailWord_633237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633240 : List Nat := [2, 1, 2, 5, 1, 3, 1, 6]
def baseStart_633240 : Nat := 118140960795 + 633240 * 2 ^ 59
def prefixEnd_633240 : Nat := 4983230072969 + 3 ^ 40 * 633240 * 2
def baseEnd_633240 : Nat := 48171331800475211746339

theorem tailTrace_633240 : CollatzResearch.WordTrace tailWord_633240 prefixEnd_633240 48171331800475211746339 := by
  unfold tailWord_633240
  simp only [CollatzResearch.WordTrace]
  refine ⟨11548080112943551813472587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15397440150591402417963449 11548080112943551813472587)
  ·
    refine ⟨17322120169415327720208881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11548080112943551813472587 17322120169415327720208881)
    ·
      refine ⟨12991590127061495790156661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17322120169415327720208881 12991590127061495790156661)
      ·
        refine ⟨1217961574412015230327187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12991590127061495790156661 1217961574412015230327187)
        ·
          refine ⟨1826942361618022845490781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217961574412015230327187 1826942361618022845490781)
          ·
            refine ⟨685103385606758567059043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1826942361618022845490781 685103385606758567059043)
            ·
              refine ⟨1027655078410137850588565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685103385606758567059043 1027655078410137850588565)
              ·
                refine ⟨48171331800475211746339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1027655078410137850588565 48171331800475211746339)
                ·
                  rfl

theorem cell21_633240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 6].length) (baseStart_633240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633240 prefixEnd_633240 := by exact prefixLift 633240
  have htrace : WordTrace (prefixWord ++ tailWord_633240) baseStart_633240 baseEnd_633240 := by
    simpa [prefixWord, tailWord_633240, baseEnd_633240] using wordTrace_append hprefix tailTrace_633240
  have hstable : (prefixWord ++ tailWord_633240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633240).length < 2 ^ (prefixWord ++ tailWord_633240).sum := by decide
  have hdescent : baseEnd_633240 < baseStart_633240 := by decide
  rcases family_descends (prefixWord ++ tailWord_633240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633271 : List Nat := [1, 1, 3, 1, 3, 4, 2, 3, 3]
def baseStart_633271 : Nat := 118140960795 + 633271 * 2 ^ 59
def prefixEnd_633271 : Nat := 4983230072969 + 3 ^ 40 * 633271 * 2
def baseEnd_633271 : Nat := 144521070023776470222287

theorem tailTrace_633271 : CollatzResearch.WordTrace tailWord_633271 prefixEnd_633271 144521070023776470222287 := by
  unfold tailWord_633271
  simp only [CollatzResearch.WordTrace]
  refine ⟨23097290888774795921323667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15398193925849863947549111 23097290888774795921323667)
  ·
    refine ⟨34645936333162193881985501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23097290888774795921323667 34645936333162193881985501)
    ·
      refine ⟨12992226124935822705744563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34645936333162193881985501 12992226124935822705744563)
      ·
        refine ⟨19488339187403734058616845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12992226124935822705744563 19488339187403734058616845)
        ·
          refine ⟨7308127195276400271981317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19488339187403734058616845 7308127195276400271981317)
          ·
            refine ⟨1370273849114325050996497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7308127195276400271981317 1370273849114325050996497)
            ·
              refine ⟨1027705386835743788247373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1370273849114325050996497 1027705386835743788247373)
              ·
                refine ⟨385389520063403920592765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1027705386835743788247373 385389520063403920592765)
                ·
                  refine ⟨144521070023776470222287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385389520063403920592765 144521070023776470222287)
                  ·
                    rfl

theorem cell21_633271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 3].length) (baseStart_633271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633271 prefixEnd_633271 := by exact prefixLift 633271
  have htrace : WordTrace (prefixWord ++ tailWord_633271) baseStart_633271 baseEnd_633271 := by
    simpa [prefixWord, tailWord_633271, baseEnd_633271] using wordTrace_append hprefix tailTrace_633271
  have hstable : (prefixWord ++ tailWord_633271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633271).length < 2 ^ (prefixWord ++ tailWord_633271).sum := by decide
  have hdescent : baseEnd_633271 < baseStart_633271 := by decide
  rcases family_descends (prefixWord ++ tailWord_633271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633313 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 5]
def baseStart_633313 : Nat := 118140960795 + 633313 * 2 ^ 59
def prefixEnd_633313 : Nat := 4983230072969 + 3 ^ 40 * 633313 * 2
def baseEnd_633313 : Nat := 144530654995993730522201

theorem tailTrace_633313 : CollatzResearch.WordTrace tailWord_633313 prefixEnd_633313 144530654995993730522201 := by
  unfold tailWord_633313
  simp only [CollatzResearch.WordTrace]
  refine ⟨23098822754622637094352593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15399215169748424729568395 23098822754622637094352593)
  ·
    refine ⟨17324117065966977820764445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23098822754622637094352593 17324117065966977820764445)
    ·
      refine ⟨6496543899737616682786667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17324117065966977820764445 6496543899737616682786667)
      ·
        refine ⟨9744815849606425024180001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6496543899737616682786667 9744815849606425024180001)
        ·
          refine ⟨7308611887204818768135001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9744815849606425024180001 7308611887204818768135001)
          ·
            refine ⟨5481458915403614076101251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7308611887204818768135001 5481458915403614076101251)
            ·
              refine ⟨8222188373105421114151877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5481458915403614076101251 8222188373105421114151877)
              ·
                refine ⟨1541660319957266458903477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8222188373105421114151877 1541660319957266458903477)
                ·
                  refine ⟨144530654995993730522201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1541660319957266458903477 144530654995993730522201)
                  ·
                    rfl

theorem cell21_633313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_633313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633313 prefixEnd_633313 := by exact prefixLift 633313
  have htrace : WordTrace (prefixWord ++ tailWord_633313) baseStart_633313 baseEnd_633313 := by
    simpa [prefixWord, tailWord_633313, baseEnd_633313] using wordTrace_append hprefix tailTrace_633313
  have hstable : (prefixWord ++ tailWord_633313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633313).length < 2 ^ (prefixWord ++ tailWord_633313).sum := by decide
  have hdescent : baseEnd_633313 < baseStart_633313 := by decide
  rcases family_descends (prefixWord ++ tailWord_633313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633333 : List Nat := [1, 3, 5, 1, 3, 1, 7]
def baseStart_633333 : Nat := 118140960795 + 633333 * 2 ^ 59
def prefixEnd_633333 : Nat := 4983230072969 + 3 ^ 40 * 633333 * 2
def baseEnd_633333 : Nat := 16059468807608682243203

theorem tailTrace_633333 : CollatzResearch.WordTrace tailWord_633333 prefixEnd_633333 16059468807608682243203 := by
  unfold tailWord_633333
  simp only [CollatzResearch.WordTrace]
  refine ⟨23099552214550180510080653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15399701476366787006720435 23099552214550180510080653)
  ·
    refine ⟨8662332080456317691280245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23099552214550180510080653 8662332080456317691280245)
    ·
      refine ⟨812093632542779783557523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8662332080456317691280245 812093632542779783557523)
      ·
        refine ⟨1218140448814169675336285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 812093632542779783557523 1218140448814169675336285)
        ·
          refine ⟨456802668305313628251107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1218140448814169675336285 456802668305313628251107)
          ·
            refine ⟨685204002457970442376661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456802668305313628251107 685204002457970442376661)
            ·
              refine ⟨16059468807608682243203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 685204002457970442376661 16059468807608682243203)
              ·
                rfl

theorem cell21_633333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 7].length) (baseStart_633333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633333 prefixEnd_633333 := by exact prefixLift 633333
  have htrace : WordTrace (prefixWord ++ tailWord_633333) baseStart_633333 baseEnd_633333 := by
    simpa [prefixWord, tailWord_633333, baseEnd_633333] using wordTrace_append hprefix tailTrace_633333
  have hstable : (prefixWord ++ tailWord_633333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633333).length < 2 ^ (prefixWord ++ tailWord_633333).sum := by decide
  have hdescent : baseEnd_633333 < baseStart_633333 := by decide
  rcases family_descends (prefixWord ++ tailWord_633333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633347 : List Nat := [1, 1, 1, 3, 2, 1, 7, 2, 3]
def baseStart_633347 : Nat := 118140960795 + 633347 * 2 ^ 59
def prefixEnd_633347 : Nat := 4983230072969 + 3 ^ 40 * 633347 * 2
def baseEnd_633347 : Nat := 144538414259217226955465

theorem tailTrace_633347 : CollatzResearch.WordTrace tailWord_633347 prefixEnd_633347 144538414259217226955465 := by
  unfold tailWord_633347
  simp only [CollatzResearch.WordTrace]
  refine ⟨23100062836499460901090295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15400041890999640600726863 23100062836499460901090295)
  ·
    refine ⟨34650094254749191351635443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23100062836499460901090295 34650094254749191351635443)
    ·
      refine ⟨51975141382123787027453165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34650094254749191351635443 51975141382123787027453165)
      ·
        refine ⟨19490678018296420135294937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51975141382123787027453165 19490678018296420135294937)
        ·
          refine ⟨14618008513722315101471203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19490678018296420135294937 14618008513722315101471203)
          ·
            refine ⟨21927012770583472652206805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14618008513722315101471203 21927012770583472652206805)
            ·
              refine ⟨513914361810550140286097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21927012770583472652206805 513914361810550140286097)
              ·
                refine ⟨385435771357912605214573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513914361810550140286097 385435771357912605214573)
                ·
                  refine ⟨144538414259217226955465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385435771357912605214573 144538414259217226955465)
                  ·
                    rfl

theorem cell21_633347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 3].length) (baseStart_633347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633347 prefixEnd_633347 := by exact prefixLift 633347
  have htrace : WordTrace (prefixWord ++ tailWord_633347) baseStart_633347 baseEnd_633347 := by
    simpa [prefixWord, tailWord_633347, baseEnd_633347] using wordTrace_append hprefix tailTrace_633347
  have hstable : (prefixWord ++ tailWord_633347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633347).length < 2 ^ (prefixWord ++ tailWord_633347).sum := by decide
  have hdescent : baseEnd_633347 < baseStart_633347 := by decide
  rcases family_descends (prefixWord ++ tailWord_633347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633350 : List Nat := [6, 2, 1, 1, 1, 2, 2, 6]
def baseStart_633350 : Nat := 118140960795 + 633350 * 2 ^ 59
def prefixEnd_633350 : Nat := 4983230072969 + 3 ^ 40 * 633350 * 2
def baseEnd_633350 : Nat := 48179699633363296135153

theorem tailTrace_633350 : CollatzResearch.WordTrace tailWord_633350 prefixEnd_633350 48179699633363296135153 := by
  unfold tailWord_633350
  simp only [CollatzResearch.WordTrace]
  refine ⟨721880382984018512920297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15400114836992394942299669 721880382984018512920297)
  ·
    refine ⟨541410287238013884690223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 721880382984018512920297 541410287238013884690223)
    ·
      refine ⟨812115430857020827035335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 541410287238013884690223 812115430857020827035335)
      ·
        refine ⟨1218173146285531240553003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 812115430857020827035335 1218173146285531240553003)
        ·
          refine ⟨1827259719428296860829505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1218173146285531240553003 1827259719428296860829505)
          ·
            refine ⟨1370444789571222645622129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1827259719428296860829505 1370444789571222645622129)
            ·
              refine ⟨1027833592178416984216597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1370444789571222645622129 1027833592178416984216597)
              ·
                refine ⟨48179699633363296135153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1027833592178416984216597 48179699633363296135153)
                ·
                  rfl

theorem cell21_633350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_633350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633350 prefixEnd_633350 := by exact prefixLift 633350
  have htrace : WordTrace (prefixWord ++ tailWord_633350) baseStart_633350 baseEnd_633350 := by
    simpa [prefixWord, tailWord_633350, baseEnd_633350] using wordTrace_append hprefix tailTrace_633350
  have hstable : (prefixWord ++ tailWord_633350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633350).length < 2 ^ (prefixWord ++ tailWord_633350).sum := by decide
  have hdescent : baseEnd_633350 < baseStart_633350 := by decide
  rcases family_descends (prefixWord ++ tailWord_633350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633420 : List Nat := [2, 2, 1, 3, 1, 2, 1, 5, 4]
def baseStart_633420 : Nat := 118140960795 + 633420 * 2 ^ 59
def prefixEnd_633420 : Nat := 4983230072969 + 3 ^ 40 * 633420 * 2
def baseEnd_633420 : Nat := 144555073853785322238649

theorem tailTrace_633420 : CollatzResearch.WordTrace tailWord_633420 prefixEnd_633420 144555073853785322238649 := by
  unfold tailWord_633420
  simp only [CollatzResearch.WordTrace]
  refine ⟨11551362682617497184248857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15401816910156662912331809 11551362682617497184248857)
  ·
    refine ⟨8663522011963122888186643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11551362682617497184248857 8663522011963122888186643)
    ·
      refine ⟨12995283017944684332279965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8663522011963122888186643 12995283017944684332279965)
      ·
        refine ⟨4873231131729256624604987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12995283017944684332279965 4873231131729256624604987)
        ·
          refine ⟨7309846697593884936907481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4873231131729256624604987 7309846697593884936907481)
          ·
            refine ⟨5482385023195413702680611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7309846697593884936907481 5482385023195413702680611)
            ·
              refine ⟨8223577534793120554020917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5482385023195413702680611 8223577534793120554020917)
              ·
                refine ⟨770960393886855051939461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8223577534793120554020917 770960393886855051939461)
                ·
                  refine ⟨144555073853785322238649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 770960393886855051939461 144555073853785322238649)
                  ·
                    rfl

theorem cell21_633420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_633420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633420 prefixEnd_633420 := by exact prefixLift 633420
  have htrace : WordTrace (prefixWord ++ tailWord_633420) baseStart_633420 baseEnd_633420 := by
    simpa [prefixWord, tailWord_633420, baseEnd_633420] using wordTrace_append hprefix tailTrace_633420
  have hstable : (prefixWord ++ tailWord_633420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633420).length < 2 ^ (prefixWord ++ tailWord_633420).sum := by decide
  have hdescent : baseEnd_633420 < baseStart_633420 := by decide
  rcases family_descends (prefixWord ++ tailWord_633420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633454 : List Nat := [4, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_633454 : Nat := 118140960795 + 633454 * 2 ^ 59
def prefixEnd_633454 : Nat := 4983230072969 + 3 ^ 40 * 633454 * 2
def baseEnd_633454 : Nat := 144562833117008818671913

theorem tailTrace_633454 : CollatzResearch.WordTrace tailWord_633454 prefixEnd_633454 144562833117008818671913 := by
  unfold tailWord_633454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2887995680888977271904427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15402643631407878783490277 2887995680888977271904427)
  ·
    refine ⟨4331993521333465907856641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2887995680888977271904427 4331993521333465907856641)
    ·
      refine ⟨3248995141000099430892481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4331993521333465907856641 3248995141000099430892481)
      ·
        refine ⟨2436746355750074573169361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3248995141000099430892481 2436746355750074573169361)
        ·
          refine ⟨1827559766812555929877021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2436746355750074573169361 1827559766812555929877021)
          ·
            refine ⟨685334912554708473703883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1827559766812555929877021 685334912554708473703883)
            ·
              refine ⟨1028002368832062710555825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685334912554708473703883 1028002368832062710555825)
              ·
                refine ⟨771001776624047032916869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1028002368832062710555825 771001776624047032916869)
                ·
                  refine ⟨144562833117008818671913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 771001776624047032916869 144562833117008818671913)
                  ·
                    rfl

theorem cell21_633454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_633454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633454 prefixEnd_633454 := by exact prefixLift 633454
  have htrace : WordTrace (prefixWord ++ tailWord_633454) baseStart_633454 baseEnd_633454 := by
    simpa [prefixWord, tailWord_633454, baseEnd_633454] using wordTrace_append hprefix tailTrace_633454
  have hstable : (prefixWord ++ tailWord_633454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633454).length < 2 ^ (prefixWord ++ tailWord_633454).sum := by decide
  have hdescent : baseEnd_633454 < baseStart_633454 := by decide
  rcases family_descends (prefixWord ++ tailWord_633454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633465 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 5]
def baseStart_633465 : Nat := 118140960795 + 633465 * 2 ^ 59
def prefixEnd_633465 : Nat := 4983230072969 + 3 ^ 40 * 633465 * 2
def baseEnd_633465 : Nat := 144565343466875243988557

theorem tailTrace_633465 : CollatzResearch.WordTrace tailWord_633465 prefixEnd_633465 144565343466875243988557 := by
  unfold tailWord_633465
  simp only [CollatzResearch.WordTrace]
  refine ⟨23104366650071967053885849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15402911100047978035923899 23104366650071967053885849)
  ·
    refine ⟨17328274987553975290414387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23104366650071967053885849 17328274987553975290414387)
    ·
      refine ⟨25992412481330962935621581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17328274987553975290414387 25992412481330962935621581)
      ·
        refine ⟨9747154680499111100858093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25992412481330962935621581 9747154680499111100858093)
        ·
          refine ⟨3655183005187166662821785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9747154680499111100858093 3655183005187166662821785)
          ·
            refine ⟨2741387253890374997116339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3655183005187166662821785 2741387253890374997116339)
            ·
              refine ⟨4112080880835562495674509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2741387253890374997116339 4112080880835562495674509)
              ·
                refine ⟨1542030330313335935877941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4112080880835562495674509 1542030330313335935877941)
                ·
                  refine ⟨144565343466875243988557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1542030330313335935877941 144565343466875243988557)
                  ·
                    rfl

theorem cell21_633465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_633465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633465 prefixEnd_633465 := by exact prefixLift 633465
  have htrace : WordTrace (prefixWord ++ tailWord_633465) baseStart_633465 baseEnd_633465 := by
    simpa [prefixWord, tailWord_633465, baseEnd_633465] using wordTrace_append hprefix tailTrace_633465
  have hstable : (prefixWord ++ tailWord_633465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633465).length < 2 ^ (prefixWord ++ tailWord_633465).sum := by decide
  have hdescent : baseEnd_633465 < baseStart_633465 := by decide
  rcases family_descends (prefixWord ++ tailWord_633465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633527 : List Nat := [1, 1, 3, 1, 6, 1, 2, 6]
def baseStart_633527 : Nat := 118140960795 + 633527 * 2 ^ 59
def prefixEnd_633527 : Nat := 4983230072969 + 3 ^ 40 * 633527 * 2
def baseEnd_633527 : Nat := 48193164237192304651699

theorem tailTrace_633527 : CollatzResearch.WordTrace tailWord_633527 prefixEnd_633527 48193164237192304651699 := by
  unfold tailWord_633527
  simp only [CollatzResearch.WordTrace]
  refine ⟨23106627975847351642642835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15404418650564901095095223 23106627975847351642642835)
  ·
    refine ⟨34659941963771027463964253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23106627975847351642642835 34659941963771027463964253)
    ·
      refine ⟨12997478236414135298986595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34659941963771027463964253 12997478236414135298986595)
      ·
        refine ⟨19496217354621202948479893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12997478236414135298986595 19496217354621202948479893)
        ·
          refine ⟨913885188497868888209995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19496217354621202948479893 913885188497868888209995)
          ·
            refine ⟨1370827782746803332314993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913885188497868888209995 1370827782746803332314993)
            ·
              refine ⟨1028120837060102499236245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1370827782746803332314993 1028120837060102499236245)
              ·
                refine ⟨48193164237192304651699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1028120837060102499236245 48193164237192304651699)
                ·
                  rfl

theorem cell21_633527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 6].length) (baseStart_633527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633527 prefixEnd_633527 := by exact prefixLift 633527
  have htrace : WordTrace (prefixWord ++ tailWord_633527) baseStart_633527 baseEnd_633527 := by
    simpa [prefixWord, tailWord_633527, baseEnd_633527] using wordTrace_append hprefix tailTrace_633527
  have hstable : (prefixWord ++ tailWord_633527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633527).length < 2 ^ (prefixWord ++ tailWord_633527).sum := by decide
  have hdescent : baseEnd_633527 < baseStart_633527 := by decide
  rcases family_descends (prefixWord ++ tailWord_633527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633572 : List Nat := [2, 3, 1, 1, 1, 4, 1, 4, 4]
def baseStart_633572 : Nat := 118140960795 + 633572 * 2 ^ 59
def prefixEnd_633572 : Nat := 4983230072969 + 3 ^ 40 * 633572 * 2
def baseEnd_633572 : Nat := 144589762324666835705005

theorem tailTrace_633572 : CollatzResearch.WordTrace tailWord_633572 prefixEnd_633572 144589762324666835705005 := by
  unfold tailWord_633572
  simp only [CollatzResearch.WordTrace]
  refine ⟨11554134630342162164015485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15405512840456216218687313 11554134630342162164015485)
  ·
    refine ⟨4332800486378310811505807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11554134630342162164015485 4332800486378310811505807)
    ·
      refine ⟨6499200729567466217258711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4332800486378310811505807 6499200729567466217258711)
      ·
        refine ⟨9748801094351199325888067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6499200729567466217258711 9748801094351199325888067)
        ·
          refine ⟨14623201641526798988832101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9748801094351199325888067 14623201641526798988832101)
          ·
            refine ⟨2741850307786274810406019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14623201641526798988832101 2741850307786274810406019)
            ·
              refine ⟨4112775461679412215609029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2741850307786274810406019 4112775461679412215609029)
              ·
                refine ⟨771145399064889790426693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4112775461679412215609029 771145399064889790426693)
                ·
                  refine ⟨144589762324666835705005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 771145399064889790426693 144589762324666835705005)
                  ·
                    rfl

theorem cell21_633572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_633572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633572 prefixEnd_633572 := by exact prefixLift 633572
  have htrace : WordTrace (prefixWord ++ tailWord_633572) baseStart_633572 baseEnd_633572 := by
    simpa [prefixWord, tailWord_633572, baseEnd_633572] using wordTrace_append hprefix tailTrace_633572
  have hstable : (prefixWord ++ tailWord_633572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633572).length < 2 ^ (prefixWord ++ tailWord_633572).sum := by decide
  have hdescent : baseEnd_633572 < baseStart_633572 := by decide
  rcases family_descends (prefixWord ++ tailWord_633572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633634 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 5]
def baseStart_633634 : Nat := 118140960795 + 633634 * 2 ^ 59
def prefixEnd_633634 : Nat := 4983230072969 + 3 ^ 40 * 633634 * 2
def baseEnd_633634 : Nat := 144603911569368505671545

theorem tailTrace_633634 : CollatzResearch.WordTrace tailWord_633634 prefixEnd_633634 144603911569368505671545 := by
  unfold tailWord_633634
  simp only [CollatzResearch.WordTrace]
  refine ⟨5777632646614927229196989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15407020390973139277858637 5777632646614927229196989)
  ·
    refine ⟨2166612242480597710948871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5777632646614927229196989 2166612242480597710948871)
    ·
      refine ⟨3249918363720896566423307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2166612242480597710948871 3249918363720896566423307)
      ·
        refine ⟨4874877545581344849634961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3249918363720896566423307 4874877545581344849634961)
        ·
          refine ⟨3656158159186008637226221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4874877545581344849634961 3656158159186008637226221)
          ·
            refine ⟨1371059309694753238959833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3656158159186008637226221 1371059309694753238959833)
            ·
              refine ⟨1028294482271064929219875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1371059309694753238959833 1028294482271064929219875)
              ·
                refine ⟨1542441723406597393829813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028294482271064929219875 1542441723406597393829813)
                ·
                  refine ⟨144603911569368505671545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1542441723406597393829813 144603911569368505671545)
                  ·
                    rfl

theorem cell21_633634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_633634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633634 prefixEnd_633634 := by exact prefixLift 633634
  have htrace : WordTrace (prefixWord ++ tailWord_633634) baseStart_633634 baseEnd_633634 := by
    simpa [prefixWord, tailWord_633634, baseEnd_633634] using wordTrace_append hprefix tailTrace_633634
  have hstable : (prefixWord ++ tailWord_633634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633634).length < 2 ^ (prefixWord ++ tailWord_633634).sum := by decide
  have hdescent : baseEnd_633634 < baseStart_633634 := by decide
  rcases family_descends (prefixWord ++ tailWord_633634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633654 : List Nat := [5, 1, 2, 2, 3, 1, 2, 5]
def baseStart_633654 : Nat := 118140960795 + 633654 * 2 ^ 59
def prefixEnd_633654 : Nat := 4983230072969 + 3 ^ 40 * 633654 * 2
def baseEnd_633654 : Nat := 48202825280617638446057

theorem tailTrace_633654 : CollatzResearch.WordTrace tailWord_633654 prefixEnd_633654 48202825280617638446057 := by
  unfold tailWord_633654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1444453752899203270782251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15407506697591501555010677 1444453752899203270782251)
  ·
    refine ⟨2166680629348804906173377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1444453752899203270782251 2166680629348804906173377)
    ·
      refine ⟨1625010472011603679630033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2166680629348804906173377 1625010472011603679630033)
      ·
        refine ⟨1218757854008702759722525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1625010472011603679630033 1218757854008702759722525)
        ·
          refine ⟨457034195253263534895947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1218757854008702759722525 457034195253263534895947)
          ·
            refine ⟨685551292879895302343921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457034195253263534895947 685551292879895302343921)
            ·
              refine ⟨514163469659921476757941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 685551292879895302343921 514163469659921476757941)
              ·
                refine ⟨48202825280617638446057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 514163469659921476757941 48202825280617638446057)
                ·
                  rfl

theorem cell21_633654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_633654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633654 prefixEnd_633654 := by exact prefixLift 633654
  have htrace : WordTrace (prefixWord ++ tailWord_633654) baseStart_633654 baseEnd_633654 := by
    simpa [prefixWord, tailWord_633654, baseEnd_633654] using wordTrace_append hprefix tailTrace_633654
  have hstable : (prefixWord ++ tailWord_633654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633654).length < 2 ^ (prefixWord ++ tailWord_633654).sum := by decide
  have hdescent : baseEnd_633654 < baseStart_633654 := by decide
  rcases family_descends (prefixWord ++ tailWord_633654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633738 : List Nat := [3, 1, 2, 4, 1, 10]
def baseStart_633738 : Nat := 118140960795 + 633738 * 2 ^ 59
def prefixEnd_633738 : Nat := 4983230072969 + 3 ^ 40 * 633738 * 2
def baseEnd_633738 : Nat := 5356579473566201331037

theorem tailTrace_633738 : CollatzResearch.WordTrace tailWord_633738 prefixEnd_633738 5356579473566201331037 := by
  unfold tailWord_633738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5778580944520733669643467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15409549185388623119049245 5778580944520733669643467)
  ·
    refine ⟨8667871416781100504465201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5778580944520733669643467 8667871416781100504465201)
    ·
      refine ⟨6500903562585825378348901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8667871416781100504465201 6500903562585825378348901)
      ·
        refine ⟨1218919417984842258440419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6500903562585825378348901 1218919417984842258440419)
        ·
          refine ⟨1828379126977263387660629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1218919417984842258440419 1828379126977263387660629)
          ·
            refine ⟨5356579473566201331037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1828379126977263387660629 5356579473566201331037)
            ·
              rfl

theorem cell21_633738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 10].length) (baseStart_633738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633738 prefixEnd_633738 := by exact prefixLift 633738
  have htrace : WordTrace (prefixWord ++ tailWord_633738) baseStart_633738 baseEnd_633738 := by
    simpa [prefixWord, tailWord_633738, baseEnd_633738] using wordTrace_append hprefix tailTrace_633738
  have hstable : (prefixWord ++ tailWord_633738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633738).length < 2 ^ (prefixWord ++ tailWord_633738).sum := by decide
  have hdescent : baseEnd_633738 < baseStart_633738 := by decide
  rcases family_descends (prefixWord ++ tailWord_633738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633786 : List Nat := [3, 1, 1, 1, 2, 1, 6, 3, 3]
def baseStart_633786 : Nat := 118140960795 + 633786 * 2 ^ 59
def prefixEnd_633786 : Nat := 4983230072969 + 3 ^ 40 * 633786 * 2
def baseEnd_633786 : Nat := 144638600040250019137901

theorem tailTrace_633786 : CollatzResearch.WordTrace tailWord_633786 prefixEnd_633786 144638600040250019137901 := by
  unfold tailWord_633786
  simp only [CollatzResearch.WordTrace]
  refine ⟨5779018620477259719080303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15410716321272692584214141 5779018620477259719080303)
  ·
    refine ⟨8668527930715889578620455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5779018620477259719080303 8668527930715889578620455)
    ·
      refine ⟨13002791896073834367930683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8668527930715889578620455 13002791896073834367930683)
      ·
        refine ⟨19504187844110751551896025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13002791896073834367930683 19504187844110751551896025)
        ·
          refine ⟨14628140883083063663922019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19504187844110751551896025 14628140883083063663922019)
          ·
            refine ⟨21942211324624595495883029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14628140883083063663922019 21942211324624595495883029)
            ·
              refine ⟨1028541155841777913869517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21942211324624595495883029 1028541155841777913869517)
              ·
                refine ⟨385702933440666717701069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1028541155841777913869517 385702933440666717701069)
                ·
                  refine ⟨144638600040250019137901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385702933440666717701069 144638600040250019137901)
                  ·
                    rfl

theorem cell21_633786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_633786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633786 prefixEnd_633786 := by exact prefixLift 633786
  have htrace : WordTrace (prefixWord ++ tailWord_633786) baseStart_633786 baseEnd_633786 := by
    simpa [prefixWord, tailWord_633786, baseEnd_633786] using wordTrace_append hprefix tailTrace_633786
  have hstable : (prefixWord ++ tailWord_633786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633786).length < 2 ^ (prefixWord ++ tailWord_633786).sum := by decide
  have hdescent : baseEnd_633786 < baseStart_633786 := by decide
  rcases family_descends (prefixWord ++ tailWord_633786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633800 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 6]
def baseStart_633800 : Nat := 118140960795 + 633800 * 2 ^ 59
def prefixEnd_633800 : Nat := 4983230072969 + 3 ^ 40 * 633800 * 2
def baseEnd_633800 : Nat := 144641795030989105904539

theorem tailTrace_633800 : CollatzResearch.WordTrace tailWord_633800 prefixEnd_633800 144641795030989105904539 := by
  unfold tailWord_633800
  simp only [CollatzResearch.WordTrace]
  refine ⟨11558292551929159633665427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15411056735905546178220569 11558292551929159633665427)
  ·
    refine ⟨17337438827893739450498141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11558292551929159633665427 17337438827893739450498141)
    ·
      refine ⟨6501539560460152293936803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17337438827893739450498141 6501539560460152293936803)
      ·
        refine ⟨9752309340690228440905205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6501539560460152293936803 9752309340690228440905205)
        ·
          refine ⟨914279000689708916334863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9752309340690228440905205 914279000689708916334863)
          ·
            refine ⟨1371418501034563374502295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914279000689708916334863 1371418501034563374502295)
            ·
              refine ⟨2057127751551845061753443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1371418501034563374502295 2057127751551845061753443)
              ·
                refine ⟨3085691627327767592630165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2057127751551845061753443 3085691627327767592630165)
                ·
                  refine ⟨144641795030989105904539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3085691627327767592630165 144641795030989105904539)
                  ·
                    rfl

theorem cell21_633800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_633800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633800 prefixEnd_633800 := by exact prefixLift 633800
  have htrace : WordTrace (prefixWord ++ tailWord_633800) baseStart_633800 baseEnd_633800 := by
    simpa [prefixWord, tailWord_633800, baseEnd_633800] using wordTrace_append hprefix tailTrace_633800
  have hstable : (prefixWord ++ tailWord_633800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633800).length < 2 ^ (prefixWord ++ tailWord_633800).sum := by decide
  have hdescent : baseEnd_633800 < baseStart_633800 := by decide
  rcases family_descends (prefixWord ++ tailWord_633800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633817 : List Nat := [1, 2, 1, 2, 5, 2, 3, 1, 4]
def baseStart_633817 : Nat := 118140960795 + 633817 * 2 ^ 59
def prefixEnd_633817 : Nat := 4983230072969 + 3 ^ 40 * 633817 * 2
def baseEnd_633817 : Nat := 144645674662600854121171

theorem tailTrace_633817 : CollatzResearch.WordTrace tailWord_633817 prefixEnd_633817 144645674662600854121171 := by
  unfold tailWord_633817
  simp only [CollatzResearch.WordTrace]
  refine ⟨23117205144796731170699705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15411470096531154113799803 23117205144796731170699705)
  ·
    refine ⟨17337903858597548378024779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23117205144796731170699705 17337903858597548378024779)
    ·
      refine ⟨26006855787896322567037169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17337903858597548378024779 26006855787896322567037169)
      ·
        refine ⟨19505141840922241925277877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26006855787896322567037169 19505141840922241925277877)
        ·
          refine ⟨1828607047586460180494801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19505141840922241925277877 1828607047586460180494801)
          ·
            refine ⟨1371455285689845135371101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1828607047586460180494801 1371455285689845135371101)
            ·
              refine ⟨514295732133691925764163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1371455285689845135371101 514295732133691925764163)
              ·
                refine ⟨771443598200537888646245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514295732133691925764163 771443598200537888646245)
                ·
                  refine ⟨144645674662600854121171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 771443598200537888646245 144645674662600854121171)
                  ·
                    rfl

theorem cell21_633817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 4].length) (baseStart_633817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633817 prefixEnd_633817 := by exact prefixLift 633817
  have htrace : WordTrace (prefixWord ++ tailWord_633817) baseStart_633817 baseEnd_633817 := by
    simpa [prefixWord, tailWord_633817, baseEnd_633817] using wordTrace_append hprefix tailTrace_633817
  have hstable : (prefixWord ++ tailWord_633817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633817).length < 2 ^ (prefixWord ++ tailWord_633817).sum := by decide
  have hdescent : baseEnd_633817 < baseStart_633817 := by decide
  rcases family_descends (prefixWord ++ tailWord_633817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633828 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 7]
def baseStart_633828 : Nat := 118140960795 + 633828 * 2 ^ 59
def prefixEnd_633828 : Nat := 4983230072969 + 3 ^ 40 * 633828 * 2
def baseEnd_633828 : Nat := 144648185012467279437815

theorem tailTrace_633828 : CollatzResearch.WordTrace tailWord_633828 prefixEnd_633828 144648185012467279437815 := by
  unfold tailWord_633828
  simp only [CollatzResearch.WordTrace]
  refine ⟨11558803173878440024675069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15411737565171253366233425 11558803173878440024675069)
  ·
    refine ⟨4334551190204415009253151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11558803173878440024675069 4334551190204415009253151)
    ·
      refine ⟨6501826785306622513879727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4334551190204415009253151 6501826785306622513879727)
      ·
        refine ⟨9752740177959933770819591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6501826785306622513879727 9752740177959933770819591)
        ·
          refine ⟨14629110266939900656229387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9752740177959933770819591 14629110266939900656229387)
          ·
            refine ⟨21943665400409850984344081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14629110266939900656229387 21943665400409850984344081)
            ·
              refine ⟨16457749050307388238258061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21943665400409850984344081 16457749050307388238258061)
              ·
                refine ⟨6171655893865270589346773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16457749050307388238258061 6171655893865270589346773)
                ·
                  refine ⟨144648185012467279437815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6171655893865270589346773 144648185012467279437815)
                  ·
                    rfl

theorem cell21_633828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_633828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633828 prefixEnd_633828 := by exact prefixLift 633828
  have htrace : WordTrace (prefixWord ++ tailWord_633828) baseStart_633828 baseEnd_633828 := by
    simpa [prefixWord, tailWord_633828, baseEnd_633828] using wordTrace_append hprefix tailTrace_633828
  have hstable : (prefixWord ++ tailWord_633828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633828).length < 2 ^ (prefixWord ++ tailWord_633828).sum := by decide
  have hdescent : baseEnd_633828 < baseStart_633828 := by decide
  rcases family_descends (prefixWord ++ tailWord_633828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633831 : List Nat := [1, 1, 5, 2, 2, 1, 4, 5]
def baseStart_633831 : Nat := 118140960795 + 633831 * 2 ^ 59
def prefixEnd_633831 : Nat := 4983230072969 + 3 ^ 40 * 633831 * 2
def baseEnd_633831 : Nat := 48216289884446646962603

theorem tailTrace_633831 : CollatzResearch.WordTrace tailWord_633831 prefixEnd_633831 48216289884446646962603 := by
  unfold tailWord_633831
  simp only [CollatzResearch.WordTrace]
  refine ⟨23117715766746011561709347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15411810511164007707806231 23117715766746011561709347)
  ·
    refine ⟨34676573650119017342564021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23117715766746011561709347 34676573650119017342564021)
    ·
      refine ⟨3250928779698657875865377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34676573650119017342564021 3250928779698657875865377)
      ·
        refine ⟨2438196584773993406899033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3250928779698657875865377 2438196584773993406899033)
        ·
          refine ⟨1828647438580495055174275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2438196584773993406899033 1828647438580495055174275)
          ·
            refine ⟨2742971157870742582761413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1828647438580495055174275 2742971157870742582761413)
            ·
              refine ⟨514307092100764234267765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2742971157870742582761413 514307092100764234267765)
              ·
                refine ⟨48216289884446646962603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 514307092100764234267765 48216289884446646962603)
                ·
                  rfl

theorem cell21_633831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 5].length) (baseStart_633831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633831 prefixEnd_633831 := by exact prefixLift 633831
  have htrace : WordTrace (prefixWord ++ tailWord_633831) baseStart_633831 baseEnd_633831 := by
    simpa [prefixWord, tailWord_633831, baseEnd_633831] using wordTrace_append hprefix tailTrace_633831
  have hstable : (prefixWord ++ tailWord_633831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633831).length < 2 ^ (prefixWord ++ tailWord_633831).sum := by decide
  have hdescent : baseEnd_633831 < baseStart_633831 := by decide
  rcases family_descends (prefixWord ++ tailWord_633831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633890 : List Nat := [3, 3, 1, 1, 1, 3, 2, 7]
def baseStart_633890 : Nat := 118140960795 + 633890 * 2 ^ 59
def prefixEnd_633890 : Nat := 4983230072969 + 3 ^ 40 * 633890 * 2
def baseEnd_633890 : Nat := 48220778085722983134785

theorem tailTrace_633890 : CollatzResearch.WordTrace tailWord_633890 prefixEnd_633890 48220778085722983134785 := by
  unfold tailWord_633890
  simp only [CollatzResearch.WordTrace]
  refine ⟨5779966918383066159526781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15413245115688176425404749 5779966918383066159526781)
  ·
    refine ⟨2167487594393649809822543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5779966918383066159526781 2167487594393649809822543)
    ·
      refine ⟨3251231391590474714733815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2167487594393649809822543 3251231391590474714733815)
      ·
        refine ⟨4876847087385712072100723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3251231391590474714733815 4876847087385712072100723)
        ·
          refine ⟨7315270631078568108151085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4876847087385712072100723 7315270631078568108151085)
          ·
            refine ⟨2743226486654463040556657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7315270631078568108151085 2743226486654463040556657)
            ·
              refine ⟨2057419864990847280417493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2743226486654463040556657 2057419864990847280417493)
              ·
                refine ⟨48220778085722983134785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2057419864990847280417493 48220778085722983134785)
                ·
                  rfl

theorem cell21_633890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_633890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633890 prefixEnd_633890 := by exact prefixLift 633890
  have htrace : WordTrace (prefixWord ++ tailWord_633890) baseStart_633890 baseEnd_633890 := by
    simpa [prefixWord, tailWord_633890, baseEnd_633890] using wordTrace_append hprefix tailTrace_633890
  have hstable : (prefixWord ++ tailWord_633890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633890).length < 2 ^ (prefixWord ++ tailWord_633890).sum := by decide
  have hdescent : baseEnd_633890 < baseStart_633890 := by decide
  rcases family_descends (prefixWord ++ tailWord_633890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633966 : List Nat := [4, 1, 2, 2, 1, 3, 8]
def baseStart_633966 : Nat := 118140960795 + 633966 * 2 ^ 59
def prefixEnd_633966 : Nat := 4983230072969 + 3 ^ 40 * 633966 * 2
def baseEnd_633966 : Nat := 16075519832512189570837

theorem tailTrace_633966 : CollatzResearch.WordTrace tailWord_633966 prefixEnd_633966 16075519832512189570837 := by
  unfold tailWord_633966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2890329952657116202234219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15415093080837953078582501 2890329952657116202234219)
  ·
    refine ⟨4335494928985674303351329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2890329952657116202234219 4335494928985674303351329)
    ·
      refine ⟨3251621196739255727513497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4335494928985674303351329 3251621196739255727513497)
      ·
        refine ⟨2438715897554441795635123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3251621196739255727513497 2438715897554441795635123)
        ·
          refine ⟨3658073846331662693452685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2438715897554441795635123 3658073846331662693452685)
          ·
            refine ⟨1371777692374373510044757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3658073846331662693452685 1371777692374373510044757)
            ·
              refine ⟨16075519832512189570837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1371777692374373510044757 16075519832512189570837)
              ·
                rfl

theorem cell21_633966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 8].length) (baseStart_633966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_633966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_633966 prefixEnd_633966 := by exact prefixLift 633966
  have htrace : WordTrace (prefixWord ++ tailWord_633966) baseStart_633966 baseEnd_633966 := by
    simpa [prefixWord, tailWord_633966, baseEnd_633966] using wordTrace_append hprefix tailTrace_633966
  have hstable : (prefixWord ++ tailWord_633966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633966).length < 2 ^ (prefixWord ++ tailWord_633966).sum := by decide
  have hdescent : baseEnd_633966 < baseStart_633966 := by decide
  rcases family_descends (prefixWord ++ tailWord_633966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634056 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 5]
def baseStart_634056 : Nat := 118140960795 + 634056 * 2 ^ 59
def prefixEnd_634056 : Nat := 4983230072969 + 3 ^ 40 * 634056 * 2
def baseEnd_634056 : Nat := 144700217718789549637349

theorem tailTrace_634056 : CollatzResearch.WordTrace tailWord_634056 prefixEnd_634056 144700217718789549637349 := by
  unfold tailWord_634056
  simp only [CollatzResearch.WordTrace]
  refine ⟨11562961095465437494325011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15417281460620583325766681 11562961095465437494325011)
  ·
    refine ⟨17344441643198156241487517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11562961095465437494325011 17344441643198156241487517)
    ·
      refine ⟨6504165616199308590557819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17344441643198156241487517 6504165616199308590557819)
      ·
        refine ⟨9756248424298962885836729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6504165616199308590557819 9756248424298962885836729)
        ·
          refine ⟨7317186318224222164377547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9756248424298962885836729 7317186318224222164377547)
          ·
            refine ⟨10975779477336333246566321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7317186318224222164377547 10975779477336333246566321)
            ·
              refine ⟨8231834608002249934924741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10975779477336333246566321 8231834608002249934924741)
              ·
                refine ⟨1543468989000421862798389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8231834608002249934924741 1543468989000421862798389)
                ·
                  refine ⟨144700217718789549637349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1543468989000421862798389 144700217718789549637349)
                  ·
                    rfl

theorem cell21_634056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_634056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634056 prefixEnd_634056 := by exact prefixLift 634056
  have htrace : WordTrace (prefixWord ++ tailWord_634056) baseStart_634056 baseEnd_634056 := by
    simpa [prefixWord, tailWord_634056, baseEnd_634056] using wordTrace_append hprefix tailTrace_634056
  have hstable : (prefixWord ++ tailWord_634056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634056).length < 2 ^ (prefixWord ++ tailWord_634056).sum := by decide
  have hdescent : baseEnd_634056 < baseStart_634056 := by decide
  rcases family_descends (prefixWord ++ tailWord_634056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634073 : List Nat := [1, 2, 1, 2, 3, 1, 1, 7, 3]
def baseStart_634073 : Nat := 118140960795 + 634073 * 2 ^ 59
def prefixEnd_634073 : Nat := 4983230072969 + 3 ^ 40 * 634073 * 2
def baseEnd_634073 : Nat := 144704097350401297853981

theorem tailTrace_634073 : CollatzResearch.WordTrace tailWord_634073 prefixEnd_634073 144704097350401297853981 := by
  unfold tailWord_634073
  simp only [CollatzResearch.WordTrace]
  refine ⟨23126542231869286892018873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15417694821246191261345915 23126542231869286892018873)
  ·
    refine ⟨17344906673901965169014155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23126542231869286892018873 17344906673901965169014155)
    ·
      refine ⟨26017360010852947753521233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17344906673901965169014155 26017360010852947753521233)
      ·
        refine ⟨19513020008139710815140925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26017360010852947753521233 19513020008139710815140925)
        ·
          refine ⟨7317382503052391555677847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19513020008139710815140925 7317382503052391555677847)
          ·
            refine ⟨10976073754578587333516771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7317382503052391555677847 10976073754578587333516771)
            ·
              refine ⟨16464110631867881000275157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10976073754578587333516771 16464110631867881000275157)
              ·
                refine ⟨385877592934403460943949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16464110631867881000275157 385877592934403460943949)
                ·
                  refine ⟨144704097350401297853981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385877592934403460943949 144704097350401297853981)
                  ·
                    rfl

theorem cell21_634073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 3].length) (baseStart_634073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634073 prefixEnd_634073 := by exact prefixLift 634073
  have htrace : WordTrace (prefixWord ++ tailWord_634073) baseStart_634073 baseEnd_634073 := by
    simpa [prefixWord, tailWord_634073, baseEnd_634073] using wordTrace_append hprefix tailTrace_634073
  have hstable : (prefixWord ++ tailWord_634073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634073).length < 2 ^ (prefixWord ++ tailWord_634073).sum := by decide
  have hdescent : baseEnd_634073 < baseStart_634073 := by decide
  rcases family_descends (prefixWord ++ tailWord_634073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634090 : List Nat := [3, 1, 3, 1, 1, 4, 1, 4, 3]
def baseStart_634090 : Nat := 118140960795 + 634090 * 2 ^ 59
def prefixEnd_634090 : Nat := 4983230072969 + 3 ^ 40 * 634090 * 2
def baseEnd_634090 : Nat := 144707976982013046070613

theorem tailTrace_634090 : CollatzResearch.WordTrace tailWord_634090 prefixEnd_634090 144707976982013046070613 := by
  unfold tailWord_634090
  simp only [CollatzResearch.WordTrace]
  refine ⟨5781790568201924698846931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15418108181871799196925149 5781790568201924698846931)
  ·
    refine ⟨8672685852302887048270397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5781790568201924698846931 8672685852302887048270397)
    ·
      refine ⟨3252257194613582643101399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8672685852302887048270397 3252257194613582643101399)
      ·
        refine ⟨4878385791920373964652099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3252257194613582643101399 4878385791920373964652099)
        ·
          refine ⟨7317578687880560946978149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4878385791920373964652099 7317578687880560946978149)
          ·
            refine ⟨1372046003977605177558403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7317578687880560946978149 1372046003977605177558403)
            ·
              refine ⟨2058069005966407766337605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372046003977605177558403 2058069005966407766337605)
              ·
                refine ⟨385887938618701456188301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2058069005966407766337605 385887938618701456188301)
                ·
                  refine ⟨144707976982013046070613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385887938618701456188301 144707976982013046070613)
                  ·
                    rfl

theorem cell21_634090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_634090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634090 prefixEnd_634090 := by exact prefixLift 634090
  have htrace : WordTrace (prefixWord ++ tailWord_634090) baseStart_634090 baseEnd_634090 := by
    simpa [prefixWord, tailWord_634090, baseEnd_634090] using wordTrace_append hprefix tailTrace_634090
  have hstable : (prefixWord ++ tailWord_634090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634090).length < 2 ^ (prefixWord ++ tailWord_634090).sum := by decide
  have hdescent : baseEnd_634090 < baseStart_634090 := by decide
  rcases family_descends (prefixWord ++ tailWord_634090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634149 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 5]
def baseStart_634149 : Nat := 118140960795 + 634149 * 2 ^ 59
def prefixEnd_634149 : Nat := 4983230072969 + 3 ^ 40 * 634149 * 2
def baseEnd_634149 : Nat := 144721441585842054587159

theorem tailTrace_634149 : CollatzResearch.WordTrace tailWord_634149 prefixEnd_634149 144721441585842054587159 := by
  unfold tailWord_634149
  simp only [CollatzResearch.WordTrace]
  refine ⟨23129314179593951871785501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15419542786395967914523667 23129314179593951871785501)
  ·
    refine ⟨8673492817347731951919563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23129314179593951871785501 8673492817347731951919563)
    ·
      refine ⟨13010239226021597927879345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8673492817347731951919563 13010239226021597927879345)
      ·
        refine ⟨9757679419516198445909509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13010239226021597927879345 9757679419516198445909509)
        ·
          refine ⟨1829564891159287208608033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9757679419516198445909509 1829564891159287208608033)
          ·
            refine ⟨1372173668369465406456025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1829564891159287208608033 1372173668369465406456025)
            ·
              refine ⟨1029130251277099054842019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1372173668369465406456025 1029130251277099054842019)
              ·
                refine ⟨1543695376915648582263029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1029130251277099054842019 1543695376915648582263029)
                ·
                  refine ⟨144721441585842054587159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1543695376915648582263029 144721441585842054587159)
                  ·
                    rfl

theorem cell21_634149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_634149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634149 prefixEnd_634149 := by exact prefixLift 634149
  have htrace : WordTrace (prefixWord ++ tailWord_634149) baseStart_634149 baseEnd_634149 := by
    simpa [prefixWord, tailWord_634149, baseEnd_634149] using wordTrace_append hprefix tailTrace_634149
  have hstable : (prefixWord ++ tailWord_634149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634149).length < 2 ^ (prefixWord ++ tailWord_634149).sum := by decide
  have hdescent : baseEnd_634149 < baseStart_634149 := by decide
  rcases family_descends (prefixWord ++ tailWord_634149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634180 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 6]
def baseStart_634180 : Nat := 118140960795 + 634180 * 2 ^ 59
def prefixEnd_634180 : Nat := 4983230072969 + 3 ^ 40 * 634180 * 2
def baseEnd_634180 : Nat := 144728516208192889570429

theorem tailTrace_634180 : CollatzResearch.WordTrace tailWord_634180 prefixEnd_634180 144728516208192889570429 := by
  unfold tailWord_634180
  simp only [CollatzResearch.WordTrace]
  refine ⟨11565222421240822083081997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15420296561654429444109329 11565222421240822083081997)
  ·
    refine ⟨4336958407965308281155749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11565222421240822083081997 4336958407965308281155749)
    ·
      refine ⟨813179701493495302716703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4336958407965308281155749 813179701493495302716703)
      ·
        refine ⟨1219769552240242954075055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 813179701493495302716703 1219769552240242954075055)
        ·
          refine ⟨1829654328360364431112583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1219769552240242954075055 1829654328360364431112583)
          ·
            refine ⟨2744481492540546646668875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1829654328360364431112583 2744481492540546646668875)
            ·
              refine ⟨4116722238810819970003313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744481492540546646668875 4116722238810819970003313)
              ·
                refine ⟨3087541679108114977502485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4116722238810819970003313 3087541679108114977502485)
                ·
                  refine ⟨144728516208192889570429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3087541679108114977502485 144728516208192889570429)
                  ·
                    rfl

theorem cell21_634180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_634180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634180 prefixEnd_634180 := by exact prefixLift 634180
  have htrace : WordTrace (prefixWord ++ tailWord_634180) baseStart_634180 baseEnd_634180 := by
    simpa [prefixWord, tailWord_634180, baseEnd_634180] using wordTrace_append hprefix tailTrace_634180
  have hstable : (prefixWord ++ tailWord_634180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634180).length < 2 ^ (prefixWord ++ tailWord_634180).sum := by decide
  have hdescent : baseEnd_634180 < baseStart_634180 := by decide
  rcases family_descends (prefixWord ++ tailWord_634180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634315 : List Nat := [1, 1, 1, 1, 3, 3, 5, 2, 4]
def baseStart_634315 : Nat := 118140960795 + 634315 * 2 ^ 59
def prefixEnd_634315 : Nat := 4983230072969 + 3 ^ 40 * 634315 * 2
def baseEnd_634315 : Nat := 144759325047462654820153

theorem tailTrace_634315 : CollatzResearch.WordTrace tailWord_634315 prefixEnd_634315 144759325047462654820153 := by
  unfold tailWord_634315
  simp only [CollatzResearch.WordTrace]
  refine ⟨23135368696992562222328399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15423579131328374814885599 23135368696992562222328399)
  ·
    refine ⟨34703053045488843333492599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23135368696992562222328399 34703053045488843333492599)
    ·
      refine ⟨52054579568233265000238899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34703053045488843333492599 52054579568233265000238899)
      ·
        refine ⟨78081869352349897500358349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52054579568233265000238899 78081869352349897500358349)
        ·
          refine ⟨29280701007131211562634381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78081869352349897500358349 29280701007131211562634381)
          ·
            refine ⟨10980262877674204335987893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29280701007131211562634381 10980262877674204335987893)
            ·
              refine ⟨1029399644781956656498865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10980262877674204335987893 1029399644781956656498865)
              ·
                refine ⟨772049733586467492374149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1029399644781956656498865 772049733586467492374149)
                ·
                  refine ⟨144759325047462654820153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 772049733586467492374149 144759325047462654820153)
                  ·
                    rfl

theorem cell21_634315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 4].length) (baseStart_634315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634315 prefixEnd_634315 := by exact prefixLift 634315
  have htrace : WordTrace (prefixWord ++ tailWord_634315) baseStart_634315 baseEnd_634315 := by
    simpa [prefixWord, tailWord_634315, baseEnd_634315] using wordTrace_append hprefix tailTrace_634315
  have hstable : (prefixWord ++ tailWord_634315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634315).length < 2 ^ (prefixWord ++ tailWord_634315).sum := by decide
  have hdescent : baseEnd_634315 < baseStart_634315 := by decide
  rcases family_descends (prefixWord ++ tailWord_634315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634346 : List Nat := [3, 1, 3, 1, 4, 1, 1, 7]
def baseStart_634346 : Nat := 118140960795 + 634346 * 2 ^ 59
def prefixEnd_634346 : Nat := 4983230072969 + 3 ^ 40 * 634346 * 2
def baseEnd_634346 : Nat := 48255466556604496601141

theorem tailTrace_634346 : CollatzResearch.WordTrace tailWord_634346 prefixEnd_634346 48255466556604496601141 := by
  unfold tailWord_634346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5784124839970063629176723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15424332906586836344471261 5784124839970063629176723)
  ·
    refine ⟨8676187259955095443765085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5784124839970063629176723 8676187259955095443765085)
    ·
      refine ⟨3253570222483160791411907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8676187259955095443765085 3253570222483160791411907)
      ·
        refine ⟨4880355333724741187117861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3253570222483160791411907 4880355333724741187117861)
        ·
          refine ⟨915066625073388972584599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4880355333724741187117861 915066625073388972584599)
          ·
            refine ⟨1372599937610083458876899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915066625073388972584599 1372599937610083458876899)
            ·
              refine ⟨2058899906415125188315349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372599937610083458876899 2058899906415125188315349)
              ·
                refine ⟨48255466556604496601141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2058899906415125188315349 48255466556604496601141)
                ·
                  rfl

theorem cell21_634346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_634346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634346 prefixEnd_634346 := by exact prefixLift 634346
  have htrace : WordTrace (prefixWord ++ tailWord_634346) baseStart_634346 baseEnd_634346 := by
    simpa [prefixWord, tailWord_634346, baseEnd_634346] using wordTrace_append hprefix tailTrace_634346
  have hstable : (prefixWord ++ tailWord_634346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634346).length < 2 ^ (prefixWord ++ tailWord_634346).sum := by decide
  have hdescent : baseEnd_634346 < baseStart_634346 := by decide
  rcases family_descends (prefixWord ++ tailWord_634346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634422 : List Nat := [5, 1, 2, 1, 3, 9]
def baseStart_634422 : Nat := 118140960795 + 634422 * 2 ^ 59
def prefixEnd_634422 : Nat := 4983230072969 + 3 ^ 40 * 634422 * 2
def baseEnd_634422 : Nat := 5362360885379786908763

theorem tailTrace_634422 : CollatzResearch.WordTrace tailWord_634422 prefixEnd_634422 5362360885379786908763 := by
  unfold tailWord_634422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1446204456725307468529595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15426180871736612997649013 1446204456725307468529595)
  ·
    refine ⟨2169306685087961202794393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1446204456725307468529595 2169306685087961202794393)
    ·
      refine ⟨1626980013815970902095795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2169306685087961202794393 1626980013815970902095795)
      ·
        refine ⟨2440470020723956353143693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1626980013815970902095795 2440470020723956353143693)
        ·
          refine ⟨915176257771483632428885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2440470020723956353143693 915176257771483632428885)
          ·
            refine ⟨5362360885379786908763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 915176257771483632428885 5362360885379786908763)
            ·
              rfl

theorem cell21_634422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 9].length) (baseStart_634422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634422 prefixEnd_634422 := by exact prefixLift 634422
  have htrace : WordTrace (prefixWord ++ tailWord_634422) baseStart_634422 baseEnd_634422 := by
    simpa [prefixWord, tailWord_634422, baseEnd_634422] using wordTrace_append hprefix tailTrace_634422
  have hstable : (prefixWord ++ tailWord_634422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634422).length < 2 ^ (prefixWord ++ tailWord_634422).sum := by decide
  have hdescent : baseEnd_634422 < baseStart_634422 := by decide
  rcases family_descends (prefixWord ++ tailWord_634422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634428 : List Nat := [2, 2, 2, 2, 5, 1, 2, 2, 3]
def baseStart_634428 : Nat := 118140960795 + 634428 * 2 ^ 59
def prefixEnd_634428 : Nat := 4983230072969 + 3 ^ 40 * 634428 * 2
def baseEnd_634428 : Nat := 144785113186999569436589

theorem tailTrace_634428 : CollatzResearch.WordTrace tailWord_634428 prefixEnd_634428 144785113186999569436589 := by
  unfold tailWord_634428
  simp only [CollatzResearch.WordTrace]
  refine ⟨11569745072791591260595969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15426326763722121680794625 11569745072791591260595969)
  ·
    refine ⟨8677308804593693445446977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11569745072791591260595969 8677308804593693445446977)
    ·
      refine ⟨6507981603445270084085233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8677308804593693445446977 6507981603445270084085233)
      ·
        refine ⟨4880986202583952563063925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6507981603445270084085233 4880986202583952563063925)
        ·
          refine ⟨457592456492245552787243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4880986202583952563063925 457592456492245552787243)
          ·
            refine ⟨686388684738368329180865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457592456492245552787243 686388684738368329180865)
            ·
              refine ⟨514791513553776246885649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686388684738368329180865 514791513553776246885649)
              ·
                refine ⟨386093635165332185164237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514791513553776246885649 386093635165332185164237)
                ·
                  refine ⟨144785113186999569436589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 386093635165332185164237 144785113186999569436589)
                  ·
                    rfl

theorem cell21_634428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_634428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634428 prefixEnd_634428 := by exact prefixLift 634428
  have htrace : WordTrace (prefixWord ++ tailWord_634428) baseStart_634428 baseEnd_634428 := by
    simpa [prefixWord, tailWord_634428, baseEnd_634428] using wordTrace_append hprefix tailTrace_634428
  have hstable : (prefixWord ++ tailWord_634428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634428).length < 2 ^ (prefixWord ++ tailWord_634428).sum := by decide
  have hdescent : baseEnd_634428 < baseStart_634428 := by decide
  rcases family_descends (prefixWord ++ tailWord_634428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634439 : List Nat := [1, 1, 4, 1, 6, 1, 1, 6]
def baseStart_634439 : Nat := 118140960795 + 634439 * 2 ^ 59
def prefixEnd_634439 : Nat := 4983230072969 + 3 ^ 40 * 634439 * 2
def baseEnd_634439 : Nat := 48262541178955331584411

theorem tailTrace_634439 : CollatzResearch.WordTrace tailWord_634439 prefixEnd_634439 48262541178955331584411 := by
  unfold tailWord_634439
  simp only [CollatzResearch.WordTrace]
  refine ⟨23139891348543331399842371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15426594232362220933228247 23139891348543331399842371)
  ·
    refine ⟨34709837022814997099763557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23139891348543331399842371 34709837022814997099763557)
    ·
      refine ⟨6508094441777811956205667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34709837022814997099763557 6508094441777811956205667)
      ·
        refine ⟨9762141662666717934308501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6508094441777811956205667 9762141662666717934308501)
        ·
          refine ⟨457600390437502403170711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9762141662666717934308501 457600390437502403170711)
          ·
            refine ⟨686400585656253604756067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457600390437502403170711 686400585656253604756067)
            ·
              refine ⟨1029600878484380407134101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686400585656253604756067 1029600878484380407134101)
              ·
                refine ⟨48262541178955331584411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1029600878484380407134101 48262541178955331584411)
                ·
                  rfl

theorem cell21_634439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 6].length) (baseStart_634439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634439 prefixEnd_634439 := by exact prefixLift 634439
  have htrace : WordTrace (prefixWord ++ tailWord_634439) baseStart_634439 baseEnd_634439 := by
    simpa [prefixWord, tailWord_634439, baseEnd_634439] using wordTrace_append hprefix tailTrace_634439
  have hstable : (prefixWord ++ tailWord_634439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634439).length < 2 ^ (prefixWord ++ tailWord_634439).sum := by decide
  have hdescent : baseEnd_634439 < baseStart_634439 := by decide
  rcases family_descends (prefixWord ++ tailWord_634439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634557 : List Nat := [1, 4, 1, 2, 1, 2, 4, 6]
def baseStart_634557 : Nat := 118140960795 + 634557 * 2 ^ 59
def prefixEnd_634557 : Nat := 4983230072969 + 3 ^ 40 * 634557 * 2
def baseEnd_634557 : Nat := 48271517581508003928775

theorem tailTrace_634557 : CollatzResearch.WordTrace tailWord_634557 prefixEnd_634557 48271517581508003928775 := by
  unfold tailWord_634557
  simp only [CollatzResearch.WordTrace]
  refine ⟨23144195162115837552637925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15429463441410558368425283 23144195162115837552637925)
  ·
    refine ⟨4339536592896719541119611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23144195162115837552637925 4339536592896719541119611)
    ·
      refine ⟨6509304889345079311679417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4339536592896719541119611 6509304889345079311679417)
      ·
        refine ⟨4881978667008809483759563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6509304889345079311679417 4881978667008809483759563)
        ·
          refine ⟨7322968000513214225639345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4881978667008809483759563 7322968000513214225639345)
          ·
            refine ⟨5492226000384910669229509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7322968000513214225639345 5492226000384910669229509)
            ·
              refine ⟨1029792375072170750480533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5492226000384910669229509 1029792375072170750480533)
              ·
                refine ⟨48271517581508003928775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1029792375072170750480533 48271517581508003928775)
                ·
                  rfl

theorem cell21_634557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 6].length) (baseStart_634557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634557 prefixEnd_634557 := by exact prefixLift 634557
  have htrace : WordTrace (prefixWord ++ tailWord_634557) baseStart_634557 baseEnd_634557 := by
    simpa [prefixWord, tailWord_634557, baseEnd_634557] using wordTrace_append hprefix tailTrace_634557
  have hstable : (prefixWord ++ tailWord_634557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634557).length < 2 ^ (prefixWord ++ tailWord_634557).sum := by decide
  have hdescent : baseEnd_634557 < baseStart_634557 := by decide
  rcases family_descends (prefixWord ++ tailWord_634557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634571 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 5]
def baseStart_634571 : Nat := 118140960795 + 634571 * 2 ^ 59
def prefixEnd_634571 : Nat := 4983230072969 + 3 ^ 40 * 634571 * 2
def baseEnd_634571 : Nat := 144817747735263098552963

theorem tailTrace_634571 : CollatzResearch.WordTrace tailWord_634571 prefixEnd_634571 144817747735263098552963 := by
  unfold tailWord_634571
  simp only [CollatzResearch.WordTrace]
  refine ⟨23144705784065117943647567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15429803856043411962431711 23144705784065117943647567)
  ·
    refine ⟨34717058676097676915471351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23144705784065117943647567 34717058676097676915471351)
    ·
      refine ⟨52075588014146515373207027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34717058676097676915471351 52075588014146515373207027)
      ·
        refine ⟨78113382021219773059810541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52075588014146515373207027 78113382021219773059810541)
        ·
          refine ⟨29292518257957414897428953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78113382021219773059810541 29292518257957414897428953)
          ·
            refine ⟨21969388693468061173071715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29292518257957414897428953 21969388693468061173071715)
            ·
              refine ⟨32954083040202091759607573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21969388693468061173071715 32954083040202091759607573)
              ·
                refine ⟨1544722642509473051231605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32954083040202091759607573 1544722642509473051231605)
                ·
                  refine ⟨144817747735263098552963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1544722642509473051231605 144817747735263098552963)
                  ·
                    rfl

theorem cell21_634571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 5].length) (baseStart_634571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634571 prefixEnd_634571 := by exact prefixLift 634571
  have htrace : WordTrace (prefixWord ++ tailWord_634571) baseStart_634571 baseEnd_634571 := by
    simpa [prefixWord, tailWord_634571, baseEnd_634571] using wordTrace_append hprefix tailTrace_634571
  have hstable : (prefixWord ++ tailWord_634571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634571).length < 2 ^ (prefixWord ++ tailWord_634571).sum := by decide
  have hdescent : baseEnd_634571 < baseStart_634571 := by decide
  rcases family_descends (prefixWord ++ tailWord_634571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634602 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 6]
def baseStart_634602 : Nat := 118140960795 + 634602 * 2 ^ 59
def prefixEnd_634602 : Nat := 4983230072969 + 3 ^ 40 * 634602 * 2
def baseEnd_634602 : Nat := 144824822357613933536233

theorem tailTrace_634602 : CollatzResearch.WordTrace tailWord_634602 prefixEnd_634602 144824822357613933536233 := by
  unfold tailWord_634602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5786459111738202559506515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15430557631301873492017373 5786459111738202559506515)
  ·
    refine ⟨8679688667607303839259773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5786459111738202559506515 8679688667607303839259773)
    ·
      refine ⟨3254883250352738939722415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8679688667607303839259773 3254883250352738939722415)
      ·
        refine ⟨4882324875529108409583623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3254883250352738939722415 4882324875529108409583623)
        ·
          refine ⟨7323487313293662614375435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4882324875529108409583623 7323487313293662614375435)
          ·
            refine ⟨10985230969940493921563153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7323487313293662614375435 10985230969940493921563153)
            ·
              refine ⟨8238923227455370441172365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10985230969940493921563153 8238923227455370441172365)
              ·
                refine ⟨3089596210295763915439637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8238923227455370441172365 3089596210295763915439637)
                ·
                  refine ⟨144824822357613933536233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3089596210295763915439637 144824822357613933536233)
                  ·
                    rfl

theorem cell21_634602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_634602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634602 prefixEnd_634602 := by exact prefixLift 634602
  have htrace : WordTrace (prefixWord ++ tailWord_634602) baseStart_634602 baseEnd_634602 := by
    simpa [prefixWord, tailWord_634602, baseEnd_634602] using wordTrace_append hprefix tailTrace_634602
  have hstable : (prefixWord ++ tailWord_634602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634602).length < 2 ^ (prefixWord ++ tailWord_634602).sum := by decide
  have hdescent : baseEnd_634602 < baseStart_634602 := by decide
  rcases family_descends (prefixWord ++ tailWord_634602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634616 : List Nat := [2, 1, 2, 1, 1, 2, 2, 10]
def baseStart_634616 : Nat := 118140960795 + 634616 * 2 ^ 59
def prefixEnd_634616 : Nat := 4983230072969 + 3 ^ 40 * 634616 * 2
def baseEnd_634616 : Nat := 48276005782784340100957

theorem tailTrace_634616 : CollatzResearch.WordTrace tailWord_634616 prefixEnd_634616 48276005782784340100957 := by
  unfold tailWord_634616
  simp only [CollatzResearch.WordTrace]
  refine ⟨11573173534451045314517851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15430898045934727086023801 11573173534451045314517851)
  ·
    refine ⟨17359760301676567971776777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11573173534451045314517851 17359760301676567971776777)
    ·
      refine ⟨13019820226257425978832583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17359760301676567971776777 13019820226257425978832583)
      ·
        refine ⟨19529730339386138968248875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13019820226257425978832583 19529730339386138968248875)
        ·
          refine ⟨29294595509079208452373313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19529730339386138968248875 29294595509079208452373313)
          ·
            refine ⟨21970946631809406339279985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29294595509079208452373313 21970946631809406339279985)
            ·
              refine ⟨16478209973857054754459989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21970946631809406339279985 16478209973857054754459989)
              ·
                refine ⟨48276005782784340100957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16478209973857054754459989 48276005782784340100957)
                ·
                  rfl

theorem cell21_634616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 10].length) (baseStart_634616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634616 prefixEnd_634616 := by exact prefixLift 634616
  have htrace : WordTrace (prefixWord ++ tailWord_634616) baseStart_634616 baseEnd_634616 := by
    simpa [prefixWord, tailWord_634616, baseEnd_634616] using wordTrace_append hprefix tailTrace_634616
  have hstable : (prefixWord ++ tailWord_634616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634616).length < 2 ^ (prefixWord ++ tailWord_634616).sum := by decide
  have hdescent : baseEnd_634616 < baseStart_634616 := by decide
  rcases family_descends (prefixWord ++ tailWord_634616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634664 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 5]
def baseStart_634664 : Nat := 118140960795 + 634664 * 2 ^ 59
def prefixEnd_634664 : Nat := 4983230072969 + 3 ^ 40 * 634664 * 2
def baseEnd_634664 : Nat := 144838971602315603502773

theorem tailTrace_634664 : CollatzResearch.WordTrace tailWord_634664 prefixEnd_634664 144838971602315603502773 := by
  unfold tailWord_634664
  simp only [CollatzResearch.WordTrace]
  refine ⟨11574048886364097413391523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15432065181818796551188697 11574048886364097413391523)
  ·
    refine ⟨17361073329546146120087285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11574048886364097413391523 17361073329546146120087285)
    ·
      refine ⟨1627600624644951198758183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17361073329546146120087285 1627600624644951198758183)
      ·
        refine ⟨2441400936967426798137275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1627600624644951198758183 2441400936967426798137275)
        ·
          refine ⟨3662101405451140197205913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2441400936967426798137275 3662101405451140197205913)
          ·
            refine ⟨2746576054088355147904435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3662101405451140197205913 2746576054088355147904435)
            ·
              refine ⟨4119864081132532721856653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2746576054088355147904435 4119864081132532721856653)
              ·
                refine ⟨1544949030424699770696245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4119864081132532721856653 1544949030424699770696245)
                ·
                  refine ⟨144838971602315603502773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1544949030424699770696245 144838971602315603502773)
                  ·
                    rfl

theorem cell21_634664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_634664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634664 prefixEnd_634664 := by exact prefixLift 634664
  have htrace : WordTrace (prefixWord ++ tailWord_634664) baseStart_634664 baseEnd_634664 := by
    simpa [prefixWord, tailWord_634664, baseEnd_634664] using wordTrace_append hprefix tailTrace_634664
  have hstable : (prefixWord ++ tailWord_634664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634664).length < 2 ^ (prefixWord ++ tailWord_634664).sum := by decide
  have hdescent : baseEnd_634664 < baseStart_634664 := by decide
  rcases family_descends (prefixWord ++ tailWord_634664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634709 : List Nat := [1, 3, 2, 2, 2, 4, 7]
def baseStart_634709 : Nat := 118140960795 + 634709 * 2 ^ 59
def prefixEnd_634709 : Nat := 4983230072969 + 3 ^ 40 * 634709 * 2
def baseEnd_634709 : Nat := 16094360135045058361409

theorem tailTrace_634709 : CollatzResearch.WordTrace tailWord_634709 prefixEnd_634709 16094360135045058361409 := by
  unfold tailWord_634709
  simp only [CollatzResearch.WordTrace]
  refine ⟨23149739057565167512171181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15433159371710111674780787 23149739057565167512171181)
  ·
    refine ⟨8681152146586937817064193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23149739057565167512171181 8681152146586937817064193)
    ·
      refine ⟨6510864109940203362798145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8681152146586937817064193 6510864109940203362798145)
      ·
        refine ⟨4883148082455152522098609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6510864109940203362798145 4883148082455152522098609)
        ·
          refine ⟨3662361061841364391573957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4883148082455152522098609 3662361061841364391573957)
          ·
            refine ⟨686692699095255823420117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3662361061841364391573957 686692699095255823420117)
            ·
              refine ⟨16094360135045058361409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 686692699095255823420117 16094360135045058361409)
              ·
                rfl

theorem cell21_634709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 7].length) (baseStart_634709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634709 prefixEnd_634709 := by exact prefixLift 634709
  have htrace : WordTrace (prefixWord ++ tailWord_634709) baseStart_634709 baseEnd_634709 := by
    simpa [prefixWord, tailWord_634709, baseEnd_634709] using wordTrace_append hprefix tailTrace_634709
  have hstable : (prefixWord ++ tailWord_634709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634709).length < 2 ^ (prefixWord ++ tailWord_634709).sum := by decide
  have hdescent : baseEnd_634709 < baseStart_634709 := by decide
  rcases family_descends (prefixWord ++ tailWord_634709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634799 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 5]
def baseStart_634799 : Nat := 118140960795 + 634799 * 2 ^ 59
def prefixEnd_634799 : Nat := 4983230072969 + 3 ^ 40 * 634799 * 2
def baseEnd_634799 : Nat := 144869780441585368752497

theorem tailTrace_634799 : CollatzResearch.WordTrace tailWord_634799 prefixEnd_634799 144869780441585368752497 := by
  unfold tailWord_634799
  simp only [CollatzResearch.WordTrace]
  refine ⟨23153021627239112882947451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15435347751492741921964967 23153021627239112882947451)
  ·
    refine ⟨34729532440858669324421177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23153021627239112882947451 34729532440858669324421177)
    ·
      refine ⟨26047149330644001993315883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34729532440858669324421177 26047149330644001993315883)
      ·
        refine ⟨39070723995966002989973825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26047149330644001993315883 39070723995966002989973825)
        ·
          refine ⟨29303042996974502242480369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39070723995966002989973825 29303042996974502242480369)
          ·
            refine ⟨21977282247730876681860277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29303042996974502242480369 21977282247730876681860277)
            ·
              refine ⟨2060370210724769688924401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21977282247730876681860277 2060370210724769688924401)
              ·
                refine ⟨1545277658043577266693301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2060370210724769688924401 1545277658043577266693301)
                ·
                  refine ⟨144869780441585368752497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1545277658043577266693301 144869780441585368752497)
                  ·
                    rfl

theorem cell21_634799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 5].length) (baseStart_634799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634799 prefixEnd_634799 := by exact prefixLift 634799
  have htrace : WordTrace (prefixWord ++ tailWord_634799) baseStart_634799 baseEnd_634799 := by
    simpa [prefixWord, tailWord_634799, baseEnd_634799] using wordTrace_append hprefix tailTrace_634799
  have hstable : (prefixWord ++ tailWord_634799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634799).length < 2 ^ (prefixWord ++ tailWord_634799).sum := by decide
  have hdescent : baseEnd_634799 < baseStart_634799 := by decide
  rcases family_descends (prefixWord ++ tailWord_634799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634830 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_634830 : Nat := 118140960795 + 634830 * 2 ^ 59
def prefixEnd_634830 : Nat := 4983230072969 + 3 ^ 40 * 634830 * 2
def baseEnd_634830 : Nat := 144876855063936203735767

theorem tailTrace_634830 : CollatzResearch.WordTrace tailWord_634830 prefixEnd_634830 144876855063936203735767 := by
  unfold tailWord_634830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2894269036265850647165743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15436101526751203451550629 2894269036265850647165743)
  ·
    refine ⟨4341403554398775970748615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2894269036265850647165743 4341403554398775970748615)
    ·
      refine ⟨6512105331598163956122923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4341403554398775970748615 6512105331598163956122923)
      ·
        refine ⟨9768157997397245934184385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6512105331598163956122923 9768157997397245934184385)
        ·
          refine ⟨7326118498047934450638289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9768157997397245934184385 7326118498047934450638289)
          ·
            refine ⟨5494588873535950837978717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7326118498047934450638289 5494588873535950837978717)
            ·
              refine ⟨2060470827575981564242019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5494588873535950837978717 2060470827575981564242019)
              ·
                refine ⟨3090706241363972346363029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2060470827575981564242019 3090706241363972346363029)
                ·
                  refine ⟨144876855063936203735767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3090706241363972346363029 144876855063936203735767)
                  ·
                    rfl

theorem cell21_634830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_634830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634830 prefixEnd_634830 := by exact prefixLift 634830
  have htrace : WordTrace (prefixWord ++ tailWord_634830) baseStart_634830 baseEnd_634830 := by
    simpa [prefixWord, tailWord_634830, baseEnd_634830] using wordTrace_append hprefix tailTrace_634830
  have hstable : (prefixWord ++ tailWord_634830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634830).length < 2 ^ (prefixWord ++ tailWord_634830).sum := by decide
  have hdescent : baseEnd_634830 < baseStart_634830 := by decide
  rcases family_descends (prefixWord ++ tailWord_634830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634878 : List Nat := [4, 2, 2, 2, 1, 3, 7]
def baseStart_634878 : Nat := 118140960795 + 634878 * 2 ^ 59
def prefixEnd_634878 : Nat := 4983230072969 + 3 ^ 40 * 634878 * 2
def baseEnd_634878 : Nat := 16098645479766531881741

theorem tailTrace_634878 : CollatzResearch.WordTrace tailWord_634878 prefixEnd_634878 16098645479766531881741 := by
  unfold tailWord_634878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2894487874244113671884161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15437268662635272916715525 2894487874244113671884161)
  ·
    refine ⟨2170865905683085253913121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2894487874244113671884161 2170865905683085253913121)
    ·
      refine ⟨1628149429262313940434841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2170865905683085253913121 1628149429262313940434841)
      ·
        refine ⟨1221112071946735455326131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1628149429262313940434841 1221112071946735455326131)
        ·
          refine ⟨1831668107920103182989197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1221112071946735455326131 1831668107920103182989197)
          ·
            refine ⟨686875540470038693620949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1831668107920103182989197 686875540470038693620949)
            ·
              refine ⟨16098645479766531881741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 686875540470038693620949 16098645479766531881741)
              ·
                rfl

theorem cell21_634878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 7].length) (baseStart_634878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634878 prefixEnd_634878 := by exact prefixLift 634878
  have htrace : WordTrace (prefixWord ++ tailWord_634878) baseStart_634878 baseEnd_634878 := by
    simpa [prefixWord, tailWord_634878, baseEnd_634878] using wordTrace_append hprefix tailTrace_634878
  have hstable : (prefixWord ++ tailWord_634878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634878).length < 2 ^ (prefixWord ++ tailWord_634878).sum := by decide
  have hdescent : baseEnd_634878 < baseStart_634878 := by decide
  rcases family_descends (prefixWord ++ tailWord_634878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634937 : List Nat := [1, 2, 1, 5, 4, 8]
def baseStart_634937 : Nat := 118140960795 + 634937 * 2 ^ 59
def prefixEnd_634937 : Nat := 4983230072969 + 3 ^ 40 * 634937 * 2
def baseEnd_634937 : Nat := 5366713848952881313045

theorem tailTrace_634937 : CollatzResearch.WordTrace tailWord_634937 prefixEnd_634937 5366713848952881313045 := by
  unfold tailWord_634937
  simp only [CollatzResearch.WordTrace]
  refine ⟨23158054900739162451471065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15438703267159441634314043 23158054900739162451471065)
  ·
    refine ⟨17368541175554371838603299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23158054900739162451471065 17368541175554371838603299)
    ·
      refine ⟨26052811763331557757904949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17368541175554371838603299 26052811763331557757904949)
      ·
        refine ⟨2442451102812333539803589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26052811763331557757904949 2442451102812333539803589)
        ·
          refine ⟨457959581777312538713173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2442451102812333539803589 457959581777312538713173)
          ·
            refine ⟨5366713848952881313045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 457959581777312538713173 5366713848952881313045)
            ·
              rfl

theorem cell21_634937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 8].length) (baseStart_634937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634937 prefixEnd_634937 := by exact prefixLift 634937
  have htrace : WordTrace (prefixWord ++ tailWord_634937) baseStart_634937 baseEnd_634937 := by
    simpa [prefixWord, tailWord_634937, baseEnd_634937] using wordTrace_append hprefix tailTrace_634937
  have hstable : (prefixWord ++ tailWord_634937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634937).length < 2 ^ (prefixWord ++ tailWord_634937).sum := by decide
  have hdescent : baseEnd_634937 < baseStart_634937 := by decide
  rcases family_descends (prefixWord ++ tailWord_634937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634951 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 5]
def baseStart_634951 : Nat := 118140960795 + 634951 * 2 ^ 59
def prefixEnd_634951 : Nat := 4983230072969 + 3 ^ 40 * 634951 * 2
def baseEnd_634951 : Nat := 144904468912466882218853

theorem tailTrace_634951 : CollatzResearch.WordTrace tailWord_634951 prefixEnd_634951 144904468912466882218853 := by
  unfold tailWord_634951
  simp only [CollatzResearch.WordTrace]
  refine ⟨23158565522688442842480707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15439043681792295228320471 23158565522688442842480707)
  ·
    refine ⟨34737848284032664263721061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23158565522688442842480707 34737848284032664263721061)
    ·
      refine ⟨6513346553256124549447699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34737848284032664263721061 6513346553256124549447699)
      ·
        refine ⟨9770019829884186824171549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6513346553256124549447699 9770019829884186824171549)
        ·
          refine ⟨3663757436206570059064331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9770019829884186824171549 3663757436206570059064331)
          ·
            refine ⟨5495636154309855088596497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3663757436206570059064331 5495636154309855088596497)
            ·
              refine ⟨4121727115732391316447373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5495636154309855088596497 4121727115732391316447373)
              ·
                refine ⟨1545647668399646743667765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4121727115732391316447373 1545647668399646743667765)
                ·
                  refine ⟨144904468912466882218853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1545647668399646743667765 144904468912466882218853)
                  ·
                    rfl

theorem cell21_634951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 5].length) (baseStart_634951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634951 prefixEnd_634951 := by exact prefixLift 634951
  have htrace : WordTrace (prefixWord ++ tailWord_634951) baseStart_634951 baseEnd_634951 := by
    simpa [prefixWord, tailWord_634951, baseEnd_634951] using wordTrace_append hprefix tailTrace_634951
  have hstable : (prefixWord ++ tailWord_634951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634951).length < 2 ^ (prefixWord ++ tailWord_634951).sum := by decide
  have hdescent : baseEnd_634951 < baseStart_634951 := by decide
  rcases family_descends (prefixWord ++ tailWord_634951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634999 : List Nat := [1, 1, 3, 1, 1, 7, 1, 2, 4]
def baseStart_634999 : Nat := 118140960795 + 634999 * 2 ^ 59
def prefixEnd_634999 : Nat := 4983230072969 + 3 ^ 40 * 634999 * 2
def baseEnd_634999 : Nat := 144915423166429465418755

theorem tailTrace_634999 : CollatzResearch.WordTrace tailWord_634999 prefixEnd_634999 144915423166429465418755 := by
  unfold tailWord_634999
  simp only [CollatzResearch.WordTrace]
  refine ⟨23160316226514547040228051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15440210817676364693485367 23160316226514547040228051)
  ·
    refine ⟨34740474339771820560342077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23160316226514547040228051 34740474339771820560342077)
    ·
      refine ⟨13027677877414432710128279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34740474339771820560342077 13027677877414432710128279)
      ·
        refine ⟨19541516816121649065192419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13027677877414432710128279 19541516816121649065192419)
        ·
          refine ⟨29312275224182473597788629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19541516816121649065192419 29312275224182473597788629)
          ·
            refine ⟨687006450566776724948171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 29312275224182473597788629 687006450566776724948171)
            ·
              refine ⟨1030509675850165087422257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687006450566776724948171 1030509675850165087422257)
              ·
                refine ⟨772882256887623815566693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1030509675850165087422257 772882256887623815566693)
                ·
                  refine ⟨144915423166429465418755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 772882256887623815566693 144915423166429465418755)
                  ·
                    rfl

theorem cell21_634999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 4].length) (baseStart_634999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_634999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_634999 prefixEnd_634999 := by exact prefixLift 634999
  have htrace : WordTrace (prefixWord ++ tailWord_634999) baseStart_634999 baseEnd_634999 := by
    simpa [prefixWord, tailWord_634999, baseEnd_634999] using wordTrace_append hprefix tailTrace_634999
  have hstable : (prefixWord ++ tailWord_634999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634999).length < 2 ^ (prefixWord ++ tailWord_634999).sum := by decide
  have hdescent : baseEnd_634999 < baseStart_634999 := by decide
  rcases family_descends (prefixWord ++ tailWord_634999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635016 : List Nat := [2, 1, 3, 4, 1, 2, 3, 1, 4]
def baseStart_635016 : Nat := 118140960795 + 635016 * 2 ^ 59
def prefixEnd_635016 : Nat := 4983230072969 + 3 ^ 40 * 635016 * 2
def baseEnd_635016 : Nat := 144919302798041213635387

theorem tailTrace_635016 : CollatzResearch.WordTrace tailWord_635016 prefixEnd_635016 144919302798041213635387 := by
  unfold tailWord_635016
  simp only [CollatzResearch.WordTrace]
  refine ⟨11580468133726479471798451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15440624178301972629064601 11580468133726479471798451)
  ·
    refine ⟨17370702200589719207697677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11580468133726479471798451 17370702200589719207697677)
    ·
      refine ⟨6514013325221144702886629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17370702200589719207697677 6514013325221144702886629)
      ·
        refine ⟨1221377498478964631791243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6514013325221144702886629 1221377498478964631791243)
        ·
          refine ⟨1832066247718446947686865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1221377498478964631791243 1832066247718446947686865)
          ·
            refine ⟨1374049685788835210765149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1832066247718446947686865 1374049685788835210765149)
            ·
              refine ⟨515268632170813204036931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1374049685788835210765149 515268632170813204036931)
              ·
                refine ⟨772902948256219806055397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515268632170813204036931 772902948256219806055397)
                ·
                  refine ⟨144919302798041213635387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 772902948256219806055397 144919302798041213635387)
                  ·
                    rfl

theorem cell21_635016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 4].length) (baseStart_635016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_635016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_635016 prefixEnd_635016 := by exact prefixLift 635016
  have htrace : WordTrace (prefixWord ++ tailWord_635016) baseStart_635016 baseEnd_635016 := by
    simpa [prefixWord, tailWord_635016, baseEnd_635016] using wordTrace_append hprefix tailTrace_635016
  have hstable : (prefixWord ++ tailWord_635016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635016).length < 2 ^ (prefixWord ++ tailWord_635016).sum := by decide
  have hdescent : baseEnd_635016 < baseStart_635016 := by decide
  rcases family_descends (prefixWord ++ tailWord_635016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635058 : List Nat := [3, 2, 1, 1, 1, 3, 2, 4, 4]
def baseStart_635058 : Nat := 118140960795 + 635058 * 2 ^ 59
def prefixEnd_635058 : Nat := 4983230072969 + 3 ^ 40 * 635058 * 2
def baseEnd_635058 : Nat := 144928887770258473935301

theorem tailTrace_635058 : CollatzResearch.WordTrace tailWord_635058 prefixEnd_635058 144928887770258473935301 := by
  unfold tailWord_635058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5790617033325200029156457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15441645422200533411083885 5790617033325200029156457)
  ·
    refine ⟨4342962774993900021867343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5790617033325200029156457 4342962774993900021867343)
    ·
      refine ⟨6514444162490850032801015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4342962774993900021867343 6514444162490850032801015)
      ·
        refine ⟨9771666243736275049201523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6514444162490850032801015 9771666243736275049201523)
        ·
          refine ⟨14657499365604412573802285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9771666243736275049201523 14657499365604412573802285)
          ·
            refine ⟨5496562262101654715175857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14657499365604412573802285 5496562262101654715175857)
            ·
              refine ⟨4122421696576241036381893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5496562262101654715175857 4122421696576241036381893)
              ·
                refine ⟨772954068108045194321605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4122421696576241036381893 772954068108045194321605)
                ·
                  refine ⟨144928887770258473935301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 772954068108045194321605 144928887770258473935301)
                  ·
                    rfl

theorem cell21_635058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_635058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_635058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_635058 prefixEnd_635058 := by exact prefixLift 635058
  have htrace : WordTrace (prefixWord ++ tailWord_635058) baseStart_635058 baseEnd_635058 := by
    simpa [prefixWord, tailWord_635058, baseEnd_635058] using wordTrace_append hprefix tailTrace_635058
  have hstable : (prefixWord ++ tailWord_635058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635058).length < 2 ^ (prefixWord ++ tailWord_635058).sum := by decide
  have hdescent : baseEnd_635058 < baseStart_635058 := by decide
  rcases family_descends (prefixWord ++ tailWord_635058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635072 : List Nat := [2, 1, 1, 2, 5, 1, 1, 8]
def baseStart_635072 : Nat := 118140960795 + 635072 * 2 ^ 59
def prefixEnd_635072 : Nat := 4983230072969 + 3 ^ 40 * 635072 * 2
def baseEnd_635072 : Nat := 48310694253665853567313

theorem tailTrace_635072 : CollatzResearch.WordTrace tailWord_635072 prefixEnd_635072 48310694253665853567313 := by
  unfold tailWord_635072
  simp only [CollatzResearch.WordTrace]
  refine ⟨11581489377625040253817735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15441985836833387005090313 11581489377625040253817735)
  ·
    refine ⟨17372234066437560380726603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11581489377625040253817735 17372234066437560380726603)
    ·
      refine ⟨26058351099656340571089905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17372234066437560380726603 26058351099656340571089905)
      ·
        refine ⟨19543763324742255428317429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26058351099656340571089905 19543763324742255428317429)
        ·
          refine ⟨1832227811694586446404759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19543763324742255428317429 1832227811694586446404759)
          ·
            refine ⟨2748341717541879669607139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1832227811694586446404759 2748341717541879669607139)
            ·
              refine ⟨4122512576312819504410709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2748341717541879669607139 4122512576312819504410709)
              ·
                refine ⟨48310694253665853567313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4122512576312819504410709 48310694253665853567313)
                ·
                  rfl

theorem cell21_635072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 8].length) (baseStart_635072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_635072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_635072 prefixEnd_635072 := by exact prefixLift 635072
  have htrace : WordTrace (prefixWord ++ tailWord_635072) baseStart_635072 baseEnd_635072 := by
    simpa [prefixWord, tailWord_635072, baseEnd_635072] using wordTrace_append hprefix tailTrace_635072
  have hstable : (prefixWord ++ tailWord_635072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635072).length < 2 ^ (prefixWord ++ tailWord_635072).sum := by decide
  have hdescent : baseEnd_635072 < baseStart_635072 := by decide
  rcases family_descends (prefixWord ++ tailWord_635072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635106 : List Nat := [3, 3, 4, 1, 10]
def baseStart_635106 : Nat := 118140960795 + 635106 * 2 ^ 59
def prefixEnd_635106 : Nat := 4983230072969 + 3 ^ 40 * 635106 * 2
def baseEnd_635106 : Nat := 1789380765731124162163

theorem tailTrace_635106 : CollatzResearch.WordTrace tailWord_635106 prefixEnd_635106 1789380765731124162163 := by
  unfold tailWord_635106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5791054709281726078593293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15442812558084602876248781 5791054709281726078593293)
  ·
    refine ⟨2171645515980647279472485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5791054709281726078593293 2171645515980647279472485)
    ·
      refine ⟨407183534246371364901091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2171645515980647279472485 407183534246371364901091)
      ·
        refine ⟨610775301369557047351637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407183534246371364901091 610775301369557047351637)
        ·
          refine ⟨1789380765731124162163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 610775301369557047351637 1789380765731124162163)
          ·
            rfl

theorem cell21_635106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 10].length) (baseStart_635106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_635106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_635106 prefixEnd_635106 := by exact prefixLift 635106
  have htrace : WordTrace (prefixWord ++ tailWord_635106) baseStart_635106 baseEnd_635106 := by
    simpa [prefixWord, tailWord_635106, baseEnd_635106] using wordTrace_append hprefix tailTrace_635106
  have hstable : (prefixWord ++ tailWord_635106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635106).length < 2 ^ (prefixWord ++ tailWord_635106).sum := by decide
  have hdescent : baseEnd_635106 < baseStart_635106 := by decide
  rcases family_descends (prefixWord ++ tailWord_635106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635165 : List Nat := [1, 4, 2, 3, 2, 1, 8]
def baseStart_635165 : Nat := 118140960795 + 635165 * 2 ^ 59
def prefixEnd_635165 : Nat := 4983230072969 + 3 ^ 40 * 635165 * 2
def baseEnd_635165 : Nat := 16105922958672229516861

theorem tailTrace_635165 : CollatzResearch.WordTrace tailWord_635165 prefixEnd_635165 16105922958672229516861 := by
  unfold tailWord_635165
  simp only [CollatzResearch.WordTrace]
  refine ⟨23166370743913157390770949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15444247162608771593847299 23166370743913157390770949)
  ·
    refine ⟨4343694514483717010769553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23166370743913157390770949 4343694514483717010769553)
    ·
      refine ⟨3257770885862787758077165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4343694514483717010769553 3257770885862787758077165)
      ·
        refine ⟨1221664082198545409278937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3257770885862787758077165 1221664082198545409278937)
        ·
          refine ⟨916248061648909056959203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1221664082198545409278937 916248061648909056959203)
          ·
            refine ⟨1374372092473363585438805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916248061648909056959203 1374372092473363585438805)
            ·
              refine ⟨16105922958672229516861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1374372092473363585438805 16105922958672229516861)
              ·
                rfl

theorem cell21_635165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 8].length) (baseStart_635165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_635165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_635165 prefixEnd_635165 := by exact prefixLift 635165
  have htrace : WordTrace (prefixWord ++ tailWord_635165) baseStart_635165 baseEnd_635165 := by
    simpa [prefixWord, tailWord_635165, baseEnd_635165] using wordTrace_append hprefix tailTrace_635165
  have hstable : (prefixWord ++ tailWord_635165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635165).length < 2 ^ (prefixWord ++ tailWord_635165).sum := by decide
  have hdescent : baseEnd_635165 < baseStart_635165 := by decide
  rcases family_descends (prefixWord ++ tailWord_635165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635244 : List Nat := [2, 2, 1, 1, 6, 2, 2, 1, 4]
def baseStart_635244 : Nat := 118140960795 + 635244 * 2 ^ 59
def prefixEnd_635244 : Nat := 4983230072969 + 3 ^ 40 * 635244 * 2
def baseEnd_635244 : Nat := 144971335504363483834921

theorem tailTrace_635244 : CollatzResearch.WordTrace tailWord_635244 prefixEnd_635244 144971335504363483834921 := by
  unfold tailWord_635244
  simp only [CollatzResearch.WordTrace]
  refine ⟨11584626055313476941448393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15446168073751302588597857 11584626055313476941448393)
  ·
    refine ⟨8688469541485107706086295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11584626055313476941448393 8688469541485107706086295)
    ·
      refine ⟨13032704312227661559129443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8688469541485107706086295 13032704312227661559129443)
      ·
        refine ⟨19549056468341492338694165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13032704312227661559129443 19549056468341492338694165)
        ·
          refine ⟨916362021953507453376289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19549056468341492338694165 916362021953507453376289)
          ·
            refine ⟨687271516465130590032217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 916362021953507453376289 687271516465130590032217)
            ·
              refine ⟨515453637348847942524163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 687271516465130590032217 515453637348847942524163)
              ·
                refine ⟨773180456023271913786245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515453637348847942524163 773180456023271913786245)
                ·
                  refine ⟨144971335504363483834921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 773180456023271913786245 144971335504363483834921)
                  ·
                    rfl

theorem cell21_635244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_635244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_635244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_635244 prefixEnd_635244 := by exact prefixLift 635244
  have htrace : WordTrace (prefixWord ++ tailWord_635244) baseStart_635244 baseEnd_635244 := by
    simpa [prefixWord, tailWord_635244, baseEnd_635244] using wordTrace_append hprefix tailTrace_635244
  have hstable : (prefixWord ++ tailWord_635244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635244).length < 2 ^ (prefixWord ++ tailWord_635244).sum := by decide
  have hdescent : baseEnd_635244 < baseStart_635244 := by decide
  rcases family_descends (prefixWord ++ tailWord_635244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635272 : List Nat := [2, 1, 3, 3, 1, 1, 2, 5, 3]
def baseStart_635272 : Nat := 118140960795 + 635272 * 2 ^ 59
def prefixEnd_635272 : Nat := 4983230072969 + 3 ^ 40 * 635272 * 2
def baseEnd_635272 : Nat := 144977725485841657368197

theorem tailTrace_635272 : CollatzResearch.WordTrace tailWord_635272 prefixEnd_635272 144977725485841657368197 := by
  unfold tailWord_635272
  simp only [CollatzResearch.WordTrace]
  refine ⟨11585136677262757332458035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15446848903017009776610713 11585136677262757332458035)
  ·
    refine ⟨17377705015894135998687053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11585136677262757332458035 17377705015894135998687053)
    ·
      refine ⟨6516639380960300999507645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17377705015894135998687053 6516639380960300999507645)
      ·
        refine ⟨2443739767860112874815367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6516639380960300999507645 2443739767860112874815367)
        ·
          refine ⟨3665609651790169312223051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2443739767860112874815367 3665609651790169312223051)
          ·
            refine ⟨5498414477685253968334577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3665609651790169312223051 5498414477685253968334577)
            ·
              refine ⟨4123810858263940476250933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5498414477685253968334577 4123810858263940476250933)
              ·
                refine ⟨386607267962244419648525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4123810858263940476250933 386607267962244419648525)
                ·
                  refine ⟨144977725485841657368197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 386607267962244419648525 144977725485841657368197)
                  ·
                    rfl

theorem cell21_635272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 3].length) (baseStart_635272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_635272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_635272 prefixEnd_635272 := by exact prefixLift 635272
  have htrace : WordTrace (prefixWord ++ tailWord_635272) baseStart_635272 baseEnd_635272 := by
    simpa [prefixWord, tailWord_635272, baseEnd_635272] using wordTrace_append hprefix tailTrace_635272
  have hstable : (prefixWord ++ tailWord_635272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635272).length < 2 ^ (prefixWord ++ tailWord_635272).sum := by decide
  have hdescent : baseEnd_635272 < baseStart_635272 := by decide
  rcases family_descends (prefixWord ++ tailWord_635272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635300 : List Nat := [2, 3, 1, 2, 1, 1, 5, 6]
def baseStart_635300 : Nat := 118140960795 + 635300 * 2 ^ 59
def prefixEnd_635300 : Nat := 4983230072969 + 3 ^ 40 * 635300 * 2
def baseEnd_635300 : Nat := 48328038489106610300491

theorem tailTrace_635300 : CollatzResearch.WordTrace tailWord_635300 prefixEnd_635300 48328038489106610300491 := by
  unfold tailWord_635300
  simp only [CollatzResearch.WordTrace]
  refine ⟨11585647299212037723467677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15447529732282716964623569 11585647299212037723467677)
  ·
    refine ⟨4344617737204514146300379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11585647299212037723467677 4344617737204514146300379)
    ·
      refine ⟨6516926605806771219450569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4344617737204514146300379 6516926605806771219450569)
      ·
        refine ⟨4887694954355078414587927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6516926605806771219450569 4887694954355078414587927)
        ·
          refine ⟨7331542431532617621881891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4887694954355078414587927 7331542431532617621881891)
          ·
            refine ⟨10997313647298926432822837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7331542431532617621881891 10997313647298926432822837)
            ·
              refine ⟨1030998154434274353077141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10997313647298926432822837 1030998154434274353077141)
              ·
                refine ⟨48328038489106610300491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1030998154434274353077141 48328038489106610300491)
                ·
                  rfl

theorem cell21_635300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 6].length) (baseStart_635300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_635300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_635300 prefixEnd_635300 := by exact prefixLift 635300
  have htrace : WordTrace (prefixWord ++ tailWord_635300) baseStart_635300 baseEnd_635300 := by
    simpa [prefixWord, tailWord_635300, baseEnd_635300] using wordTrace_append hprefix tailTrace_635300
  have hstable : (prefixWord ++ tailWord_635300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635300).length < 2 ^ (prefixWord ++ tailWord_635300).sum := by decide
  have hdescent : baseEnd_635300 < baseStart_635300 := by decide
  rcases family_descends (prefixWord ++ tailWord_635300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635306 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 5]
def baseStart_635306 : Nat := 118140960795 + 635306 * 2 ^ 59
def prefixEnd_635306 : Nat := 4983230072969 + 3 ^ 40 * 635306 * 2
def baseEnd_635306 : Nat := 144985484749065153801461

theorem tailTrace_635306 : CollatzResearch.WordTrace tailWord_635306 prefixEnd_635306 144985484749065153801461 := by
  unfold tailWord_635306
  simp only [CollatzResearch.WordTrace]
  refine ⟨5792878359100584617913443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15447675624268225647769181 5792878359100584617913443)
  ·
    refine ⟨8689317538650876926870165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5792878359100584617913443 8689317538650876926870165)
    ·
      refine ⟨407311759624259855947039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8689317538650876926870165 407311759624259855947039)
      ·
        refine ⟨610967639436389783920559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407311759624259855947039 610967639436389783920559)
        ·
          refine ⟨916451459154584675880839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610967639436389783920559 916451459154584675880839)
          ·
            refine ⟨1374677188731877013821259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916451459154584675880839 1374677188731877013821259)
            ·
              refine ⟨2062015783097815520731889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374677188731877013821259 2062015783097815520731889)
              ·
                refine ⟨1546511837323361640548917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2062015783097815520731889 1546511837323361640548917)
                ·
                  refine ⟨144985484749065153801461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1546511837323361640548917 144985484749065153801461)
                  ·
                    rfl

theorem cell21_635306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_635306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_635306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_635306 prefixEnd_635306 := by exact prefixLift 635306
  have htrace : WordTrace (prefixWord ++ tailWord_635306) baseStart_635306 baseEnd_635306 := by
    simpa [prefixWord, tailWord_635306, baseEnd_635306] using wordTrace_append hprefix tailTrace_635306
  have hstable : (prefixWord ++ tailWord_635306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635306).length < 2 ^ (prefixWord ++ tailWord_635306).sum := by decide
  have hdescent : baseEnd_635306 < baseStart_635306 := by decide
  rcases family_descends (prefixWord ++ tailWord_635306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635348 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 5]
def baseStart_635348 : Nat := 118140960795 + 635348 * 2 ^ 59
def prefixEnd_635348 : Nat := 4983230072969 + 3 ^ 40 * 635348 * 2
def baseEnd_635348 : Nat := 144995069721282414101375

theorem tailTrace_635348 : CollatzResearch.WordTrace tailWord_635348 prefixEnd_635348 144995069721282414101375 := by
  unfold tailWord_635348
  simp only [CollatzResearch.WordTrace]
  refine ⟨11586522651125089822341349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15448696868166786429788465 11586522651125089822341349)
  ·
    refine ⟨2172472997085954341689003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11586522651125089822341349 2172472997085954341689003)
    ·
      refine ⟨3258709495628931512533505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2172472997085954341689003 3258709495628931512533505)
      ·
        refine ⟨2444032121721698634400129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3258709495628931512533505 2444032121721698634400129)
        ·
          refine ⟨1833024091291273975800097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2444032121721698634400129 1833024091291273975800097)
          ·
            refine ⟨1374768068468455481850073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1833024091291273975800097 1374768068468455481850073)
            ·
              refine ⟨1031076051351341611387555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1374768068468455481850073 1031076051351341611387555)
              ·
                refine ⟨1546614077027012417081333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1031076051351341611387555 1546614077027012417081333)
                ·
                  refine ⟨144995069721282414101375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1546614077027012417081333 144995069721282414101375)
                  ·
                    rfl

theorem cell21_635348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_635348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_635348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_635348 prefixEnd_635348 := by exact prefixLift 635348
  have htrace : WordTrace (prefixWord ++ tailWord_635348) baseStart_635348 baseEnd_635348 := by
    simpa [prefixWord, tailWord_635348, baseEnd_635348] using wordTrace_append hprefix tailTrace_635348
  have hstable : (prefixWord ++ tailWord_635348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635348).length < 2 ^ (prefixWord ++ tailWord_635348).sum := by decide
  have hdescent : baseEnd_635348 < baseStart_635348 := by decide
  rcases family_descends (prefixWord ++ tailWord_635348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635469 : List Nat := [1, 6, 1, 1, 2, 1, 3, 6]
def baseStart_635469 : Nat := 118140960795 + 635469 * 2 ^ 59
def prefixEnd_635469 : Nat := 4983230072969 + 3 ^ 40 * 635469 * 2
def baseEnd_635469 : Nat := 48340894523271030861487

theorem tailTrace_635469 : CollatzResearch.WordTrace tailWord_635469 prefixEnd_635469 48340894523271030861487 := by
  unfold tailWord_635469
  simp only [CollatzResearch.WordTrace]
  refine ⟨23177458534811817309837461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15451639023207878206558307 23177458534811817309837461)
  ·
    refine ⟨1086443368819303936398631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23177458534811817309837461 1086443368819303936398631)
    ·
      refine ⟨1629665053228955904597947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1086443368819303936398631 1629665053228955904597947)
      ·
        refine ⟨2444497579843433856896921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1629665053228955904597947 2444497579843433856896921)
        ·
          refine ⟨1833373184882575392672691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2444497579843433856896921 1833373184882575392672691)
          ·
            refine ⟨2750059777323863089009037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1833373184882575392672691 2750059777323863089009037)
            ·
              refine ⟨1031272416496448658378389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2750059777323863089009037 1031272416496448658378389)
              ·
                refine ⟨48340894523271030861487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1031272416496448658378389 48340894523271030861487)
                ·
                  rfl

theorem cell21_635469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 6].length) (baseStart_635469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_635469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_635469 prefixEnd_635469 := by exact prefixLift 635469
  have htrace : WordTrace (prefixWord ++ tailWord_635469) baseStart_635469 baseEnd_635469 := by
    simpa [prefixWord, tailWord_635469, baseEnd_635469] using wordTrace_append hprefix tailTrace_635469
  have hstable : (prefixWord ++ tailWord_635469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635469).length < 2 ^ (prefixWord ++ tailWord_635469).sum := by decide
  have hdescent : baseEnd_635469 < baseStart_635469 := by decide
  rcases family_descends (prefixWord ++ tailWord_635469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635562 : List Nat := [3, 1, 5, 2, 1, 2, 7]
def baseStart_635562 : Nat := 118140960795 + 635562 * 2 ^ 59
def prefixEnd_635562 : Nat := 4983230072969 + 3 ^ 40 * 635562 * 2
def baseEnd_635562 : Nat := 16115989715207288614919

theorem tailTrace_635562 : CollatzResearch.WordTrace tailWord_635562 prefixEnd_635562 16115989715207288614919 := by
  unfold tailWord_635562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5795212630868723548243235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15453900348983262795315293 5795212630868723548243235)
  ·
    refine ⟨8692818946303085322364853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5795212630868723548243235 8692818946303085322364853)
    ·
      refine ⟨814951776215914248971705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8692818946303085322364853 814951776215914248971705)
      ·
        refine ⟨611213832161935686728779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 814951776215914248971705 611213832161935686728779)
        ·
          refine ⟨916820748242903530093169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611213832161935686728779 916820748242903530093169)
          ·
            refine ⟨687615561182177647569877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 916820748242903530093169 687615561182177647569877)
            ·
              refine ⟨16115989715207288614919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 687615561182177647569877 16115989715207288614919)
              ·
                rfl

theorem cell21_635562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 7].length) (baseStart_635562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_635562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_635562 prefixEnd_635562 := by exact prefixLift 635562
  have htrace : WordTrace (prefixWord ++ tailWord_635562) baseStart_635562 baseEnd_635562 := by
    simpa [prefixWord, tailWord_635562, baseEnd_635562] using wordTrace_append hprefix tailTrace_635562
  have hstable : (prefixWord ++ tailWord_635562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635562).length < 2 ^ (prefixWord ++ tailWord_635562).sum := by decide
  have hdescent : baseEnd_635562 < baseStart_635562 := by decide
  rcases family_descends (prefixWord ++ tailWord_635562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635700 : List Nat := [2, 5, 1, 1, 3, 1, 3, 1, 4]
def baseStart_635700 : Nat := 118140960795 + 635700 * 2 ^ 59
def prefixEnd_635700 : Nat := 4983230072969 + 3 ^ 40 * 635700 * 2
def baseEnd_635700 : Nat := 145075400917008024233989

theorem tailTrace_635700 : CollatzResearch.WordTrace tailWord_635700 prefixEnd_635700 145075400917008024233989 := by
  unfold tailWord_635700
  simp only [CollatzResearch.WordTrace]
  refine ⟨11592941898487471880748277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15457255864649962507664369 11592941898487471880748277)
  ·
    refine ⟨1086838302983200488820151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11592941898487471880748277 1086838302983200488820151)
    ·
      refine ⟨1630257454474800733230227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1086838302983200488820151 1630257454474800733230227)
      ·
        refine ⟨2445386181712201099845341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1630257454474800733230227 2445386181712201099845341)
        ·
          refine ⟨917019818142075412442003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2445386181712201099845341 917019818142075412442003)
          ·
            refine ⟨1375529727213113118663005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917019818142075412442003 1375529727213113118663005)
            ·
              refine ⟨515823647704917419498627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1375529727213113118663005 515823647704917419498627)
              ·
                refine ⟨773735471557376129247941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515823647704917419498627 773735471557376129247941)
                ·
                  refine ⟨145075400917008024233989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 773735471557376129247941 145075400917008024233989)
                  ·
                    rfl

theorem cell21_635700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_635700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_635700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_635700 prefixEnd_635700 := by exact prefixLift 635700
  have htrace : WordTrace (prefixWord ++ tailWord_635700) baseStart_635700 baseEnd_635700 := by
    simpa [prefixWord, tailWord_635700, baseEnd_635700] using wordTrace_append hprefix tailTrace_635700
  have hstable : (prefixWord ++ tailWord_635700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635700).length < 2 ^ (prefixWord ++ tailWord_635700).sum := by decide
  have hdescent : baseEnd_635700 < baseStart_635700 := by decide
  rcases family_descends (prefixWord ++ tailWord_635700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635832 : List Nat := [2, 1, 2, 1, 2, 5, 3, 5]
def baseStart_635832 : Nat := 118140960795 + 635832 * 2 ^ 59
def prefixEnd_635832 : Nat := 4983230072969 + 3 ^ 40 * 635832 * 2
def baseEnd_635832 : Nat := 48368508371801709344573

theorem tailTrace_635832 : CollatzResearch.WordTrace tailWord_635832 prefixEnd_635832 48368508371801709344573 := by
  unfold tailWord_635832
  simp only [CollatzResearch.WordTrace]
  refine ⟨11595349116248365152650875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15460465488331153536867833 11595349116248365152650875)
  ·
    refine ⟨17393023674372547728976313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11595349116248365152650875 17393023674372547728976313)
    ·
      refine ⟨13044767755779410796732235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17393023674372547728976313 13044767755779410796732235)
      ·
        refine ⟨19567151633669116195098353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13044767755779410796732235 19567151633669116195098353)
        ·
          refine ⟨14675363725251837146323765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19567151633669116195098353 14675363725251837146323765)
          ·
            refine ⟨1375815349242359732467853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14675363725251837146323765 1375815349242359732467853)
            ·
              refine ⟨515930755965884899675445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1375815349242359732467853 515930755965884899675445)
              ·
                refine ⟨48368508371801709344573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 515930755965884899675445 48368508371801709344573)
                ·
                  rfl

theorem cell21_635832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 5].length) (baseStart_635832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_635832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_635832 prefixEnd_635832 := by exact prefixLift 635832
  have htrace : WordTrace (prefixWord ++ tailWord_635832) baseStart_635832 baseEnd_635832 := by
    simpa [prefixWord, tailWord_635832, baseEnd_635832] using wordTrace_append hprefix tailTrace_635832
  have hstable : (prefixWord ++ tailWord_635832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635832).length < 2 ^ (prefixWord ++ tailWord_635832).sum := by decide
  have hdescent : baseEnd_635832 < baseStart_635832 := by decide
  rcases family_descends (prefixWord ++ tailWord_635832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636012 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 6]
def baseStart_636012 : Nat := 118140960795 + 636012 * 2 ^ 59
def prefixEnd_636012 : Nat := 4983230072969 + 3 ^ 40 * 636012 * 2
def baseEnd_636012 : Nat := 145146603567764815033351

theorem tailTrace_636012 : CollatzResearch.WordTrace tailWord_636012 prefixEnd_636012 145146603567764815033351 := by
  unfold tailWord_636012
  simp only [CollatzResearch.WordTrace]
  refine ⟨11598631685922310523427145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15464842247896414031236193 11598631685922310523427145)
  ·
    refine ⟨8698973764441732892570359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11598631685922310523427145 8698973764441732892570359)
    ·
      refine ⟨13048460646662599338855539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8698973764441732892570359 13048460646662599338855539)
      ·
        refine ⟨19572690969993899008283309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13048460646662599338855539 19572690969993899008283309)
        ·
          refine ⟨7339759113747712128106241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19572690969993899008283309 7339759113747712128106241)
          ·
            refine ⟨5504819335310784096079681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7339759113747712128106241 5504819335310784096079681)
            ·
              refine ⟨4128614501483088072059761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5504819335310784096079681 4128614501483088072059761)
              ·
                refine ⟨3096460876112316054044821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4128614501483088072059761 3096460876112316054044821)
                ·
                  refine ⟨145146603567764815033351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3096460876112316054044821 145146603567764815033351)
                  ·
                    rfl

theorem cell21_636012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_636012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636012 prefixEnd_636012 := by exact prefixLift 636012
  have htrace : WordTrace (prefixWord ++ tailWord_636012) baseStart_636012 baseEnd_636012 := by
    simpa [prefixWord, tailWord_636012, baseEnd_636012] using wordTrace_append hprefix tailTrace_636012
  have hstable : (prefixWord ++ tailWord_636012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636012).length < 2 ^ (prefixWord ++ tailWord_636012).sum := by decide
  have hdescent : baseEnd_636012 < baseStart_636012 := by decide
  rcases family_descends (prefixWord ++ tailWord_636012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636015 : List Nat := [1, 1, 2, 1, 3, 3, 4, 3, 3]
def baseStart_636015 : Nat := 118140960795 + 636015 * 2 ^ 59
def prefixEnd_636015 : Nat := 4983230072969 + 3 ^ 40 * 636015 * 2
def baseEnd_636015 : Nat := 145147288208637476483345

theorem tailTrace_636015 : CollatzResearch.WordTrace tailWord_636015 prefixEnd_636015 145147288208637476483345 := by
  unfold tailWord_636015
  simp only [CollatzResearch.WordTrace]
  refine ⟨23197372790833752559213499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15464915193889168372808999 23197372790833752559213499)
  ·
    refine ⟨34796059186250628838820249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23197372790833752559213499 34796059186250628838820249)
    ·
      refine ⟨26097044389687971629115187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34796059186250628838820249 26097044389687971629115187)
      ·
        refine ⟨39145566584531957443672781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26097044389687971629115187 39145566584531957443672781)
        ·
          refine ⟨14679587469199484041377293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39145566584531957443672781 14679587469199484041377293)
          ·
            refine ⟨5504845300949806515516485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14679587469199484041377293 5504845300949806515516485)
            ·
              refine ⟨1032158493928088721659341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5504845300949806515516485 1032158493928088721659341)
              ·
                refine ⟨387059435223033270622253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1032158493928088721659341 387059435223033270622253)
                ·
                  refine ⟨145147288208637476483345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387059435223033270622253 145147288208637476483345)
                  ·
                    rfl

theorem cell21_636015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 3].length) (baseStart_636015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636015 prefixEnd_636015 := by exact prefixLift 636015
  have htrace : WordTrace (prefixWord ++ tailWord_636015) baseStart_636015 baseEnd_636015 := by
    simpa [prefixWord, tailWord_636015, baseEnd_636015] using wordTrace_append hprefix tailTrace_636015
  have hstable : (prefixWord ++ tailWord_636015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636015).length < 2 ^ (prefixWord ++ tailWord_636015).sum := by decide
  have hdescent : baseEnd_636015 < baseStart_636015 := by decide
  rcases family_descends (prefixWord ++ tailWord_636015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636060 : List Nat := [2, 2, 3, 2, 1, 2, 4, 5]
def baseStart_636060 : Nat := 118140960795 + 636060 * 2 ^ 59
def prefixEnd_636060 : Nat := 4983230072969 + 3 ^ 40 * 636060 * 2
def baseEnd_636060 : Nat := 48385852607242466077751

theorem tailTrace_636060 : CollatzResearch.WordTrace tailWord_636060 prefixEnd_636060 48385852607242466077751 := by
  unfold tailWord_636060
  simp only [CollatzResearch.WordTrace]
  refine ⟨11599507037835362622300817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15466009383780483496401089 11599507037835362622300817)
  ·
    refine ⟨8699630278376521966725613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11599507037835362622300817 8699630278376521966725613)
    ·
      refine ⟨3262361354391195737522105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8699630278376521966725613 3262361354391195737522105)
      ·
        refine ⟨2446771015793396803141579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3262361354391195737522105 2446771015793396803141579)
        ·
          refine ⟨3670156523690095204712369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2446771015793396803141579 3670156523690095204712369)
          ·
            refine ⟨2752617392767571403534277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3670156523690095204712369 2752617392767571403534277)
            ·
              refine ⟨516115761143919638162677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2752617392767571403534277 516115761143919638162677)
              ·
                refine ⟨48385852607242466077751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 516115761143919638162677 48385852607242466077751)
                ·
                  rfl

theorem cell21_636060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 5].length) (baseStart_636060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636060 prefixEnd_636060 := by exact prefixLift 636060
  have htrace : WordTrace (prefixWord ++ tailWord_636060) baseStart_636060 baseEnd_636060 := by
    simpa [prefixWord, tailWord_636060, baseEnd_636060] using wordTrace_append hprefix tailTrace_636060
  have hstable : (prefixWord ++ tailWord_636060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636060).length < 2 ^ (prefixWord ++ tailWord_636060).sum := by decide
  have hdescent : baseEnd_636060 < baseStart_636060 := by decide
  rcases family_descends (prefixWord ++ tailWord_636060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636066 : List Nat := [3, 3, 1, 3, 3, 1, 1, 3, 3]
def baseStart_636066 : Nat := 118140960795 + 636066 * 2 ^ 59
def prefixEnd_636066 : Nat := 4983230072969 + 3 ^ 40 * 636066 * 2
def baseEnd_636066 : Nat := 145158927103472721133241

theorem tailTrace_636066 : CollatzResearch.WordTrace tailWord_636066 prefixEnd_636066 145158927103472721133241 := by
  unfold tailWord_636066
  simp only [CollatzResearch.WordTrace]
  refine ⟨5799808228412247067330013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15466155275765992179546701 5799808228412247067330013)
  ·
    refine ⟨2174928085654592650248755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5799808228412247067330013 2174928085654592650248755)
    ·
      refine ⟨3262392128481888975373133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2174928085654592650248755 3262392128481888975373133)
      ·
        refine ⟨1223397048180708365764925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3262392128481888975373133 1223397048180708365764925)
        ·
          refine ⟨458773893067765637161847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1223397048180708365764925 458773893067765637161847)
          ·
            refine ⟨688160839601648455742771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458773893067765637161847 688160839601648455742771)
            ·
              refine ⟨1032241259402472683614157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688160839601648455742771 1032241259402472683614157)
              ·
                refine ⟨387090472275927256355309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1032241259402472683614157 387090472275927256355309)
                ·
                  refine ⟨145158927103472721133241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387090472275927256355309 145158927103472721133241)
                  ·
                    rfl

theorem cell21_636066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_636066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636066 prefixEnd_636066 := by exact prefixLift 636066
  have htrace : WordTrace (prefixWord ++ tailWord_636066) baseStart_636066 baseEnd_636066 := by
    simpa [prefixWord, tailWord_636066, baseEnd_636066] using wordTrace_append hprefix tailTrace_636066
  have hstable : (prefixWord ++ tailWord_636066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636066).length < 2 ^ (prefixWord ++ tailWord_636066).sum := by decide
  have hdescent : baseEnd_636066 < baseStart_636066 := by decide
  rcases family_descends (prefixWord ++ tailWord_636066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636077 : List Nat := [1, 5, 2, 1, 4, 1, 7]
def baseStart_636077 : Nat := 118140960795 + 636077 * 2 ^ 59
def prefixEnd_636077 : Nat := 4983230072969 + 3 ^ 40 * 636077 * 2
def baseEnd_636077 : Nat := 16129048605926571827765

theorem tailTrace_636077 : CollatzResearch.WordTrace tailWord_636077 prefixEnd_636077 16129048605926571827765 := by
  unfold tailWord_636077
  simp only [CollatzResearch.WordTrace]
  refine ⟨23199634116609137147970485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15466422744406091431980323 23199634116609137147970485)
  ·
    refine ⟨2174965698432106607622233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23199634116609137147970485 2174965698432106607622233)
    ·
      refine ⟨1631224273824079955716675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2174965698432106607622233 1631224273824079955716675)
      ·
        refine ⟨2446836410736119933575013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1631224273824079955716675 2446836410736119933575013)
        ·
          refine ⟨458781827013022487545315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2446836410736119933575013 458781827013022487545315)
          ·
            refine ⟨688172740519533731317973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458781827013022487545315 688172740519533731317973)
            ·
              refine ⟨16129048605926571827765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 688172740519533731317973 16129048605926571827765)
              ·
                rfl

theorem cell21_636077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 7].length) (baseStart_636077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636077 prefixEnd_636077 := by exact prefixLift 636077
  have htrace : WordTrace (prefixWord ++ tailWord_636077) baseStart_636077 baseEnd_636077 := by
    simpa [prefixWord, tailWord_636077, baseEnd_636077] using wordTrace_append hprefix tailTrace_636077
  have hstable : (prefixWord ++ tailWord_636077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636077).length < 2 ^ (prefixWord ++ tailWord_636077).sum := by decide
  have hdescent : baseEnd_636077 < baseStart_636077 := by decide
  rcases family_descends (prefixWord ++ tailWord_636077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636150 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_636150 : Nat := 118140960795 + 636150 * 2 ^ 59
def prefixEnd_636150 : Nat := 4983230072969 + 3 ^ 40 * 636150 * 2
def baseEnd_636150 : Nat := 145178097047907241733069

theorem tailTrace_636150 : CollatzResearch.WordTrace tailWord_636150 prefixEnd_636150 145178097047907241733069 := by
  unfold tailWord_636150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1450143540334041913461119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15468197763563113743585269 1450143540334041913461119)
  ·
    refine ⟨2175215310501062870191679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1450143540334041913461119 2175215310501062870191679)
    ·
      refine ⟨3262822965751594305287519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2175215310501062870191679 3262822965751594305287519)
      ·
        refine ⟨4894234448627391457931279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3262822965751594305287519 4894234448627391457931279)
        ·
          refine ⟨7341351672941087186896919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4894234448627391457931279 7341351672941087186896919)
          ·
            refine ⟨11012027509411630780345379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7341351672941087186896919 11012027509411630780345379)
            ·
              refine ⟨16518041264117446170518069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11012027509411630780345379 16518041264117446170518069)
              ·
                refine ⟨1548566368511010578486069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16518041264117446170518069 1548566368511010578486069)
                ·
                  refine ⟨145178097047907241733069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1548566368511010578486069 145178097047907241733069)
                  ·
                    rfl

theorem cell21_636150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_636150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636150 prefixEnd_636150 := by exact prefixLift 636150
  have htrace : WordTrace (prefixWord ++ tailWord_636150) baseStart_636150 baseEnd_636150 := by
    simpa [prefixWord, tailWord_636150, baseEnd_636150] using wordTrace_append hprefix tailTrace_636150
  have hstable : (prefixWord ++ tailWord_636150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636150).length < 2 ^ (prefixWord ++ tailWord_636150).sum := by decide
  have hdescent : baseEnd_636150 < baseStart_636150 := by decide
  rcases family_descends (prefixWord ++ tailWord_636150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636260 : List Nat := [2, 3, 1, 1, 3, 3, 3, 2, 3]
def baseStart_636260 : Nat := 118140960795 + 636260 * 2 ^ 59
def prefixEnd_636260 : Nat := 4983230072969 + 3 ^ 40 * 636260 * 2
def baseEnd_636260 : Nat := 145203200546571494899511

theorem tailTrace_636260 : CollatzResearch.WordTrace tailWord_636260 prefixEnd_636260 145203200546571494899511 := by
  unfold tailWord_636260
  simp only [CollatzResearch.WordTrace]
  refine ⟨11603154337473079700941117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15470872449964106267921489 11603154337473079700941117)
  ·
    refine ⟨4351182876552404887852919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11603154337473079700941117 4351182876552404887852919)
    ·
      refine ⟨6526774314828607331779379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4351182876552404887852919 6526774314828607331779379)
      ·
        refine ⟨9790161472242910997669069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6526774314828607331779379 9790161472242910997669069)
        ·
          refine ⟨3671310552091091624125901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9790161472242910997669069 3671310552091091624125901)
          ·
            refine ⟨1376741457034159359047213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3671310552091091624125901 1376741457034159359047213)
            ·
              refine ⟨516278046387809759642705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1376741457034159359047213 516278046387809759642705)
              ·
                refine ⟨387208534790857319732029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516278046387809759642705 387208534790857319732029)
                ·
                  refine ⟨145203200546571494899511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387208534790857319732029 145203200546571494899511)
                  ·
                    rfl

theorem cell21_636260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_636260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636260 prefixEnd_636260 := by exact prefixLift 636260
  have htrace : WordTrace (prefixWord ++ tailWord_636260) baseStart_636260 baseEnd_636260 := by
    simpa [prefixWord, tailWord_636260, baseEnd_636260] using wordTrace_append hprefix tailTrace_636260
  have hstable : (prefixWord ++ tailWord_636260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636260).length < 2 ^ (prefixWord ++ tailWord_636260).sum := by decide
  have hdescent : baseEnd_636260 < baseStart_636260 := by decide
  rcases family_descends (prefixWord ++ tailWord_636260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636285 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 7]
def baseStart_636285 : Nat := 118140960795 + 636285 * 2 ^ 59
def prefixEnd_636285 : Nat := 4983230072969 + 3 ^ 40 * 636285 * 2
def baseEnd_636285 : Nat := 145208905887177006982793

theorem tailTrace_636285 : CollatzResearch.WordTrace tailWord_636285 prefixEnd_636285 145208905887177006982793 := by
  unfold tailWord_636285
  simp only [CollatzResearch.WordTrace]
  refine ⟨23207220499855588671542309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15471480333237059114361539 23207220499855588671542309)
  ·
    refine ⟨4351353843722922875914183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23207220499855588671542309 4351353843722922875914183)
    ·
      refine ⟨6527030765584384313871275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4351353843722922875914183 6527030765584384313871275)
      ·
        refine ⟨9790546148376576470806913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6527030765584384313871275 9790546148376576470806913)
        ·
          refine ⟨7342909611282432353105185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9790546148376576470806913 7342909611282432353105185)
          ·
            refine ⟨5507182208461824264828889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7342909611282432353105185 5507182208461824264828889)
            ·
              refine ⟨4130386656346368198621667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5507182208461824264828889 4130386656346368198621667)
              ·
                refine ⟨6195579984519552297932501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4130386656346368198621667 6195579984519552297932501)
                ·
                  refine ⟨145208905887177006982793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6195579984519552297932501 145208905887177006982793)
                  ·
                    rfl

theorem cell21_636285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_636285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636285 prefixEnd_636285 := by exact prefixLift 636285
  have htrace : WordTrace (prefixWord ++ tailWord_636285) baseStart_636285 baseEnd_636285 := by
    simpa [prefixWord, tailWord_636285, baseEnd_636285] using wordTrace_append hprefix tailTrace_636285
  have hstable : (prefixWord ++ tailWord_636285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636285).length < 2 ^ (prefixWord ++ tailWord_636285).sum := by decide
  have hdescent : baseEnd_636285 < baseStart_636285 := by decide
  rcases family_descends (prefixWord ++ tailWord_636285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636319 : List Nat := [1, 1, 2, 5, 1, 3, 1, 4, 3]
def baseStart_636319 : Nat := 118140960795 + 636319 * 2 ^ 59
def prefixEnd_636319 : Nat := 4983230072969 + 3 ^ 40 * 636319 * 2
def baseEnd_636319 : Nat := 145216665150400503416057

theorem tailTrace_636319 : CollatzResearch.WordTrace tailWord_636319 prefixEnd_636319 145216665150400503416057 := by
  unfold tailWord_636319
  simp only [CollatzResearch.WordTrace]
  refine ⟨23208460581732412478280011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15472307054488274985520007 23208460581732412478280011)
  ·
    refine ⟨34812690872598618717420017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23208460581732412478280011 34812690872598618717420017)
    ·
      refine ⟨26109518154448964038065013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34812690872598618717420017 26109518154448964038065013)
      ·
        refine ⟨2447767326979590378568595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26109518154448964038065013 2447767326979590378568595)
        ·
          refine ⟨3671650990469385567852893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2447767326979590378568595 3671650990469385567852893)
          ·
            refine ⟨1376869121426019587944835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3671650990469385567852893 1376869121426019587944835)
            ·
              refine ⟨2065303682139029381917253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1376869121426019587944835 2065303682139029381917253)
              ·
                refine ⟨387244440401068009109485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2065303682139029381917253 387244440401068009109485)
                ·
                  refine ⟨145216665150400503416057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387244440401068009109485 145216665150400503416057)
                  ·
                    rfl

theorem cell21_636319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 3].length) (baseStart_636319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636319 prefixEnd_636319 := by exact prefixLift 636319
  have htrace : WordTrace (prefixWord ++ tailWord_636319) baseStart_636319 baseEnd_636319 := by
    simpa [prefixWord, tailWord_636319, baseEnd_636319] using wordTrace_append hprefix tailTrace_636319
  have hstable : (prefixWord ++ tailWord_636319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636319).length < 2 ^ (prefixWord ++ tailWord_636319).sum := by decide
  have hdescent : baseEnd_636319 < baseStart_636319 := by decide
  rcases family_descends (prefixWord ++ tailWord_636319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636378 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 5]
def baseStart_636378 : Nat := 118140960795 + 636378 * 2 ^ 59
def prefixEnd_636378 : Nat := 4983230072969 + 3 ^ 40 * 636378 * 2
def baseEnd_636378 : Nat := 145230129754229511932603

theorem tailTrace_636378 : CollatzResearch.WordTrace tailWord_636378 prefixEnd_636378 145230129754229511932603 := by
  unfold tailWord_636378
  simp only [CollatzResearch.WordTrace]
  refine ⟨5802653122129666388669447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15473741659012443703118525 5802653122129666388669447)
  ·
    refine ⟨8703979683194499583004171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5802653122129666388669447 8703979683194499583004171)
    ·
      refine ⟨13055969524791749374506257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8703979683194499583004171 13055969524791749374506257)
      ·
        refine ⟨9791977143593812030879693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13055969524791749374506257 9791977143593812030879693)
        ·
          refine ⟨3671991428847679511579885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9791977143593812030879693 3671991428847679511579885)
          ·
            refine ⟨1376996785817879816842457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3671991428847679511579885 1376996785817879816842457)
            ·
              refine ⟨1032747589363409862631843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1376996785817879816842457 1032747589363409862631843)
              ·
                refine ⟨1549121384045114793947765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032747589363409862631843 1549121384045114793947765)
                ·
                  refine ⟨145230129754229511932603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1549121384045114793947765 145230129754229511932603)
                  ·
                    rfl

theorem cell21_636378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_636378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636378 prefixEnd_636378 := by exact prefixLift 636378
  have htrace : WordTrace (prefixWord ++ tailWord_636378) baseStart_636378 baseEnd_636378 := by
    simpa [prefixWord, tailWord_636378, baseEnd_636378] using wordTrace_append hprefix tailTrace_636378
  have hstable : (prefixWord ++ tailWord_636378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636378).length < 2 ^ (prefixWord ++ tailWord_636378).sum := by decide
  have hdescent : baseEnd_636378 < baseStart_636378 := by decide
  rcases family_descends (prefixWord ++ tailWord_636378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636423 : List Nat := [1, 1, 4, 3, 2, 3, 7]
def baseStart_636423 : Nat := 118140960795 + 636423 * 2 ^ 59
def prefixEnd_636423 : Nat := 4983230072969 + 3 ^ 40 * 636423 * 2
def baseEnd_636423 : Nat := 16137822151924381520279

theorem tailTrace_636423 : CollatzResearch.WordTrace tailWord_636423 prefixEnd_636423 16137822151924381520279 := by
  unfold tailWord_636423
  simp only [CollatzResearch.WordTrace]
  refine ⟨23212253773355638240065923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15474835848903758826710615 23212253773355638240065923)
  ·
    refine ⟨34818380660033457360098885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23212253773355638240065923 34818380660033457360098885)
    ·
      refine ⟨6528446373756273255018541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34818380660033457360098885 6528446373756273255018541)
      ·
        refine ⟨2448167390158602470631953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6528446373756273255018541 2448167390158602470631953)
        ·
          refine ⟨1836125542618951852973965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2448167390158602470631953 1836125542618951852973965)
          ·
            refine ⟨688547078482106944865237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1836125542618951852973965 688547078482106944865237)
            ·
              refine ⟨16137822151924381520279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 688547078482106944865237 16137822151924381520279)
              ·
                rfl

theorem cell21_636423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 7].length) (baseStart_636423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636423 prefixEnd_636423 := by exact prefixLift 636423
  have htrace : WordTrace (prefixWord ++ tailWord_636423) baseStart_636423 baseEnd_636423 := by
    simpa [prefixWord, tailWord_636423, baseEnd_636423] using wordTrace_append hprefix tailTrace_636423
  have hstable : (prefixWord ++ tailWord_636423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636423).length < 2 ^ (prefixWord ++ tailWord_636423).sum := by decide
  have hdescent : baseEnd_636423 < baseStart_636423 := by decide
  rcases family_descends (prefixWord ++ tailWord_636423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636429 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 5]
def baseStart_636429 : Nat := 118140960795 + 636429 * 2 ^ 59
def prefixEnd_636429 : Nat := 4983230072969 + 3 ^ 40 * 636429 * 2
def baseEnd_636429 : Nat := 145241768649064756582499

theorem tailTrace_636429 : CollatzResearch.WordTrace tailWord_636429 prefixEnd_636429 145241768649064756582499 := by
  unfold tailWord_636429
  simp only [CollatzResearch.WordTrace]
  refine ⟨23212472611333901264784341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15474981740889267509856227 23212472611333901264784341)
  ·
    refine ⟨544042326828138310893383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 23212472611333901264784341 544042326828138310893383)
    ·
      refine ⟨816063490242207466340075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 544042326828138310893383 816063490242207466340075)
      ·
        refine ⟨1224095235363311199510113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 816063490242207466340075 1224095235363311199510113)
        ·
          refine ⟨918071426522483399632585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1224095235363311199510113 918071426522483399632585)
          ·
            refine ⟨688553569891862549724439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 918071426522483399632585 688553569891862549724439)
            ·
              refine ⟨1032830354837793824586659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688553569891862549724439 1032830354837793824586659)
              ·
                refine ⟨1549245532256690736879989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032830354837793824586659 1549245532256690736879989)
                ·
                  refine ⟨145241768649064756582499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1549245532256690736879989 145241768649064756582499)
                  ·
                    rfl

theorem cell21_636429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_636429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636429 prefixEnd_636429 := by exact prefixLift 636429
  have htrace : WordTrace (prefixWord ++ tailWord_636429) baseStart_636429 baseEnd_636429 := by
    simpa [prefixWord, tailWord_636429, baseEnd_636429] using wordTrace_append hprefix tailTrace_636429
  have hstable : (prefixWord ++ tailWord_636429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636429).length < 2 ^ (prefixWord ++ tailWord_636429).sum := by decide
  have hdescent : baseEnd_636429 < baseStart_636429 := by decide
  rcases family_descends (prefixWord ++ tailWord_636429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636513 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 5]
def baseStart_636513 : Nat := 118140960795 + 636513 * 2 ^ 59
def prefixEnd_636513 : Nat := 4983230072969 + 3 ^ 40 * 636513 * 2
def baseEnd_636513 : Nat := 145260938593499277182327

theorem tailTrace_636513 : CollatzResearch.WordTrace tailWord_636513 prefixEnd_636513 145260938593499277182327 := by
  unfold tailWord_636513
  simp only [CollatzResearch.WordTrace]
  refine ⟨23215536343029583610842193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15477024228686389073894795 23215536343029583610842193)
  ·
    refine ⟨17411652257272187708131645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23215536343029583610842193 17411652257272187708131645)
    ·
      refine ⟨6529369596477070390549367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17411652257272187708131645 6529369596477070390549367)
      ·
        refine ⟨9794054394715605585824051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6529369596477070390549367 9794054394715605585824051)
        ·
          refine ⟨14691081592073408378736077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9794054394715605585824051 14691081592073408378736077)
          ·
            refine ⟨5509155597027528142026029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14691081592073408378736077 5509155597027528142026029)
            ·
              refine ⟨2065933348885323053259761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5509155597027528142026029 2065933348885323053259761)
              ·
                refine ⟨1549450011663992289944821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2065933348885323053259761 1549450011663992289944821)
                ·
                  refine ⟨145260938593499277182327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1549450011663992289944821 145260938593499277182327)
                  ·
                    rfl

theorem cell21_636513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_636513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636513 prefixEnd_636513 := by exact prefixLift 636513
  have htrace : WordTrace (prefixWord ++ tailWord_636513) baseStart_636513 baseEnd_636513 := by
    simpa [prefixWord, tailWord_636513, baseEnd_636513] using wordTrace_append hprefix tailTrace_636513
  have hstable : (prefixWord ++ tailWord_636513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636513).length < 2 ^ (prefixWord ++ tailWord_636513).sum := by decide
  have hdescent : baseEnd_636513 < baseStart_636513 := by decide
  rcases family_descends (prefixWord ++ tailWord_636513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636527 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 6]
def baseStart_636527 : Nat := 118140960795 + 636527 * 2 ^ 59
def prefixEnd_636527 : Nat := 4983230072969 + 3 ^ 40 * 636527 * 2
def baseEnd_636527 : Nat := 145264133584238363948965

theorem tailTrace_636527 : CollatzResearch.WordTrace tailWord_636527 prefixEnd_636527 145264133584238363948965 := by
  unfold tailWord_636527
  simp only [CollatzResearch.WordTrace]
  refine ⟨23216046964978864001851835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15477364643319242667901223 23216046964978864001851835)
  ·
    refine ⟨34824070447468296002777753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23216046964978864001851835 34824070447468296002777753)
    ·
      refine ⟨26118052835601222002083315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34824070447468296002777753 26118052835601222002083315)
      ·
        refine ⟨39177079253401833003124973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26118052835601222002083315 39177079253401833003124973)
        ·
          refine ⟨14691404720025687376171865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39177079253401833003124973 14691404720025687376171865)
          ·
            refine ⟨11018553540019265532128899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14691404720025687376171865 11018553540019265532128899)
            ·
              refine ⟨16527830310028898298193349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11018553540019265532128899 16527830310028898298193349)
              ·
                refine ⟨3098968183130418430911253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16527830310028898298193349 3098968183130418430911253)
                ·
                  refine ⟨145264133584238363948965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3098968183130418430911253 145264133584238363948965)
                  ·
                    rfl

theorem cell21_636527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 6].length) (baseStart_636527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636527 prefixEnd_636527 := by exact prefixLift 636527
  have htrace : WordTrace (prefixWord ++ tailWord_636527) baseStart_636527 baseEnd_636527 := by
    simpa [prefixWord, tailWord_636527, baseEnd_636527] using wordTrace_append hprefix tailTrace_636527
  have hstable : (prefixWord ++ tailWord_636527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636527).length < 2 ^ (prefixWord ++ tailWord_636527).sum := by decide
  have hdescent : baseEnd_636527 < baseStart_636527 := by decide
  rcases family_descends (prefixWord ++ tailWord_636527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636606 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_636606 : Nat := 118140960795 + 636606 * 2 ^ 59
def prefixEnd_636606 : Nat := 4983230072969 + 3 ^ 40 * 636606 * 2
def baseEnd_636606 : Nat := 145282162460551782132137

theorem tailTrace_636606 : CollatzResearch.WordTrace tailWord_636606 prefixEnd_636606 145282162460551782132137 := by
  unfold tailWord_636606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2902366041461582561747209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15479285554461773662651781 2902366041461582561747209)
  ·
    refine ⟨2176774531096186921310407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2902366041461582561747209 2176774531096186921310407)
    ·
      refine ⟨3265161796644280381965611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2176774531096186921310407 3265161796644280381965611)
      ·
        refine ⟨4897742694966420572948417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3265161796644280381965611 4897742694966420572948417)
        ·
          refine ⟨3673307021224815429711313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4897742694966420572948417 3673307021224815429711313)
          ·
            refine ⟨2754980265918611572283485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3673307021224815429711313 2754980265918611572283485)
            ·
              refine ⟨1033117599719479339606307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2754980265918611572283485 1033117599719479339606307)
              ·
                refine ⟨1549676399579219009409461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1033117599719479339606307 1549676399579219009409461)
                ·
                  refine ⟨145282162460551782132137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1549676399579219009409461 145282162460551782132137)
                  ·
                    rfl

theorem cell21_636606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_636606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636606 prefixEnd_636606 := by exact prefixLift 636606
  have htrace : WordTrace (prefixWord ++ tailWord_636606) baseStart_636606 baseEnd_636606 := by
    simpa [prefixWord, tailWord_636606, baseEnd_636606] using wordTrace_append hprefix tailTrace_636606
  have hstable : (prefixWord ++ tailWord_636606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636606).length < 2 ^ (prefixWord ++ tailWord_636606).sum := by decide
  have hdescent : baseEnd_636606 < baseStart_636606 := by decide
  rcases family_descends (prefixWord ++ tailWord_636606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636634 : List Nat := [3, 1, 1, 2, 2, 3, 2, 7]
def baseStart_636634 : Nat := 118140960795 + 636634 * 2 ^ 59
def prefixEnd_636634 : Nat := 4983230072969 + 3 ^ 40 * 636634 * 2
def baseEnd_636634 : Nat := 48429517480676651888471

theorem tailTrace_636634 : CollatzResearch.WordTrace tailWord_636634 prefixEnd_636634 48429517480676651888471 := by
  unfold tailWord_636634
  simp only [CollatzResearch.WordTrace]
  refine ⟨5804987393897805318999239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15479966383727480850664637 5804987393897805318999239)
  ·
    refine ⟨8707481090846707978498859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5804987393897805318999239 8707481090846707978498859)
    ·
      refine ⟨13061221636270061967748289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8707481090846707978498859 13061221636270061967748289)
      ·
        refine ⟨9795916227202546475811217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13061221636270061967748289 9795916227202546475811217)
        ·
          refine ⟨7346937170401909856858413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9795916227202546475811217 7346937170401909856858413)
          ·
            refine ⟨2755101438900716196321905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7346937170401909856858413 2755101438900716196321905)
            ·
              refine ⟨2066326079175537147241429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2755101438900716196321905 2066326079175537147241429)
              ·
                refine ⟨48429517480676651888471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2066326079175537147241429 48429517480676651888471)
                ·
                  rfl

theorem cell21_636634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_636634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636634 prefixEnd_636634 := by exact prefixLift 636634
  have htrace : WordTrace (prefixWord ++ tailWord_636634) baseStart_636634 baseEnd_636634 := by
    simpa [prefixWord, tailWord_636634, baseEnd_636634] using wordTrace_append hprefix tailTrace_636634
  have hstable : (prefixWord ++ tailWord_636634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636634).length < 2 ^ (prefixWord ++ tailWord_636634).sum := by decide
  have hdescent : baseEnd_636634 < baseStart_636634 := by decide
  rcases family_descends (prefixWord ++ tailWord_636634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636775 : List Nat := [1, 1, 5, 1, 2, 1, 5, 2, 3]
def baseStart_636775 : Nat := 118140960795 + 636775 * 2 ^ 59
def prefixEnd_636775 : Nat := 4983230072969 + 3 ^ 40 * 636775 * 2
def baseEnd_636775 : Nat := 145320730563045043815125

theorem tailTrace_636775 : CollatzResearch.WordTrace tailWord_636775 prefixEnd_636775 145320730563045043815125 := by
  unfold tailWord_636775
  simp only [CollatzResearch.WordTrace]
  refine ⟨23225092268080402356879779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15483394845386934904586519 23225092268080402356879779)
  ·
    refine ⟨34837638402120603535319669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23225092268080402356879779 34837638402120603535319669)
    ·
      refine ⟨3266028600198806581436219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34837638402120603535319669 3266028600198806581436219)
      ·
        refine ⟨4899042900298209872154329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3266028600198806581436219 4899042900298209872154329)
        ·
          refine ⟨3674282175223657404115747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4899042900298209872154329 3674282175223657404115747)
          ·
            refine ⟨5511423262835486106173621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3674282175223657404115747 5511423262835486106173621)
            ·
              refine ⟨516695930890826822453777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5511423262835486106173621 516695930890826822453777)
              ·
                refine ⟨387521948168120116840333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516695930890826822453777 387521948168120116840333)
                ·
                  refine ⟨145320730563045043815125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387521948168120116840333 145320730563045043815125)
                  ·
                    rfl

theorem cell21_636775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 3].length) (baseStart_636775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636775 prefixEnd_636775 := by exact prefixLift 636775
  have htrace : WordTrace (prefixWord ++ tailWord_636775) baseStart_636775 baseEnd_636775 := by
    simpa [prefixWord, tailWord_636775, baseEnd_636775] using wordTrace_append hprefix tailTrace_636775
  have hstable : (prefixWord ++ tailWord_636775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636775).length < 2 ^ (prefixWord ++ tailWord_636775).sum := by decide
  have hdescent : baseEnd_636775 < baseStart_636775 := by decide
  rcases family_descends (prefixWord ++ tailWord_636775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636800 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 7]
def baseStart_636800 : Nat := 118140960795 + 636800 * 2 ^ 59
def prefixEnd_636800 : Nat := 4983230072969 + 3 ^ 40 * 636800 * 2
def baseEnd_636800 : Nat := 145326435903650555898407

theorem tailTrace_636800 : CollatzResearch.WordTrace tailWord_636800 prefixEnd_636800 145326435903650555898407 := by
  unfold tailWord_636800
  simp only [CollatzResearch.WordTrace]
  refine ⟨11613002046494915813269927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15484002728659887751026569 11613002046494915813269927)
  ·
    refine ⟨17419503069742373719904891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11613002046494915813269927 17419503069742373719904891)
    ·
      refine ⟨26129254604613560579857337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17419503069742373719904891 26129254604613560579857337)
      ·
        refine ⟨19596940953460170434893003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26129254604613560579857337 19596940953460170434893003)
        ·
          refine ⟨29395411430190255652339505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19596940953460170434893003 29395411430190255652339505)
          ·
            refine ⟨22046558572642691739254629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29395411430190255652339505 22046558572642691739254629)
            ·
              refine ⟨4133729732370504701110243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22046558572642691739254629 4133729732370504701110243)
              ·
                refine ⟨6200594598555757051665365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4133729732370504701110243 6200594598555757051665365)
                ·
                  refine ⟨145326435903650555898407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6200594598555757051665365 145326435903650555898407)
                  ·
                    rfl

theorem cell21_636800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_636800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636800 prefixEnd_636800 := by exact prefixLift 636800
  have htrace : WordTrace (prefixWord ++ tailWord_636800) baseStart_636800 baseEnd_636800 := by
    simpa [prefixWord, tailWord_636800, baseEnd_636800] using wordTrace_append hprefix tailTrace_636800
  have hstable : (prefixWord ++ tailWord_636800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636800).length < 2 ^ (prefixWord ++ tailWord_636800).sum := by decide
  have hdescent : baseEnd_636800 < baseStart_636800 := by decide
  rcases family_descends (prefixWord ++ tailWord_636800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636882 : List Nat := [3, 2, 2, 3, 2, 2, 1, 2, 4]
def baseStart_636882 : Nat := 118140960795 + 636882 * 2 ^ 59
def prefixEnd_636882 : Nat := 4983230072969 + 3 ^ 40 * 636882 * 2
def baseEnd_636882 : Nat := 145345149420836635531573

theorem tailTrace_636882 : CollatzResearch.WordTrace tailWord_636882 prefixEnd_636882 145345149420836635531573 := by
  unfold tailWord_636882
  simp only [CollatzResearch.WordTrace]
  refine ⟨5807248719673189907756225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15485996585795173087349933 5807248719673189907756225)
  ·
    refine ⟨4355436539754892430817169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5807248719673189907756225 4355436539754892430817169)
    ·
      refine ⟨3266577404816169323112877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4355436539754892430817169 3266577404816169323112877)
      ·
        refine ⟨1224966526806063496167329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3266577404816169323112877 1224966526806063496167329)
        ·
          refine ⟨918724895104547622125497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1224966526806063496167329 918724895104547622125497)
          ·
            refine ⟨689043671328410716594123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 918724895104547622125497 689043671328410716594123)
            ·
              refine ⟨1033565506992616074891185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689043671328410716594123 1033565506992616074891185)
              ·
                refine ⟨775174130244462056168389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1033565506992616074891185 775174130244462056168389)
                ·
                  refine ⟨145345149420836635531573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 775174130244462056168389 145345149420836635531573)
                  ·
                    rfl

theorem cell21_636882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_636882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636882 prefixEnd_636882 := by exact prefixLift 636882
  have htrace : WordTrace (prefixWord ++ tailWord_636882) baseStart_636882 baseEnd_636882 := by
    simpa [prefixWord, tailWord_636882, baseEnd_636882] using wordTrace_append hprefix tailTrace_636882
  have hstable : (prefixWord ++ tailWord_636882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636882).length < 2 ^ (prefixWord ++ tailWord_636882).sum := by decide
  have hdescent : baseEnd_636882 < baseStart_636882 := by decide
  rcases family_descends (prefixWord ++ tailWord_636882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636907 : List Nat := [1, 1, 1, 1, 2, 3, 1, 7, 4]
def baseStart_636907 : Nat := 118140960795 + 636907 * 2 ^ 59
def prefixEnd_636907 : Nat := 4983230072969 + 3 ^ 40 * 636907 * 2
def baseEnd_636907 : Nat := 145350854761442147614855

theorem tailTrace_636907 : CollatzResearch.WordTrace tailWord_636907 prefixEnd_636907 145350854761442147614855 := by
  unfold tailWord_636907
  simp only [CollatzResearch.WordTrace]
  refine ⟨23229906703602188900684975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15486604469068125933789983 23229906703602188900684975)
  ·
    refine ⟨34844860055403283351027463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23229906703602188900684975 34844860055403283351027463)
    ·
      refine ⟨52267290083104925026541195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34844860055403283351027463 52267290083104925026541195)
      ·
        refine ⟨78400935124657387539811793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52267290083104925026541195 78400935124657387539811793)
        ·
          refine ⟨58800701343493040654858845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78400935124657387539811793 58800701343493040654858845)
          ·
            refine ⟨22050263003809890245572067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58800701343493040654858845 22050263003809890245572067)
            ·
              refine ⟨33075394505714835368358101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22050263003809890245572067 33075394505714835368358101)
              ·
                refine ⟨775204558727691453945893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 33075394505714835368358101 775204558727691453945893)
                ·
                  refine ⟨145350854761442147614855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 775204558727691453945893 145350854761442147614855)
                  ·
                    rfl

theorem cell21_636907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 4].length) (baseStart_636907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_636907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_636907 prefixEnd_636907 := by exact prefixLift 636907
  have htrace : WordTrace (prefixWord ++ tailWord_636907) baseStart_636907 baseEnd_636907 := by
    simpa [prefixWord, tailWord_636907, baseEnd_636907] using wordTrace_append hprefix tailTrace_636907
  have hstable : (prefixWord ++ tailWord_636907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636907).length < 2 ^ (prefixWord ++ tailWord_636907).sum := by decide
  have hdescent : baseEnd_636907 < baseStart_636907 := by decide
  rcases family_descends (prefixWord ++ tailWord_636907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637028 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 7]
def baseStart_637028 : Nat := 118140960795 + 637028 * 2 ^ 59
def prefixEnd_637028 : Nat := 4983230072969 + 3 ^ 40 * 637028 * 2
def baseEnd_637028 : Nat := 145378468609972826097941

theorem tailTrace_637028 : CollatzResearch.WordTrace tailWord_637028 prefixEnd_637028 145378468609972826097941 := by
  unfold tailWord_637028
  simp only [CollatzResearch.WordTrace]
  refine ⟨11617159968081913282919869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15489546624109217710559825 11617159968081913282919869)
  ·
    refine ⟨4356434988030717481094951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11617159968081913282919869 4356434988030717481094951)
    ·
      refine ⟨6534652482046076221642427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4356434988030717481094951 6534652482046076221642427)
      ·
        refine ⟨9801978723069114332463641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6534652482046076221642427 9801978723069114332463641)
        ·
          refine ⟨7351484042301835749347731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9801978723069114332463641 7351484042301835749347731)
          ·
            refine ⟨11027226063452753624021597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7351484042301835749347731 11027226063452753624021597)
            ·
              refine ⟨4135209773794782609008099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11027226063452753624021597 4135209773794782609008099)
              ·
                refine ⟨6202814660692173913512149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4135209773794782609008099 6202814660692173913512149)
                ·
                  refine ⟨145378468609972826097941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6202814660692173913512149 145378468609972826097941)
                  ·
                    rfl

theorem cell21_637028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_637028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637028 prefixEnd_637028 := by exact prefixLift 637028
  have htrace : WordTrace (prefixWord ++ tailWord_637028) baseStart_637028 baseEnd_637028 := by
    simpa [prefixWord, tailWord_637028, baseEnd_637028] using wordTrace_append hprefix tailTrace_637028
  have hstable : (prefixWord ++ tailWord_637028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637028).length < 2 ^ (prefixWord ++ tailWord_637028).sum := by decide
  have hdescent : baseEnd_637028 < baseStart_637028 := by decide
  rcases family_descends (prefixWord ++ tailWord_637028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637059 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 6]
def baseStart_637059 : Nat := 118140960795 + 637059 * 2 ^ 59
def prefixEnd_637059 : Nat := 4983230072969 + 3 ^ 40 * 637059 * 2
def baseEnd_637059 : Nat := 145385543232323661081211

theorem tailTrace_637059 : CollatzResearch.WordTrace tailWord_637059 prefixEnd_637059 145385543232323661081211 := by
  unfold tailWord_637059
  simp only [CollatzResearch.WordTrace]
  refine ⟨23235450599051518860218231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15490300399367679240145487 23235450599051518860218231)
  ·
    refine ⟨34853175898577278290327347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23235450599051518860218231 34853175898577278290327347)
    ·
      refine ⟨52279763847865917435491021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34853175898577278290327347 52279763847865917435491021)
      ·
        refine ⟨19604911442949719038309133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52279763847865917435491021 19604911442949719038309133)
        ·
          refine ⟨7351841791106144639365925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19604911442949719038309133 7351841791106144639365925)
          ·
            refine ⟨1378470335832402119881111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7351841791106144639365925 1378470335832402119881111)
            ·
              refine ⟨2067705503748603179821667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1378470335832402119881111 2067705503748603179821667)
              ·
                refine ⟨3101558255622904769732501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2067705503748603179821667 3101558255622904769732501)
                ·
                  refine ⟨145385543232323661081211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3101558255622904769732501 145385543232323661081211)
                  ·
                    rfl

theorem cell21_637059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 6].length) (baseStart_637059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637059 prefixEnd_637059 := by exact prefixLift 637059
  have htrace : WordTrace (prefixWord ++ tailWord_637059) baseStart_637059 baseEnd_637059 := by
    simpa [prefixWord, tailWord_637059, baseEnd_637059] using wordTrace_append hprefix tailTrace_637059
  have hstable : (prefixWord ++ tailWord_637059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637059).length < 2 ^ (prefixWord ++ tailWord_637059).sum := by decide
  have hdescent : baseEnd_637059 < baseStart_637059 := by decide
  rcases family_descends (prefixWord ++ tailWord_637059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637135 : List Nat := [1, 1, 2, 1, 1, 3, 5, 3, 4]
def baseStart_637135 : Nat := 118140960795 + 637135 * 2 ^ 59
def prefixEnd_637135 : Nat := 4983230072969 + 3 ^ 40 * 637135 * 2
def baseEnd_637135 : Nat := 145402887467764417814389

theorem tailTrace_637135 : CollatzResearch.WordTrace tailWord_637135 prefixEnd_637135 145402887467764417814389 := by
  unfold tailWord_637135
  simp only [CollatzResearch.WordTrace]
  refine ⟨23238222546776183839984859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15492148364517455893323239 23238222546776183839984859)
  ·
    refine ⟨34857333820164275759977289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23238222546776183839984859 34857333820164275759977289)
    ·
      refine ⟨26143000365123206819982967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34857333820164275759977289 26143000365123206819982967)
      ·
        refine ⟨39214500547684810229974451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26143000365123206819982967 39214500547684810229974451)
        ·
          refine ⟨58821750821527215344961677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39214500547684810229974451 58821750821527215344961677)
          ·
            refine ⟨22058156558072705754360629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58821750821527215344961677 22058156558072705754360629)
            ·
              refine ⟨2067952177319316164471309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22058156558072705754360629 2067952177319316164471309)
              ·
                refine ⟨775482066494743561676741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2067952177319316164471309 775482066494743561676741)
                ·
                  refine ⟨145402887467764417814389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 775482066494743561676741 145402887467764417814389)
                  ·
                    rfl

theorem cell21_637135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 4].length) (baseStart_637135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637135 prefixEnd_637135 := by exact prefixLift 637135
  have htrace : WordTrace (prefixWord ++ tailWord_637135) baseStart_637135 baseEnd_637135 := by
    simpa [prefixWord, tailWord_637135, baseEnd_637135] using wordTrace_append hprefix tailTrace_637135
  have hstable : (prefixWord ++ tailWord_637135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637135).length < 2 ^ (prefixWord ++ tailWord_637135).sum := by decide
  have hdescent : baseEnd_637135 < baseStart_637135 := by decide
  rcases family_descends (prefixWord ++ tailWord_637135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637256 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 5]
def baseStart_637256 : Nat := 118140960795 + 637256 * 2 ^ 59
def prefixEnd_637256 : Nat := 4983230072969 + 3 ^ 40 * 637256 * 2
def baseEnd_637256 : Nat := 145430501316295096297475

theorem tailTrace_637256 : CollatzResearch.WordTrace tailWord_637256 prefixEnd_637256 145430501316295096297475 := by
  unfold tailWord_637256
  simp only [CollatzResearch.WordTrace]
  refine ⟨11621317889668910752569811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15495090519558547670093081 11621317889668910752569811)
  ·
    refine ⟨17431976834503366128854717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11621317889668910752569811 17431976834503366128854717)
    ·
      refine ⟨6536991312938762298320519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17431976834503366128854717 6536991312938762298320519)
      ·
        refine ⟨9805486969408143447480779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6536991312938762298320519 9805486969408143447480779)
        ·
          refine ⟨14708230454112215171221169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9805486969408143447480779 14708230454112215171221169)
          ·
            refine ⟨11031172840584161378415877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14708230454112215171221169 11031172840584161378415877)
            ·
              refine ⟨2068344907609530258452977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11031172840584161378415877 2068344907609530258452977)
              ·
                refine ⟨1551258680707147693839733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2068344907609530258452977 1551258680707147693839733)
                ·
                  refine ⟨145430501316295096297475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1551258680707147693839733 145430501316295096297475)
                  ·
                    rfl

theorem cell21_637256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_637256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637256 prefixEnd_637256 := by exact prefixLift 637256
  have htrace : WordTrace (prefixWord ++ tailWord_637256) baseStart_637256 baseEnd_637256 := by
    simpa [prefixWord, tailWord_637256, baseEnd_637256] using wordTrace_append hprefix tailTrace_637256
  have hstable : (prefixWord ++ tailWord_637256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637256).length < 2 ^ (prefixWord ++ tailWord_637256).sum := by decide
  have hdescent : baseEnd_637256 < baseStart_637256 := by decide
  rcases family_descends (prefixWord ++ tailWord_637256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637276 : List Nat := [2, 2, 4, 3, 2, 1, 7]
def baseStart_637276 : Nat := 118140960795 + 637276 * 2 ^ 59
def prefixEnd_637276 : Nat := 4983230072969 + 3 ^ 40 * 637276 * 2
def baseEnd_637276 : Nat := 16159451732086611773789

theorem tailTrace_637276 : CollatzResearch.WordTrace tailWord_637276 prefixEnd_637276 16159451732086611773789 := by
  unfold tailWord_637276
  simp only [CollatzResearch.WordTrace]
  refine ⟨11621682619632682460433841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15495576826176909947245121 11621682619632682460433841)
  ·
    refine ⟨8716261964724511845325381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11621682619632682460433841 8716261964724511845325381)
    ·
      refine ⟨1634299118385845970998509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8716261964724511845325381 1634299118385845970998509)
      ·
        refine ⟨612862169394692239124441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1634299118385845970998509 612862169394692239124441)
        ·
          refine ⟨459646627046019179343331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 612862169394692239124441 459646627046019179343331)
          ·
            refine ⟨689469940569028769014997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459646627046019179343331 689469940569028769014997)
            ·
              refine ⟨16159451732086611773789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 689469940569028769014997 16159451732086611773789)
              ·
                rfl

theorem cell21_637276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 7].length) (baseStart_637276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637276 prefixEnd_637276 := by exact prefixLift 637276
  have htrace : WordTrace (prefixWord ++ tailWord_637276) baseStart_637276 baseEnd_637276 := by
    simpa [prefixWord, tailWord_637276, baseEnd_637276] using wordTrace_append hprefix tailTrace_637276
  have hstable : (prefixWord ++ tailWord_637276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637276).length < 2 ^ (prefixWord ++ tailWord_637276).sum := by decide
  have hdescent : baseEnd_637276 < baseStart_637276 := by decide
  rcases family_descends (prefixWord ++ tailWord_637276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637287 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 6]
def baseStart_637287 : Nat := 118140960795 + 637287 * 2 ^ 59
def prefixEnd_637287 : Nat := 4983230072969 + 3 ^ 40 * 637287 * 2
def baseEnd_637287 : Nat := 145437575938645931280745

theorem tailTrace_637287 : CollatzResearch.WordTrace tailWord_637287 prefixEnd_637287 145437575938645931280745 := by
  unfold tailWord_637287
  simp only [CollatzResearch.WordTrace]
  refine ⟨23243766442225513799518115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15495844294817009199678743 23243766442225513799518115)
  ·
    refine ⟨34865649663338270699277173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23243766442225513799518115 34865649663338270699277173)
    ·
      refine ⟨3268654655937962878057235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34865649663338270699277173 3268654655937962878057235)
      ·
        refine ⟨4902981983906944317085853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3268654655937962878057235 4902981983906944317085853)
        ·
          refine ⟨1838618243965104118907195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4902981983906944317085853 1838618243965104118907195)
          ·
            refine ⟨2757927365947656178360793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1838618243965104118907195 2757927365947656178360793)
            ·
              refine ⟨2068445524460742133770595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2757927365947656178360793 2068445524460742133770595)
              ·
                refine ⟨3102668286691113200655893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2068445524460742133770595 3102668286691113200655893)
                ·
                  refine ⟨145437575938645931280745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3102668286691113200655893 145437575938645931280745)
                  ·
                    rfl

theorem cell21_637287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 6].length) (baseStart_637287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637287 prefixEnd_637287 := by exact prefixLift 637287
  have htrace : WordTrace (prefixWord ++ tailWord_637287) baseStart_637287 baseEnd_637287 := by
    simpa [prefixWord, tailWord_637287, baseEnd_637287] using wordTrace_append hprefix tailTrace_637287
  have hstable : (prefixWord ++ tailWord_637287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637287).length < 2 ^ (prefixWord ++ tailWord_637287).sum := by decide
  have hdescent : baseEnd_637287 < baseStart_637287 := by decide
  rcases family_descends (prefixWord ++ tailWord_637287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637290 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 5]
def baseStart_637290 : Nat := 118140960795 + 637290 * 2 ^ 59
def prefixEnd_637290 : Nat := 4983230072969 + 3 ^ 40 * 637290 * 2
def baseEnd_637290 : Nat := 145438260579518592730739

theorem tailTrace_637290 : CollatzResearch.WordTrace tailWord_637290 prefixEnd_637290 145438260579518592730739 := by
  unfold tailWord_637290
  simp only [CollatzResearch.WordTrace]
  refine ⟨5810968965303661327969331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15495917240809763541251549 5810968965303661327969331)
  ·
    refine ⟨8716453447955491991953997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5810968965303661327969331 8716453447955491991953997)
    ·
      refine ⟨3268670042983309496982749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8716453447955491991953997 3268670042983309496982749)
      ·
        refine ⟨1225751266118741061368531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3268670042983309496982749 1225751266118741061368531)
        ·
          refine ⟨1838626899178111592052797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1225751266118741061368531 1838626899178111592052797)
          ·
            refine ⟨689485087191791847019799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1838626899178111592052797 689485087191791847019799)
            ·
              refine ⟨1034227630787687770529699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689485087191791847019799 1034227630787687770529699)
              ·
                refine ⟨1551341446181531655794549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034227630787687770529699 1551341446181531655794549)
                ·
                  refine ⟨145438260579518592730739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1551341446181531655794549 145438260579518592730739)
                  ·
                    rfl

theorem cell21_637290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_637290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637290 prefixEnd_637290 := by exact prefixLift 637290
  have htrace : WordTrace (prefixWord ++ tailWord_637290) baseStart_637290 baseEnd_637290 := by
    simpa [prefixWord, tailWord_637290, baseEnd_637290] using wordTrace_append hprefix tailTrace_637290
  have hstable : (prefixWord ++ tailWord_637290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637290).length < 2 ^ (prefixWord ++ tailWord_637290).sum := by decide
  have hdescent : baseEnd_637290 < baseStart_637290 := by decide
  rcases family_descends (prefixWord ++ tailWord_637290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637349 : List Nat := [1, 3, 1, 2, 1, 1, 5, 4, 3]
def baseStart_637349 : Nat := 118140960795 + 637349 * 2 ^ 59
def prefixEnd_637349 : Nat := 4983230072969 + 3 ^ 40 * 637349 * 2
def baseEnd_637349 : Nat := 145451725183347601247285

theorem tailTrace_637349 : CollatzResearch.WordTrace tailWord_637349 prefixEnd_637349 145451725183347601247285 := by
  unfold tailWord_637349
  simp only [CollatzResearch.WordTrace]
  refine ⟨23246027768000898388275101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15497351845333932258850067 23246027768000898388275101)
  ·
    refine ⟨8717260413000336895603163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23246027768000898388275101 8717260413000336895603163)
    ·
      refine ⟨13075890619500505343404745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8717260413000336895603163 13075890619500505343404745)
      ·
        refine ⟨9806917964625379007553559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13075890619500505343404745 9806917964625379007553559)
        ·
          refine ⟨14710376946938068511330339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9806917964625379007553559 14710376946938068511330339)
          ·
            refine ⟨22065565420407102766995509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14710376946938068511330339 22065565420407102766995509)
            ·
              refine ⟨2068646758163165884405829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22065565420407102766995509 2068646758163165884405829)
              ·
                refine ⟨387871267155593603326093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2068646758163165884405829 387871267155593603326093)
                ·
                  refine ⟨145451725183347601247285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387871267155593603326093 145451725183347601247285)
                  ·
                    rfl

theorem cell21_637349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_637349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637349 prefixEnd_637349 := by exact prefixLift 637349
  have htrace : WordTrace (prefixWord ++ tailWord_637349) baseStart_637349 baseEnd_637349 := by
    simpa [prefixWord, tailWord_637349, baseEnd_637349] using wordTrace_append hprefix tailTrace_637349
  have hstable : (prefixWord ++ tailWord_637349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637349).length < 2 ^ (prefixWord ++ tailWord_637349).sum := by decide
  have hdescent : baseEnd_637349 < baseStart_637349 := by decide
  rcases family_descends (prefixWord ++ tailWord_637349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637391 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 9]
def baseStart_637391 : Nat := 118140960795 + 637391 * 2 ^ 59
def prefixEnd_637391 : Nat := 4983230072969 + 3 ^ 40 * 637391 * 2
def baseEnd_637391 : Nat := 145461310155564861547199

theorem tailTrace_637391 : CollatzResearch.WordTrace tailWord_637391 prefixEnd_637391 145461310155564861547199 := by
  unfold tailWord_637391
  simp only [CollatzResearch.WordTrace]
  refine ⟨23247559633848739561304027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15498373089232493040869351 23247559633848739561304027)
  ·
    refine ⟨34871339450773109341956041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23247559633848739561304027 34871339450773109341956041)
    ·
      refine ⟨26153504588079832006467031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34871339450773109341956041 26153504588079832006467031)
      ·
        refine ⟨39230256882119748009700547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26153504588079832006467031 39230256882119748009700547)
        ·
          refine ⟨58845385323179622014550821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39230256882119748009700547 58845385323179622014550821)
          ·
            refine ⟨11033509748096179127728279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58845385323179622014550821 11033509748096179127728279)
            ·
              refine ⟨16550264622144268691592419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11033509748096179127728279 16550264622144268691592419)
              ·
                refine ⟨24825396933216403037388629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16550264622144268691592419 24825396933216403037388629)
                ·
                  refine ⟨145461310155564861547199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24825396933216403037388629 145461310155564861547199)
                  ·
                    rfl

theorem cell21_637391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 9].length) (baseStart_637391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637391 prefixEnd_637391 := by exact prefixLift 637391
  have htrace : WordTrace (prefixWord ++ tailWord_637391) baseStart_637391 baseEnd_637391 := by
    simpa [prefixWord, tailWord_637391, baseEnd_637391] using wordTrace_append hprefix tailTrace_637391
  have hstable : (prefixWord ++ tailWord_637391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637391).length < 2 ^ (prefixWord ++ tailWord_637391).sum := by decide
  have hdescent : baseEnd_637391 < baseStart_637391 := by decide
  rcases family_descends (prefixWord ++ tailWord_637391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637408 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 5]
def baseStart_637408 : Nat := 118140960795 + 637408 * 2 ^ 59
def prefixEnd_637408 : Nat := 4983230072969 + 3 ^ 40 * 637408 * 2
def baseEnd_637408 : Nat := 145465189787176609763831

theorem tailTrace_637408 : CollatzResearch.WordTrace tailWord_637408 prefixEnd_637408 145465189787176609763831 := by
  unfold tailWord_637408
  simp only [CollatzResearch.WordTrace]
  refine ⟨11624089837393575732336439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15498786449858100976448585 11624089837393575732336439)
  ·
    refine ⟨17436134756090363598504659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11624089837393575732336439 17436134756090363598504659)
    ·
      refine ⟨26154202134135545397756989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17436134756090363598504659 26154202134135545397756989)
      ·
        refine ⟨9807825800300829524158871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26154202134135545397756989 9807825800300829524158871)
        ·
          refine ⟨14711738700451244286238307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9807825800300829524158871 14711738700451244286238307)
          ·
            refine ⟨22067608050676866429357461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14711738700451244286238307 22067608050676866429357461)
            ·
              refine ⟨1034419127375478113876131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22067608050676866429357461 1034419127375478113876131)
              ·
                refine ⟨1551628691063217170814197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034419127375478113876131 1551628691063217170814197)
                ·
                  refine ⟨145465189787176609763831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1551628691063217170814197 145465189787176609763831)
                  ·
                    rfl

theorem cell21_637408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_637408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637408 prefixEnd_637408 := by exact prefixLift 637408
  have htrace : WordTrace (prefixWord ++ tailWord_637408) baseStart_637408 baseEnd_637408 := by
    simpa [prefixWord, tailWord_637408, baseEnd_637408] using wordTrace_append hprefix tailTrace_637408
  have hstable : (prefixWord ++ tailWord_637408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637408).length < 2 ^ (prefixWord ++ tailWord_637408).sum := by decide
  have hdescent : baseEnd_637408 < baseStart_637408 := by decide
  rcases family_descends (prefixWord ++ tailWord_637408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637518 : List Nat := [4, 1, 1, 1, 1, 2, 6, 2, 3]
def baseStart_637518 : Nat := 118140960795 + 637518 * 2 ^ 59
def prefixEnd_637518 : Nat := 4983230072969 + 3 ^ 40 * 637518 * 2
def baseEnd_637518 : Nat := 145490293285840862930273

theorem tailTrace_637518 : CollatzResearch.WordTrace tailWord_637518 prefixEnd_637518 145490293285840862930273 := by
  unfold tailWord_637518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2906523963048580031397151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15501461136259093500784805 2906523963048580031397151)
  ·
    refine ⟨4359785944572870047095727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2906523963048580031397151 4359785944572870047095727)
    ·
      refine ⟨6539678916859305070643591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4359785944572870047095727 6539678916859305070643591)
      ·
        refine ⟨9809518375288957605965387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6539678916859305070643591 9809518375288957605965387)
        ·
          refine ⟨14714277562933436408948081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9809518375288957605965387 14714277562933436408948081)
          ·
            refine ⟨11035708172200077306711061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14714277562933436408948081 11035708172200077306711061)
            ·
              refine ⟨517298820571878623752081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11035708172200077306711061 517298820571878623752081)
              ·
                refine ⟨387974115428908967814061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 517298820571878623752081 387974115428908967814061)
                ·
                  refine ⟨145490293285840862930273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387974115428908967814061 145490293285840862930273)
                  ·
                    rfl

theorem cell21_637518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_637518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637518 prefixEnd_637518 := by exact prefixLift 637518
  have htrace : WordTrace (prefixWord ++ tailWord_637518) baseStart_637518 baseEnd_637518 := by
    simpa [prefixWord, tailWord_637518, baseEnd_637518] using wordTrace_append hprefix tailTrace_637518
  have hstable : (prefixWord ++ tailWord_637518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637518).length < 2 ^ (prefixWord ++ tailWord_637518).sum := by decide
  have hdescent : baseEnd_637518 < baseStart_637518 := by decide
  rcases family_descends (prefixWord ++ tailWord_637518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637546 : List Nat := [3, 1, 3, 2, 1, 1, 5, 5]
def baseStart_637546 : Nat := 118140960795 + 637546 * 2 ^ 59
def prefixEnd_637546 : Nat := 4983230072969 + 3 ^ 40 * 637546 * 2
def baseEnd_637546 : Nat := 48498894422439678821183

theorem tailTrace_637546 : CollatzResearch.WordTrace tailWord_637546 prefixEnd_637546 48498894422439678821183 := by
  unfold tailWord_637546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5813303237071800258299123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15502141965524800688797661 5813303237071800258299123)
  ·
    refine ⟨8719954855607700387448685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5813303237071800258299123 8719954855607700387448685)
    ·
      refine ⟨3269983070852887645293257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8719954855607700387448685 3269983070852887645293257)
      ·
        refine ⟨2452487303139665733969943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3269983070852887645293257 2452487303139665733969943)
        ·
          refine ⟨3678730954709498600954915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2452487303139665733969943 3678730954709498600954915)
          ·
            refine ⟨5518096432064247901432373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3678730954709498600954915 5518096432064247901432373)
            ·
              refine ⟨517321540506023240759285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5518096432064247901432373 517321540506023240759285)
              ·
                refine ⟨48498894422439678821183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 517321540506023240759285 48498894422439678821183)
                ·
                  rfl

theorem cell21_637546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_637546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637546 prefixEnd_637546 := by exact prefixLift 637546
  have htrace : WordTrace (prefixWord ++ tailWord_637546) baseStart_637546 baseEnd_637546 := by
    simpa [prefixWord, tailWord_637546, baseEnd_637546] using wordTrace_append hprefix tailTrace_637546
  have hstable : (prefixWord ++ tailWord_637546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637546).length < 2 ^ (prefixWord ++ tailWord_637546).sum := by decide
  have hdescent : baseEnd_637546 < baseStart_637546 := by decide
  rcases family_descends (prefixWord ++ tailWord_637546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637695 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 5]
def baseStart_637695 : Nat := 118140960795 + 637695 * 2 ^ 59
def prefixEnd_637695 : Nat := 4983230072969 + 3 ^ 40 * 637695 * 2
def baseEnd_637695 : Nat := 145530687097327888479911

theorem tailTrace_637695 : CollatzResearch.WordTrace tailWord_637695 prefixEnd_637695 145530687097327888479911 := by
  unfold tailWord_637695
  simp only [CollatzResearch.WordTrace]
  refine ⟨23258647424747399480370539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15505764949831599653580359 23258647424747399480370539)
  ·
    refine ⟨34887971137121099220555809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23258647424747399480370539 34887971137121099220555809)
    ·
      refine ⟨26165978352840824415416857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34887971137121099220555809 26165978352840824415416857)
      ·
        refine ⟨19624483764630618311562643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26165978352840824415416857 19624483764630618311562643)
        ·
          refine ⟨29436725646945927467343965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19624483764630618311562643 29436725646945927467343965)
          ·
            refine ⟨11038772117604722800253987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29436725646945927467343965 11038772117604722800253987)
            ·
              refine ⟨16558158176407084200380981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11038772117604722800253987 16558158176407084200380981)
              ·
                refine ⟨1552327329038164143785717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16558158176407084200380981 1552327329038164143785717)
                ·
                  refine ⟨145530687097327888479911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1552327329038164143785717 145530687097327888479911)
                  ·
                    rfl

theorem cell21_637695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 5].length) (baseStart_637695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637695 prefixEnd_637695 := by exact prefixLift 637695
  have htrace : WordTrace (prefixWord ++ tailWord_637695) baseStart_637695 baseEnd_637695 := by
    simpa [prefixWord, tailWord_637695, baseEnd_637695] using wordTrace_append hprefix tailTrace_637695
  have hstable : (prefixWord ++ tailWord_637695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637695).length < 2 ^ (prefixWord ++ tailWord_637695).sum := by decide
  have hdescent : baseEnd_637695 < baseStart_637695 := by decide
  rcases family_descends (prefixWord ++ tailWord_637695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637698 : List Nat := [3, 4, 1, 1, 1, 2, 3, 6]
def baseStart_637698 : Nat := 118140960795 + 637698 * 2 ^ 59
def prefixEnd_637698 : Nat := 4983230072969 + 3 ^ 40 * 637698 * 2
def baseEnd_637698 : Nat := 48510457246066849976635

theorem tailTrace_637698 : CollatzResearch.WordTrace tailWord_637698 prefixEnd_637698 48510457246066849976635 := by
  unfold tailWord_637698
  simp only [CollatzResearch.WordTrace]
  refine ⟨5814689210934132748182437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15505837895824353995153165 5814689210934132748182437)
  ·
    refine ⟨1090254227050149890284207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5814689210934132748182437 1090254227050149890284207)
    ·
      refine ⟨1635381340575224835426311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1090254227050149890284207 1635381340575224835426311)
      ·
        refine ⟨2453072010862837253139467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1635381340575224835426311 2453072010862837253139467)
        ·
          refine ⟨3679608016294255879709201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2453072010862837253139467 3679608016294255879709201)
          ·
            refine ⟨2759706012220691909781901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3679608016294255879709201 2759706012220691909781901)
            ·
              refine ⟨1034889754582759466168213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2759706012220691909781901 1034889754582759466168213)
              ·
                refine ⟨48510457246066849976635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1034889754582759466168213 48510457246066849976635)
                ·
                  rfl

theorem cell21_637698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_637698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637698 prefixEnd_637698 := by exact prefixLift 637698
  have htrace : WordTrace (prefixWord ++ tailWord_637698) baseStart_637698 baseEnd_637698 := by
    simpa [prefixWord, tailWord_637698, baseEnd_637698] using wordTrace_append hprefix tailTrace_637698
  have hstable : (prefixWord ++ tailWord_637698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637698).length < 2 ^ (prefixWord ++ tailWord_637698).sum := by decide
  have hdescent : baseEnd_637698 < baseStart_637698 := by decide
  rcases family_descends (prefixWord ++ tailWord_637698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637729 : List Nat := [1, 2, 3, 2, 1, 2, 4, 3, 3]
def baseStart_637729 : Nat := 118140960795 + 637729 * 2 ^ 59
def prefixEnd_637729 : Nat := 4983230072969 + 3 ^ 40 * 637729 * 2
def baseEnd_637729 : Nat := 145538446360551384913175

theorem tailTrace_637729 : CollatzResearch.WordTrace tailWord_637729 prefixEnd_637729 145538446360551384913175 := by
  unfold tailWord_637729
  simp only [CollatzResearch.WordTrace]
  refine ⟨23259887506624223287108241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15506591671082815524738827 23259887506624223287108241)
  ·
    refine ⟨17444915629968167465331181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23259887506624223287108241 17444915629968167465331181)
    ·
      refine ⟨6541843361238062799499193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17444915629968167465331181 6541843361238062799499193)
      ·
        refine ⟨4906382520928547099624395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6541843361238062799499193 4906382520928547099624395)
        ·
          refine ⟨7359573781392820649436593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4906382520928547099624395 7359573781392820649436593)
          ·
            refine ⟨5519680336044615487077445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7359573781392820649436593 5519680336044615487077445)
            ·
              refine ⟨1034940063008365403827021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5519680336044615487077445 1034940063008365403827021)
              ·
                refine ⟨388102523628137026435133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1034940063008365403827021 388102523628137026435133)
                ·
                  refine ⟨145538446360551384913175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 388102523628137026435133 145538446360551384913175)
                  ·
                    rfl

theorem cell21_637729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 3].length) (baseStart_637729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637729 prefixEnd_637729 := by exact prefixLift 637729
  have htrace : WordTrace (prefixWord ++ tailWord_637729) baseStart_637729 baseEnd_637729 := by
    simpa [prefixWord, tailWord_637729, baseEnd_637729] using wordTrace_append hprefix tailTrace_637729
  have hstable : (prefixWord ++ tailWord_637729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637729).length < 2 ^ (prefixWord ++ tailWord_637729).sum := by decide
  have hdescent : baseEnd_637729 < baseStart_637729 := by decide
  rcases family_descends (prefixWord ++ tailWord_637729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637740 : List Nat := [2, 2, 1, 1, 1, 4, 10]
def baseStart_637740 : Nat := 118140960795 + 637740 * 2 ^ 59
def prefixEnd_637740 : Nat := 4983230072969 + 3 ^ 40 * 637740 * 2
def baseEnd_637740 : Nat := 16171217412268645581091

theorem tailTrace_637740 : CollatzResearch.WordTrace tailWord_637740 prefixEnd_637740 16171217412268645581091 := by
  unfold tailWord_637740
  simp only [CollatzResearch.WordTrace]
  refine ⟨11630144354792186082879337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15506859139722914777172449 11630144354792186082879337)
  ·
    refine ⟨8722608266094139562159503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11630144354792186082879337 8722608266094139562159503)
    ·
      refine ⟨13083912399141209343239255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8722608266094139562159503 13083912399141209343239255)
      ·
        refine ⟨19625868598711814014858883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13083912399141209343239255 19625868598711814014858883)
        ·
          refine ⟨29438802898067721022288325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19625868598711814014858883 29438802898067721022288325)
          ·
            refine ⟨5519775543387697691679061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29438802898067721022288325 5519775543387697691679061)
            ·
              refine ⟨16171217412268645581091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5519775543387697691679061 16171217412268645581091)
              ·
                rfl

theorem cell21_637740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 10].length) (baseStart_637740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637740 prefixEnd_637740 := by exact prefixLift 637740
  have htrace : WordTrace (prefixWord ++ tailWord_637740) baseStart_637740 baseEnd_637740 := by
    simpa [prefixWord, tailWord_637740, baseEnd_637740] using wordTrace_append hprefix tailTrace_637740
  have hstable : (prefixWord ++ tailWord_637740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637740).length < 2 ^ (prefixWord ++ tailWord_637740).sum := by decide
  have hdescent : baseEnd_637740 < baseStart_637740 := by decide
  rcases family_descends (prefixWord ++ tailWord_637740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637819 : List Nat := [1, 1, 1, 1, 1, 5, 6, 1, 4]
def baseStart_637819 : Nat := 118140960795 + 637819 * 2 ^ 59
def prefixEnd_637819 : Nat := 4983230072969 + 3 ^ 40 * 637819 * 2
def baseEnd_637819 : Nat := 145558985586731228412991

theorem tailTrace_637819 : CollatzResearch.WordTrace tailWord_637819 prefixEnd_637819 145558985586731228412991 := by
  unfold tailWord_637819
  simp only [CollatzResearch.WordTrace]
  refine ⟨23263170076298168657884511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15508780050865445771923007 23263170076298168657884511)
  ·
    refine ⟨34894755114447252986826767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23263170076298168657884511 34894755114447252986826767)
    ·
      refine ⟨52342132671670879480240151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34894755114447252986826767 52342132671670879480240151)
      ·
        refine ⟨78513199007506319220360227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52342132671670879480240151 78513199007506319220360227)
        ·
          refine ⟨117769798511259478830540341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78513199007506319220360227 117769798511259478830540341)
          ·
            refine ⟨11040918610430576140363157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117769798511259478830540341 11040918610430576140363157)
            ·
              refine ⟨517543059863933256579523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11040918610430576140363157 517543059863933256579523)
              ·
                refine ⟨776314589795899884869285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517543059863933256579523 776314589795899884869285)
                ·
                  refine ⟨145558985586731228412991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 776314589795899884869285 145558985586731228412991)
                  ·
                    rfl

theorem cell21_637819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 4].length) (baseStart_637819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637819 prefixEnd_637819 := by exact prefixLift 637819
  have htrace : WordTrace (prefixWord ++ tailWord_637819) baseStart_637819 baseEnd_637819 := by
    simpa [prefixWord, tailWord_637819, baseEnd_637819] using wordTrace_append hprefix tailTrace_637819
  have hstable : (prefixWord ++ tailWord_637819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637819).length < 2 ^ (prefixWord ++ tailWord_637819).sum := by decide
  have hdescent : baseEnd_637819 < baseStart_637819 := by decide
  rcases family_descends (prefixWord ++ tailWord_637819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637909 : List Nat := [1, 3, 2, 3, 3, 1, 8]
def baseStart_637909 : Nat := 118140960795 + 637909 * 2 ^ 59
def prefixEnd_637909 : Nat := 4983230072969 + 3 ^ 40 * 637909 * 2
def baseEnd_637909 : Nat := 16175502756990119101423

theorem tailTrace_637909 : CollatzResearch.WordTrace tailWord_637909 prefixEnd_637909 16175502756990119101423 := by
  unfold tailWord_637909
  simp only [CollatzResearch.WordTrace]
  refine ⟨23266452645972114028660781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15510968430648076019107187 23266452645972114028660781)
  ·
    refine ⟨8724919742239542760747793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23266452645972114028660781 8724919742239542760747793)
    ·
      refine ⟨6543689806679657070560845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8724919742239542760747793 6543689806679657070560845)
      ·
        refine ⟨2453883677504871401460317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6543689806679657070560845 2453883677504871401460317)
        ·
          refine ⟨920206379064326775547619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2453883677504871401460317 920206379064326775547619)
          ·
            refine ⟨1380309568596490163321429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920206379064326775547619 1380309568596490163321429)
            ·
              refine ⟨16175502756990119101423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1380309568596490163321429 16175502756990119101423)
              ·
                rfl

theorem cell21_637909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 8].length) (baseStart_637909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637909 prefixEnd_637909 := by exact prefixLift 637909
  have htrace : WordTrace (prefixWord ++ tailWord_637909) baseStart_637909 baseEnd_637909 := by
    simpa [prefixWord, tailWord_637909, baseEnd_637909] using wordTrace_append hprefix tailTrace_637909
  have hstable : (prefixWord ++ tailWord_637909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637909).length < 2 ^ (prefixWord ++ tailWord_637909).sum := by decide
  have hdescent : baseEnd_637909 < baseStart_637909 := by decide
  rcases family_descends (prefixWord ++ tailWord_637909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637985 : List Nat := [1, 2, 3, 2, 3, 2, 2, 6]
def baseStart_637985 : Nat := 118140960795 + 637985 * 2 ^ 59
def prefixEnd_637985 : Nat := 4983230072969 + 3 ^ 40 * 637985 * 2
def baseEnd_637985 : Nat := 48532289682783942881995

theorem tailTrace_637985 : CollatzResearch.WordTrace tailWord_637985 prefixEnd_637985 48532289682783942881995 := by
  unfold tailWord_637985
  simp only [CollatzResearch.WordTrace]
  refine ⟨23269224593696779008427409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15512816395797852672284939 23269224593696779008427409)
  ·
    refine ⟨17451918445272584256320557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23269224593696779008427409 17451918445272584256320557)
    ·
      refine ⟨6544469416977219096120209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17451918445272584256320557 6544469416977219096120209)
      ·
        refine ⟨4908352062732914322090157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6544469416977219096120209 4908352062732914322090157)
        ·
          refine ⟨1840632023524842870783809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4908352062732914322090157 1840632023524842870783809)
          ·
            refine ⟨1380474017643632153087857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1840632023524842870783809 1380474017643632153087857)
            ·
              refine ⟨1035355513232724114815893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1380474017643632153087857 1035355513232724114815893)
              ·
                refine ⟨48532289682783942881995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1035355513232724114815893 48532289682783942881995)
                ·
                  rfl

theorem cell21_637985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 6].length) (baseStart_637985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637985 prefixEnd_637985 := by exact prefixLift 637985
  have htrace : WordTrace (prefixWord ++ tailWord_637985) baseStart_637985 baseEnd_637985 := by
    simpa [prefixWord, tailWord_637985, baseEnd_637985] using wordTrace_append hprefix tailTrace_637985
  have hstable : (prefixWord ++ tailWord_637985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637985).length < 2 ^ (prefixWord ++ tailWord_637985).sum := by decide
  have hdescent : baseEnd_637985 < baseStart_637985 := by decide
  rcases family_descends (prefixWord ++ tailWord_637985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637988 : List Nat := [2, 3, 1, 4, 1, 1, 4, 1, 4]
def baseStart_637988 : Nat := 118140960795 + 637988 * 2 ^ 59
def prefixEnd_637988 : Nat := 4983230072969 + 3 ^ 40 * 637988 * 2
def baseEnd_637988 : Nat := 145597553689224490095979

theorem tailTrace_637988 : CollatzResearch.WordTrace tailWord_637988 prefixEnd_637988 145597553689224490095979 := by
  unfold tailWord_637988
  simp only [CollatzResearch.WordTrace]
  refine ⟨11634667006342955260393309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15512889341790607013857745 11634667006342955260393309)
  ·
    refine ⟨4363000127378608222647491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11634667006342955260393309 4363000127378608222647491)
    ·
      refine ⟨6544500191067912333971237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4363000127378608222647491 6544500191067912333971237)
      ·
        refine ⟨1227093785825233562619607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6544500191067912333971237 1227093785825233562619607)
        ·
          refine ⟨1840640678737850343929411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1227093785825233562619607 1840640678737850343929411)
          ·
            refine ⟨2760961018106775515894117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840640678737850343929411 2760961018106775515894117)
            ·
              refine ⟨517680190895020409230147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2760961018106775515894117 517680190895020409230147)
              ·
                refine ⟨776520286342530613845221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517680190895020409230147 776520286342530613845221)
                ·
                  refine ⟨145597553689224490095979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 776520286342530613845221 145597553689224490095979)
                  ·
                    rfl

theorem cell21_637988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_637988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_637988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_637988 prefixEnd_637988 := by exact prefixLift 637988
  have htrace : WordTrace (prefixWord ++ tailWord_637988) baseStart_637988 baseEnd_637988 := by
    simpa [prefixWord, tailWord_637988, baseEnd_637988] using wordTrace_append hprefix tailTrace_637988
  have hstable : (prefixWord ++ tailWord_637988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637988).length < 2 ^ (prefixWord ++ tailWord_637988).sum := by decide
  have hdescent : baseEnd_637988 < baseStart_637988 := by decide
  rcases family_descends (prefixWord ++ tailWord_637988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638016 : List Nat := [2, 1, 1, 2, 2, 3, 2, 5, 3]
def baseStart_638016 : Nat := 118140960795 + 638016 * 2 ^ 59
def prefixEnd_638016 : Nat := 4983230072969 + 3 ^ 40 * 638016 * 2
def baseEnd_638016 : Nat := 145603943670702663629255

theorem tailTrace_638016 : CollatzResearch.WordTrace tailWord_638016 prefixEnd_638016 145603943670702663629255 := by
  unfold tailWord_638016
  simp only [CollatzResearch.WordTrace]
  refine ⟨11635177628292235651402951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15513570171056314201870601 11635177628292235651402951)
  ·
    refine ⟨17452766442438353477104427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11635177628292235651402951 17452766442438353477104427)
    ·
      refine ⟨26179149663657530215656641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17452766442438353477104427 26179149663657530215656641)
      ·
        refine ⟨19634362247743147661742481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26179149663657530215656641 19634362247743147661742481)
        ·
          refine ⟨14725771685807360746306861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19634362247743147661742481 14725771685807360746306861)
          ·
            refine ⟨5522164382177760279865073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14725771685807360746306861 5522164382177760279865073)
            ·
              refine ⟨4141623286633320209898805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5522164382177760279865073 4141623286633320209898805)
              ·
                refine ⟨388277183121873769678013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4141623286633320209898805 388277183121873769678013)
                ·
                  refine ⟨145603943670702663629255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 388277183121873769678013 145603943670702663629255)
                  ·
                    rfl

theorem cell21_638016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 3].length) (baseStart_638016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_638016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_638016 prefixEnd_638016 := by exact prefixLift 638016
  have htrace : WordTrace (prefixWord ++ tailWord_638016) baseStart_638016 baseEnd_638016 := by
    simpa [prefixWord, tailWord_638016, baseEnd_638016] using wordTrace_append hprefix tailTrace_638016
  have hstable : (prefixWord ++ tailWord_638016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638016).length < 2 ^ (prefixWord ++ tailWord_638016).sum := by decide
  have hdescent : baseEnd_638016 < baseStart_638016 := by decide
  rcases family_descends (prefixWord ++ tailWord_638016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638033 : List Nat := [1, 2, 2, 1, 3, 1, 6, 2, 3]
def baseStart_638033 : Nat := 118140960795 + 638033 * 2 ^ 59
def prefixEnd_638033 : Nat := 4983230072969 + 3 ^ 40 * 638033 * 2
def baseEnd_638033 : Nat := 145607823302314411845887

theorem tailTrace_638033 : CollatzResearch.WordTrace tailWord_638033 prefixEnd_638033 145607823302314411845887 := by
  unfold tailWord_638033
  simp only [CollatzResearch.WordTrace]
  refine ⟨23270975297522883206174753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15513983531681922137449835 23270975297522883206174753)
  ·
    refine ⟨17453231473142162404631065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23270975297522883206174753 17453231473142162404631065)
    ·
      refine ⟨13089923604856621803473299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17453231473142162404631065 13089923604856621803473299)
      ·
        refine ⟨19634885407284932705209949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13089923604856621803473299 19634885407284932705209949)
        ·
          refine ⟨7363082027731849764453731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19634885407284932705209949 7363082027731849764453731)
          ·
            refine ⟨11044623041597774646680597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7363082027731849764453731 11044623041597774646680597)
            ·
              refine ⟨517716705074895686563153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11044623041597774646680597 517716705074895686563153)
              ·
                refine ⟨388287528806171764922365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 517716705074895686563153 388287528806171764922365)
                ·
                  refine ⟨145607823302314411845887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 388287528806171764922365 145607823302314411845887)
                  ·
                    rfl

theorem cell21_638033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 3].length) (baseStart_638033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_638033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_638033 prefixEnd_638033 := by exact prefixLift 638033
  have htrace : WordTrace (prefixWord ++ tailWord_638033) baseStart_638033 baseEnd_638033 := by
    simpa [prefixWord, tailWord_638033, baseEnd_638033] using wordTrace_append hprefix tailTrace_638033
  have hstable : (prefixWord ++ tailWord_638033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638033).length < 2 ^ (prefixWord ++ tailWord_638033).sum := by decide
  have hdescent : baseEnd_638033 < baseStart_638033 := by decide
  rcases family_descends (prefixWord ++ tailWord_638033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638157 : List Nat := [1, 6, 2, 2, 1, 1, 1, 3, 4]
def baseStart_638157 : Nat := 118140960795 + 638157 * 2 ^ 59
def prefixEnd_638157 : Nat := 4983230072969 + 3 ^ 40 * 638157 * 2
def baseEnd_638157 : Nat := 145636121791717751778967

theorem tailTrace_638157 : CollatzResearch.WordTrace tailWord_638157 prefixEnd_638157 145636121791717751778967 := by
  unfold tailWord_638157
  simp only [CollatzResearch.WordTrace]
  refine ⟨23275497949073652383688725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15516998632715768255792483 23275497949073652383688725)
  ·
    refine ⟨1091038966362827455485409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23275497949073652383688725 1091038966362827455485409)
    ·
      refine ⟨818279224772120591614057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1091038966362827455485409 818279224772120591614057)
      ·
        refine ⟨613709418579090443710543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 818279224772120591614057 613709418579090443710543)
        ·
          refine ⟨920564127868635665565815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613709418579090443710543 920564127868635665565815)
          ·
            refine ⟨1380846191802953498348723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920564127868635665565815 1380846191802953498348723)
            ·
              refine ⟨2071269287704430247523085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380846191802953498348723 2071269287704430247523085)
              ·
                refine ⟨776725982889161342821157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2071269287704430247523085 776725982889161342821157)
                ·
                  refine ⟨145636121791717751778967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 776725982889161342821157 145636121791717751778967)
                  ·
                    rfl

theorem cell21_638157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_638157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_638157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_638157 prefixEnd_638157 := by exact prefixLift 638157
  have htrace : WordTrace (prefixWord ++ tailWord_638157) baseStart_638157 baseEnd_638157 := by
    simpa [prefixWord, tailWord_638157, baseEnd_638157] using wordTrace_append hprefix tailTrace_638157
  have hstable : (prefixWord ++ tailWord_638157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638157).length < 2 ^ (prefixWord ++ tailWord_638157).sum := by decide
  have hdescent : baseEnd_638157 < baseStart_638157 := by decide
  rcases family_descends (prefixWord ++ tailWord_638157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638241 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 6]
def baseStart_638241 : Nat := 118140960795 + 638241 * 2 ^ 59
def prefixEnd_638241 : Nat := 4983230072969 + 3 ^ 40 * 638241 * 2
def baseEnd_638241 : Nat := 145655291736152272378795

theorem tailTrace_638241 : CollatzResearch.WordTrace tailWord_638241 prefixEnd_638241 145655291736152272378795 := by
  unfold tailWord_638241
  simp only [CollatzResearch.WordTrace]
  refine ⟨23278561680769334729746577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15519041120512889819831051 23278561680769334729746577)
  ·
    refine ⟨17458921260577001047309933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23278561680769334729746577 17458921260577001047309933)
    ·
      refine ⟨6547095472716375392741225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17458921260577001047309933 6547095472716375392741225)
      ·
        refine ⟨4910321604537281544555919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6547095472716375392741225 4910321604537281544555919)
        ·
          refine ⟨7365482406805922316833879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4910321604537281544555919 7365482406805922316833879)
          ·
            refine ⟨11048223610208883475250819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7365482406805922316833879 11048223610208883475250819)
            ·
              refine ⟨16572335415313325212876229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11048223610208883475250819 16572335415313325212876229)
              ·
                refine ⟨3107312890371248477414293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16572335415313325212876229 3107312890371248477414293)
                ·
                  refine ⟨145655291736152272378795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3107312890371248477414293 145655291736152272378795)
                  ·
                    rfl

theorem cell21_638241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_638241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_638241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_638241 prefixEnd_638241 := by exact prefixLift 638241
  have htrace : WordTrace (prefixWord ++ tailWord_638241) baseStart_638241 baseEnd_638241 := by
    simpa [prefixWord, tailWord_638241, baseEnd_638241] using wordTrace_append hprefix tailTrace_638241
  have hstable : (prefixWord ++ tailWord_638241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638241).length < 2 ^ (prefixWord ++ tailWord_638241).sum := by decide
  have hdescent : baseEnd_638241 < baseStart_638241 := by decide
  rcases family_descends (prefixWord ++ tailWord_638241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638258 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 6]
def baseStart_638258 : Nat := 118140960795 + 638258 * 2 ^ 59
def prefixEnd_638258 : Nat := 4983230072969 + 3 ^ 40 * 638258 * 2
def baseEnd_638258 : Nat := 145659171367764020595427

theorem tailTrace_638258 : CollatzResearch.WordTrace tailWord_638258 prefixEnd_638258 145659171367764020595427 := by
  unfold tailWord_638258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5819795430426936658278857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15519454481138497755410285 5819795430426936658278857)
  ·
    refine ⟨4364846572820202493709143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5819795430426936658278857 4364846572820202493709143)
    ·
      refine ⟨6547269859230303740563715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4364846572820202493709143 6547269859230303740563715)
      ·
        refine ⟨9820904788845455610845573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6547269859230303740563715 9820904788845455610845573)
        ·
          refine ⟨1841419647908522927033545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9820904788845455610845573 1841419647908522927033545)
          ·
            refine ⟨1381064735931392195275159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1841419647908522927033545 1381064735931392195275159)
            ·
              refine ⟨2071597103897088292912739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1381064735931392195275159 2071597103897088292912739)
              ·
                refine ⟨3107395655845632439369109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2071597103897088292912739 3107395655845632439369109)
                ·
                  refine ⟨145659171367764020595427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3107395655845632439369109 145659171367764020595427)
                  ·
                    rfl

theorem cell21_638258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_638258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_638258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_638258 prefixEnd_638258 := by exact prefixLift 638258
  have htrace : WordTrace (prefixWord ++ tailWord_638258) baseStart_638258 baseEnd_638258 := by
    simpa [prefixWord, tailWord_638258, baseEnd_638258] using wordTrace_append hprefix tailTrace_638258
  have hstable : (prefixWord ++ tailWord_638258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638258).length < 2 ^ (prefixWord ++ tailWord_638258).sum := by decide
  have hdescent : baseEnd_638258 < baseStart_638258 := by decide
  rcases family_descends (prefixWord ++ tailWord_638258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638396 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 5]
def baseStart_638396 : Nat := 118140960795 + 638396 * 2 ^ 59
def prefixEnd_638396 : Nat := 4983230072969 + 3 ^ 40 * 638396 * 2
def baseEnd_638396 : Nat := 145690664847906447295145

theorem tailTrace_638396 : CollatzResearch.WordTrace tailWord_638396 prefixEnd_638396 145690664847906447295145 := by
  unfold tailWord_638396
  simp only [CollatzResearch.WordTrace]
  refine ⟨11642107497603898100819521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15522809996805197467759361 11642107497603898100819521)
  ·
    refine ⟨8731580623202923575614641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11642107497603898100819521 8731580623202923575614641)
    ·
      refine ⟨6548685467402192681710981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8731580623202923575614641 6548685467402192681710981)
      ·
        refine ⟨1227878525137911127820809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6548685467402192681710981 1227878525137911127820809)
        ·
          refine ⟨920908893853433345865607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1227878525137911127820809 920908893853433345865607)
          ·
            refine ⟨1381363340780150018798411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920908893853433345865607 1381363340780150018798411)
            ·
              refine ⟨2072045011170225028197617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1381363340780150018798411 2072045011170225028197617)
              ·
                refine ⟨1554033758377668771148213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2072045011170225028197617 1554033758377668771148213)
                ·
                  refine ⟨145690664847906447295145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1554033758377668771148213 145690664847906447295145)
                  ·
                    rfl

theorem cell21_638396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_638396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_638396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_638396 prefixEnd_638396 := by exact prefixLift 638396
  have htrace : WordTrace (prefixWord ++ tailWord_638396) baseStart_638396 baseEnd_638396 := by
    simpa [prefixWord, tailWord_638396, baseEnd_638396] using wordTrace_append hprefix tailTrace_638396
  have hstable : (prefixWord ++ tailWord_638396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638396).length < 2 ^ (prefixWord ++ tailWord_638396).sum := by decide
  have hdescent : baseEnd_638396 < baseStart_638396 := by decide
  rcases family_descends (prefixWord ++ tailWord_638396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638472 : List Nat := [2, 1, 3, 2, 1, 1, 5, 3, 3]
def baseStart_638472 : Nat := 118140960795 + 638472 * 2 ^ 59
def prefixEnd_638472 : Nat := 4983230072969 + 3 ^ 40 * 638472 * 2
def baseEnd_638472 : Nat := 145708009083347204028323

theorem tailTrace_638472 : CollatzResearch.WordTrace tailWord_638472 prefixEnd_638472 145708009083347204028323 := by
  unfold tailWord_638472
  simp only [CollatzResearch.WordTrace]
  refine ⟨11643493471466230590702835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15524657961954974120937113 11643493471466230590702835)
  ·
    refine ⟨17465240207199345886054253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11643493471466230590702835 17465240207199345886054253)
    ·
      refine ⟨6549465077699754707270345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17465240207199345886054253 6549465077699754707270345)
      ·
        refine ⟨4912098808274816030452759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6549465077699754707270345 4912098808274816030452759)
        ·
          refine ⟨7368148212412224045679139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4912098808274816030452759 7368148212412224045679139)
          ·
            refine ⟨11052222318618336068518709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7368148212412224045679139 11052222318618336068518709)
            ·
              refine ⟨1036145842370469006423629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11052222318618336068518709 1036145842370469006423629)
              ·
                refine ⟨388554690888925877408861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1036145842370469006423629 388554690888925877408861)
                ·
                  refine ⟨145708009083347204028323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 388554690888925877408861 145708009083347204028323)
                  ·
                    rfl

theorem cell21_638472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 3].length) (baseStart_638472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_638472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_638472 prefixEnd_638472 := by exact prefixLift 638472
  have htrace : WordTrace (prefixWord ++ tailWord_638472) baseStart_638472 baseEnd_638472 := by
    simpa [prefixWord, tailWord_638472, baseEnd_638472] using wordTrace_append hprefix tailTrace_638472
  have hstable : (prefixWord ++ tailWord_638472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638472).length < 2 ^ (prefixWord ++ tailWord_638472).sum := by decide
  have hdescent : baseEnd_638472 < baseStart_638472 := by decide
  rcases family_descends (prefixWord ++ tailWord_638472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638483 : List Nat := [1, 1, 1, 2, 1, 6, 9]
def baseStart_638483 : Nat := 118140960795 + 638483 * 2 ^ 59
def prefixEnd_638483 : Nat := 4983230072969 + 3 ^ 40 * 638483 * 2
def baseEnd_638483 : Nat := 16190057714801514371663

theorem tailTrace_638483 : CollatzResearch.WordTrace tailWord_638483 prefixEnd_638483 16190057714801514371663 := by
  unfold tailWord_638483
  simp only [CollatzResearch.WordTrace]
  refine ⟨23287388145892610060056103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15524925430595073373370735 23287388145892610060056103)
  ·
    refine ⟨34931082218838915090084155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23287388145892610060056103 34931082218838915090084155)
    ·
      refine ⟨52396623328258372635126233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34931082218838915090084155 52396623328258372635126233)
      ·
        refine ⟨39297467496193779476344675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52396623328258372635126233 39297467496193779476344675)
        ·
          refine ⟨58946201244290669214517013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39297467496193779476344675 58946201244290669214517013)
          ·
            refine ⟨2763103183326125119430485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58946201244290669214517013 2763103183326125119430485)
            ·
              refine ⟨16190057714801514371663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2763103183326125119430485 16190057714801514371663)
              ·
                rfl

theorem cell21_638483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 9].length) (baseStart_638483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_638483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_638483 prefixEnd_638483 := by exact prefixLift 638483
  have htrace : WordTrace (prefixWord ++ tailWord_638483) baseStart_638483 baseEnd_638483 := by
    simpa [prefixWord, tailWord_638483, baseEnd_638483] using wordTrace_append hprefix tailTrace_638483
  have hstable : (prefixWord ++ tailWord_638483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638483).length < 2 ^ (prefixWord ++ tailWord_638483).sum := by decide
  have hdescent : baseEnd_638483 < baseStart_638483 := by decide
  rcases family_descends (prefixWord ++ tailWord_638483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638514 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 7]
def baseStart_638514 : Nat := 118140960795 + 638514 * 2 ^ 59
def prefixEnd_638514 : Nat := 4983230072969 + 3 ^ 40 * 638514 * 2
def baseEnd_638514 : Nat := 145717594055564464328237

theorem tailTrace_638514 : CollatzResearch.WordTrace tailWord_638514 prefixEnd_638514 145717594055564464328237 := by
  unfold tailWord_638514
  simp only [CollatzResearch.WordTrace]
  refine ⟨5822129702195075588608649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15525679205853534902956397 5822129702195075588608649)
  ·
    refine ⟨4366597276646306691456487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5822129702195075588608649 4366597276646306691456487)
    ·
      refine ⟨6549895914969460037184731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4366597276646306691456487 6549895914969460037184731)
      ·
        refine ⟨9824843872454190055777097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6549895914969460037184731 9824843872454190055777097)
        ·
          refine ⟨7368632904340642541832823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9824843872454190055777097 7368632904340642541832823)
          ·
            refine ⟨11052949356510963812749235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7368632904340642541832823 11052949356510963812749235)
            ·
              refine ⟨16579424034766445719123853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11052949356510963812749235 16579424034766445719123853)
              ·
                refine ⟨6217284013037417144671445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16579424034766445719123853 6217284013037417144671445)
                ·
                  refine ⟨145717594055564464328237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6217284013037417144671445 145717594055564464328237)
                  ·
                    rfl

theorem cell21_638514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_638514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_638514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_638514 prefixEnd_638514 := by exact prefixLift 638514
  have htrace : WordTrace (prefixWord ++ tailWord_638514) baseStart_638514 baseEnd_638514 := by
    simpa [prefixWord, tailWord_638514, baseEnd_638514] using wordTrace_append hprefix tailTrace_638514
  have hstable : (prefixWord ++ tailWord_638514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638514).length < 2 ^ (prefixWord ++ tailWord_638514).sum := by decide
  have hdescent : baseEnd_638514 < baseStart_638514 := by decide
  rcases family_descends (prefixWord ++ tailWord_638514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638534 : List Nat := [6, 1, 1, 1, 4, 8]
def baseStart_638534 : Nat := 118140960795 + 638534 * 2 ^ 59
def prefixEnd_638534 : Nat := 4983230072969 + 3 ^ 40 * 638534 * 2
def baseEnd_638534 : Nat := 5397116975112921259069

theorem tailTrace_638534 : CollatzResearch.WordTrace tailWord_638534 prefixEnd_638534 5397116975112921259069 := by
  unfold tailWord_638534
  simp only [CollatzResearch.WordTrace]
  refine ⟨727789008397120180317583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15526165512471897180108437 727789008397120180317583)
  ·
    refine ⟨1091683512595680270476375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 727789008397120180317583 1091683512595680270476375)
    ·
      refine ⟨1637525268893520405714563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1091683512595680270476375 1637525268893520405714563)
      ·
        refine ⟨2456287903340280608571845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637525268893520405714563 2456287903340280608571845)
        ·
          refine ⟨460553981876302614107221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2456287903340280608571845 460553981876302614107221)
          ·
            refine ⟨5397116975112921259069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 460553981876302614107221 5397116975112921259069)
            ·
              rfl

theorem cell21_638534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 8].length) (baseStart_638534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_638534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_638534 prefixEnd_638534 := by exact prefixLift 638534
  have htrace : WordTrace (prefixWord ++ tailWord_638534) baseStart_638534 baseEnd_638534 := by
    simpa [prefixWord, tailWord_638534, baseEnd_638534] using wordTrace_append hprefix tailTrace_638534
  have hstable : (prefixWord ++ tailWord_638534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638534).length < 2 ^ (prefixWord ++ tailWord_638534).sum := by decide
  have hdescent : baseEnd_638534 < baseStart_638534 := by decide
  rcases family_descends (prefixWord ++ tailWord_638534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638548 : List Nat := [2, 4, 1, 1, 1, 2, 3, 4, 3]
def baseStart_638548 : Nat := 118140960795 + 638548 * 2 ^ 59
def prefixEnd_638548 : Nat := 4983230072969 + 3 ^ 40 * 638548 * 2
def baseEnd_638548 : Nat := 145725353318787960761501

theorem tailTrace_638548 : CollatzResearch.WordTrace tailWord_638548 prefixEnd_638548 145725353318787960761501 := by
  unfold tailWord_638548
  simp only [CollatzResearch.WordTrace]
  refine ⟨11644879445328563080586149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15526505927104750774114865 11644879445328563080586149)
  ·
    refine ⟨2183414895999105577609903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11644879445328563080586149 2183414895999105577609903)
    ·
      refine ⟨3275122343998658366414855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2183414895999105577609903 3275122343998658366414855)
      ·
        refine ⟨4912683515997987549622283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3275122343998658366414855 4912683515997987549622283)
        ·
          refine ⟨7369025273996981324433425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4912683515997987549622283 7369025273996981324433425)
          ·
            refine ⟨5526768955497735993325069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7369025273996981324433425 5526768955497735993325069)
            ·
              refine ⟨2072538358311650997496901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5526768955497735993325069 2072538358311650997496901)
              ·
                refine ⟨388600942183434562030669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2072538358311650997496901 388600942183434562030669)
                ·
                  refine ⟨145725353318787960761501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 388600942183434562030669 145725353318787960761501)
                  ·
                    rfl

theorem cell21_638548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_638548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_638548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_638548 prefixEnd_638548 := by exact prefixLift 638548
  have htrace : WordTrace (prefixWord ++ tailWord_638548) baseStart_638548 baseEnd_638548 := by
    simpa [prefixWord, tailWord_638548, baseEnd_638548] using wordTrace_append hprefix tailTrace_638548
  have hstable : (prefixWord ++ tailWord_638548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638548).length < 2 ^ (prefixWord ++ tailWord_638548).sum := by decide
  have hdescent : baseEnd_638548 < baseStart_638548 := by decide
  rcases family_descends (prefixWord ++ tailWord_638548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638596 : List Nat := [2, 3, 2, 1, 5, 1, 1, 2, 4]
def baseStart_638596 : Nat := 118140960795 + 638596 * 2 ^ 59
def prefixEnd_638596 : Nat := 4983230072969 + 3 ^ 40 * 638596 * 2
def baseEnd_638596 : Nat := 145736307572750543961403

theorem tailTrace_638596 : CollatzResearch.WordTrace tailWord_638596 prefixEnd_638596 145736307572750543961403 := by
  unfold tailWord_638596
  simp only [CollatzResearch.WordTrace]
  refine ⟨11645754797241615179459821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15527673062988820239279761 11645754797241615179459821)
  ·
    refine ⟨4367158048965605692297433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11645754797241615179459821 4367158048965605692297433)
    ·
      refine ⟨3275368536724204269223075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4367158048965605692297433 3275368536724204269223075)
      ·
        refine ⟨4913052805086306403834613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3275368536724204269223075 4913052805086306403834613)
        ·
          refine ⟨460598700476841225359495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4913052805086306403834613 460598700476841225359495)
          ·
            refine ⟨690898050715261838039243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460598700476841225359495 690898050715261838039243)
            ·
              refine ⟨1036347076072892757058865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 690898050715261838039243 1036347076072892757058865)
              ·
                refine ⟨777260307054669567794149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1036347076072892757058865 777260307054669567794149)
                ·
                  refine ⟨145736307572750543961403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 777260307054669567794149 145736307572750543961403)
                  ·
                    rfl

theorem cell21_638596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_638596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_638596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_638596 prefixEnd_638596 := by exact prefixLift 638596
  have htrace : WordTrace (prefixWord ++ tailWord_638596) baseStart_638596 baseEnd_638596 := by
    simpa [prefixWord, tailWord_638596, baseEnd_638596] using wordTrace_append hprefix tailTrace_638596
  have hstable : (prefixWord ++ tailWord_638596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638596).length < 2 ^ (prefixWord ++ tailWord_638596).sum := by decide
  have hdescent : baseEnd_638596 < baseStart_638596 := by decide
  rcases family_descends (prefixWord ++ tailWord_638596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638652 : List Nat := [2, 2, 2, 3, 1, 4, 7]
def baseStart_638652 : Nat := 118140960795 + 638652 * 2 ^ 59
def prefixEnd_638652 : Nat := 4983230072969 + 3 ^ 40 * 638652 * 2
def baseEnd_638652 : Nat := 16194343059522987891995

theorem tailTrace_638652 : CollatzResearch.WordTrace tailWord_638652 prefixEnd_638652 16194343059522987891995 := by
  unfold tailWord_638652
  simp only [CollatzResearch.WordTrace]
  refine ⟨11646776041140175961479105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15529034721520234615305473 11646776041140175961479105)
  ·
    refine ⟨8735082030855131971109329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11646776041140175961479105 8735082030855131971109329)
    ·
      refine ⟨6551311523141348978331997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8735082030855131971109329 6551311523141348978331997)
      ·
        refine ⟨2456741821178005866874499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6551311523141348978331997 2456741821178005866874499)
        ·
          refine ⟨3685112731767008800311749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2456741821178005866874499 3685112731767008800311749)
          ·
            refine ⟨690958637206314150058453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3685112731767008800311749 690958637206314150058453)
            ·
              refine ⟨16194343059522987891995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 690958637206314150058453 16194343059522987891995)
              ·
                rfl

theorem cell21_638652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 7].length) (baseStart_638652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_638652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_638652 prefixEnd_638652 := by exact prefixLift 638652
  have htrace : WordTrace (prefixWord ++ tailWord_638652) baseStart_638652 baseEnd_638652 := by
    simpa [prefixWord, tailWord_638652, baseEnd_638652] using wordTrace_append hprefix tailTrace_638652
  have hstable : (prefixWord ++ tailWord_638652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638652).length < 2 ^ (prefixWord ++ tailWord_638652).sum := by decide
  have hdescent : baseEnd_638652 < baseStart_638652 := by decide
  rcases family_descends (prefixWord ++ tailWord_638652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638669 : List Nat := [1, 6, 2, 1, 1, 1, 1, 8]
def baseStart_638669 : Nat := 118140960795 + 638669 * 2 ^ 59
def prefixEnd_638669 : Nat := 4983230072969 + 3 ^ 40 * 638669 * 2
def baseEnd_638669 : Nat := 48584322389106213081529

theorem tailTrace_638669 : CollatzResearch.WordTrace tailWord_638669 prefixEnd_638669 48584322389106213081529 := by
  unfold tailWord_638669
  simp only [CollatzResearch.WordTrace]
  refine ⟨23294172123218763826327061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15529448082145842550884707 23294172123218763826327061)
  ·
    refine ⟨1091914318275879554359081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23294172123218763826327061 1091914318275879554359081)
    ·
      refine ⟨818935738706909665769311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1091914318275879554359081 818935738706909665769311)
      ·
        refine ⟨1228403608060364498653967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 818935738706909665769311 1228403608060364498653967)
        ·
          refine ⟨1842605412090546747980951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1228403608060364498653967 1842605412090546747980951)
          ·
            refine ⟨2763908118135820121971427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1842605412090546747980951 2763908118135820121971427)
            ·
              refine ⟨4145862177203730182957141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2763908118135820121971427 4145862177203730182957141)
              ·
                refine ⟨48584322389106213081529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4145862177203730182957141 48584322389106213081529)
                ·
                  rfl

theorem cell21_638669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 8].length) (baseStart_638669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_638669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_638669 prefixEnd_638669 := by exact prefixLift 638669
  have htrace : WordTrace (prefixWord ++ tailWord_638669) baseStart_638669 baseEnd_638669 := by
    simpa [prefixWord, tailWord_638669, baseEnd_638669] using wordTrace_append hprefix tailTrace_638669
  have hstable : (prefixWord ++ tailWord_638669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638669).length < 2 ^ (prefixWord ++ tailWord_638669).sum := by decide
  have hdescent : baseEnd_638669 < baseStart_638669 := by decide
  rcases family_descends (prefixWord ++ tailWord_638669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638804 : List Nat := [2, 4, 1, 1, 3, 2, 1, 7]
def baseStart_638804 : Nat := 118140960795 + 638804 * 2 ^ 59
def prefixEnd_638804 : Nat := 4983230072969 + 3 ^ 40 * 638804 * 2
def baseEnd_638804 : Nat := 48594592002196134831437

theorem tailTrace_638804 : CollatzResearch.WordTrace tailWord_638804 prefixEnd_638804 48594592002196134831437 := by
  unfold tailWord_638804
  simp only [CollatzResearch.WordTrace]
  refine ⟨11649547988864840941245733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15532730651819787921660977 11649547988864840941245733)
  ·
    refine ⟨2184290247912157676483575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11649547988864840941245733 2184290247912157676483575)
    ·
      refine ⟨3276435371868236514725363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2184290247912157676483575 3276435371868236514725363)
      ·
        refine ⟨4914653057802354772088045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3276435371868236514725363 4914653057802354772088045)
        ·
          refine ⟨1842994896675883039533017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4914653057802354772088045 1842994896675883039533017)
          ·
            refine ⟨1382246172506912279649763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1842994896675883039533017 1382246172506912279649763)
            ·
              refine ⟨2073369258760368419474645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1382246172506912279649763 2073369258760368419474645)
              ·
                refine ⟨48594592002196134831437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2073369258760368419474645 48594592002196134831437)
                ·
                  rfl

theorem cell21_638804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 7].length) (baseStart_638804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_638804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_638804 prefixEnd_638804 := by exact prefixLift 638804
  have htrace : WordTrace (prefixWord ++ tailWord_638804) baseStart_638804 baseEnd_638804 := by
    simpa [prefixWord, tailWord_638804, baseEnd_638804] using wordTrace_append hprefix tailTrace_638804
  have hstable : (prefixWord ++ tailWord_638804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638804).length < 2 ^ (prefixWord ++ tailWord_638804).sum := by decide
  have hdescent : baseEnd_638804 < baseStart_638804 := by decide
  rcases family_descends (prefixWord ++ tailWord_638804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638984 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 8]
def baseStart_638984 : Nat := 118140960795 + 638984 * 2 ^ 59
def prefixEnd_638984 : Nat := 4983230072969 + 3 ^ 40 * 638984 * 2
def baseEnd_638984 : Nat := 145824854458948091493943

theorem tailTrace_638984 : CollatzResearch.WordTrace tailWord_638984 prefixEnd_638984 145824854458948091493943 := by
  unfold tailWord_638984
  simp only [CollatzResearch.WordTrace]
  refine ⟨11652830558538786312022003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15537107411385048416029337 11652830558538786312022003)
  ·
    refine ⟨17479245837808179468033005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11652830558538786312022003 17479245837808179468033005)
    ·
      refine ⟨6554717189178067300512377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17479245837808179468033005 6554717189178067300512377)
      ·
        refine ⟨4916037891883550475384283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6554717189178067300512377 4916037891883550475384283)
        ·
          refine ⟨7374056837825325713076425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4916037891883550475384283 7374056837825325713076425)
          ·
            refine ⟨5530542628368994284807319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7374056837825325713076425 5530542628368994284807319)
            ·
              refine ⟨8295813942553491427210979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5530542628368994284807319 8295813942553491427210979)
              ·
                refine ⟨12443720913830237140816469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8295813942553491427210979 12443720913830237140816469)
                ·
                  refine ⟨145824854458948091493943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12443720913830237140816469 145824854458948091493943)
                  ·
                    rfl

theorem cell21_638984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_638984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_638984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_638984 prefixEnd_638984 := by exact prefixLift 638984
  have htrace : WordTrace (prefixWord ++ tailWord_638984) baseStart_638984 baseEnd_638984 := by
    simpa [prefixWord, tailWord_638984, baseEnd_638984] using wordTrace_append hprefix tailTrace_638984
  have hstable : (prefixWord ++ tailWord_638984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638984).length < 2 ^ (prefixWord ++ tailWord_638984).sum := by decide
  have hdescent : baseEnd_638984 < baseStart_638984 := by decide
  rcases family_descends (prefixWord ++ tailWord_638984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639018 : List Nat := [3, 1, 4, 1, 2, 2, 1, 3, 4]
def baseStart_639018 : Nat := 118140960795 + 639018 * 2 ^ 59
def prefixEnd_639018 : Nat := 4983230072969 + 3 ^ 40 * 639018 * 2
def baseEnd_639018 : Nat := 145832613722171587927207

theorem tailTrace_639018 : CollatzResearch.WordTrace tailWord_639018 prefixEnd_639018 145832613722171587927207 := by
  unfold tailWord_639018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5826725299738599107695427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15537934132636264287187805 5826725299738599107695427)
  ·
    refine ⟨8740087949607898661543141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5826725299738599107695427 8740087949607898661543141)
    ·
      refine ⟨1638766490551480999039339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8740087949607898661543141 1638766490551480999039339)
      ·
        refine ⟨2458149735827221498559009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1638766490551480999039339 2458149735827221498559009)
        ·
          refine ⟨1843612301870416123919257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2458149735827221498559009 1843612301870416123919257)
          ·
            refine ⟨1382709226402812092939443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1843612301870416123919257 1382709226402812092939443)
            ·
              refine ⟨2074063839604218139409165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1382709226402812092939443 2074063839604218139409165)
              ·
                refine ⟨777773939851581802278437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2074063839604218139409165 777773939851581802278437)
                ·
                  refine ⟨145832613722171587927207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 777773939851581802278437 145832613722171587927207)
                  ·
                    rfl

theorem cell21_639018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_639018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_639018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_639018 prefixEnd_639018 := by exact prefixLift 639018
  have htrace : WordTrace (prefixWord ++ tailWord_639018) baseStart_639018 baseEnd_639018 := by
    simpa [prefixWord, tailWord_639018, baseEnd_639018] using wordTrace_append hprefix tailTrace_639018
  have hstable : (prefixWord ++ tailWord_639018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639018).length < 2 ^ (prefixWord ++ tailWord_639018).sum := by decide
  have hdescent : baseEnd_639018 < baseStart_639018 := by decide
  rcases family_descends (prefixWord ++ tailWord_639018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639077 : List Nat := [1, 3, 1, 3, 2, 2, 2, 3, 4]
def baseStart_639077 : Nat := 118140960795 + 639077 * 2 ^ 59
def prefixEnd_639077 : Nat := 4983230072969 + 3 ^ 40 * 639077 * 2
def baseEnd_639077 : Nat := 145846078326000596443753

theorem tailTrace_639077 : CollatzResearch.WordTrace tailWord_639077 prefixEnd_639077 145846078326000596443753 := by
  unfold tailWord_639077
  simp only [CollatzResearch.WordTrace]
  refine ⟨23309053105740649507179485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15539368737160433004786323 23309053105740649507179485)
  ·
    refine ⟨8740894914652743565192307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23309053105740649507179485 8740894914652743565192307)
    ·
      refine ⟨13111342371979115347788461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8740894914652743565192307 13111342371979115347788461)
      ·
        refine ⟨4916753389492168255420673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13111342371979115347788461 4916753389492168255420673)
        ·
          refine ⟨3687565042119126191565505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4916753389492168255420673 3687565042119126191565505)
          ·
            refine ⟨2765673781589344643674129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3687565042119126191565505 2765673781589344643674129)
            ·
              refine ⟨2074255336192008482755597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2765673781589344643674129 2074255336192008482755597)
              ·
                refine ⟨777845751072003181033349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2074255336192008482755597 777845751072003181033349)
                ·
                  refine ⟨145846078326000596443753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 777845751072003181033349 145846078326000596443753)
                  ·
                    rfl

theorem cell21_639077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_639077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_639077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_639077 prefixEnd_639077 := by exact prefixLift 639077
  have htrace : WordTrace (prefixWord ++ tailWord_639077) baseStart_639077 baseEnd_639077 := by
    simpa [prefixWord, tailWord_639077, baseEnd_639077] using wordTrace_append hprefix tailTrace_639077
  have hstable : (prefixWord ++ tailWord_639077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639077).length < 2 ^ (prefixWord ++ tailWord_639077).sum := by decide
  have hdescent : baseEnd_639077 < baseStart_639077 := by decide
  rcases family_descends (prefixWord ++ tailWord_639077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639226 : List Nat := [3, 1, 1, 1, 1, 14]
def baseStart_639226 : Nat := 118140960795 + 639226 * 2 ^ 59
def prefixEnd_639226 : Nat := 4983230072969 + 3 ^ 40 * 639226 * 2
def baseEnd_639226 : Nat := 5402966005778127720745

theorem tailTrace_639226 : CollatzResearch.WordTrace tailWord_639226 prefixEnd_639226 5402966005778127720745 := by
  unfold tailWord_639226
  simp only [CollatzResearch.WordTrace]
  refine ⟨5828621895550211988588383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15542991721467231969569021 5828621895550211988588383)
  ·
    refine ⟨8742932843325317982882575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5828621895550211988588383 8742932843325317982882575)
    ·
      refine ⟨13114399264987976974323863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8742932843325317982882575 13114399264987976974323863)
      ·
        refine ⟨19671598897481965461485795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13114399264987976974323863 19671598897481965461485795)
        ·
          refine ⟨29507398346222948192228693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19671598897481965461485795 29507398346222948192228693)
          ·
            refine ⟨5402966005778127720745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 29507398346222948192228693 5402966005778127720745)
            ·
              rfl

theorem cell21_639226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 14].length) (baseStart_639226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_639226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_639226 prefixEnd_639226 := by exact prefixLift 639226
  have htrace : WordTrace (prefixWord ++ tailWord_639226) baseStart_639226 baseEnd_639226 := by
    simpa [prefixWord, tailWord_639226, baseEnd_639226] using wordTrace_append hprefix tailTrace_639226
  have hstable : (prefixWord ++ tailWord_639226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639226).length < 2 ^ (prefixWord ++ tailWord_639226).sum := by decide
  have hdescent : baseEnd_639226 < baseStart_639226 := by decide
  rcases family_descends (prefixWord ++ tailWord_639226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639423 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 10]
def baseStart_639423 : Nat := 118140960795 + 639423 * 2 ^ 59
def prefixEnd_639423 : Nat := 4983230072969 + 3 ^ 40 * 639423 * 2
def baseEnd_639423 : Nat := 145925040239980883676379

theorem tailTrace_639423 : CollatzResearch.WordTrace tailWord_639423 prefixEnd_639423 145925040239980883676379 := by
  unfold tailWord_639423
  simp only [CollatzResearch.WordTrace]
  refine ⟨23321672762487150599274923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15547781841658100399516615 23321672762487150599274923)
  ·
    refine ⟨34982509143730725898912385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23321672762487150599274923 34982509143730725898912385)
    ·
      refine ⟨26236881857798044424184289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34982509143730725898912385 26236881857798044424184289)
      ·
        refine ⟨19677661393348533318138217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26236881857798044424184289 19677661393348533318138217)
        ·
          refine ⟨14758246045011399988603663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19677661393348533318138217 14758246045011399988603663)
          ·
            refine ⟨22137369067517099982905495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14758246045011399988603663 22137369067517099982905495)
            ·
              refine ⟨33206053601275649974358243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22137369067517099982905495 33206053601275649974358243)
              ·
                refine ⟨49809080401913474961537365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33206053601275649974358243 49809080401913474961537365)
                ·
                  refine ⟨145925040239980883676379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 49809080401913474961537365 145925040239980883676379)
                  ·
                    rfl

theorem cell21_639423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 10].length) (baseStart_639423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_639423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_639423 prefixEnd_639423 := by exact prefixLift 639423
  have htrace : WordTrace (prefixWord ++ tailWord_639423) baseStart_639423 baseEnd_639423 := by
    simpa [prefixWord, tailWord_639423, baseEnd_639423] using wordTrace_append hprefix tailTrace_639423
  have hstable : (prefixWord ++ tailWord_639423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639423).length < 2 ^ (prefixWord ++ tailWord_639423).sum := by decide
  have hdescent : baseEnd_639423 < baseStart_639423 := by decide
  rcases family_descends (prefixWord ++ tailWord_639423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639485 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 5]
def baseStart_639485 : Nat := 118140960795 + 639485 * 2 ^ 59
def prefixEnd_639485 : Nat := 4983230072969 + 3 ^ 40 * 639485 * 2
def baseEnd_639485 : Nat := 145939189484682553642919

theorem tailTrace_639485 : CollatzResearch.WordTrace tailWord_639485 prefixEnd_639485 145939189484682553642919 := by
  unfold tailWord_639485
  simp only [CollatzResearch.WordTrace]
  refine ⟨23323934088262535188031909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15549289392175023458687939 23323934088262535188031909)
  ·
    refine ⟨4373237641549225347755983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23323934088262535188031909 4373237641549225347755983)
    ·
      refine ⟨6559856462323838021633975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4373237641549225347755983 6559856462323838021633975)
      ·
        refine ⟨9839784693485757032450963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6559856462323838021633975 9839784693485757032450963)
        ·
          refine ⟨14759677040228635548676445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9839784693485757032450963 14759677040228635548676445)
          ·
            refine ⟨5534878890085738330753667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14759677040228635548676445 5534878890085738330753667)
            ·
              refine ⟨8302318335128607496130501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5534878890085738330753667 8302318335128607496130501)
              ·
                refine ⟨1556684687836613905524469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8302318335128607496130501 1556684687836613905524469)
                ·
                  refine ⟨145939189484682553642919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1556684687836613905524469 145939189484682553642919)
                  ·
                    rfl

theorem cell21_639485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_639485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_639485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_639485 prefixEnd_639485 := by exact prefixLift 639485
  have htrace : WordTrace (prefixWord ++ tailWord_639485) baseStart_639485 baseEnd_639485 := by
    simpa [prefixWord, tailWord_639485, baseEnd_639485] using wordTrace_append hprefix tailTrace_639485
  have hstable : (prefixWord ++ tailWord_639485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639485).length < 2 ^ (prefixWord ++ tailWord_639485).sum := by decide
  have hdescent : baseEnd_639485 < baseStart_639485 := by decide
  rcases family_descends (prefixWord ++ tailWord_639485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639494 : List Nat := [6, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_639494 : Nat := 118140960795 + 639494 * 2 ^ 59
def prefixEnd_639494 : Nat := 4983230072969 + 3 ^ 40 * 639494 * 2
def baseEnd_639494 : Nat := 145941243407300537992901

theorem tailTrace_639494 : CollatzResearch.WordTrace tailWord_639494 prefixEnd_639494 145941243407300537992901 := by
  unfold tailWord_639494
  simp only [CollatzResearch.WordTrace]
  refine ⟨728883198288435303909673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15549508230153286483406357 728883198288435303909673)
  ·
    refine ⟨546662398716326477932255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 728883198288435303909673 546662398716326477932255)
    ·
      refine ⟨819993598074489716898383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 546662398716326477932255 819993598074489716898383)
      ·
        refine ⟨1229990397111734575347575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 819993598074489716898383 1229990397111734575347575)
        ·
          refine ⟨1844985595667601863021363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229990397111734575347575 1844985595667601863021363)
          ·
            refine ⟨2767478393501402794532045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844985595667601863021363 2767478393501402794532045)
            ·
              refine ⟨1037804397563026047949517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2767478393501402794532045 1037804397563026047949517)
              ·
                refine ⟨389176649086134767981069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1037804397563026047949517 389176649086134767981069)
                ·
                  refine ⟨145941243407300537992901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 389176649086134767981069 145941243407300537992901)
                  ·
                    rfl

theorem cell21_639494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_639494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_639494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_639494 prefixEnd_639494 := by exact prefixLift 639494
  have htrace : WordTrace (prefixWord ++ tailWord_639494) baseStart_639494 baseEnd_639494 := by
    simpa [prefixWord, tailWord_639494, baseEnd_639494] using wordTrace_append hprefix tailTrace_639494
  have hstable : (prefixWord ++ tailWord_639494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639494).length < 2 ^ (prefixWord ++ tailWord_639494).sum := by decide
  have hdescent : baseEnd_639494 < baseStart_639494 := by decide
  rcases family_descends (prefixWord ++ tailWord_639494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639516 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 6]
def baseStart_639516 : Nat := 118140960795 + 639516 * 2 ^ 59
def prefixEnd_639516 : Nat := 4983230072969 + 3 ^ 40 * 639516 * 2
def baseEnd_639516 : Nat := 145946264107033388626189

theorem tailTrace_639516 : CollatzResearch.WordTrace tailWord_639516 prefixEnd_639516 145946264107033388626189 := by
  unfold tailWord_639516
  simp only [CollatzResearch.WordTrace]
  refine ⟨11662532375575113741205201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15550043167433484988273601 11662532375575113741205201)
  ·
    refine ⟨8746899281681335305903901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11662532375575113741205201 8746899281681335305903901)
    ·
      refine ⟨3280087230630500739713963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8746899281681335305903901 3280087230630500739713963)
      ·
        refine ⟨4920130845945751109570945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3280087230630500739713963 4920130845945751109570945)
        ·
          refine ⟨3690098134459313332178209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4920130845945751109570945 3690098134459313332178209)
          ·
            refine ⟨2767573600844484999133657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3690098134459313332178209 2767573600844484999133657)
            ·
              refine ⟨2075680200633363749350243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2767573600844484999133657 2075680200633363749350243)
              ·
                refine ⟨3113520300950045624025365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2075680200633363749350243 3113520300950045624025365)
                ·
                  refine ⟨145946264107033388626189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3113520300950045624025365 145946264107033388626189)
                  ·
                    rfl

theorem cell21_639516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_639516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_639516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_639516 prefixEnd_639516 := by exact prefixLift 639516
  have htrace : WordTrace (prefixWord ++ tailWord_639516) baseStart_639516 baseEnd_639516 := by
    simpa [prefixWord, tailWord_639516, baseEnd_639516] using wordTrace_append hprefix tailTrace_639516
  have hstable : (prefixWord ++ tailWord_639516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639516).length < 2 ^ (prefixWord ++ tailWord_639516).sum := by decide
  have hdescent : baseEnd_639516 < baseStart_639516 := by decide
  rcases family_descends (prefixWord ++ tailWord_639516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639626 : List Nat := [3, 1, 2, 3, 3, 2, 1, 2, 4]
def baseStart_639626 : Nat := 118140960795 + 639626 * 2 ^ 59
def prefixEnd_639626 : Nat := 4983230072969 + 3 ^ 40 * 639626 * 2
def baseEnd_639626 : Nat := 145971367605697641792631

theorem tailTrace_639626 : CollatzResearch.WordTrace tailWord_639626 prefixEnd_639626 145971367605697641792631 := by
  unfold tailWord_639626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5832269195187929067228683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15552717853834477512609821 5832269195187929067228683)
  ·
    refine ⟨8748403792781893600843025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5832269195187929067228683 8748403792781893600843025)
    ·
      refine ⟨6561302844586420200632269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8748403792781893600843025 6561302844586420200632269)
      ·
        refine ⟨2460488566719907575237101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6561302844586420200632269 2460488566719907575237101)
        ·
          refine ⟨922683212519965340713913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2460488566719907575237101 922683212519965340713913)
          ·
            refine ⟨692012409389974005535435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 922683212519965340713913 692012409389974005535435)
            ·
              refine ⟨1038018614084961008303153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692012409389974005535435 1038018614084961008303153)
              ·
                refine ⟨778513960563720756227365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1038018614084961008303153 778513960563720756227365)
                ·
                  refine ⟨145971367605697641792631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 778513960563720756227365 145971367605697641792631)
                  ·
                    rfl

theorem cell21_639626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_639626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_639626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_639626 prefixEnd_639626 := by exact prefixLift 639626
  have htrace : WordTrace (prefixWord ++ tailWord_639626) baseStart_639626 baseEnd_639626 := by
    simpa [prefixWord, tailWord_639626, baseEnd_639626] using wordTrace_append hprefix tailTrace_639626
  have hstable : (prefixWord ++ tailWord_639626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639626).length < 2 ^ (prefixWord ++ tailWord_639626).sum := by decide
  have hdescent : baseEnd_639626 < baseStart_639626 := by decide
  rcases family_descends (prefixWord ++ tailWord_639626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639733 : List Nat := [1, 3, 6, 1, 2, 8]
def baseStart_639733 : Nat := 118140960795 + 639733 * 2 ^ 59
def prefixEnd_639733 : Nat := 4983230072969 + 3 ^ 40 * 639733 * 2
def baseEnd_639733 : Nat := 5407251350499601241077

theorem tailTrace_639733 : CollatzResearch.WordTrace tailWord_639733 prefixEnd_639733 5407251350499601241077 := by
  unfold tailWord_639733
  simp only [CollatzResearch.WordTrace]
  refine ⟨23332979391364073543059853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15555319594242715695373235 23332979391364073543059853)
  ·
    refine ⟨8749867271761527578647445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23332979391364073543059853 8749867271761527578647445)
    ·
      refine ⟨410150028363821605249099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8749867271761527578647445 410150028363821605249099)
      ·
        refine ⟨615225042545732407873649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410150028363821605249099 615225042545732407873649)
        ·
          refine ⟨461418781909299305905237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 615225042545732407873649 461418781909299305905237)
          ·
            refine ⟨5407251350499601241077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 461418781909299305905237 5407251350499601241077)
            ·
              rfl

theorem cell21_639733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 8].length) (baseStart_639733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_639733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_639733 prefixEnd_639733 := by exact prefixLift 639733
  have htrace : WordTrace (prefixWord ++ tailWord_639733) baseStart_639733 baseEnd_639733 := by
    simpa [prefixWord, tailWord_639733, baseEnd_639733] using wordTrace_append hprefix tailTrace_639733
  have hstable : (prefixWord ++ tailWord_639733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639733).length < 2 ^ (prefixWord ++ tailWord_639733).sum := by decide
  have hdescent : baseEnd_639733 < baseStart_639733 := by decide
  rcases family_descends (prefixWord ++ tailWord_639733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639775 : List Nat := [1, 1, 2, 4, 2, 3, 3, 5]
def baseStart_639775 : Nat := 118140960795 + 639775 * 2 ^ 59
def prefixEnd_639775 : Nat := 4983230072969 + 3 ^ 40 * 639775 * 2
def baseEnd_639775 : Nat := 48668457145235497936331

theorem tailTrace_639775 : CollatzResearch.WordTrace tailWord_639775 prefixEnd_639775 48668457145235497936331 := by
  unfold tailWord_639775
  simp only [CollatzResearch.WordTrace]
  refine ⟨23334511257211914716088779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15556340838141276477392519 23334511257211914716088779)
  ·
    refine ⟨35001766885817872074133169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23334511257211914716088779 35001766885817872074133169)
    ·
      refine ⟨26251325164363404055599877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35001766885817872074133169 26251325164363404055599877)
      ·
        refine ⟨4922123468318138260424977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26251325164363404055599877 4922123468318138260424977)
        ·
          refine ⟨3691592601238603695318733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4922123468318138260424977 3691592601238603695318733)
          ·
            refine ⟨1384347225464476385744525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3691592601238603695318733 1384347225464476385744525)
            ·
              refine ⟨519130209549178644654197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1384347225464476385744525 519130209549178644654197)
              ·
                refine ⟨48668457145235497936331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 519130209549178644654197 48668457145235497936331)
                ·
                  rfl

theorem cell21_639775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 5].length) (baseStart_639775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_639775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_639775 prefixEnd_639775 := by exact prefixLift 639775
  have htrace : WordTrace (prefixWord ++ tailWord_639775) baseStart_639775 baseEnd_639775 := by
    simpa [prefixWord, tailWord_639775, baseEnd_639775] using wordTrace_append hprefix tailTrace_639775
  have hstable : (prefixWord ++ tailWord_639775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639775).length < 2 ^ (prefixWord ++ tailWord_639775).sum := by decide
  have hdescent : baseEnd_639775 < baseStart_639775 := by decide
  rcases family_descends (prefixWord ++ tailWord_639775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639834 : List Nat := [3, 1, 1, 2, 1, 5, 1, 7]
def baseStart_639834 : Nat := 118140960795 + 639834 * 2 ^ 59
def prefixEnd_639834 : Nat := 4983230072969 + 3 ^ 40 * 639834 * 2
def baseEnd_639834 : Nat := 48672945346511834108513

theorem tailTrace_639834 : CollatzResearch.WordTrace tailWord_639834 prefixEnd_639834 48672945346511834108513 := by
  unfold tailWord_639834
  simp only [CollatzResearch.WordTrace]
  refine ⟨5834165790999541948121639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15557775442665445194991037 5834165790999541948121639)
  ·
    refine ⟨8751248686499312922182459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5834165790999541948121639 8751248686499312922182459)
    ·
      refine ⟨13126873029748969383273689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8751248686499312922182459 13126873029748969383273689)
      ·
        refine ⟨9845154772311727037455267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13126873029748969383273689 9845154772311727037455267)
        ·
          refine ⟨14767732158467590556182901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9845154772311727037455267 14767732158467590556182901)
          ·
            refine ⟨1384474889856336614642147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14767732158467590556182901 1384474889856336614642147)
            ·
              refine ⟨2076712334784504921963221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1384474889856336614642147 2076712334784504921963221)
              ·
                refine ⟨48672945346511834108513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2076712334784504921963221 48672945346511834108513)
                ·
                  rfl

theorem cell21_639834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_639834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_639834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_639834 prefixEnd_639834 := by exact prefixLift 639834
  have htrace : WordTrace (prefixWord ++ tailWord_639834) baseStart_639834 baseEnd_639834 := by
    simpa [prefixWord, tailWord_639834, baseEnd_639834] using wordTrace_append hprefix tailTrace_639834
  have hstable : (prefixWord ++ tailWord_639834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639834).length < 2 ^ (prefixWord ++ tailWord_639834).sum := by decide
  have hdescent : baseEnd_639834 < baseStart_639834 := by decide
  rcases family_descends (prefixWord ++ tailWord_639834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639865 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 5]
def baseStart_639865 : Nat := 118140960795 + 639865 * 2 ^ 59
def prefixEnd_639865 : Nat := 4983230072969 + 3 ^ 40 * 639865 * 2
def baseEnd_639865 : Nat := 146025910661886337308809

theorem tailTrace_639865 : CollatzResearch.WordTrace tailWord_639865 prefixEnd_639865 146025910661886337308809 := by
  unfold tailWord_639865
  simp only [CollatzResearch.WordTrace]
  refine ⟨23337793826885860086865049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15558529217923906724576699 23337793826885860086865049)
  ·
    refine ⟨17503345370164395065148787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23337793826885860086865049 17503345370164395065148787)
    ·
      refine ⟨26255018055246592597723181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17503345370164395065148787 26255018055246592597723181)
      ·
        refine ⟨9845631770717472224146193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26255018055246592597723181 9845631770717472224146193)
        ·
          refine ⟨7384223828038104168109645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9845631770717472224146193 7384223828038104168109645)
          ·
            refine ⟨2769083935514289063041117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7384223828038104168109645 2769083935514289063041117)
            ·
              refine ⟨1038406475817858398640419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2769083935514289063041117 1038406475817858398640419)
              ·
                refine ⟨1557609713726787597960629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038406475817858398640419 1557609713726787597960629)
                ·
                  refine ⟨146025910661886337308809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1557609713726787597960629 146025910661886337308809)
                  ·
                    rfl

theorem cell21_639865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_639865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_639865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_639865 prefixEnd_639865 := by exact prefixLift 639865
  have htrace : WordTrace (prefixWord ++ tailWord_639865) baseStart_639865 baseEnd_639865 := by
    simpa [prefixWord, tailWord_639865, baseEnd_639865] using wordTrace_append hprefix tailTrace_639865
  have hstable : (prefixWord ++ tailWord_639865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639865).length < 2 ^ (prefixWord ++ tailWord_639865).sum := by decide
  have hdescent : baseEnd_639865 < baseStart_639865 := by decide
  rcases family_descends (prefixWord ++ tailWord_639865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640031 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 6]
def baseStart_640031 : Nat := 118140960795 + 640031 * 2 ^ 59
def prefixEnd_640031 : Nat := 4983230072969 + 3 ^ 40 * 640031 * 2
def baseEnd_640031 : Nat := 146063794123506937541803

theorem tailTrace_640031 : CollatzResearch.WordTrace tailWord_640031 prefixEnd_640031 146063794123506937541803 := by
  unfold tailWord_640031
  simp only [CollatzResearch.WordTrace]
  refine ⟨23343848344284470437407947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15562565562856313624938631 23343848344284470437407947)
  ·
    refine ⟨35015772516426705656111921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23343848344284470437407947 35015772516426705656111921)
    ·
      refine ⟨26261829387320029242083941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35015772516426705656111921 26261829387320029242083941)
      ·
        refine ⟨4924093010122505482890739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26261829387320029242083941 4924093010122505482890739)
        ·
          refine ⟨7386139515183758224336109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4924093010122505482890739 7386139515183758224336109)
          ·
            refine ⟨2769802318193909334126041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7386139515183758224336109 2769802318193909334126041)
            ·
              refine ⟨2077351738645432000594531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2769802318193909334126041 2077351738645432000594531)
              ·
                refine ⟨3116027607968148000891797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2077351738645432000594531 3116027607968148000891797)
                ·
                  refine ⟨146063794123506937541803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3116027607968148000891797 146063794123506937541803)
                  ·
                    rfl

theorem cell21_640031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 6].length) (baseStart_640031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640031 prefixEnd_640031 := by exact prefixLift 640031
  have htrace : WordTrace (prefixWord ++ tailWord_640031) baseStart_640031 baseEnd_640031 := by
    simpa [prefixWord, tailWord_640031, baseEnd_640031] using wordTrace_append hprefix tailTrace_640031
  have hstable : (prefixWord ++ tailWord_640031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640031).length < 2 ^ (prefixWord ++ tailWord_640031).sum := by decide
  have hdescent : baseEnd_640031 < baseStart_640031 := by decide
  rcases family_descends (prefixWord ++ tailWord_640031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640034 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 5]
def baseStart_640034 : Nat := 118140960795 + 640034 * 2 ^ 59
def prefixEnd_640034 : Nat := 4983230072969 + 3 ^ 40 * 640034 * 2
def baseEnd_640034 : Nat := 146064478764379598991797

theorem tailTrace_640034 : CollatzResearch.WordTrace tailWord_640034 prefixEnd_640034 146064478764379598991797 := by
  unfold tailWord_640034
  simp only [CollatzResearch.WordTrace]
  refine ⟨5835989440818400487441789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15562638508849067966511437 5835989440818400487441789)
  ·
    refine ⟨2188496040306900182790671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5835989440818400487441789 2188496040306900182790671)
    ·
      refine ⟨3282744060460350274186007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2188496040306900182790671 3282744060460350274186007)
      ·
        refine ⟨4924116090690525411279011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3282744060460350274186007 4924116090690525411279011)
        ·
          refine ⟨7386174136035788116918517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4924116090690525411279011 7386174136035788116918517)
          ·
            refine ⟨692453825253355135961111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7386174136035788116918517 692453825253355135961111)
            ·
              refine ⟨1038680737880032703941667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692453825253355135961111 1038680737880032703941667)
              ·
                refine ⟨1558021106820049055912501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038680737880032703941667 1558021106820049055912501)
                ·
                  refine ⟨146064478764379598991797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1558021106820049055912501 146064478764379598991797)
                  ·
                    rfl

theorem cell21_640034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_640034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640034 prefixEnd_640034 := by exact prefixLift 640034
  have htrace : WordTrace (prefixWord ++ tailWord_640034) baseStart_640034 baseEnd_640034 := by
    simpa [prefixWord, tailWord_640034, baseEnd_640034] using wordTrace_append hprefix tailTrace_640034
  have hstable : (prefixWord ++ tailWord_640034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640034).length < 2 ^ (prefixWord ++ tailWord_640034).sum := by decide
  have hdescent : baseEnd_640034 < baseStart_640034 := by decide
  rcases family_descends (prefixWord ++ tailWord_640034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640158 : List Nat := [4, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_640158 : Nat := 118140960795 + 640158 * 2 ^ 59
def prefixEnd_640158 : Nat := 4983230072969 + 3 ^ 40 * 640158 * 2
def baseEnd_640158 : Nat := 146092777253782938924877

theorem tailTrace_640158 : CollatzResearch.WordTrace tailWord_640158 prefixEnd_640158 146092777253782938924877 := by
  unfold tailWord_640158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2918560051853046390910141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15565653609882914084854085 2918560051853046390910141)
  ·
    refine ⟨1094460019444892396591303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2918560051853046390910141 1094460019444892396591303)
    ·
      refine ⟨1641690029167338594886955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1094460019444892396591303 1641690029167338594886955)
      ·
        refine ⟨2462535043751007892330433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1641690029167338594886955 2462535043751007892330433)
        ·
          refine ⟨1846901282813255919247825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2462535043751007892330433 1846901282813255919247825)
          ·
            refine ⟨1385175962109941939435869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1846901282813255919247825 1385175962109941939435869)
            ·
              refine ⟨519440985791228227288451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1385175962109941939435869 519440985791228227288451)
              ·
                refine ⟨779161478686842340932677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519440985791228227288451 779161478686842340932677)
                ·
                  refine ⟨146092777253782938924877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 779161478686842340932677 146092777253782938924877)
                  ·
                    rfl

theorem cell21_640158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_640158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640158 prefixEnd_640158 := by exact prefixLift 640158
  have htrace : WordTrace (prefixWord ++ tailWord_640158) baseStart_640158 baseEnd_640158 := by
    simpa [prefixWord, tailWord_640158, baseEnd_640158] using wordTrace_append hprefix tailTrace_640158
  have hstable : (prefixWord ++ tailWord_640158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640158).length < 2 ^ (prefixWord ++ tailWord_640158).sum := by decide
  have hdescent : baseEnd_640158 < baseStart_640158 := by decide
  rcases family_descends (prefixWord ++ tailWord_640158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640228 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 5]
def baseStart_640228 : Nat := 118140960795 + 640228 * 2 ^ 59
def prefixEnd_640228 : Nat := 4983230072969 + 3 ^ 40 * 640228 * 2
def baseEnd_640228 : Nat := 146108752207478372758067

theorem tailTrace_640228 : CollatzResearch.WordTrace tailWord_640228 prefixEnd_640228 146108752207478372758067 := by
  unfold tailWord_640228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11675516762285386541164669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15567355683047182054886225 11675516762285386541164669)
  ·
    refine ⟨4378318785857019952936751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11675516762285386541164669 4378318785857019952936751)
    ·
      refine ⟨6567478178785529929405127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4378318785857019952936751 6567478178785529929405127)
      ·
        refine ⟨9851217268178294894107691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6567478178785529929405127 9851217268178294894107691)
        ·
          refine ⟨14776825902267442341161537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9851217268178294894107691 14776825902267442341161537)
          ·
            refine ⟨11082619426700581755871153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14776825902267442341161537 11082619426700581755871153)
            ·
              refine ⟨8311964570025436316903365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11082619426700581755871153 8311964570025436316903365)
              ·
                refine ⟨1558493356879769309419381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8311964570025436316903365 1558493356879769309419381)
                ·
                  refine ⟨146108752207478372758067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1558493356879769309419381 146108752207478372758067)
                  ·
                    rfl

theorem cell21_640228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_640228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640228 prefixEnd_640228 := by exact prefixLift 640228
  have htrace : WordTrace (prefixWord ++ tailWord_640228) baseStart_640228 baseEnd_640228 := by
    simpa [prefixWord, tailWord_640228, baseEnd_640228] using wordTrace_append hprefix tailTrace_640228
  have hstable : (prefixWord ++ tailWord_640228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640228).length < 2 ^ (prefixWord ++ tailWord_640228).sum := by decide
  have hdescent : baseEnd_640228 < baseStart_640228 := by decide
  rcases family_descends (prefixWord ++ tailWord_640228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640259 : List Nat := [1, 1, 1, 3, 2, 4, 1, 4, 4]
def baseStart_640259 : Nat := 118140960795 + 640259 * 2 ^ 59
def prefixEnd_640259 : Nat := 4983230072969 + 3 ^ 40 * 640259 * 2
def baseEnd_640259 : Nat := 146115826829829207741337

theorem tailTrace_640259 : CollatzResearch.WordTrace tailWord_640259 prefixEnd_640259 146115826829829207741337 := by
  unfold tailWord_640259
  simp only [CollatzResearch.WordTrace]
  refine ⟨23352164187458465376707831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15568109458305643584471887 23352164187458465376707831)
  ·
    refine ⟨35028246281187698065061747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23352164187458465376707831 35028246281187698065061747)
    ·
      refine ⟨52542369421781547097592621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35028246281187698065061747 52542369421781547097592621)
      ·
        refine ⟨19703388533168080161597233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52542369421781547097592621 19703388533168080161597233)
        ·
          refine ⟨14777541399876060121197925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19703388533168080161597233 14777541399876060121197925)
          ·
            refine ⟨2770789012476761272724611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14777541399876060121197925 2770789012476761272724611)
            ·
              refine ⟨4156183518715141909086917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2770789012476761272724611 4156183518715141909086917)
              ·
                refine ⟨779284409759089107953797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4156183518715141909086917 779284409759089107953797)
                ·
                  refine ⟨146115826829829207741337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 779284409759089107953797 146115826829829207741337)
                  ·
                    rfl

theorem cell21_640259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 4].length) (baseStart_640259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640259 prefixEnd_640259 := by exact prefixLift 640259
  have htrace : WordTrace (prefixWord ++ tailWord_640259) baseStart_640259 baseEnd_640259 := by
    simpa [prefixWord, tailWord_640259, baseEnd_640259] using wordTrace_append hprefix tailTrace_640259
  have hstable : (prefixWord ++ tailWord_640259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640259).length < 2 ^ (prefixWord ++ tailWord_640259).sum := by decide
  have hdescent : baseEnd_640259 < baseStart_640259 := by decide
  rcases family_descends (prefixWord ++ tailWord_640259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640321 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 5]
def baseStart_640321 : Nat := 118140960795 + 640321 * 2 ^ 59
def prefixEnd_640321 : Nat := 4983230072969 + 3 ^ 40 * 640321 * 2
def baseEnd_640321 : Nat := 146129976074530877707877

theorem tailTrace_640321 : CollatzResearch.WordTrace tailWord_640321 prefixEnd_640321 146129976074530877707877 := by
  unfold tailWord_640321
  simp only [CollatzResearch.WordTrace]
  refine ⟨23354425513233849965464817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15569617008822566643643211 23354425513233849965464817)
  ·
    refine ⟨17515819134925387474098613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23354425513233849965464817 17515819134925387474098613)
    ·
      refine ⟨1642108043899255075696745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17515819134925387474098613 1642108043899255075696745)
      ·
        refine ⟨1231581032924441306772559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1642108043899255075696745 1231581032924441306772559)
        ·
          refine ⟨1847371549386661960158839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1231581032924441306772559 1847371549386661960158839)
          ·
            refine ⟨2771057324079992940238259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847371549386661960158839 2771057324079992940238259)
            ·
              refine ⟨4156585986119989410357389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2771057324079992940238259 4156585986119989410357389)
              ·
                refine ⟨1558719744794996028884021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4156585986119989410357389 1558719744794996028884021)
                ·
                  refine ⟨146129976074530877707877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1558719744794996028884021 146129976074530877707877)
                  ·
                    rfl

theorem cell21_640321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_640321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640321 prefixEnd_640321 := by exact prefixLift 640321
  have htrace : WordTrace (prefixWord ++ tailWord_640321) baseStart_640321 baseEnd_640321 := by
    simpa [prefixWord, tailWord_640321, baseEnd_640321] using wordTrace_append hprefix tailTrace_640321
  have hstable : (prefixWord ++ tailWord_640321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640321).length < 2 ^ (prefixWord ++ tailWord_640321).sum := by decide
  have hdescent : baseEnd_640321 < baseStart_640321 := by decide
  rcases family_descends (prefixWord ++ tailWord_640321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640386 : List Nat := [3, 4, 2, 1, 1, 1, 4, 1, 4]
def baseStart_640386 : Nat := 118140960795 + 640386 * 2 ^ 59
def prefixEnd_640386 : Nat := 4983230072969 + 3 ^ 40 * 640386 * 2
def baseEnd_640386 : Nat := 146144809960105209124411

theorem tailTrace_640386 : CollatzResearch.WordTrace tailWord_640386 prefixEnd_640386 146144809960105209124411 := by
  unfold tailWord_640386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5839199064499591516645253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15571197505332244044387341 5839199064499591516645253)
  ·
    refine ⟨1094849824593673409370985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5839199064499591516645253 1094849824593673409370985)
    ·
      refine ⟨821137368445255057028239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1094849824593673409370985 821137368445255057028239)
      ·
        refine ⟨1231706052667882585542359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 821137368445255057028239 1231706052667882585542359)
        ·
          refine ⟨1847559079001823878313539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1231706052667882585542359 1847559079001823878313539)
          ·
            refine ⟨2771338618502735817470309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847559079001823878313539 2771338618502735817470309)
            ·
              refine ⟨519625990969262965775683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2771338618502735817470309 519625990969262965775683)
              ·
                refine ⟨779438986453894448663525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519625990969262965775683 779438986453894448663525)
                ·
                  refine ⟨146144809960105209124411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 779438986453894448663525 146144809960105209124411)
                  ·
                    rfl

theorem cell21_640386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_640386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640386 prefixEnd_640386 := by exact prefixLift 640386
  have htrace : WordTrace (prefixWord ++ tailWord_640386) baseStart_640386 baseEnd_640386 := by
    simpa [prefixWord, tailWord_640386, baseEnd_640386] using wordTrace_append hprefix tailTrace_640386
  have hstable : (prefixWord ++ tailWord_640386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640386).length < 2 ^ (prefixWord ++ tailWord_640386).sum := by decide
  have hdescent : baseEnd_640386 < baseStart_640386 := by decide
  rcases family_descends (prefixWord ++ tailWord_640386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640456 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 5]
def baseStart_640456 : Nat := 118140960795 + 640456 * 2 ^ 59
def prefixEnd_640456 : Nat := 4983230072969 + 3 ^ 40 * 640456 * 2
def baseEnd_640456 : Nat := 146160784913800642957601

theorem tailTrace_640456 : CollatzResearch.WordTrace tailWord_640456 prefixEnd_640456 146160784913800642957601 := by
  unfold tailWord_640456
  simp only [CollatzResearch.WordTrace]
  refine ⟨11679674683872384010814611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15572899578496512014419481 11679674683872384010814611)
  ·
    refine ⟨17519512025808576016221917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11679674683872384010814611 17519512025808576016221917)
    ·
      refine ⟨6569817009678216006083219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17519512025808576016221917 6569817009678216006083219)
      ·
        refine ⟨9854725514517324009124829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6569817009678216006083219 9854725514517324009124829)
        ·
          refine ⟨3695522067943996503421811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9854725514517324009124829 3695522067943996503421811)
          ·
            refine ⟨5543283101915994755132717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3695522067943996503421811 5543283101915994755132717)
            ·
              refine ⟨2078731163218498033174769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5543283101915994755132717 2078731163218498033174769)
              ·
                refine ⟨1559048372413873524881077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2078731163218498033174769 1559048372413873524881077)
                ·
                  refine ⟨146160784913800642957601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1559048372413873524881077 146160784913800642957601)
                  ·
                    rfl

theorem cell21_640456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_640456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640456 prefixEnd_640456 := by exact prefixLift 640456
  have htrace : WordTrace (prefixWord ++ tailWord_640456) baseStart_640456 baseEnd_640456 := by
    simpa [prefixWord, tailWord_640456, baseEnd_640456] using wordTrace_append hprefix tailTrace_640456
  have hstable : (prefixWord ++ tailWord_640456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640456).length < 2 ^ (prefixWord ++ tailWord_640456).sum := by decide
  have hdescent : baseEnd_640456 < baseStart_640456 := by decide
  rcases family_descends (prefixWord ++ tailWord_640456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640473 : List Nat := [1, 2, 1, 2, 4, 2, 1, 5, 3]
def baseStart_640473 : Nat := 118140960795 + 640473 * 2 ^ 59
def prefixEnd_640473 : Nat := 4983230072969 + 3 ^ 40 * 640473 * 2
def baseEnd_640473 : Nat := 146164664545412391174233

theorem tailTrace_640473 : CollatzResearch.WordTrace tailWord_640473 prefixEnd_640473 146164664545412391174233 := by
  unfold tailWord_640473
  simp only [CollatzResearch.WordTrace]
  refine ⟨23359969408683179924998073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15573312939122119949998715 23359969408683179924998073)
  ·
    refine ⟨17519977056512384943748555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23359969408683179924998073 17519977056512384943748555)
    ·
      refine ⟨26279965584768577415622833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17519977056512384943748555 26279965584768577415622833)
      ·
        refine ⟨19709974188576433061717125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26279965584768577415622833 19709974188576433061717125)
        ·
          refine ⟨3695620160358081199071961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19709974188576433061717125 3695620160358081199071961)
          ·
            refine ⟨2771715120268560899303971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3695620160358081199071961 2771715120268560899303971)
            ·
              refine ⟨4157572680402841348955957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2771715120268560899303971 4157572680402841348955957)
              ·
                refine ⟨389772438787766376464621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4157572680402841348955957 389772438787766376464621)
                ·
                  refine ⟨146164664545412391174233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 389772438787766376464621 146164664545412391174233)
                  ·
                    rfl

theorem cell21_640473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 3].length) (baseStart_640473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640473 prefixEnd_640473 := by exact prefixLift 640473
  have htrace : WordTrace (prefixWord ++ tailWord_640473) baseStart_640473 baseEnd_640473 := by
    simpa [prefixWord, tailWord_640473, baseEnd_640473] using wordTrace_append hprefix tailTrace_640473
  have hstable : (prefixWord ++ tailWord_640473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640473).length < 2 ^ (prefixWord ++ tailWord_640473).sum := by decide
  have hdescent : baseEnd_640473 < baseStart_640473 := by decide
  rcases family_descends (prefixWord ++ tailWord_640473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640487 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 6]
def baseStart_640487 : Nat := 118140960795 + 640487 * 2 ^ 59
def prefixEnd_640487 : Nat := 4983230072969 + 3 ^ 40 * 640487 * 2
def baseEnd_640487 : Nat := 146167859536151477940871

theorem tailTrace_640487 : CollatzResearch.WordTrace tailWord_640487 prefixEnd_640487 146167859536151477940871 := by
  unfold tailWord_640487
  simp only [CollatzResearch.WordTrace]
  refine ⟨23360480030632460316007715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15573653353754973544005143 23360480030632460316007715)
  ·
    refine ⟨35040720045948690474011573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23360480030632460316007715 35040720045948690474011573)
    ·
      refine ⟨3285067504307689731938585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35040720045948690474011573 3285067504307689731938585)
      ·
        refine ⟨2463800628230767298953939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3285067504307689731938585 2463800628230767298953939)
        ·
          refine ⟨3695700942346150948430909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2463800628230767298953939 3695700942346150948430909)
          ·
            refine ⟨1385887853379806605661591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3695700942346150948430909 1385887853379806605661591)
            ·
              refine ⟨2078831780069709908492387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1385887853379806605661591 2078831780069709908492387)
              ·
                refine ⟨3118247670104564862738581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2078831780069709908492387 3118247670104564862738581)
                ·
                  refine ⟨146167859536151477940871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3118247670104564862738581 146167859536151477940871)
                  ·
                    rfl

theorem cell21_640487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 6].length) (baseStart_640487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640487 prefixEnd_640487 := by exact prefixLift 640487
  have htrace : WordTrace (prefixWord ++ tailWord_640487) baseStart_640487 baseEnd_640487 := by
    simpa [prefixWord, tailWord_640487, baseEnd_640487] using wordTrace_append hprefix tailTrace_640487
  have hstable : (prefixWord ++ tailWord_640487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640487).length < 2 ^ (prefixWord ++ tailWord_640487).sum := by decide
  have hdescent : baseEnd_640487 < baseStart_640487 := by decide
  rcases family_descends (prefixWord ++ tailWord_640487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
