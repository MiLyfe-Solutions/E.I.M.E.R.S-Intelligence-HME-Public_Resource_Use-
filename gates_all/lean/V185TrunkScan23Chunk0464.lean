import V185TrunkScan23Chunk0463

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2745187 : List Nat := [1, 1, 1, 5, 3, 1, 2, 4, 1, 4]
def baseStart_2745187 : Nat := 118140960795 + 2745187 * 2 ^ 59
def prefixEnd_2745187 : Nat := 4983230072969 + 3 ^ 40 * 2745187 * 2
def baseEnd_2745187 : Nat := 469866805824752058979207

theorem tailTrace_2745187 : CollatzResearch.WordTrace tailWord_2745187 prefixEnd_2745187 469866805824752058979207 := by
  unfold tailWord_2745187
  simp only [CollatzResearch.WordTrace]
  refine ⟨100125195505663814458401815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66750130337109209638934543 100125195505663814458401815)
  ·
    refine ⟨150187793258495721687602723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100125195505663814458401815 150187793258495721687602723)
    ·
      refine ⟨225281689887743582531404085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150187793258495721687602723 225281689887743582531404085)
      ·
        refine ⟨21120158426975960862319133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 225281689887743582531404085 21120158426975960862319133)
        ·
          refine ⟨7920059410115985323369675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21120158426975960862319133 7920059410115985323369675)
          ·
            refine ⟨11880089115173977985054513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7920059410115985323369675 11880089115173977985054513)
            ·
              refine ⟨8910066836380483488790885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11880089115173977985054513 8910066836380483488790885)
              ·
                refine ⟨1670637531821340654148291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8910066836380483488790885 1670637531821340654148291)
                ·
                  refine ⟨2505956297732010981222437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1670637531821340654148291 2505956297732010981222437)
                  ·
                    refine ⟨469866805824752058979207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2505956297732010981222437 469866805824752058979207)
                    ·
                      rfl

theorem cell23_2745187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 1, 4].length) (baseStart_2745187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745187 prefixEnd_2745187 := by exact prefixLift 2745187
  have htrace : WordTrace (prefixWord ++ tailWord_2745187) baseStart_2745187 baseEnd_2745187 := by
    simpa [prefixWord, tailWord_2745187, baseEnd_2745187] using wordTrace_append hprefix tailTrace_2745187
  have hstable : (prefixWord ++ tailWord_2745187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745187).length < 2 ^ (prefixWord ++ tailWord_2745187).sum := by decide
  have hdescent : baseEnd_2745187 < baseStart_2745187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745213 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 3, 5]
def baseStart_2745213 : Nat := 118140960795 + 2745213 * 2 ^ 59
def prefixEnd_2745213 : Nat := 4983230072969 + 3 ^ 40 * 2745213 * 2
def baseEnd_2745213 : Nat := 469871255990424358404167

theorem tailTrace_2745213 : CollatzResearch.WordTrace tailWord_2745213 prefixEnd_2745213 469871255990424358404167 := by
  unfold tailWord_2745213
  simp only [CollatzResearch.WordTrace]
  refine ⟨100126143803569620898848293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66750762535713080599232195 100126143803569620898848293)
  ·
    refine ⟨18773651963169303918534055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100126143803569620898848293 18773651963169303918534055)
    ·
      refine ⟨28160477944753955877801083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18773651963169303918534055 28160477944753955877801083)
      ·
        refine ⟨42240716917130933816701625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28160477944753955877801083 42240716917130933816701625)
        ·
          refine ⟨31680537687848200362526219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42240716917130933816701625 31680537687848200362526219)
          ·
            refine ⟨47520806531772300543789329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31680537687848200362526219 47520806531772300543789329)
            ·
              refine ⟨35640604898829225407841997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47520806531772300543789329 35640604898829225407841997)
              ·
                refine ⟨13365226837060959527940749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35640604898829225407841997 13365226837060959527940749)
                ·
                  refine ⟨5011960063897859822977781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13365226837060959527940749 5011960063897859822977781)
                  ·
                    refine ⟨469871255990424358404167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5011960063897859822977781 469871255990424358404167)
                    ·
                      rfl

theorem cell23_2745213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_2745213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745213 prefixEnd_2745213 := by exact prefixLift 2745213
  have htrace : WordTrace (prefixWord ++ tailWord_2745213) baseStart_2745213 baseEnd_2745213 := by
    simpa [prefixWord, tailWord_2745213, baseEnd_2745213] using wordTrace_append hprefix tailTrace_2745213
  have hstable : (prefixWord ++ tailWord_2745213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745213).length < 2 ^ (prefixWord ++ tailWord_2745213).sum := by decide
  have hdescent : baseEnd_2745213 < baseStart_2745213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745233 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 4]
def baseStart_2745233 : Nat := 118140960795 + 2745233 * 2 ^ 59
def prefixEnd_2745233 : Nat := 4983230072969 + 3 ^ 40 * 2745233 * 2
def baseEnd_2745233 : Nat := 1409624037584362996962409

theorem tailTrace_2745233 : CollatzResearch.WordTrace tailWord_2745233 prefixEnd_2745233 1409624037584362996962409 := by
  unfold tailWord_2745233
  simp only [CollatzResearch.WordTrace]
  refine ⟨100126873263497164314576353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66751248842331442876384235 100126873263497164314576353)
  ·
    refine ⟨75095154947622873235932265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100126873263497164314576353 75095154947622873235932265)
    ·
      refine ⟨56321366210717154926949199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75095154947622873235932265 56321366210717154926949199)
      ·
        refine ⟨84482049316075732390423799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56321366210717154926949199 84482049316075732390423799)
        ·
          refine ⟨126723073974113598585635699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84482049316075732390423799 126723073974113598585635699)
          ·
            refine ⟨190084610961170397878453549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126723073974113598585635699 190084610961170397878453549)
            ·
              refine ⟨71281729110438899204420081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190084610961170397878453549 71281729110438899204420081)
              ·
                refine ⟨53461296832829174403315061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71281729110438899204420081 53461296832829174403315061)
                ·
                  refine ⟨5011996578077735100310787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53461296832829174403315061 5011996578077735100310787)
                  ·
                    refine ⟨7517994867116602650466181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5011996578077735100310787 7517994867116602650466181)
                    ·
                      refine ⟨1409624037584362996962409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7517994867116602650466181 1409624037584362996962409)
                      ·
                        rfl

theorem cell23_2745233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_2745233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745233 prefixEnd_2745233 := by exact prefixLift 2745233
  have htrace : WordTrace (prefixWord ++ tailWord_2745233) baseStart_2745233 baseEnd_2745233 := by
    simpa [prefixWord, tailWord_2745233, baseEnd_2745233] using wordTrace_append hprefix tailTrace_2745233
  have hstable : (prefixWord ++ tailWord_2745233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745233).length < 2 ^ (prefixWord ++ tailWord_2745233).sum := by decide
  have hdescent : baseEnd_2745233 < baseStart_2745233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745237 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 2, 3, 2]
def baseStart_2745237 : Nat := 118140960795 + 2745237 * 2 ^ 59
def prefixEnd_2745237 : Nat := 4983230072969 + 3 ^ 40 * 2745237 * 2
def baseEnd_2745237 : Nat := 1409626091506980981312391

theorem tailTrace_2745237 : CollatzResearch.WordTrace tailWord_2745237 prefixEnd_2745237 1409626091506980981312391 := by
  unfold tailWord_2745237
  simp only [CollatzResearch.WordTrace]
  refine ⟨100127019155482672997721965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66751346103655115331814643 100127019155482672997721965)
  ·
    refine ⟨37547632183306002374145737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100127019155482672997721965 37547632183306002374145737)
    ·
      refine ⟨28160724137479501780609303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37547632183306002374145737 28160724137479501780609303)
      ·
        refine ⟨42241086206219252670913955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28160724137479501780609303 42241086206219252670913955)
        ·
          refine ⟨63361629309328879006370933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42241086206219252670913955 63361629309328879006370933)
          ·
            refine ⟨5940152747749582406847275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63361629309328879006370933 5940152747749582406847275)
            ·
              refine ⟨8910229121624373610270913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5940152747749582406847275 8910229121624373610270913)
              ·
                refine ⟨6682671841218280207703185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8910229121624373610270913 6682671841218280207703185)
                ·
                  refine ⟨5012003880913710155777389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6682671841218280207703185 5012003880913710155777389)
                  ·
                    refine ⟨1879501455342641308416521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5012003880913710155777389 1879501455342641308416521)
                    ·
                      refine ⟨1409626091506980981312391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1879501455342641308416521 1409626091506980981312391)
                      ·
                        rfl

theorem cell23_2745237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_2745237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745237 prefixEnd_2745237 := by exact prefixLift 2745237
  have htrace : WordTrace (prefixWord ++ tailWord_2745237) baseStart_2745237 baseEnd_2745237 := by
    simpa [prefixWord, tailWord_2745237, baseEnd_2745237] using wordTrace_append hprefix tailTrace_2745237
  have hstable : (prefixWord ++ tailWord_2745237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745237).length < 2 ^ (prefixWord ++ tailWord_2745237).sum := by decide
  have hdescent : baseEnd_2745237 < baseStart_2745237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745253 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 1, 8, 3]
def baseStart_2745253 : Nat := 118140960795 + 2745253 * 2 ^ 59
def prefixEnd_2745253 : Nat := 4983230072969 + 3 ^ 40 * 2745253 * 2
def baseEnd_2745253 : Nat := 1409634307197452918712317

theorem tailTrace_2745253 : CollatzResearch.WordTrace tailWord_2745253 prefixEnd_2745253 1409634307197452918712317 := by
  unfold tailWord_2745253
  simp only [CollatzResearch.WordTrace]
  refine ⟨100127602723424707730304413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66751735148949805153536275 100127602723424707730304413)
  ·
    refine ⟨37547851021284265398864155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100127602723424707730304413 37547851021284265398864155)
    ·
      refine ⟨56321776531926398098296233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37547851021284265398864155 56321776531926398098296233)
      ·
        refine ⟨42241332398944798573722175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56321776531926398098296233 42241332398944798573722175)
        ·
          refine ⟨63361998598417197860583263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42241332398944798573722175 63361998598417197860583263)
          ·
            refine ⟨95042997897625796790874895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63361998598417197860583263 95042997897625796790874895)
            ·
              refine ⟨142564496846438695186312343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95042997897625796790874895 142564496846438695186312343)
              ·
                refine ⟨213846745269658042779468515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142564496846438695186312343 213846745269658042779468515)
                ·
                  refine ⟨320770117904487064169202773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213846745269658042779468515 320770117904487064169202773)
                  ·
                    refine ⟨3759024819193207783232845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 320770117904487064169202773 3759024819193207783232845)
                    ·
                      refine ⟨1409634307197452918712317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3759024819193207783232845 1409634307197452918712317)
                      ·
                        rfl

theorem cell23_2745253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_2745253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745253 prefixEnd_2745253 := by exact prefixLift 2745253
  have htrace : WordTrace (prefixWord ++ tailWord_2745253) baseStart_2745253 baseEnd_2745253 := by
    simpa [prefixWord, tailWord_2745253, baseEnd_2745253] using wordTrace_append hprefix tailTrace_2745253
  have hstable : (prefixWord ++ tailWord_2745253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745253).length < 2 ^ (prefixWord ++ tailWord_2745253).sum := by decide
  have hdescent : baseEnd_2745253 < baseStart_2745253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745260 : List Nat := [2, 2, 1, 1, 1, 1, 2, 7, 2, 4]
def baseStart_2745260 : Nat := 118140960795 + 2745260 * 2 ^ 59
def prefixEnd_2745260 : Nat := 4983230072969 + 3 ^ 40 * 2745260 * 2
def baseEnd_2745260 : Nat := 469879300520678130441595

theorem tailTrace_2745260 : CollatzResearch.WordTrace tailWord_2745260 prefixEnd_2745260 469879300520678130441595 := by
  unfold tailWord_2745260
  simp only [CollatzResearch.WordTrace]
  refine ⟨50063929017199673962904617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66751905356266231950539489 50063929017199673962904617)
  ·
    refine ⟨37547946762899755472178463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50063929017199673962904617 37547946762899755472178463)
    ·
      refine ⟨56321920144349633208267695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37547946762899755472178463 56321920144349633208267695)
      ·
        refine ⟨84482880216524449812401543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56321920144349633208267695 84482880216524449812401543)
        ·
          refine ⟨126724320324786674718602315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84482880216524449812401543 126724320324786674718602315)
          ·
            refine ⟨190086480487180012077903473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126724320324786674718602315 190086480487180012077903473)
            ·
              refine ⟨142564860365385009058427605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190086480487180012077903473 142564860365385009058427605)
              ·
                refine ⟨3341363914813711149806897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 142564860365385009058427605 3341363914813711149806897)
                ·
                  refine ⟨2506022936110283362355173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3341363914813711149806897 2506022936110283362355173)
                  ·
                    refine ⟨469879300520678130441595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2506022936110283362355173 469879300520678130441595)
                    ·
                      rfl

theorem cell23_2745260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_2745260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745260 prefixEnd_2745260 := by exact prefixLift 2745260
  have htrace : WordTrace (prefixWord ++ tailWord_2745260) baseStart_2745260 baseEnd_2745260 := by
    simpa [prefixWord, tailWord_2745260, baseEnd_2745260] using wordTrace_append hprefix tailTrace_2745260
  have hstable : (prefixWord ++ tailWord_2745260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745260).length < 2 ^ (prefixWord ++ tailWord_2745260).sum := by decide
  have hdescent : baseEnd_2745260 < baseStart_2745260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745273 : List Nat := [1, 2, 1, 4, 2, 2, 2, 9]
def baseStart_2745273 : Nat := 118140960795 + 2745273 * 2 ^ 59
def prefixEnd_2745273 : Nat := 4983230072969 + 3 ^ 40 * 2745273 * 2
def baseEnd_2745273 : Nat := 52209058400390475572675

theorem tailTrace_2745273 : CollatzResearch.WordTrace tailWord_2745273 prefixEnd_2745273 52209058400390475572675 := by
  unfold tailWord_2745273
  simp only [CollatzResearch.WordTrace]
  refine ⟨100128332183352251146032473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66752221455568167430688315 100128332183352251146032473)
  ·
    refine ⟨75096249137514188359524355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100128332183352251146032473 75096249137514188359524355)
    ·
      refine ⟨112644373706271282539286533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75096249137514188359524355 112644373706271282539286533)
      ·
        refine ⟨21120820069925865476116225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112644373706271282539286533 21120820069925865476116225)
        ·
          refine ⟨15840615052444399107087169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21120820069925865476116225 15840615052444399107087169)
          ·
            refine ⟨11880461289333299330315377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15840615052444399107087169 11880461289333299330315377)
            ·
              refine ⟨8910345966999974497736533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11880461289333299330315377 8910345966999974497736533)
              ·
                refine ⟨52209058400390475572675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8910345966999974497736533 52209058400390475572675)
                ·
                  rfl

theorem cell23_2745273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 9].length) (baseStart_2745273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745273 prefixEnd_2745273 := by exact prefixLift 2745273
  have htrace : WordTrace (prefixWord ++ tailWord_2745273) baseStart_2745273 baseEnd_2745273 := by
    simpa [prefixWord, tailWord_2745273, baseEnd_2745273] using wordTrace_append hprefix tailTrace_2745273
  have hstable : (prefixWord ++ tailWord_2745273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745273).length < 2 ^ (prefixWord ++ tailWord_2745273).sum := by decide
  have hdescent : baseEnd_2745273 < baseStart_2745273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745280 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 4]
def baseStart_2745280 : Nat := 118140960795 + 2745280 * 2 ^ 59
def prefixEnd_2745280 : Nat := 4983230072969 + 3 ^ 40 * 2745280 * 2
def baseEnd_2745280 : Nat := 1409648171175124313074693

theorem tailTrace_2745280 : CollatzResearch.WordTrace tailWord_2745280 prefixEnd_2745280 1409648171175124313074693 := by
  unfold tailWord_2745280
  simp only [CollatzResearch.WordTrace]
  refine ⟨50064293747163445670768647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66752391662884594227691529 50064293747163445670768647)
  ·
    refine ⟨75096440620745168506152971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50064293747163445670768647 75096440620745168506152971)
    ·
      refine ⟨112644660931117752759229457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75096440620745168506152971 112644660931117752759229457)
      ·
        refine ⟨84483495698338314569422093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112644660931117752759229457 84483495698338314569422093)
        ·
          refine ⟨31681310886876867963533285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84483495698338314569422093 31681310886876867963533285)
          ·
            refine ⟨5940245791289412743162491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31681310886876867963533285 5940245791289412743162491)
            ·
              refine ⟨8910368686934119114743737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5940245791289412743162491 8910368686934119114743737)
              ·
                refine ⟨6682776515200589336057803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8910368686934119114743737 6682776515200589336057803)
                ·
                  refine ⟨10024164772800884004086705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6682776515200589336057803 10024164772800884004086705)
                  ·
                    refine ⟨7518123579600663003065029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10024164772800884004086705 7518123579600663003065029)
                    ·
                      refine ⟨1409648171175124313074693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7518123579600663003065029 1409648171175124313074693)
                      ·
                        rfl

theorem cell23_2745280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_2745280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745280 prefixEnd_2745280 := by exact prefixLift 2745280
  have htrace : WordTrace (prefixWord ++ tailWord_2745280) baseStart_2745280 baseEnd_2745280 := by
    simpa [prefixWord, tailWord_2745280, baseEnd_2745280] using wordTrace_append hprefix tailTrace_2745280
  have hstable : (prefixWord ++ tailWord_2745280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745280).length < 2 ^ (prefixWord ++ tailWord_2745280).sum := by decide
  have hdescent : baseEnd_2745280 < baseStart_2745280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745313 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_2745313 : Nat := 118140960795 + 2745313 * 2 ^ 59
def prefixEnd_2745313 : Nat := 4983230072969 + 3 ^ 40 * 2745313 * 2
def baseEnd_2745313 : Nat := 1409665116036722683962041

theorem tailTrace_2745313 : CollatzResearch.WordTrace tailWord_2745313 prefixEnd_2745313 1409665116036722683962041 := by
  unfold tailWord_2745313
  simp only [CollatzResearch.WordTrace]
  refine ⟨100129791103207337977488593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66753194068804891984992395 100129791103207337977488593)
  ·
    refine ⟨75097343327405503483116445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100129791103207337977488593 75097343327405503483116445)
    ·
      refine ⟨28161503747777063806168667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75097343327405503483116445 28161503747777063806168667)
      ·
        refine ⟨42242255621665595709253001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28161503747777063806168667 42242255621665595709253001)
        ·
          refine ⟨31681691716249196781939751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42242255621665595709253001 31681691716249196781939751)
          ·
            refine ⟨47522537574373795172909627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31681691716249196781939751 47522537574373795172909627)
            ·
              refine ⟨71283806361560692759364441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47522537574373795172909627 71283806361560692759364441)
              ·
                refine ⟨53462854771170519569523331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71283806361560692759364441 53462854771170519569523331)
                ·
                  refine ⟨80194282156755779354284997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53462854771170519569523331 80194282156755779354284997)
                  ·
                    refine ⟨15036427904391708628928437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80194282156755779354284997 15036427904391708628928437)
                    ·
                      refine ⟨1409665116036722683962041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15036427904391708628928437 1409665116036722683962041)
                      ·
                        rfl

theorem cell23_2745313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_2745313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745313 prefixEnd_2745313 := by exact prefixLift 2745313
  have htrace : WordTrace (prefixWord ++ tailWord_2745313) baseStart_2745313 baseEnd_2745313 := by
    simpa [prefixWord, tailWord_2745313, baseEnd_2745313] using wordTrace_append hprefix tailTrace_2745313
  have hstable : (prefixWord ++ tailWord_2745313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745313).length < 2 ^ (prefixWord ++ tailWord_2745313).sum := by decide
  have hdescent : baseEnd_2745313 < baseStart_2745313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745314 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_2745314 : Nat := 118140960795 + 2745314 * 2 ^ 59
def prefixEnd_2745314 : Nat := 4983230072969 + 3 ^ 40 * 2745314 * 2
def baseEnd_2745314 : Nat := 1409665629517377180049537

theorem tailTrace_2745314 : CollatzResearch.WordTrace tailWord_2745314 prefixEnd_2745314 1409665629517377180049537 := by
  unfold tailWord_2745314
  simp only [CollatzResearch.WordTrace]
  refine ⟨25032456894050928787068749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66753218384135810098849997 25032456894050928787068749)
  ·
    refine ⟨9387171335269098295150781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25032456894050928787068749 9387171335269098295150781)
    ·
      refine ⟨3520189250725911860681543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9387171335269098295150781 3520189250725911860681543)
      ·
        refine ⟨5280283876088867791022315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3520189250725911860681543 5280283876088867791022315)
        ·
          refine ⟨7920425814133301686533473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5280283876088867791022315 7920425814133301686533473)
          ·
            refine ⟨5940319360599976264900105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7920425814133301686533473 5940319360599976264900105)
            ·
              refine ⟨4455239520449982198675079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5940319360599976264900105 4455239520449982198675079)
              ·
                refine ⟨6682859280674973298012619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4455239520449982198675079 6682859280674973298012619)
                ·
                  refine ⟨10024288921012459947018929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6682859280674973298012619 10024288921012459947018929)
                  ·
                    refine ⟨7518216690759344960264197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10024288921012459947018929 7518216690759344960264197)
                    ·
                      refine ⟨1409665629517377180049537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7518216690759344960264197 1409665629517377180049537)
                      ·
                        rfl

theorem cell23_2745314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_2745314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745314 prefixEnd_2745314 := by exact prefixLift 2745314
  have htrace : WordTrace (prefixWord ++ tailWord_2745314) baseStart_2745314 baseEnd_2745314 := by
    simpa [prefixWord, tailWord_2745314, baseEnd_2745314] using wordTrace_append hprefix tailTrace_2745314
  have hstable : (prefixWord ++ tailWord_2745314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745314).length < 2 ^ (prefixWord ++ tailWord_2745314).sum := by decide
  have hdescent : baseEnd_2745314 < baseStart_2745314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745327 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 3, 3, 2]
def baseStart_2745327 : Nat := 118140960795 + 2745327 * 2 ^ 59
def prefixEnd_2745327 : Nat := 4983230072969 + 3 ^ 40 * 2745327 * 2
def baseEnd_2745327 : Nat := 1409672304765885629186977

theorem tailTrace_2745327 : CollatzResearch.WordTrace tailWord_2745327 prefixEnd_2745327 1409672304765885629186977 := by
  unfold tailWord_2745327
  simp only [CollatzResearch.WordTrace]
  refine ⟨100130301725156618368498235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66753534483437745578998823 100130301725156618368498235)
  ·
    refine ⟨150195452587734927552747353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100130301725156618368498235 150195452587734927552747353)
    ·
      refine ⟨112646589440801195664560515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150195452587734927552747353 112646589440801195664560515)
      ·
        refine ⟨168969884161201793496840773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112646589440801195664560515 168969884161201793496840773)
        ·
          refine ⟨31681853280225336280657645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168969884161201793496840773 31681853280225336280657645)
          ·
            refine ⟨11880694980084501105246617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31681853280225336280657645 11880694980084501105246617)
            ·
              refine ⟨8910521235063375828934963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11880694980084501105246617 8910521235063375828934963)
              ·
                refine ⟨13365781852595063743402445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8910521235063375828934963 13365781852595063743402445)
                ·
                  refine ⟨5012168194723148903775917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13365781852595063743402445 5012168194723148903775917)
                  ·
                    refine ⟨1879563073021180838915969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5012168194723148903775917 1879563073021180838915969)
                    ·
                      refine ⟨1409672304765885629186977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1879563073021180838915969 1409672304765885629186977)
                      ·
                        rfl

theorem cell23_2745327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 3, 2].length) (baseStart_2745327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745327 prefixEnd_2745327 := by exact prefixLift 2745327
  have htrace : WordTrace (prefixWord ++ tailWord_2745327) baseStart_2745327 baseEnd_2745327 := by
    simpa [prefixWord, tailWord_2745327, baseEnd_2745327] using wordTrace_append hprefix tailTrace_2745327
  have hstable : (prefixWord ++ tailWord_2745327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745327).length < 2 ^ (prefixWord ++ tailWord_2745327).sum := by decide
  have hdescent : baseEnd_2745327 < baseStart_2745327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745332 : List Nat := [2, 6, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2745332 : Nat := 118140960795 + 2745332 * 2 ^ 59
def prefixEnd_2745332 : Nat := 4983230072969 + 3 ^ 40 * 2745332 * 2
def baseEnd_2745332 : Nat := 469891624056386036541485

theorem tailTrace_2745332 : CollatzResearch.WordTrace tailWord_2745332 prefixEnd_2745332 469891624056386036541485 := by
  unfold tailWord_2745332
  simp only [CollatzResearch.WordTrace]
  refine ⟨50065242045069252111215125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66753656060092336148286833 50065242045069252111215125)
  ·
    refine ⟨2346808220862621192713209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50065242045069252111215125 2346808220862621192713209)
    ·
      refine ⟨1760106165646965894534907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2346808220862621192713209 1760106165646965894534907)
      ·
        refine ⟨2640159248470448841802361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1760106165646965894534907 2640159248470448841802361)
        ·
          refine ⟨1980119436352836631351771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2640159248470448841802361 1980119436352836631351771)
          ·
            refine ⟨2970179154529254947027657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1980119436352836631351771 2970179154529254947027657)
            ·
              refine ⟨2227634365896941210270743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2970179154529254947027657 2227634365896941210270743)
              ·
                refine ⟨3341451548845411815406115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227634365896941210270743 3341451548845411815406115)
                ·
                  refine ⟨5012177323268117723109173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3341451548845411815406115 5012177323268117723109173)
                  ·
                    refine ⟨469891624056386036541485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5012177323268117723109173 469891624056386036541485)
                    ·
                      rfl

theorem cell23_2745332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2745332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745332 prefixEnd_2745332 := by exact prefixLift 2745332
  have htrace : WordTrace (prefixWord ++ tailWord_2745332) baseStart_2745332 baseEnd_2745332 := by
    simpa [prefixWord, tailWord_2745332, baseEnd_2745332] using wordTrace_append hprefix tailTrace_2745332
  have hstable : (prefixWord ++ tailWord_2745332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745332).length < 2 ^ (prefixWord ++ tailWord_2745332).sum := by decide
  have hdescent : baseEnd_2745332 < baseStart_2745332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745370 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4]
def baseStart_2745370 : Nat := 118140960795 + 2745370 * 2 ^ 59
def prefixEnd_2745370 : Nat := 4983230072969 + 3 ^ 40 * 2745370 * 2
def baseEnd_2745370 : Nat := 1409694384434028960949279

theorem tailTrace_2745370 : CollatzResearch.WordTrace tailWord_2745370 prefixEnd_2745370 1409694384434028960949279 := by
  unfold tailWord_2745370
  simp only [CollatzResearch.WordTrace]
  refine ⟨25032967516000209178078391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66754580042667224474875709 25032967516000209178078391)
  ·
    refine ⟨37549451274000313767117587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25032967516000209178078391 37549451274000313767117587)
    ·
      refine ⟨56324176911000470650676381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37549451274000313767117587 56324176911000470650676381)
      ·
        refine ⟨21121566341625176494003643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56324176911000470650676381 21121566341625176494003643)
        ·
          refine ⟨31682349512437764741005465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21121566341625176494003643 31682349512437764741005465)
          ·
            refine ⟨23761762134328323555754099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31682349512437764741005465 23761762134328323555754099)
            ·
              refine ⟨35642643201492485333631149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23761762134328323555754099 35642643201492485333631149)
              ·
                refine ⟨13365991200559682000111681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35642643201492485333631149 13365991200559682000111681)
                ·
                  refine ⟨10024493400419761500083761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13365991200559682000111681 10024493400419761500083761)
                  ·
                    refine ⟨7518370050314821125062821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10024493400419761500083761 7518370050314821125062821)
                    ·
                      refine ⟨1409694384434028960949279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7518370050314821125062821 1409694384434028960949279)
                      ·
                        rfl

theorem cell23_2745370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_2745370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745370 prefixEnd_2745370 := by exact prefixLift 2745370
  have htrace : WordTrace (prefixWord ++ tailWord_2745370) baseStart_2745370 baseEnd_2745370 := by
    simpa [prefixWord, tailWord_2745370, baseEnd_2745370] using wordTrace_append hprefix tailTrace_2745370
  have hstable : (prefixWord ++ tailWord_2745370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745370).length < 2 ^ (prefixWord ++ tailWord_2745370).sum := by decide
  have hdescent : baseEnd_2745370 < baseStart_2745370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745414 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_2745414 : Nat := 118140960795 + 2745414 * 2 ^ 59
def prefixEnd_2745414 : Nat := 4983230072969 + 3 ^ 40 * 2745414 * 2
def baseEnd_2745414 : Nat := 156635219731425198755453

theorem tailTrace_2745414 : CollatzResearch.WordTrace tailWord_2745414 prefixEnd_2745414 156635219731425198755453 := by
  unfold tailWord_2745414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3129171089870044757091103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66755649917227621484610197 3129171089870044757091103)
  ·
    refine ⟨4693756634805067135636655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3129171089870044757091103 4693756634805067135636655)
    ·
      refine ⟨7040634952207600703454983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4693756634805067135636655 7040634952207600703454983)
      ·
        refine ⟨10560952428311401055182475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7040634952207600703454983 10560952428311401055182475)
        ·
          refine ⟨15841428642467101582773713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10560952428311401055182475 15841428642467101582773713)
          ·
            refine ⟨11881071481850326187080285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15841428642467101582773713 11881071481850326187080285)
            ·
              refine ⟨4455401805693872320155107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11881071481850326187080285 4455401805693872320155107)
              ·
                refine ⟨6683102708540808480232661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4455401805693872320155107 6683102708540808480232661)
                ·
                  refine ⟨156635219731425198755453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6683102708540808480232661 156635219731425198755453)
                  ·
                    rfl

theorem cell23_2745414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_2745414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745414 prefixEnd_2745414 := by exact prefixLift 2745414
  have htrace : WordTrace (prefixWord ++ tailWord_2745414) baseStart_2745414 baseEnd_2745414 := by
    simpa [prefixWord, tailWord_2745414, baseEnd_2745414] using wordTrace_append hprefix tailTrace_2745414
  have hstable : (prefixWord ++ tailWord_2745414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745414).length < 2 ^ (prefixWord ++ tailWord_2745414).sum := by decide
  have hdescent : baseEnd_2745414 < baseStart_2745414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745447 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_2745447 : Nat := 118140960795 + 2745447 * 2 ^ 59
def prefixEnd_2745447 : Nat := 4983230072969 + 3 ^ 40 * 2745447 * 2
def baseEnd_2745447 : Nat := 1409733922444425159686425

theorem tailTrace_2745447 : CollatzResearch.WordTrace tailWord_2745447 prefixEnd_2745447 1409733922444425159686425 := by
  unfold tailWord_2745447
  simp only [CollatzResearch.WordTrace]
  refine ⟨100134678484721878862866595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66756452323147919241911063 100134678484721878862866595)
  ·
    refine ⟨150202017727082818294299893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100134678484721878862866595 150202017727082818294299893)
    ·
      refine ⟨14081439161914014215090615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150202017727082818294299893 14081439161914014215090615)
      ·
        refine ⟨21122158742871021322635923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14081439161914014215090615 21122158742871021322635923)
        ·
          refine ⟨31683238114306531983953885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21122158742871021322635923 31683238114306531983953885)
          ·
            refine ⟨11881214292864949493982707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31683238114306531983953885 11881214292864949493982707)
            ·
              refine ⟨17821821439297424240974061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11881214292864949493982707 17821821439297424240974061)
              ·
                refine ⟨6683183039736534090365273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17821821439297424240974061 6683183039736534090365273)
                ·
                  refine ⟨5012387279802400567773955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6683183039736534090365273 5012387279802400567773955)
                  ·
                    refine ⟨7518580919703600851660933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5012387279802400567773955 7518580919703600851660933)
                    ·
                      refine ⟨1409733922444425159686425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7518580919703600851660933 1409733922444425159686425)
                      ·
                        rfl

theorem cell23_2745447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_2745447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745447 prefixEnd_2745447 := by exact prefixLift 2745447
  have htrace : WordTrace (prefixWord ++ tailWord_2745447) baseStart_2745447 baseEnd_2745447 := by
    simpa [prefixWord, tailWord_2745447, baseEnd_2745447] using wordTrace_append hprefix tailTrace_2745447
  have hstable : (prefixWord ++ tailWord_2745447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745447).length < 2 ^ (prefixWord ++ tailWord_2745447).sum := by decide
  have hdescent : baseEnd_2745447 < baseStart_2745447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745554 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 2, 6, 2]
def baseStart_2745554 : Nat := 118140960795 + 2745554 * 2 ^ 59
def prefixEnd_2745554 : Nat := 4983230072969 + 3 ^ 40 * 2745554 * 2
def baseEnd_2745554 : Nat := 1409788864874456241048433

theorem tailTrace_2745554 : CollatzResearch.WordTrace tailWord_2745554 prefixEnd_2745554 1409788864874456241048433 := by
  unfold tailWord_2745554
  simp only [CollatzResearch.WordTrace]
  refine ⟨25034645273833559034252929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66759054063556157424674477 25034645273833559034252929)
  ·
    refine ⟨18775983955375169275689697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25034645273833559034252929 18775983955375169275689697)
    ·
      refine ⟨14081987966531376956767273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18775983955375169275689697 14081987966531376956767273)
      ·
        refine ⟨10561490974898532717575455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14081987966531376956767273 10561490974898532717575455)
        ·
          refine ⟨15842236462347799076363183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10561490974898532717575455 15842236462347799076363183)
          ·
            refine ⟨23763354693521698614544775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15842236462347799076363183 23763354693521698614544775)
            ·
              refine ⟨35645032040282547921817163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23763354693521698614544775 35645032040282547921817163)
              ·
                refine ⟨53467548060423821882725745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35645032040282547921817163 53467548060423821882725745)
                ·
                  refine ⟨40100661045317866412044309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53467548060423821882725745 40100661045317866412044309)
                  ·
                    refine ⟨1879718486499274988064577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40100661045317866412044309 1879718486499274988064577)
                    ·
                      refine ⟨1409788864874456241048433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1879718486499274988064577 1409788864874456241048433)
                      ·
                        rfl

theorem cell23_2745554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_2745554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745554 prefixEnd_2745554 := by exact prefixLift 2745554
  have htrace : WordTrace (prefixWord ++ tailWord_2745554) baseStart_2745554 baseEnd_2745554 := by
    simpa [prefixWord, tailWord_2745554, baseEnd_2745554] using wordTrace_append hprefix tailTrace_2745554
  have hstable : (prefixWord ++ tailWord_2745554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745554).length < 2 ^ (prefixWord ++ tailWord_2745554).sum := by decide
  have hdescent : baseEnd_2745554 < baseStart_2745554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745567 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 4]
def baseStart_2745567 : Nat := 118140960795 + 2745567 * 2 ^ 59
def prefixEnd_2745567 : Nat := 4983230072969 + 3 ^ 40 * 2745567 * 2
def baseEnd_2745567 : Nat := 1409795540122964690185873

theorem tailTrace_2745567 : CollatzResearch.WordTrace tailWord_2745567 prefixEnd_2745567 1409795540122964690185873 := by
  unfold tailWord_2745567
  simp only [CollatzResearch.WordTrace]
  refine ⟨100139055244287139357234955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66759370162858092904823303 100139055244287139357234955)
  ·
    refine ⟨150208582866430709035852433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100139055244287139357234955 150208582866430709035852433)
    ·
      refine ⟨112656437149823031776889325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150208582866430709035852433 112656437149823031776889325)
      ·
        refine ⟨42246163931183636916333497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112656437149823031776889325 42246163931183636916333497)
        ·
          refine ⟨31684622948387727687250123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42246163931183636916333497 31684622948387727687250123)
          ·
            refine ⟨47526934422581591530875185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31684622948387727687250123 47526934422581591530875185)
            ·
              refine ⟨35645200816936193648156389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47526934422581591530875185 35645200816936193648156389)
              ·
                refine ⟨6683475153175536309029323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35645200816936193648156389 6683475153175536309029323)
                ·
                  refine ⟨10025212729763304463543985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6683475153175536309029323 10025212729763304463543985)
                  ·
                    refine ⟨7518909547322478347657989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10025212729763304463543985 7518909547322478347657989)
                    ·
                      refine ⟨1409795540122964690185873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7518909547322478347657989 1409795540122964690185873)
                      ·
                        rfl

theorem cell23_2745567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_2745567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745567 prefixEnd_2745567 := by exact prefixLift 2745567
  have htrace : WordTrace (prefixWord ++ tailWord_2745567) baseStart_2745567 baseEnd_2745567 := by
    simpa [prefixWord, tailWord_2745567, baseEnd_2745567] using wordTrace_append hprefix tailTrace_2745567
  have hstable : (prefixWord ++ tailWord_2745567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745567).length < 2 ^ (prefixWord ++ tailWord_2745567).sum := by decide
  have hdescent : baseEnd_2745567 < baseStart_2745567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745598 : List Nat := [4, 2, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_2745598 : Nat := 118140960795 + 2745598 * 2 ^ 59
def prefixEnd_2745598 : Nat := 4983230072969 + 3 ^ 40 * 2745598 * 2
def baseEnd_2745598 : Nat := 469937152674418022966077

theorem tailTrace_2745598 : CollatzResearch.WordTrace tailWord_2745598 prefixEnd_2745598 469937152674418022966077 := by
  unfold tailWord_2745598
  simp only [CollatzResearch.WordTrace]
  refine ⟨12517523238396853956451681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66760123938116554434408965 12517523238396853956451681)
  ·
    refine ⟨9388142428797640467338761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12517523238396853956451681 9388142428797640467338761)
    ·
      refine ⟨7041106821598230350504071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9388142428797640467338761 7041106821598230350504071)
      ·
        refine ⟨10561660232397345525756107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7041106821598230350504071 10561660232397345525756107)
        ·
          refine ⟨15842490348596018288634161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10561660232397345525756107 15842490348596018288634161)
          ·
            refine ⟨11881867761447013716475621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15842490348596018288634161 11881867761447013716475621)
            ·
              refine ⟨2227850205271315071839179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11881867761447013716475621 2227850205271315071839179)
              ·
                refine ⟨3341775307906972607758769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227850205271315071839179 3341775307906972607758769)
                ·
                  refine ⟨2506331480930229455819077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3341775307906972607758769 2506331480930229455819077)
                  ·
                    refine ⟨469937152674418022966077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2506331480930229455819077 469937152674418022966077)
                    ·
                      rfl

theorem cell23_2745598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_2745598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745598 prefixEnd_2745598 := by exact prefixLift 2745598
  have htrace : WordTrace (prefixWord ++ tailWord_2745598) baseStart_2745598 baseEnd_2745598 := by
    simpa [prefixWord, tailWord_2745598, baseEnd_2745598] using wordTrace_append hprefix tailTrace_2745598
  have hstable : (prefixWord ++ tailWord_2745598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745598).length < 2 ^ (prefixWord ++ tailWord_2745598).sum := by decide
  have hdescent : baseEnd_2745598 < baseStart_2745598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745608 : List Nat := [2, 1, 3, 2, 4, 2, 1, 2, 1, 2, 3]
def baseStart_2745608 : Nat := 118140960795 + 2745608 * 2 ^ 59
def prefixEnd_2745608 : Nat := 4983230072969 + 3 ^ 40 * 2745608 * 2
def baseEnd_2745608 : Nat := 1409816592829799029773185

theorem tailTrace_2745608 : CollatzResearch.WordTrace tailWord_2745608 prefixEnd_2745608 1409816592829799029773185 := by
  unfold tailWord_2745608
  simp only [CollatzResearch.WordTrace]
  refine ⟨50070275318569301679738739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66760367091425735572984985 50070275318569301679738739)
  ·
    refine ⟨75105412977853952519608109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50070275318569301679738739 75105412977853952519608109)
    ·
      refine ⟨28164529866695232194853041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75105412977853952519608109 28164529866695232194853041)
      ·
        refine ⟨21123397400021424146139781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28164529866695232194853041 21123397400021424146139781)
        ·
          refine ⟨3960637012504017027401209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21123397400021424146139781 3960637012504017027401209)
          ·
            refine ⟨2970477759378012770550907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3960637012504017027401209 2970477759378012770550907)
            ·
              refine ⟨4455716639067019155826361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2970477759378012770550907 4455716639067019155826361)
              ·
                refine ⟨3341787479300264366869771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4455716639067019155826361 3341787479300264366869771)
                ·
                  refine ⟨5012681218950396550304657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3341787479300264366869771 5012681218950396550304657)
                  ·
                    refine ⟨3759510914212797412728493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5012681218950396550304657 3759510914212797412728493)
                    ·
                      refine ⟨1409816592829799029773185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3759510914212797412728493 1409816592829799029773185)
                      ·
                        rfl

theorem cell23_2745608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_2745608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745608 prefixEnd_2745608 := by exact prefixLift 2745608
  have htrace : WordTrace (prefixWord ++ tailWord_2745608) baseStart_2745608 baseEnd_2745608 := by
    simpa [prefixWord, tailWord_2745608, baseEnd_2745608] using wordTrace_append hprefix tailTrace_2745608
  have hstable : (prefixWord ++ tailWord_2745608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745608).length < 2 ^ (prefixWord ++ tailWord_2745608).sum := by decide
  have hdescent : baseEnd_2745608 < baseStart_2745608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745618 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2745618 : Nat := 118140960795 + 2745618 * 2 ^ 59
def prefixEnd_2745618 : Nat := 4983230072969 + 3 ^ 40 * 2745618 * 2
def baseEnd_2745618 : Nat := 1409821727636343990648139

theorem tailTrace_2745618 : CollatzResearch.WordTrace tailWord_2745618 prefixEnd_2745618 1409821727636343990648139 := by
  unfold tailWord_2745618
  simp only [CollatzResearch.WordTrace]
  refine ⟨25035228841775593766835377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66760610244734916711561005 25035228841775593766835377)
  ·
    refine ⟨18776421631331695325126533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25035228841775593766835377 18776421631331695325126533)
    ·
      refine ⟨3520579055874692873461225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18776421631331695325126533 3520579055874692873461225)
      ·
        refine ⟨2640434291906019655095919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3520579055874692873461225 2640434291906019655095919)
        ·
          refine ⟨3960651437859029482643879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2640434291906019655095919 3960651437859029482643879)
          ·
            refine ⟨5940977156788544223965819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3960651437859029482643879 5940977156788544223965819)
            ·
              refine ⟨8911465735182816335948729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5940977156788544223965819 8911465735182816335948729)
              ·
                refine ⟨6683599301387112251961547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8911465735182816335948729 6683599301387112251961547)
                ·
                  refine ⟨10025398952080668377942321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6683599301387112251961547 10025398952080668377942321)
                  ·
                    refine ⟨7519049214060501283456741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10025398952080668377942321 7519049214060501283456741)
                    ·
                      refine ⟨1409821727636343990648139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7519049214060501283456741 1409821727636343990648139)
                      ·
                        rfl

theorem cell23_2745618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2745618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745618 prefixEnd_2745618 := by exact prefixLift 2745618
  have htrace : WordTrace (prefixWord ++ tailWord_2745618) baseStart_2745618 baseEnd_2745618 := by
    simpa [prefixWord, tailWord_2745618, baseEnd_2745618] using wordTrace_append hprefix tailTrace_2745618
  have hstable : (prefixWord ++ tailWord_2745618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745618).length < 2 ^ (prefixWord ++ tailWord_2745618).sum := by decide
  have hdescent : baseEnd_2745618 < baseStart_2745618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745644 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 5, 4, 2]
def baseStart_2745644 : Nat := 118140960795 + 2745644 * 2 ^ 59
def prefixEnd_2745644 : Nat := 4983230072969 + 3 ^ 40 * 2745644 * 2
def baseEnd_2745644 : Nat := 1409835078133360888923019

theorem tailTrace_2745644 : CollatzResearch.WordTrace tailWord_2745644 prefixEnd_2745644 1409835078133360888923019 := by
  unfold tailWord_2745644
  simp only [CollatzResearch.WordTrace]
  refine ⟨50070931832504090753893993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66761242443338787671858657 50070931832504090753893993)
  ·
    refine ⟨37553198874378068065420495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50070931832504090753893993 37553198874378068065420495)
    ·
      refine ⟨56329798311567102098130743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37553198874378068065420495 56329798311567102098130743)
      ·
        refine ⟨84494697467350653147196115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56329798311567102098130743 84494697467350653147196115)
        ·
          refine ⟨126742046201025979720794173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84494697467350653147196115 126742046201025979720794173)
          ·
            refine ⟨47528267325384742395297815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126742046201025979720794173 47528267325384742395297815)
            ·
              refine ⟨71292400988077113592946723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47528267325384742395297815 71292400988077113592946723)
              ·
                refine ⟨106938601482115670389420085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71292400988077113592946723 106938601482115670389420085)
                ·
                  refine ⟨10025493888948344099008133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106938601482115670389420085 10025493888948344099008133)
                  ·
                    refine ⟨1879780104177814518564025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10025493888948344099008133 1879780104177814518564025)
                    ·
                      refine ⟨1409835078133360888923019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1879780104177814518564025 1409835078133360888923019)
                      ·
                        rfl

theorem cell23_2745644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 4, 2].length) (baseStart_2745644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745644 prefixEnd_2745644 := by exact prefixLift 2745644
  have htrace : WordTrace (prefixWord ++ tailWord_2745644) baseStart_2745644 baseEnd_2745644 := by
    simpa [prefixWord, tailWord_2745644, baseEnd_2745644] using wordTrace_append hprefix tailTrace_2745644
  have hstable : (prefixWord ++ tailWord_2745644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745644).length < 2 ^ (prefixWord ++ tailWord_2745644).sum := by decide
  have hdescent : baseEnd_2745644 < baseStart_2745644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745758 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2745758 : Nat := 118140960795 + 2745758 * 2 ^ 59
def prefixEnd_2745758 : Nat := 4983230072969 + 3 ^ 40 * 2745758 * 2
def baseEnd_2745758 : Nat := 1409893614927973442897495

theorem tailTrace_2745758 : CollatzResearch.WordTrace tailWord_2745758 prefixEnd_2745758 1409893614927973442897495 := by
  unfold tailWord_2745758
  simp only [CollatzResearch.WordTrace]
  refine ⟨12518252698324397372179741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66764014391063452651625285 12518252698324397372179741)
  ·
    refine ⟨4694344761871649014567403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12518252698324397372179741 4694344761871649014567403)
    ·
      refine ⟨7041517142807473521851105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4694344761871649014567403 7041517142807473521851105)
      ·
        refine ⟨5281137857105605141388329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7041517142807473521851105 5281137857105605141388329)
        ·
          refine ⟨3960853392829203856041247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5281137857105605141388329 3960853392829203856041247)
          ·
            refine ⟨5941280089243805784061871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3960853392829203856041247 5941280089243805784061871)
            ·
              refine ⟨8911920133865708676092807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5941280089243805784061871 8911920133865708676092807)
              ·
                refine ⟨13367880200798563014139211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8911920133865708676092807 13367880200798563014139211)
                ·
                  refine ⟨20051820301197844521208817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13367880200798563014139211 20051820301197844521208817)
                  ·
                    refine ⟨15038865225898383390906613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20051820301197844521208817 15038865225898383390906613)
                    ·
                      refine ⟨1409893614927973442897495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15038865225898383390906613 1409893614927973442897495)
                      ·
                        rfl

theorem cell23_2745758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2745758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745758 prefixEnd_2745758 := by exact prefixLift 2745758
  have htrace : WordTrace (prefixWord ++ tailWord_2745758) baseStart_2745758 baseEnd_2745758 := by
    simpa [prefixWord, tailWord_2745758, baseEnd_2745758] using wordTrace_append hprefix tailTrace_2745758
  have hstable : (prefixWord ++ tailWord_2745758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745758).length < 2 ^ (prefixWord ++ tailWord_2745758).sum := by decide
  have hdescent : baseEnd_2745758 < baseStart_2745758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745784 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 2, 5, 3]
def baseStart_2745784 : Nat := 118140960795 + 2745784 * 2 ^ 59
def prefixEnd_2745784 : Nat := 4983230072969 + 3 ^ 40 * 2745784 * 2
def baseEnd_2745784 : Nat := 1409906965424990341172375

theorem tailTrace_2745784 : CollatzResearch.WordTrace tailWord_2745784 prefixEnd_2745784 1409906965424990341172375 := by
  unfold tailWord_2745784
  simp only [CollatzResearch.WordTrace]
  refine ⟨50073484942250492708942203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66764646589667323611922937 50073484942250492708942203)
  ·
    refine ⟨75110227413375739063413305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50073484942250492708942203 75110227413375739063413305)
    ·
      refine ⟨56332670560031804297559979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75110227413375739063413305 56332670560031804297559979)
      ·
        refine ⟨84499005840047706446339969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56332670560031804297559979 84499005840047706446339969)
        ·
          refine ⟨63374254380035779834754977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84499005840047706446339969 63374254380035779834754977)
          ·
            refine ⟨47530690785026834876066233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63374254380035779834754977 47530690785026834876066233)
            ·
              refine ⟨35648018088770126157049675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47530690785026834876066233 35648018088770126157049675)
              ·
                refine ⟨53472027133155189235574513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35648018088770126157049675 53472027133155189235574513)
                ·
                  refine ⟨40104020349866391926680885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53472027133155189235574513 40104020349866391926680885)
                  ·
                    refine ⟨3759751907799974243126333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40104020349866391926680885 3759751907799974243126333)
                    ·
                      refine ⟨1409906965424990341172375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3759751907799974243126333 1409906965424990341172375)
                      ·
                        rfl

theorem cell23_2745784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_2745784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745784 prefixEnd_2745784 := by exact prefixLift 2745784
  have htrace : WordTrace (prefixWord ++ tailWord_2745784) baseStart_2745784 baseEnd_2745784 := by
    simpa [prefixWord, tailWord_2745784, baseEnd_2745784] using wordTrace_append hprefix tailTrace_2745784
  have hstable : (prefixWord ++ tailWord_2745784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745784).length < 2 ^ (prefixWord ++ tailWord_2745784).sum := by decide
  have hdescent : baseEnd_2745784 < baseStart_2745784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745821 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2745821 : Nat := 118140960795 + 2745821 * 2 ^ 59
def prefixEnd_2745821 : Nat := 4983230072969 + 3 ^ 40 * 2745821 * 2
def baseEnd_2745821 : Nat := 469975321403068898803235

theorem tailTrace_2745821 : CollatzResearch.WordTrace tailWord_2745821 prefixEnd_2745821 469975321403068898803235 := by
  unfold tailWord_2745821
  simp only [CollatzResearch.WordTrace]
  refine ⟨100148319385366940736981317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66765546256911293824654211 100148319385366940736981317)
  ·
    refine ⟨18777809884756301388183997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100148319385366940736981317 18777809884756301388183997)
    ·
      refine ⟨7041678706783613020568999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18777809884756301388183997 7041678706783613020568999)
      ·
        refine ⟨10562518060175419530853499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7041678706783613020568999 10562518060175419530853499)
        ·
          refine ⟨15843777090263129296280249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10562518060175419530853499 15843777090263129296280249)
          ·
            refine ⟨11882832817697346972210187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15843777090263129296280249 11882832817697346972210187)
            ·
              refine ⟨17824249226546020458315281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11882832817697346972210187 17824249226546020458315281)
              ·
                refine ⟨13368186919909515343736461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17824249226546020458315281 13368186919909515343736461)
                ·
                  refine ⟨5013070094966068253901173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13368186919909515343736461 5013070094966068253901173)
                  ·
                    refine ⟨469975321403068898803235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5013070094966068253901173 469975321403068898803235)
                    ·
                      rfl

theorem cell23_2745821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2745821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745821 prefixEnd_2745821 := by exact prefixLift 2745821
  have htrace : WordTrace (prefixWord ++ tailWord_2745821) baseStart_2745821 baseEnd_2745821 := by
    simpa [prefixWord, tailWord_2745821, baseEnd_2745821] using wordTrace_append hprefix tailTrace_2745821
  have hstable : (prefixWord ++ tailWord_2745821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745821).length < 2 ^ (prefixWord ++ tailWord_2745821).sum := by decide
  have hdescent : baseEnd_2745821 < baseStart_2745821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745841 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 3, 1, 4]
def baseStart_2745841 : Nat := 118140960795 + 2745841 * 2 ^ 59
def prefixEnd_2745841 : Nat := 4983230072969 + 3 ^ 40 * 2745841 * 2
def baseEnd_2745841 : Nat := 1409936233822296618159613

theorem tailTrace_2745841 : CollatzResearch.WordTrace tailWord_2745841 prefixEnd_2745841 1409936233822296618159613 := by
  unfold tailWord_2745841
  simp only [CollatzResearch.WordTrace]
  refine ⟨100149048845294484152709377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66766032563529656101806251 100149048845294484152709377)
  ·
    refine ⟨75111786633970863114532033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100149048845294484152709377 75111786633970863114532033)
    ·
      refine ⟨56333839975478147335899025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75111786633970863114532033 56333839975478147335899025)
      ·
        refine ⟨42250379981608610501924269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56333839975478147335899025 42250379981608610501924269)
        ·
          refine ⟨15843892493103228938221601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42250379981608610501924269 15843892493103228938221601)
          ·
            refine ⟨11882919369827421703666201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15843892493103228938221601 11882919369827421703666201)
            ·
              refine ⟨8912189527370566277749651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11882919369827421703666201 8912189527370566277749651)
              ·
                refine ⟨13368284291055849416624477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8912189527370566277749651 13368284291055849416624477)
                ·
                  refine ⟨5013106609145943531234179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13368284291055849416624477 5013106609145943531234179)
                  ·
                    refine ⟨7519659913718915296851269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5013106609145943531234179 7519659913718915296851269)
                    ·
                      refine ⟨1409936233822296618159613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7519659913718915296851269 1409936233822296618159613)
                      ·
                        rfl

theorem cell23_2745841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_2745841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745841 prefixEnd_2745841 := by exact prefixLift 2745841
  have htrace : WordTrace (prefixWord ++ tailWord_2745841) baseStart_2745841 baseEnd_2745841 := by
    simpa [prefixWord, tailWord_2745841, baseEnd_2745841] using wordTrace_append hprefix tailTrace_2745841
  have hstable : (prefixWord ++ tailWord_2745841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745841).length < 2 ^ (prefixWord ++ tailWord_2745841).sum := by decide
  have hdescent : baseEnd_2745841 < baseStart_2745841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745845 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_2745845 : Nat := 118140960795 + 2745845 * 2 ^ 59
def prefixEnd_2745845 : Nat := 4983230072969 + 3 ^ 40 * 2745845 * 2
def baseEnd_2745845 : Nat := 1409938287744914602509595

theorem tailTrace_2745845 : CollatzResearch.WordTrace tailWord_2745845 prefixEnd_2745845 1409938287744914602509595 := by
  unfold tailWord_2745845
  simp only [CollatzResearch.WordTrace]
  refine ⟨100149194737279992835854989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66766129824853328557236659 100149194737279992835854989)
  ·
    refine ⟨37555948026479997313445621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100149194737279992835854989 37555948026479997313445621)
    ·
      refine ⟨3520870127482499748135527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37555948026479997313445621 3520870127482499748135527)
      ·
        refine ⟨5281305191223749622203291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3520870127482499748135527 5281305191223749622203291)
        ·
          refine ⟨7921957786835624433304937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5281305191223749622203291 7921957786835624433304937)
          ·
            refine ⟨5941468340126718324978703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7921957786835624433304937 5941468340126718324978703)
            ·
              refine ⟨8912202510190077487468055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5941468340126718324978703 8912202510190077487468055)
              ·
                refine ⟨13368303765285116231202083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8912202510190077487468055 13368303765285116231202083)
                ·
                  refine ⟨20052455647927674346803125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13368303765285116231202083 20052455647927674346803125)
                  ·
                    refine ⟨1879917716993219470012793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20052455647927674346803125 1879917716993219470012793)
                    ·
                      refine ⟨1409938287744914602509595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1879917716993219470012793 1409938287744914602509595)
                      ·
                        rfl

theorem cell23_2745845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_2745845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745845 prefixEnd_2745845 := by exact prefixLift 2745845
  have htrace : WordTrace (prefixWord ++ tailWord_2745845) baseStart_2745845 baseEnd_2745845 := by
    simpa [prefixWord, tailWord_2745845, baseEnd_2745845] using wordTrace_append hprefix tailTrace_2745845
  have hstable : (prefixWord ++ tailWord_2745845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745845).length < 2 ^ (prefixWord ++ tailWord_2745845).sum := by decide
  have hdescent : baseEnd_2745845 < baseStart_2745845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745868 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 4, 4]
def baseStart_2745868 : Nat := 118140960795 + 2745868 * 2 ^ 59
def prefixEnd_2745868 : Nat := 4983230072969 + 3 ^ 40 * 2745868 * 2
def baseEnd_2745868 : Nat := 469983365933322670840663

theorem tailTrace_2745868 : CollatzResearch.WordTrace tailWord_2745868 prefixEnd_2745868 469983365933322670840663 := by
  unfold tailWord_2745868
  simp only [CollatzResearch.WordTrace]
  refine ⟨50075016808098333881971129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66766689077464445175961505 50075016808098333881971129)
  ·
    refine ⟨37556262606073750411478347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50075016808098333881971129 37556262606073750411478347)
    ·
      refine ⟨56334393909110625617217521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37556262606073750411478347 56334393909110625617217521)
      ·
        refine ⟨42250795431832969212913141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56334393909110625617217521 42250795431832969212913141)
        ·
          refine ⟨3961012071734340863710607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42250795431832969212913141 3961012071734340863710607)
          ·
            refine ⟨5941518107601511295565911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3961012071734340863710607 5941518107601511295565911)
            ·
              refine ⟨8912277161402266943348867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5941518107601511295565911 8912277161402266943348867)
              ·
                refine ⟨13368415742103400415023301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8912277161402266943348867 13368415742103400415023301)
                ·
                  refine ⟨2506577951644387577816869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13368415742103400415023301 2506577951644387577816869)
                  ·
                    refine ⟨469983365933322670840663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2506577951644387577816869 469983365933322670840663)
                    ·
                      rfl

theorem cell23_2745868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_2745868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745868 prefixEnd_2745868 := by exact prefixLift 2745868
  have htrace : WordTrace (prefixWord ++ tailWord_2745868) baseStart_2745868 baseEnd_2745868 := by
    simpa [prefixWord, tailWord_2745868, baseEnd_2745868] using wordTrace_append hprefix tailTrace_2745868
  have hstable : (prefixWord ++ tailWord_2745868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745868).length < 2 ^ (prefixWord ++ tailWord_2745868).sum := by decide
  have hdescent : baseEnd_2745868 < baseStart_2745868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745869 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_2745869 : Nat := 118140960795 + 2745869 * 2 ^ 59
def prefixEnd_2745869 : Nat := 4983230072969 + 3 ^ 40 * 2745869 * 2
def baseEnd_2745869 : Nat := 1409950611280622508609485

theorem tailTrace_2745869 : CollatzResearch.WordTrace tailWord_2745869 prefixEnd_2745869 1409950611280622508609485 := by
  unfold tailWord_2745869
  simp only [CollatzResearch.WordTrace]
  refine ⟨100150070089193044934728661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66766713392795363289819107 100150070089193044934728661)
  ·
    refine ⟨2347267267715461990657703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 100150070089193044934728661 2347267267715461990657703)
    ·
      refine ⟨3520900901573192985986555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2347267267715461990657703 3520900901573192985986555)
      ·
        refine ⟨5281351352359789478979833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3520900901573192985986555 5281351352359789478979833)
        ·
          refine ⟨3961013514269842109234875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5281351352359789478979833 3961013514269842109234875)
          ·
            refine ⟨5941520271404763163852313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3961013514269842109234875 5941520271404763163852313)
            ·
              refine ⟨4456140203553572372889235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5941520271404763163852313 4456140203553572372889235)
              ·
                refine ⟨6684210305330358559333853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4456140203553572372889235 6684210305330358559333853)
                ·
                  refine ⟨2506578864498884459750195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6684210305330358559333853 2506578864498884459750195)
                  ·
                    refine ⟨3759868296748326689625293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2506578864498884459750195 3759868296748326689625293)
                    ·
                      refine ⟨1409950611280622508609485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3759868296748326689625293 1409950611280622508609485)
                      ·
                        rfl

theorem cell23_2745869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_2745869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745869 prefixEnd_2745869 := by exact prefixLift 2745869
  have htrace : WordTrace (prefixWord ++ tailWord_2745869) baseStart_2745869 baseEnd_2745869 := by
    simpa [prefixWord, tailWord_2745869, baseEnd_2745869] using wordTrace_append hprefix tailTrace_2745869
  have hstable : (prefixWord ++ tailWord_2745869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745869).length < 2 ^ (prefixWord ++ tailWord_2745869).sum := by decide
  have hdescent : baseEnd_2745869 < baseStart_2745869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745875 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 3, 2, 2]
def baseStart_2745875 : Nat := 118140960795 + 2745875 * 2 ^ 59
def prefixEnd_2745875 : Nat := 4983230072969 + 3 ^ 40 * 2745875 * 2
def baseEnd_2745875 : Nat := 1409953692164549485134457

theorem tailTrace_2745875 : CollatzResearch.WordTrace tailWord_2745875 prefixEnd_2745875 1409953692164549485134457 := by
  unfold tailWord_2745875
  simp only [CollatzResearch.WordTrace]
  refine ⟨100150288927171307959447079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66766859284780871972964719 100150288927171307959447079)
  ·
    refine ⟨150225433390756961939170619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100150288927171307959447079 150225433390756961939170619)
    ·
      refine ⟨225338150086135442908755929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150225433390756961939170619 225338150086135442908755929)
      ·
        refine ⟨169003612564601582181566947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225338150086135442908755929 169003612564601582181566947)
        ·
          refine ⟨253505418846902373272350421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169003612564601582181566947 253505418846902373272350421)
          ·
            refine ⟨5941533254224274373570713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 253505418846902373272350421 5941533254224274373570713)
            ·
              refine ⟨4456149940668205780178035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5941533254224274373570713 4456149940668205780178035)
              ·
                refine ⟨6684224911002308670267053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4456149940668205780178035 6684224911002308670267053)
                ·
                  refine ⟨2506584341625865751350145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6684224911002308670267053 2506584341625865751350145)
                  ·
                    refine ⟨1879938256219399313512609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2506584341625865751350145 1879938256219399313512609)
                    ·
                      refine ⟨1409953692164549485134457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1879938256219399313512609 1409953692164549485134457)
                      ·
                        rfl

theorem cell23_2745875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 2, 2].length) (baseStart_2745875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745875 prefixEnd_2745875 := by exact prefixLift 2745875
  have htrace : WordTrace (prefixWord ++ tailWord_2745875) baseStart_2745875 baseEnd_2745875 := by
    simpa [prefixWord, tailWord_2745875, baseEnd_2745875] using wordTrace_append hprefix tailTrace_2745875
  have hstable : (prefixWord ++ tailWord_2745875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745875).length < 2 ^ (prefixWord ++ tailWord_2745875).sum := by decide
  have hdescent : baseEnd_2745875 < baseStart_2745875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745885 : List Nat := [1, 4, 2, 2, 1, 1, 5, 1, 2, 4]
def baseStart_2745885 : Nat := 118140960795 + 2745885 * 2 ^ 59
def prefixEnd_2745885 : Nat := 4983230072969 + 3 ^ 40 * 2745885 * 2
def baseEnd_2745885 : Nat := 469986275657031482003137

theorem tailTrace_2745885 : CollatzResearch.WordTrace tailWord_2745885 prefixEnd_2745885 469986275657031482003137 := by
  unfold tailWord_2745885
  simp only [CollatzResearch.WordTrace]
  refine ⟨100150653657135079667311109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66767102438090053111540739 100150653657135079667311109)
  ·
    refine ⟨18778247560712827437620833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100150653657135079667311109 18778247560712827437620833)
    ·
      refine ⟨14083685670534620578215625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18778247560712827437620833 14083685670534620578215625)
      ·
        refine ⟨10562764252900965433661719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14083685670534620578215625 10562764252900965433661719)
        ·
          refine ⟨15844146379351448150492579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10562764252900965433661719 15844146379351448150492579)
          ·
            refine ⟨23766219569027172225738869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15844146379351448150492579 23766219569027172225738869)
            ·
              refine ⟨2228083084596297396163019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23766219569027172225738869 2228083084596297396163019)
              ·
                refine ⟨3342124626894446094244529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2228083084596297396163019 3342124626894446094244529)
                ·
                  refine ⟨2506593470170834570683397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3342124626894446094244529 2506593470170834570683397)
                  ·
                    refine ⟨469986275657031482003137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2506593470170834570683397 469986275657031482003137)
                    ·
                      rfl

theorem cell23_2745885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_2745885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745885 prefixEnd_2745885 := by exact prefixLift 2745885
  have htrace : WordTrace (prefixWord ++ tailWord_2745885) baseStart_2745885 baseEnd_2745885 := by
    simpa [prefixWord, tailWord_2745885, baseEnd_2745885] using wordTrace_append hprefix tailTrace_2745885
  have hstable : (prefixWord ++ tailWord_2745885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745885).length < 2 ^ (prefixWord ++ tailWord_2745885).sum := by decide
  have hdescent : baseEnd_2745885 < baseStart_2745885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745888 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2745888 : Nat := 118140960795 + 2745888 * 2 ^ 59
def prefixEnd_2745888 : Nat := 4983230072969 + 3 ^ 40 * 2745888 * 2
def baseEnd_2745888 : Nat := 1409960367413057934271897

theorem tailTrace_2745888 : CollatzResearch.WordTrace tailWord_2745888 prefixEnd_2745888 1409960367413057934271897 := by
  unfold tailWord_2745888
  simp only [CollatzResearch.WordTrace]
  refine ⟨50075381538062105589835159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66767175384082807453113545 50075381538062105589835159)
  ·
    refine ⟨75113072307093158384752739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50075381538062105589835159 75113072307093158384752739)
    ·
      refine ⟨112669608460639737577129109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75113072307093158384752739 112669608460639737577129109)
      ·
        refine ⟨5281387896592487698927927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 112669608460639737577129109 5281387896592487698927927)
        ·
          refine ⟨7922081844888731548391891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5281387896592487698927927 7922081844888731548391891)
          ·
            refine ⟨11883122767333097322587837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7922081844888731548391891 11883122767333097322587837)
            ·
              refine ⟨4456171037749911495970439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11883122767333097322587837 4456171037749911495970439)
              ·
                refine ⟨6684256556624867243955659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4456171037749911495970439 6684256556624867243955659)
                ·
                  refine ⟨10026384834937300865933489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6684256556624867243955659 10026384834937300865933489)
                  ·
                    refine ⟨7519788626202975649450117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10026384834937300865933489 7519788626202975649450117)
                    ·
                      refine ⟨1409960367413057934271897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7519788626202975649450117 1409960367413057934271897)
                      ·
                        rfl

theorem cell23_2745888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2745888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745888 prefixEnd_2745888 := by exact prefixLift 2745888
  have htrace : WordTrace (prefixWord ++ tailWord_2745888) baseStart_2745888 baseEnd_2745888 := by
    simpa [prefixWord, tailWord_2745888, baseEnd_2745888] using wordTrace_append hprefix tailTrace_2745888
  have hstable : (prefixWord ++ tailWord_2745888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745888).length < 2 ^ (prefixWord ++ tailWord_2745888).sum := by decide
  have hdescent : baseEnd_2745888 < baseStart_2745888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745909 : List Nat := [1, 3, 3, 1, 1, 5, 1, 3, 1, 2, 2]
def baseStart_2745909 : Nat := 118140960795 + 2745909 * 2 ^ 59
def prefixEnd_2745909 : Nat := 4983230072969 + 3 ^ 40 * 2745909 * 2
def baseEnd_2745909 : Nat := 1409971150506802352109301

theorem tailTrace_2745909 : CollatzResearch.WordTrace tailWord_2745909 prefixEnd_2745909 1409971150506802352109301 := by
  unfold tailWord_2745909
  simp only [CollatzResearch.WordTrace]
  refine ⟨100151529009048131766184781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66767686006032087844123187 100151529009048131766184781)
  ·
    refine ⟨37556823378393049412319293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100151529009048131766184781 37556823378393049412319293)
    ·
      refine ⟨14083808766897393529619735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37556823378393049412319293 14083808766897393529619735)
      ·
        refine ⟨21125713150346090294429603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14083808766897393529619735 21125713150346090294429603)
        ·
          refine ⟨31688569725519135441644405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21125713150346090294429603 31688569725519135441644405)
          ·
            refine ⟨2970803411767418947654163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31688569725519135441644405 2970803411767418947654163)
            ·
              refine ⟨4456205117651128421481245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2970803411767418947654163 4456205117651128421481245)
              ·
                refine ⟨1671076919119173158055467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4456205117651128421481245 1671076919119173158055467)
                ·
                  refine ⟨2506615378678759737083201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1671076919119173158055467 2506615378678759737083201)
                  ·
                    refine ⟨1879961534009069802812401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2506615378678759737083201 1879961534009069802812401)
                    ·
                      refine ⟨1409971150506802352109301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1879961534009069802812401 1409971150506802352109301)
                      ·
                        rfl

theorem cell23_2745909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_2745909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745909 prefixEnd_2745909 := by exact prefixLift 2745909
  have htrace : WordTrace (prefixWord ++ tailWord_2745909) baseStart_2745909 baseEnd_2745909 := by
    simpa [prefixWord, tailWord_2745909, baseEnd_2745909] using wordTrace_append hprefix tailTrace_2745909
  have hstable : (prefixWord ++ tailWord_2745909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745909).length < 2 ^ (prefixWord ++ tailWord_2745909).sum := by decide
  have hdescent : baseEnd_2745909 < baseStart_2745909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745921 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2745921 : Nat := 118140960795 + 2745921 * 2 ^ 59
def prefixEnd_2745921 : Nat := 4983230072969 + 3 ^ 40 * 2745921 * 2
def baseEnd_2745921 : Nat := 1409977312274656305159245

theorem tailTrace_2745921 : CollatzResearch.WordTrace tailWord_2745921 prefixEnd_2745921 1409977312274656305159245 := by
  unfold tailWord_2745921
  simp only [CollatzResearch.WordTrace]
  refine ⟨100151966685004657815621617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66767977790003105210414411 100151966685004657815621617)
  ·
    refine ⟨75113975013753493361716213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100151966685004657815621617 75113975013753493361716213)
    ·
      refine ⟨7041935157539390002660895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75113975013753493361716213 7041935157539390002660895)
      ·
        refine ⟨10562902736309085003991343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7041935157539390002660895 10562902736309085003991343)
        ·
          refine ⟨15844354104463627505987015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10562902736309085003991343 15844354104463627505987015)
          ·
            refine ⟨23766531156695441258980523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15844354104463627505987015 23766531156695441258980523)
            ·
              refine ⟨35649796735043161888470785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23766531156695441258980523 35649796735043161888470785)
              ·
                refine ⟨26737347551282371416353089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35649796735043161888470785 26737347551282371416353089)
                ·
                  refine ⟨20053010663461778562264817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26737347551282371416353089 20053010663461778562264817)
                  ·
                    refine ⟨15039757997596333921698613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20053010663461778562264817 15039757997596333921698613)
                    ·
                      refine ⟨1409977312274656305159245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15039757997596333921698613 1409977312274656305159245)
                      ·
                        rfl

theorem cell23_2745921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2745921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745921 prefixEnd_2745921 := by exact prefixLift 2745921
  have htrace : WordTrace (prefixWord ++ tailWord_2745921) baseStart_2745921 baseEnd_2745921 := by
    simpa [prefixWord, tailWord_2745921, baseEnd_2745921] using wordTrace_append hprefix tailTrace_2745921
  have hstable : (prefixWord ++ tailWord_2745921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745921).length < 2 ^ (prefixWord ++ tailWord_2745921).sum := by decide
  have hdescent : baseEnd_2745921 < baseStart_2745921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745926 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_2745926 : Nat := 118140960795 + 2745926 * 2 ^ 59
def prefixEnd_2745926 : Nat := 4983230072969 + 3 ^ 40 * 2745926 * 2
def baseEnd_2745926 : Nat := 1409979879677928785596723

theorem tailTrace_2745926 : CollatzResearch.WordTrace tailWord_2745926 prefixEnd_2745926 1409979879677928785596723 := by
  unfold tailWord_2745926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3129754657812079489673551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66768099366657695779702421 3129754657812079489673551)
  ·
    refine ⟨4694631986718119234510327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3129754657812079489673551 4694631986718119234510327)
    ·
      refine ⟨7041947980077178851765491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4694631986718119234510327 7041947980077178851765491)
      ·
        refine ⟨10562921970115768277648237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7041947980077178851765491 10562921970115768277648237)
        ·
          refine ⟨3961095738793413104118089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10562921970115768277648237 3961095738793413104118089)
          ·
            refine ⟨2970821804095059828088567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3961095738793413104118089 2970821804095059828088567)
            ·
              refine ⟨4456232706142589742132851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2970821804095059828088567 4456232706142589742132851)
              ·
                refine ⟨6684349059213884613199277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4456232706142589742132851 6684349059213884613199277)
                ·
                  refine ⟨2506630897205206729949729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6684349059213884613199277 2506630897205206729949729)
                  ·
                    refine ⟨1879973172903905047462297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2506630897205206729949729 1879973172903905047462297)
                    ·
                      refine ⟨1409979879677928785596723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1879973172903905047462297 1409979879677928785596723)
                      ·
                        rfl

theorem cell23_2745926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_2745926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745926 prefixEnd_2745926 := by exact prefixLift 2745926
  have htrace : WordTrace (prefixWord ++ tailWord_2745926) baseStart_2745926 baseEnd_2745926 := by
    simpa [prefixWord, tailWord_2745926, baseEnd_2745926] using wordTrace_append hprefix tailTrace_2745926
  have hstable : (prefixWord ++ tailWord_2745926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745926).length < 2 ^ (prefixWord ++ tailWord_2745926).sum := by decide
  have hdescent : baseEnd_2745926 < baseStart_2745926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745998 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3]
def baseStart_2745998 : Nat := 118140960795 + 2745998 * 2 ^ 59
def prefixEnd_2745998 : Nat := 4983230072969 + 3 ^ 40 * 2745998 * 2
def baseEnd_2745998 : Nat := 1410016850285052503896391

theorem tailTrace_2745998 : CollatzResearch.WordTrace tailWord_2745998 prefixEnd_2745998 1410016850285052503896391 := by
  unfold tailWord_2745998
  simp only [CollatzResearch.WordTrace]
  refine ⟨12519346888215712495771831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66769850070483799977449765 12519346888215712495771831)
  ·
    refine ⟨18779020332323568743657747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12519346888215712495771831 18779020332323568743657747)
    ·
      refine ⟨28168530498485353115486621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18779020332323568743657747 28168530498485353115486621)
      ·
        refine ⟨10563198936932007418307483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28168530498485353115486621 10563198936932007418307483)
        ·
          refine ⟨15844798405398011127461225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10563198936932007418307483 15844798405398011127461225)
          ·
            refine ⟨11883598804048508345595919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15844798405398011127461225 11883598804048508345595919)
            ·
              refine ⟨17825398206072762518393879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11883598804048508345595919 17825398206072762518393879)
              ·
                refine ⟨26738097309109143777590819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17825398206072762518393879 26738097309109143777590819)
                ·
                  refine ⟨40107145963663715666386229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26738097309109143777590819 40107145963663715666386229)
                  ·
                    refine ⟨3760044934093473343723709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40107145963663715666386229 3760044934093473343723709)
                    ·
                      refine ⟨1410016850285052503896391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3760044934093473343723709 1410016850285052503896391)
                      ·
                        rfl

theorem cell23_2745998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_2745998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2745998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2745998 prefixEnd_2745998 := by exact prefixLift 2745998
  have htrace : WordTrace (prefixWord ++ tailWord_2745998) baseStart_2745998 baseEnd_2745998 := by
    simpa [prefixWord, tailWord_2745998, baseEnd_2745998] using wordTrace_append hprefix tailTrace_2745998
  have hstable : (prefixWord ++ tailWord_2745998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745998).length < 2 ^ (prefixWord ++ tailWord_2745998).sum := by decide
  have hdescent : baseEnd_2745998 < baseStart_2745998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746041 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2746041 : Nat := 118140960795 + 2746041 * 2 ^ 59
def prefixEnd_2746041 : Nat := 4983230072969 + 3 ^ 40 * 2746041 * 2
def baseEnd_2746041 : Nat := 1410038929953195835658693

theorem tailTrace_2746041 : CollatzResearch.WordTrace tailWord_2746041 prefixEnd_2746041 1410038929953195835658693 := by
  unfold tailWord_2746041
  simp only [CollatzResearch.WordTrace]
  refine ⟨100156343444569918309989977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66770895629713278873326651 100156343444569918309989977)
  ·
    refine ⟨75117257583427438732492483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100156343444569918309989977 75117257583427438732492483)
    ·
      refine ⟨112675886375141158098738725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75117257583427438732492483 112675886375141158098738725)
      ·
        refine ⟨21126728695338967143513511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112675886375141158098738725 21126728695338967143513511)
        ·
          refine ⟨31690093043008450715270267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21126728695338967143513511 31690093043008450715270267)
          ·
            refine ⟨47535139564512676072905401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31690093043008450715270267 47535139564512676072905401)
            ·
              refine ⟨35651354673384507054679051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47535139564512676072905401 35651354673384507054679051)
              ·
                refine ⟨53477032010076760582018577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35651354673384507054679051 53477032010076760582018577)
                ·
                  refine ⟨40107774007557570436513933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53477032010076760582018577 40107774007557570436513933)
                  ·
                    refine ⟨15040415252834088913692725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40107774007557570436513933 15040415252834088913692725)
                    ·
                      refine ⟨1410038929953195835658693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15040415252834088913692725 1410038929953195835658693)
                      ·
                        rfl

theorem cell23_2746041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2746041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746041 prefixEnd_2746041 := by exact prefixLift 2746041
  have htrace : WordTrace (prefixWord ++ tailWord_2746041) baseStart_2746041 baseEnd_2746041 := by
    simpa [prefixWord, tailWord_2746041, baseEnd_2746041] using wordTrace_append hprefix tailTrace_2746041
  have hstable : (prefixWord ++ tailWord_2746041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746041).length < 2 ^ (prefixWord ++ tailWord_2746041).sum := by decide
  have hdescent : baseEnd_2746041 < baseStart_2746041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746050 : List Nat := [3, 5, 1, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_2746050 : Nat := 118140960795 + 2746050 * 2 ^ 59
def prefixEnd_2746050 : Nat := 4983230072969 + 3 ^ 40 * 2746050 * 2
def baseEnd_2746050 : Nat := 1410043551279086300446153

theorem tailTrace_2746050 : CollatzResearch.WordTrace tailWord_2746050 prefixEnd_2746050 1410043551279086300446153 := by
  unfold tailWord_2746050
  simp only [CollatzResearch.WordTrace]
  refine ⟨25039167925384328211766901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66771114467691541898045069 25039167925384328211766901)
  ·
    refine ⟨2347421993004780769853147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25039167925384328211766901 2347421993004780769853147)
    ·
      refine ⟨3521132989507171154779721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2347421993004780769853147 3521132989507171154779721)
      ·
        refine ⟨2640849742130378366084791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3521132989507171154779721 2640849742130378366084791)
        ·
          refine ⟨3961274613195567549127187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2640849742130378366084791 3961274613195567549127187)
          ·
            refine ⟨5941911919793351323690781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3961274613195567549127187 5941911919793351323690781)
            ·
              refine ⟨2228216969922506746384043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5941911919793351323690781 2228216969922506746384043)
              ·
                refine ⟨3342325454883760119576065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2228216969922506746384043 3342325454883760119576065)
                ·
                  refine ⟨2506744091162820089682049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3342325454883760119576065 2506744091162820089682049)
                  ·
                    refine ⟨1880058068372115067261537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2506744091162820089682049 1880058068372115067261537)
                    ·
                      refine ⟨1410043551279086300446153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1880058068372115067261537 1410043551279086300446153)
                      ·
                        rfl

theorem cell23_2746050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_2746050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746050 prefixEnd_2746050 := by exact prefixLift 2746050
  have htrace : WordTrace (prefixWord ++ tailWord_2746050) baseStart_2746050 baseEnd_2746050 := by
    simpa [prefixWord, tailWord_2746050, baseEnd_2746050] using wordTrace_append hprefix tailTrace_2746050
  have hstable : (prefixWord ++ tailWord_2746050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746050).length < 2 ^ (prefixWord ++ tailWord_2746050).sum := by decide
  have hdescent : baseEnd_2746050 < baseStart_2746050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746108 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 3, 5]
def baseStart_2746108 : Nat := 118140960795 + 2746108 * 2 ^ 59
def prefixEnd_2746108 : Nat := 4983230072969 + 3 ^ 40 * 2746108 * 2
def baseEnd_2746108 : Nat := 470024444385682357840295

theorem tailTrace_2746108 : CollatzResearch.WordTrace tailWord_2746108 prefixEnd_2746108 470024444385682357840295 := by
  unfold tailWord_2746108
  simp only [CollatzResearch.WordTrace]
  refine ⟨50079393567663594376339489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66772524756884792501785985 50079393567663594376339489)
  ·
    refine ⟨37559545175747695782254617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50079393567663594376339489 37559545175747695782254617)
    ·
      refine ⟨28169658881810771836690963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37559545175747695782254617 28169658881810771836690963)
      ·
        refine ⟨42254488322716157755036445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28169658881810771836690963 42254488322716157755036445)
        ·
          refine ⟨15845433121018559158138667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42254488322716157755036445 15845433121018559158138667)
          ·
            refine ⟨23768149681527838737208001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15845433121018559158138667 23768149681527838737208001)
            ·
              refine ⟨17826112261145879052906001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23768149681527838737208001 17826112261145879052906001)
              ·
                refine ⟨13369584195859409289679501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17826112261145879052906001 13369584195859409289679501)
                ·
                  refine ⟨5013594073447278483629813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13369584195859409289679501 5013594073447278483629813)
                  ·
                    refine ⟨470024444385682357840295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5013594073447278483629813 470024444385682357840295)
                    ·
                      rfl

theorem cell23_2746108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_2746108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746108 prefixEnd_2746108 := by exact prefixLift 2746108
  have htrace : WordTrace (prefixWord ++ tailWord_2746108) baseStart_2746108 baseEnd_2746108 := by
    simpa [prefixWord, tailWord_2746108, baseEnd_2746108] using wordTrace_append hprefix tailTrace_2746108
  have hstable : (prefixWord ++ tailWord_2746108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746108).length < 2 ^ (prefixWord ++ tailWord_2746108).sum := by decide
  have hdescent : baseEnd_2746108 < baseStart_2746108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746138 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 3, 6]
def baseStart_2746138 : Nat := 118140960795 + 2746138 * 2 ^ 59
def prefixEnd_2746138 : Nat := 4983230072969 + 3 ^ 40 * 2746138 * 2
def baseEnd_2746138 : Nat := 470029579192227318715249

theorem tailTrace_2746138 : CollatzResearch.WordTrace tailWord_2746138 prefixEnd_2746138 470029579192227318715249 := by
  unfold tailWord_2746138
  simp only [CollatzResearch.WordTrace]
  refine ⟨25039970331304625969067767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66773254216812335917514045 25039970331304625969067767)
  ·
    refine ⟨37559955496956938953601651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25039970331304625969067767 37559955496956938953601651)
    ·
      refine ⟨56339933245435408430402477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37559955496956938953601651 56339933245435408430402477)
      ·
        refine ⟨21127474967038278161400929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56339933245435408430402477 21127474967038278161400929)
        ·
          refine ⟨15845606225278708621050697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21127474967038278161400929 15845606225278708621050697)
          ·
            refine ⟨11884204668959031465788023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15845606225278708621050697 11884204668959031465788023)
            ·
              refine ⟨17826307003438547198682035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11884204668959031465788023 17826307003438547198682035)
              ·
                refine ⟨26739460505157820798023053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17826307003438547198682035 26739460505157820798023053)
                ·
                  refine ⟨10027297689434182799258645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26739460505157820798023053 10027297689434182799258645)
                  ·
                    refine ⟨470029579192227318715249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10027297689434182799258645 470029579192227318715249)
                    ·
                      rfl

theorem cell23_2746138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_2746138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746138 prefixEnd_2746138 := by exact prefixLift 2746138
  have htrace : WordTrace (prefixWord ++ tailWord_2746138) baseStart_2746138 baseEnd_2746138 := by
    simpa [prefixWord, tailWord_2746138, baseEnd_2746138] using wordTrace_append hprefix tailTrace_2746138
  have hstable : (prefixWord ++ tailWord_2746138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746138).length < 2 ^ (prefixWord ++ tailWord_2746138).sum := by decide
  have hdescent : baseEnd_2746138 < baseStart_2746138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746151 : List Nat := [1, 1, 21]
def baseStart_2746151 : Nat := 118140960795 + 2746151 * 2 ^ 59
def prefixEnd_2746151 : Nat := 4983230072969 + 3 ^ 40 * 2746151 * 2
def baseEnd_2746151 : Nat := 214920806710134187667

theorem tailTrace_2746151 : CollatzResearch.WordTrace tailWord_2746151 prefixEnd_2746151 214920806710134187667 := by
  unfold tailWord_2746151
  simp only [CollatzResearch.WordTrace]
  refine ⟨100160355474171407096494307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66773570316114271397662871 100160355474171407096494307)
  ·
    refine ⟨150240533211257110644741461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100160355474171407096494307 150240533211257110644741461)
    ·
      refine ⟨214920806710134187667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 21 150240533211257110644741461 214920806710134187667)
      ·
        rfl

theorem cell23_2746151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 21].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 21].length) (baseStart_2746151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746151 prefixEnd_2746151 := by exact prefixLift 2746151
  have htrace : WordTrace (prefixWord ++ tailWord_2746151) baseStart_2746151 baseEnd_2746151 := by
    simpa [prefixWord, tailWord_2746151, baseEnd_2746151] using wordTrace_append hprefix tailTrace_2746151
  have hstable : (prefixWord ++ tailWord_2746151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746151).length < 2 ^ (prefixWord ++ tailWord_2746151).sum := by decide
  have hdescent : baseEnd_2746151 < baseStart_2746151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746156 : List Nat := [2, 2, 1, 1, 1, 7, 2, 2, 1, 1, 3]
def baseStart_2746156 : Nat := 118140960795 + 2746156 * 2 ^ 59
def prefixEnd_2746156 : Nat := 4983230072969 + 3 ^ 40 * 2746156 * 2
def baseEnd_2746156 : Nat := 1410097980228462885720665

theorem tailTrace_2746156 : CollatzResearch.WordTrace tailWord_2746156 prefixEnd_2746156 1410097980228462885720665 := by
  unfold tailWord_2746156
  simp only [CollatzResearch.WordTrace]
  refine ⟨50080268919576646475213161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66773691892768861966950881 50080268919576646475213161)
  ·
    refine ⟨37560201689682484856409871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50080268919576646475213161 37560201689682484856409871)
    ·
      refine ⟨56340302534523727284614807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37560201689682484856409871 56340302534523727284614807)
      ·
        refine ⟨84510453801785590926922211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56340302534523727284614807 84510453801785590926922211)
        ·
          refine ⟨126765680702678386390383317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84510453801785590926922211 126765680702678386390383317)
          ·
            refine ⟨2971070641469024681024609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 126765680702678386390383317 2971070641469024681024609)
            ·
              refine ⟨2228302981101768510768457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2971070641469024681024609 2228302981101768510768457)
              ·
                refine ⟨1671227235826326383076343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2228302981101768510768457 1671227235826326383076343)
                ·
                  refine ⟨2506840853739489574614515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1671227235826326383076343 2506840853739489574614515)
                  ·
                    refine ⟨3760261280609234361921773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2506840853739489574614515 3760261280609234361921773)
                    ·
                      refine ⟨1410097980228462885720665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3760261280609234361921773 1410097980228462885720665)
                      ·
                        rfl

theorem cell23_2746156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 1, 1, 3].length) (baseStart_2746156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746156 prefixEnd_2746156 := by exact prefixLift 2746156
  have htrace : WordTrace (prefixWord ++ tailWord_2746156) baseStart_2746156 baseEnd_2746156 := by
    simpa [prefixWord, tailWord_2746156, baseEnd_2746156] using wordTrace_append hprefix tailTrace_2746156
  have hstable : (prefixWord ++ tailWord_2746156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746156).length < 2 ^ (prefixWord ++ tailWord_2746156).sum := by decide
  have hdescent : baseEnd_2746156 < baseStart_2746156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746168 : List Nat := [2, 1, 2, 1, 3, 3, 3, 8]
def baseStart_2746168 : Nat := 118140960795 + 2746168 * 2 ^ 59
def prefixEnd_2746168 : Nat := 4983230072969 + 3 ^ 40 * 2746168 * 2
def baseEnd_2746168 : Nat := 52226079333196919954467

theorem tailTrace_2746168 : CollatzResearch.WordTrace tailWord_2746168 prefixEnd_2746168 52226079333196919954467 := by
  unfold tailWord_2746168
  simp only [CollatzResearch.WordTrace]
  refine ⟨50080487757554909499931579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66773983676739879333242105 50080487757554909499931579)
  ·
    refine ⟨75120731636332364249897369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50080487757554909499931579 75120731636332364249897369)
    ·
      refine ⟨56340548727249273187423027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75120731636332364249897369 56340548727249273187423027)
      ·
        refine ⟨84510823090873909781134541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56340548727249273187423027 84510823090873909781134541)
        ·
          refine ⟨31691558659077716167925453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84510823090873909781134541 31691558659077716167925453)
          ·
            refine ⟨11884334497154143562972045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31691558659077716167925453 11884334497154143562972045)
            ·
              refine ⟨4456625436432803836114517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11884334497154143562972045 4456625436432803836114517)
              ·
                refine ⟨52226079333196919954467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4456625436432803836114517 52226079333196919954467)
                ·
                  rfl

theorem cell23_2746168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 8].length) (baseStart_2746168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746168 prefixEnd_2746168 := by exact prefixLift 2746168
  have htrace : WordTrace (prefixWord ++ tailWord_2746168) baseStart_2746168 baseEnd_2746168 := by
    simpa [prefixWord, tailWord_2746168, baseEnd_2746168] using wordTrace_append hprefix tailTrace_2746168
  have hstable : (prefixWord ++ tailWord_2746168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746168).length < 2 ^ (prefixWord ++ tailWord_2746168).sum := by decide
  have hdescent : baseEnd_2746168 < baseStart_2746168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746196 : List Nat := [2, 4, 1, 1, 3, 1, 1, 5, 1, 2, 2]
def baseStart_2746196 : Nat := 118140960795 + 2746196 * 2 ^ 59
def prefixEnd_2746196 : Nat := 4983230072969 + 3 ^ 40 * 2746196 * 2
def baseEnd_2746196 : Nat := 1410118519454642729220481

theorem tailTrace_2746196 : CollatzResearch.WordTrace tailWord_2746196 prefixEnd_2746196 1410118519454642729220481 := by
  unfold tailWord_2746196
  simp only [CollatzResearch.WordTrace]
  refine ⟨50080998379504189890941221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66774664506005586521254961 50080998379504189890941221)
  ·
    refine ⟨9390187196157035604551479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50080998379504189890941221 9390187196157035604551479)
    ·
      refine ⟨14085280794235553406827219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9390187196157035604551479 14085280794235553406827219)
      ·
        refine ⟨21127921191353330110240829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14085280794235553406827219 21127921191353330110240829)
        ·
          refine ⟨7922970446757498791340311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21127921191353330110240829 7922970446757498791340311)
          ·
            refine ⟨11884455670136248187010467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7922970446757498791340311 11884455670136248187010467)
            ·
              refine ⟨17826683505204372280515701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11884455670136248187010467 17826683505204372280515701)
              ·
                refine ⟨1671251578612909901298347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17826683505204372280515701 1671251578612909901298347)
                ·
                  refine ⟨2506877367919364851947521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1671251578612909901298347 2506877367919364851947521)
                  ·
                    refine ⟨1880158025939523638960641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2506877367919364851947521 1880158025939523638960641)
                    ·
                      refine ⟨1410118519454642729220481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1880158025939523638960641 1410118519454642729220481)
                      ·
                        rfl

theorem cell23_2746196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_2746196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746196 prefixEnd_2746196 := by exact prefixLift 2746196
  have htrace : WordTrace (prefixWord ++ tailWord_2746196) baseStart_2746196 baseEnd_2746196 := by
    simpa [prefixWord, tailWord_2746196, baseEnd_2746196] using wordTrace_append hprefix tailTrace_2746196
  have hstable : (prefixWord ++ tailWord_2746196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746196).length < 2 ^ (prefixWord ++ tailWord_2746196).sum := by decide
  have hdescent : baseEnd_2746196 < baseStart_2746196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746269 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 4, 2, 2]
def baseStart_2746269 : Nat := 118140960795 + 2746269 * 2 ^ 59
def prefixEnd_2746269 : Nat := 4983230072969 + 3 ^ 40 * 2746269 * 2
def baseEnd_2746269 : Nat := 1410156003542420943607645

theorem tailTrace_2746269 : CollatzResearch.WordTrace tailWord_2746269 prefixEnd_2746269 1410156003542420943607645 := by
  unfold tailWord_2746269
  simp only [CollatzResearch.WordTrace]
  refine ⟨100164659287743913249289861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66776439525162608832859907 100164659287743913249289861)
  ·
    refine ⟨18780873616451983734241849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100164659287743913249289861 18780873616451983734241849)
    ·
      refine ⟨14085655212338987800681387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18780873616451983734241849 14085655212338987800681387)
      ·
        refine ⟨21128482818508481701022081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14085655212338987800681387 21128482818508481701022081)
        ·
          refine ⟨15846362113881361275766561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21128482818508481701022081 15846362113881361275766561)
          ·
            refine ⟨11884771585411020956824921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15846362113881361275766561 11884771585411020956824921)
            ·
              refine ⟨8913578689058265717618691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11884771585411020956824921 8913578689058265717618691)
              ·
                refine ⟨13370368033587398576428037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8913578689058265717618691 13370368033587398576428037)
                ·
                  refine ⟨2506944006297637233080257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13370368033587398576428037 2506944006297637233080257)
                  ·
                    refine ⟨1880208004723227924810193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2506944006297637233080257 1880208004723227924810193)
                    ·
                      refine ⟨1410156003542420943607645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1880208004723227924810193 1410156003542420943607645)
                      ·
                        rfl

theorem cell23_2746269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_2746269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746269 prefixEnd_2746269 := by exact prefixLift 2746269
  have htrace : WordTrace (prefixWord ++ tailWord_2746269) baseStart_2746269 baseEnd_2746269 := by
    simpa [prefixWord, tailWord_2746269, baseEnd_2746269] using wordTrace_append hprefix tailTrace_2746269
  have hstable : (prefixWord ++ tailWord_2746269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746269).length < 2 ^ (prefixWord ++ tailWord_2746269).sum := by decide
  have hdescent : baseEnd_2746269 < baseStart_2746269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746280 : List Nat := [2, 1, 6, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_2746280 : Nat := 118140960795 + 2746280 * 2 ^ 59
def prefixEnd_2746280 : Nat := 4983230072969 + 3 ^ 40 * 2746280 * 2
def baseEnd_2746280 : Nat := 1410161651829620400570095

theorem tailTrace_2746280 : CollatzResearch.WordTrace tailWord_2746280 prefixEnd_2746280 1410161651829620400570095 := by
  unfold tailWord_2746280
  simp only [CollatzResearch.WordTrace]
  refine ⟨50082530245352031063970147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66776706993802708085293529 50082530245352031063970147)
  ·
    refine ⟨75123795368028046595955221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50082530245352031063970147 75123795368028046595955221)
    ·
      refine ⟨3521427907876314684185401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 75123795368028046595955221 3521427907876314684185401)
      ·
        refine ⟨2641070930907236013139051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3521427907876314684185401 2641070930907236013139051)
        ·
          refine ⟨3961606396360854019708577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2641070930907236013139051 3961606396360854019708577)
          ·
            refine ⟨2971204797270640514781433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3961606396360854019708577 2971204797270640514781433)
            ·
              refine ⟨2228403597952980386086075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2971204797270640514781433 2228403597952980386086075)
              ·
                refine ⟨3342605396929470579129113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2228403597952980386086075 3342605396929470579129113)
                ·
                  refine ⟨2506954047697102934346835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3342605396929470579129113 2506954047697102934346835)
                  ·
                    refine ⟨3760431071545654401520253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2506954047697102934346835 3760431071545654401520253)
                    ·
                      refine ⟨1410161651829620400570095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3760431071545654401520253 1410161651829620400570095)
                      ·
                        rfl

theorem cell23_2746280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_2746280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746280 prefixEnd_2746280 := by exact prefixLift 2746280
  have htrace : WordTrace (prefixWord ++ tailWord_2746280) baseStart_2746280 baseEnd_2746280 := by
    simpa [prefixWord, tailWord_2746280, baseEnd_2746280] using wordTrace_append hprefix tailTrace_2746280
  have hstable : (prefixWord ++ tailWord_2746280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746280).length < 2 ^ (prefixWord ++ tailWord_2746280).sum := by decide
  have hdescent : baseEnd_2746280 < baseStart_2746280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746326 : List Nat := [5, 2, 1, 1, 3, 1, 1, 4, 5]
def baseStart_2746326 : Nat := 118140960795 + 2746326 * 2 ^ 59
def prefixEnd_2746326 : Nat := 4983230072969 + 3 ^ 40 * 2746326 * 2
def baseEnd_2746326 : Nat := 156687252437747468954987

theorem tailTrace_2746326 : CollatzResearch.WordTrace tailWord_2746326 prefixEnd_2746326 156687252437747468954987 := by
  unfold tailWord_2746326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6260421140533588249007177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66777825499024941322743221 6260421140533588249007177)
  ·
    refine ⟨4695315855400191186755383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6260421140533588249007177 4695315855400191186755383)
    ·
      refine ⟨7042973783100286780133075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4695315855400191186755383 7042973783100286780133075)
      ·
        refine ⟨10564460674650430170199613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7042973783100286780133075 10564460674650430170199613)
        ·
          refine ⟨3961672752993911313824855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10564460674650430170199613 3961672752993911313824855)
          ·
            refine ⟨5942509129490866970737283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3961672752993911313824855 5942509129490866970737283)
            ·
              refine ⟨8913763694236300456105925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5942509129490866970737283 8913763694236300456105925)
              ·
                refine ⟨1671330692669306335519861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8913763694236300456105925 1671330692669306335519861)
                ·
                  refine ⟨156687252437747468954987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1671330692669306335519861 156687252437747468954987)
                  ·
                    rfl

theorem cell23_2746326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_2746326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746326 prefixEnd_2746326 := by exact prefixLift 2746326
  have htrace : WordTrace (prefixWord ++ tailWord_2746326) baseStart_2746326 baseEnd_2746326 := by
    simpa [prefixWord, tailWord_2746326, baseEnd_2746326] using wordTrace_append hprefix tailTrace_2746326
  have hstable : (prefixWord ++ tailWord_2746326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746326).length < 2 ^ (prefixWord ++ tailWord_2746326).sum := by decide
  have hdescent : baseEnd_2746326 < baseStart_2746326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746395 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 3, 5]
def baseStart_2746395 : Nat := 118140960795 + 2746395 * 2 ^ 59
def prefixEnd_2746395 : Nat := 4983230072969 + 3 ^ 40 * 2746395 * 2
def baseEnd_2746395 : Nat := 470073567368295816877355

theorem tailTrace_2746395 : CollatzResearch.WordTrace tailWord_2746395 prefixEnd_2746395 470073567368295816877355 := by
  unfold tailWord_2746395
  simp only [CollatzResearch.WordTrace]
  refine ⟨100169254885287436768376639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66779503256858291178917759 100169254885287436768376639)
  ·
    refine ⟨150253882327931155152564959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100169254885287436768376639 150253882327931155152564959)
    ·
      refine ⟨225380823491896732728847439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150253882327931155152564959 225380823491896732728847439)
      ·
        refine ⟨338071235237845099093271159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225380823491896732728847439 338071235237845099093271159)
        ·
          refine ⟨507106852856767648639906739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338071235237845099093271159 507106852856767648639906739)
          ·
            refine ⟨760660279285151472959860109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507106852856767648639906739 760660279285151472959860109)
            ·
              refine ⟨285247604731931802359947541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 760660279285151472959860109 285247604731931802359947541)
              ·
                refine ⟨13370981471809303235622541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 285247604731931802359947541 13370981471809303235622541)
                ·
                  refine ⟨5014118051928488713358453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13370981471809303235622541 5014118051928488713358453)
                  ·
                    refine ⟨470073567368295816877355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5014118051928488713358453 470073567368295816877355)
                    ·
                      rfl

theorem cell23_2746395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 5].length) (baseStart_2746395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746395 prefixEnd_2746395 := by exact prefixLift 2746395
  have htrace : WordTrace (prefixWord ++ tailWord_2746395) baseStart_2746395 baseEnd_2746395 := by
    simpa [prefixWord, tailWord_2746395, baseEnd_2746395] using wordTrace_append hprefix tailTrace_2746395
  have hstable : (prefixWord ++ tailWord_2746395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746395).length < 2 ^ (prefixWord ++ tailWord_2746395).sum := by decide
  have hdescent : baseEnd_2746395 < baseStart_2746395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746420 : List Nat := [2, 5, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_2746420 : Nat := 118140960795 + 2746420 * 2 ^ 59
def prefixEnd_2746420 : Nat := 4983230072969 + 3 ^ 40 * 2746420 * 2
def baseEnd_2746420 : Nat := 470077846373749950939817

theorem tailTrace_2746420 : CollatzResearch.WordTrace tailWord_2746420 prefixEnd_2746420 470077846373749950939817 := by
  unfold tailWord_2746420
  simp only [CollatzResearch.WordTrace]
  refine ⟨50085083355098433019018357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66780111140131244025357809 50085083355098433019018357)
  ·
    refine ⟨4695476564540478095532971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50085083355098433019018357 4695476564540478095532971)
    ·
      refine ⟨7043214846810717143299457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4695476564540478095532971 7043214846810717143299457)
      ·
        refine ⟨5282411135108037857474593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7043214846810717143299457 5282411135108037857474593)
        ·
          refine ⟨3961808351331028393105945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5282411135108037857474593 3961808351331028393105945)
          ·
            refine ⟨2971356263498271294829459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3961808351331028393105945 2971356263498271294829459)
            ·
              refine ⟨4457034395247406942244189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2971356263498271294829459 4457034395247406942244189)
              ·
                refine ⟨1671387898217777603341571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4457034395247406942244189 1671387898217777603341571)
                ·
                  refine ⟨2507081847326666405012357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1671387898217777603341571 2507081847326666405012357)
                  ·
                    refine ⟨470077846373749950939817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2507081847326666405012357 470077846373749950939817)
                    ·
                      rfl

theorem cell23_2746420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_2746420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746420 prefixEnd_2746420 := by exact prefixLift 2746420
  have htrace : WordTrace (prefixWord ++ tailWord_2746420) baseStart_2746420 baseEnd_2746420 := by
    simpa [prefixWord, tailWord_2746420, baseEnd_2746420] using wordTrace_append hprefix tailTrace_2746420
  have hstable : (prefixWord ++ tailWord_2746420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746420).length < 2 ^ (prefixWord ++ tailWord_2746420).sum := by decide
  have hdescent : baseEnd_2746420 < baseStart_2746420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746452 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_2746452 : Nat := 118140960795 + 2746452 * 2 ^ 59
def prefixEnd_2746452 : Nat := 4983230072969 + 3 ^ 40 * 2746452 * 2
def baseEnd_2746452 : Nat := 1410249970502193727619303

theorem tailTrace_2746452 : CollatzResearch.WordTrace tailWord_2746452 prefixEnd_2746452 1410249970502193727619303 := by
  unfold tailWord_2746452
  simp only [CollatzResearch.WordTrace]
  refine ⟨50085666923040467751600805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66780889230720623668801073 50085666923040467751600805)
  ·
    refine ⟨9391062548070087703425151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50085666923040467751600805 9391062548070087703425151)
    ·
      refine ⟨14086593822105131555137727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9391062548070087703425151 14086593822105131555137727)
      ·
        refine ⟨21129890733157697332706591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14086593822105131555137727 21129890733157697332706591)
        ·
          refine ⟨31694836099736545999059887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21129890733157697332706591 31694836099736545999059887)
          ·
            refine ⟨47542254149604818998589831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31694836099736545999059887 47542254149604818998589831)
            ·
              refine ⟨71313381224407228497884747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47542254149604818998589831 71313381224407228497884747)
              ·
                refine ⟨106970071836610842746827121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71313381224407228497884747 106970071836610842746827121)
                ·
                  refine ⟨80227553877458132060120341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106970071836610842746827121 80227553877458132060120341)
                  ·
                    refine ⟨3760666588005849940318141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80227553877458132060120341 3760666588005849940318141)
                    ·
                      refine ⟨1410249970502193727619303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3760666588005849940318141 1410249970502193727619303)
                      ·
                        rfl

theorem cell23_2746452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_2746452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746452 prefixEnd_2746452 := by exact prefixLift 2746452
  have htrace : WordTrace (prefixWord ++ tailWord_2746452) baseStart_2746452 baseEnd_2746452 := by
    simpa [prefixWord, tailWord_2746452, baseEnd_2746452] using wordTrace_append hprefix tailTrace_2746452
  have hstable : (prefixWord ++ tailWord_2746452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746452).length < 2 ^ (prefixWord ++ tailWord_2746452).sum := by decide
  have hdescent : baseEnd_2746452 < baseStart_2746452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746455 : List Nat := [1, 1, 3, 2, 2, 1, 3, 10]
def baseStart_2746455 : Nat := 118140960795 + 2746455 * 2 ^ 59
def prefixEnd_2746455 : Nat := 4983230072969 + 3 ^ 40 * 2746455 * 2
def baseEnd_2746455 : Nat := 52231537442376193180807

theorem tailTrace_2746455 : CollatzResearch.WordTrace tailWord_2746455 prefixEnd_2746455 52231537442376193180807 := by
  unfold tailWord_2746455
  simp only [CollatzResearch.WordTrace]
  refine ⟨100171443265070067015560819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66780962176713378010373879 100171443265070067015560819)
  ·
    refine ⟨150257164897605100523341229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100171443265070067015560819 150257164897605100523341229)
    ·
      refine ⟨56346436836601912696252961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150257164897605100523341229 56346436836601912696252961)
      ·
        refine ⟨42259827627451434522189721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56346436836601912696252961 42259827627451434522189721)
        ·
          refine ⟨31694870720588575891642291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42259827627451434522189721 31694870720588575891642291)
          ·
            refine ⟨47542306080882863837463437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31694870720588575891642291 47542306080882863837463437)
            ·
              refine ⟨17828364780331073939048789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47542306080882863837463437 17828364780331073939048789)
              ·
                refine ⟨52231537442376193180807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17828364780331073939048789 52231537442376193180807)
                ·
                  rfl

theorem cell23_2746455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 10].length) (baseStart_2746455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746455 prefixEnd_2746455 := by exact prefixLift 2746455
  have htrace : WordTrace (prefixWord ++ tailWord_2746455) baseStart_2746455 baseEnd_2746455 := by
    simpa [prefixWord, tailWord_2746455, baseEnd_2746455] using wordTrace_append hprefix tailTrace_2746455
  have hstable : (prefixWord ++ tailWord_2746455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746455).length < 2 ^ (prefixWord ++ tailWord_2746455).sum := by decide
  have hdescent : baseEnd_2746455 < baseStart_2746455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746466 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2746466 : Nat := 118140960795 + 2746466 * 2 ^ 59
def prefixEnd_2746466 : Nat := 4983230072969 + 3 ^ 40 * 2746466 * 2
def baseEnd_2746466 : Nat := 1410257159231356672844239

theorem tailTrace_2746466 : CollatzResearch.WordTrace tailWord_2746466 prefixEnd_2746466 1410257159231356672844239 := by
  unfold tailWord_2746466
  simp only [CollatzResearch.WordTrace]
  refine ⟨25042961117007553973552813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66781229645353477262807501 25042961117007553973552813)
  ·
    refine ⟨9391110418877832740082305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25042961117007553973552813 9391110418877832740082305)
    ·
      refine ⟨7043332814158374555061729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9391110418877832740082305 7043332814158374555061729)
      ·
        refine ⟨5282499610618780916296297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7043332814158374555061729 5282499610618780916296297)
        ·
          refine ⟨3961874707964085687222223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5282499610618780916296297 3961874707964085687222223)
          ·
            refine ⟨5942812061946128530833335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3961874707964085687222223 5942812061946128530833335)
            ·
              refine ⟨8914218092919192796250003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5942812061946128530833335 8914218092919192796250003)
              ·
                refine ⟨13371327139378789194375005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8914218092919192796250003 13371327139378789194375005)
                ·
                  refine ⟨5014247677267045947890627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13371327139378789194375005 5014247677267045947890627)
                  ·
                    refine ⟨7521371515900568921835941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5014247677267045947890627 7521371515900568921835941)
                    ·
                      refine ⟨1410257159231356672844239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7521371515900568921835941 1410257159231356672844239)
                      ·
                        rfl

theorem cell23_2746466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2746466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746466 prefixEnd_2746466 := by exact prefixLift 2746466
  have htrace : WordTrace (prefixWord ++ tailWord_2746466) baseStart_2746466 baseEnd_2746466 := by
    simpa [prefixWord, tailWord_2746466, baseEnd_2746466] using wordTrace_append hprefix tailTrace_2746466
  have hstable : (prefixWord ++ tailWord_2746466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746466).length < 2 ^ (prefixWord ++ tailWord_2746466).sum := by decide
  have hdescent : baseEnd_2746466 < baseStart_2746466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746469 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 3, 2, 3]
def baseStart_2746469 : Nat := 118140960795 + 2746469 * 2 ^ 59
def prefixEnd_2746469 : Nat := 4983230072969 + 3 ^ 40 * 2746469 * 2
def baseEnd_2746469 : Nat := 1410258699673320161106725

theorem tailTrace_2746469 : CollatzResearch.WordTrace tailWord_2746469 prefixEnd_2746469 1410258699673320161106725 := by
  unfold tailWord_2746469
  simp only [CollatzResearch.WordTrace]
  refine ⟨100171953887019347406570461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66781302591346231604380307 100171953887019347406570461)
  ·
    refine ⟨37564482707632255277463923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100171953887019347406570461 37564482707632255277463923)
    ·
      refine ⟨56346724061448382916195885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37564482707632255277463923 56346724061448382916195885)
      ·
        refine ⟨21130021523043143593573457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56346724061448382916195885 21130021523043143593573457)
        ·
          refine ⟨15847516142282357695180093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21130021523043143593573457 15847516142282357695180093)
          ·
            refine ⟨5942818553355884135692535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15847516142282357695180093 5942818553355884135692535)
            ·
              refine ⟨8914227830033826203538803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5942818553355884135692535 8914227830033826203538803)
              ·
                refine ⟨13371341745050739305308205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8914227830033826203538803 13371341745050739305308205)
                ·
                  refine ⟨5014253154394027239490577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13371341745050739305308205 5014253154394027239490577)
                  ·
                    refine ⟨3760689865795520429617933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5014253154394027239490577 3760689865795520429617933)
                    ·
                      refine ⟨1410258699673320161106725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3760689865795520429617933 1410258699673320161106725)
                      ·
                        rfl

theorem cell23_2746469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_2746469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746469 prefixEnd_2746469 := by exact prefixLift 2746469
  have htrace : WordTrace (prefixWord ++ tailWord_2746469) baseStart_2746469 baseEnd_2746469 := by
    simpa [prefixWord, tailWord_2746469, baseEnd_2746469] using wordTrace_append hprefix tailTrace_2746469
  have hstable : (prefixWord ++ tailWord_2746469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746469).length < 2 ^ (prefixWord ++ tailWord_2746469).sum := by decide
  have hdescent : baseEnd_2746469 < baseStart_2746469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746486 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_2746486 : Nat := 118140960795 + 2746486 * 2 ^ 59
def prefixEnd_2746486 : Nat := 4983230072969 + 3 ^ 40 * 2746486 * 2
def baseEnd_2746486 : Nat := 1410267428844446594594147

theorem tailTrace_2746486 : CollatzResearch.WordTrace tailWord_2746486 prefixEnd_2746486 1410267428844446594594147 := by
  unfold tailWord_2746486
  simp only [CollatzResearch.WordTrace]
  refine ⟨6260785870497359956871207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66781715951971839539959541 6260785870497359956871207)
  ·
    refine ⟨9391178805746039935306811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6260785870497359956871207 9391178805746039935306811)
    ·
      refine ⟨14086768208619059902960217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9391178805746039935306811 14086768208619059902960217)
      ·
        refine ⟨10565076156464294927220163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14086768208619059902960217 10565076156464294927220163)
        ·
          refine ⟨15847614234696442390830245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10565076156464294927220163 15847614234696442390830245)
          ·
            refine ⟨2971427669005582948280671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15847614234696442390830245 2971427669005582948280671)
            ·
              refine ⟨4457141503508374422421007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2971427669005582948280671 4457141503508374422421007)
              ·
                refine ⟨6685712255262561633631511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4457141503508374422421007 6685712255262561633631511)
                ·
                  refine ⟨10028568382893842450447267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6685712255262561633631511 10028568382893842450447267)
                  ·
                    refine ⟨15042852574340763675670901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10028568382893842450447267 15042852574340763675670901)
                    ·
                      refine ⟨1410267428844446594594147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15042852574340763675670901 1410267428844446594594147)
                      ·
                        rfl

theorem cell23_2746486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_2746486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746486 prefixEnd_2746486 := by exact prefixLift 2746486
  have htrace : WordTrace (prefixWord ++ tailWord_2746486) baseStart_2746486 baseEnd_2746486 := by
    simpa [prefixWord, tailWord_2746486, baseEnd_2746486] using wordTrace_append hprefix tailTrace_2746486
  have hstable : (prefixWord ++ tailWord_2746486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746486).length < 2 ^ (prefixWord ++ tailWord_2746486).sum := by decide
  have hdescent : baseEnd_2746486 < baseStart_2746486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746495 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 7]
def baseStart_2746495 : Nat := 118140960795 + 2746495 * 2 ^ 59
def prefixEnd_2746495 : Nat := 4983230072969 + 3 ^ 40 * 2746495 * 2
def baseEnd_2746495 : Nat := 1410272050170337059381605

theorem tailTrace_2746495 : CollatzResearch.WordTrace tailWord_2746495 prefixEnd_2746495 1410272050170337059381605 := by
  unfold tailWord_2746495
  simp only [CollatzResearch.WordTrace]
  refine ⟨100172902184925153847016939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66781934789950102564677959 100172902184925153847016939)
  ·
    refine ⟨150259353277387730770525409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100172902184925153847016939 150259353277387730770525409)
    ·
      refine ⟨112694514958040798077894057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150259353277387730770525409 112694514958040798077894057)
      ·
        refine ⟨84520886218530598558420543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112694514958040798077894057 84520886218530598558420543)
        ·
          refine ⟨126781329327795897837630815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84520886218530598558420543 126781329327795897837630815)
          ·
            refine ⟨190171993991693846756446223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126781329327795897837630815 190171993991693846756446223)
            ·
              refine ⟨285257990987540770134669335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190171993991693846756446223 285257990987540770134669335)
              ·
                refine ⟨427886986481311155202004003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285257990987540770134669335 427886986481311155202004003)
                ·
                  refine ⟨641830479721966732803006005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427886986481311155202004003 641830479721966732803006005)
                  ·
                    refine ⟨60171607473934381200281813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 641830479721966732803006005 60171607473934381200281813)
                    ·
                      refine ⟨1410272050170337059381605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60171607473934381200281813 1410272050170337059381605)
                      ·
                        rfl

theorem cell23_2746495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_2746495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746495 prefixEnd_2746495 := by exact prefixLift 2746495
  have htrace : WordTrace (prefixWord ++ tailWord_2746495) baseStart_2746495 baseEnd_2746495 := by
    simpa [prefixWord, tailWord_2746495, baseEnd_2746495] using wordTrace_append hprefix tailTrace_2746495
  have hstable : (prefixWord ++ tailWord_2746495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746495).length < 2 ^ (prefixWord ++ tailWord_2746495).sum := by decide
  have hdescent : baseEnd_2746495 < baseStart_2746495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746552 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 4, 2, 4]
def baseStart_2746552 : Nat := 118140960795 + 2746552 * 2 ^ 59
def prefixEnd_2746552 : Nat := 4983230072969 + 3 ^ 40 * 2746552 * 2
def baseEnd_2746552 : Nat := 1410301318567643336368843

theorem tailTrace_2746552 : CollatzResearch.WordTrace tailWord_2746552 prefixEnd_2746552 1410301318567643336368843 := by
  unfold tailWord_2746552
  simp only [CollatzResearch.WordTrace]
  refine ⟨50087490572859326290920955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66783320763812435054561273 50087490572859326290920955)
  ·
    refine ⟨75131235859288989436381433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50087490572859326290920955 75131235859288989436381433)
    ·
      refine ⟨56348426894466742077286075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75131235859288989436381433 56348426894466742077286075)
      ·
        refine ⟨84522640341700113115929113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56348426894466742077286075 84522640341700113115929113)
        ·
          refine ⟨63391980256275084836946835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84522640341700113115929113 63391980256275084836946835)
          ·
            refine ⟨95087970384412627255420253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63391980256275084836946835 95087970384412627255420253)
            ·
              refine ⟨35657988894154735220782595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95087970384412627255420253 35657988894154735220782595)
              ·
                refine ⟨53486983341232102831173893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35657988894154735220782595 53486983341232102831173893)
                ·
                  refine ⟨10028809376481019280845105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53486983341232102831173893 10028809376481019280845105)
                  ·
                    refine ⟨7521607032360764460633829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10028809376481019280845105 7521607032360764460633829)
                    ·
                      refine ⟨1410301318567643336368843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7521607032360764460633829 1410301318567643336368843)
                      ·
                        rfl

theorem cell23_2746552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_2746552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746552 prefixEnd_2746552 := by exact prefixLift 2746552
  have htrace : WordTrace (prefixWord ++ tailWord_2746552) baseStart_2746552 baseEnd_2746552 := by
    simpa [prefixWord, tailWord_2746552, baseEnd_2746552] using wordTrace_append hprefix tailTrace_2746552
  have hstable : (prefixWord ++ tailWord_2746552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746552).length < 2 ^ (prefixWord ++ tailWord_2746552).sum := by decide
  have hdescent : baseEnd_2746552 < baseStart_2746552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746592 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 1, 7]
def baseStart_2746592 : Nat := 118140960795 + 2746592 * 2 ^ 59
def prefixEnd_2746592 : Nat := 4983230072969 + 3 ^ 40 * 2746592 * 2
def baseEnd_2746592 : Nat := 470107285931274393289553

theorem tailTrace_2746592 : CollatzResearch.WordTrace tailWord_2746592 prefixEnd_2746592 470107285931274393289553 := by
  unfold tailWord_2746592
  simp only [CollatzResearch.WordTrace]
  refine ⟨50088220032786869706649015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66784293377049159608865353 50088220032786869706649015)
  ·
    refine ⟨75132330049180304559973523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50088220032786869706649015 75132330049180304559973523)
    ·
      refine ⟨112698495073770456839960285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75132330049180304559973523 112698495073770456839960285)
      ·
        refine ⟨42261935652663921314985107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112698495073770456839960285 42261935652663921314985107)
        ·
          refine ⟨63392903478995881972477661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42261935652663921314985107 63392903478995881972477661)
          ·
            refine ⟨23772338804623455739679123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63392903478995881972477661 23772338804623455739679123)
            ·
              refine ⟨35658508206935183609518685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23772338804623455739679123 35658508206935183609518685)
              ·
                refine ⟨13371940577600693853569507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35658508206935183609518685 13371940577600693853569507)
                ·
                  refine ⟨20057910866401040780354261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13371940577600693853569507 20057910866401040780354261)
                  ·
                    refine ⟨470107285931274393289553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20057910866401040780354261 470107285931274393289553)
                    ·
                      rfl

theorem cell23_2746592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 1, 7].length) (baseStart_2746592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746592 prefixEnd_2746592 := by exact prefixLift 2746592
  have htrace : WordTrace (prefixWord ++ tailWord_2746592) baseStart_2746592 baseEnd_2746592 := by
    simpa [prefixWord, tailWord_2746592, baseEnd_2746592] using wordTrace_append hprefix tailTrace_2746592
  have hstable : (prefixWord ++ tailWord_2746592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746592).length < 2 ^ (prefixWord ++ tailWord_2746592).sum := by decide
  have hdescent : baseEnd_2746592 < baseStart_2746592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746639 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 3, 4]
def baseStart_2746639 : Nat := 118140960795 + 2746639 * 2 ^ 59
def prefixEnd_2746639 : Nat := 4983230072969 + 3 ^ 40 * 2746639 * 2
def baseEnd_2746639 : Nat := 470115330461528165326981

theorem tailTrace_2746639 : CollatzResearch.WordTrace tailWord_2746639 prefixEnd_2746639 470115330461528165326981 := by
  unfold tailWord_2746639
  simp only [CollatzResearch.WordTrace]
  refine ⟨100178154296403466440258971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66785436197602310960172647 100178154296403466440258971)
  ·
    refine ⟨150267231444605199660388457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100178154296403466440258971 150267231444605199660388457)
    ·
      refine ⟨112700423583453899745291343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150267231444605199660388457 112700423583453899745291343)
      ·
        refine ⟨169050635375180849617937015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112700423583453899745291343 169050635375180849617937015)
        ·
          refine ⟨253575953062771274426905523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169050635375180849617937015 253575953062771274426905523)
          ·
            refine ⟨380363929594156911640358285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253575953062771274426905523 380363929594156911640358285)
            ·
              refine ⟨142636473597808841865134357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 380363929594156911640358285 142636473597808841865134357)
              ·
                refine ⟨6686084699897289462428173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142636473597808841865134357 6686084699897289462428173)
                ·
                  refine ⟨2507281762461483548410565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6686084699897289462428173 2507281762461483548410565)
                  ·
                    refine ⟨470115330461528165326981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2507281762461483548410565 470115330461528165326981)
                    ·
                      rfl

theorem cell23_2746639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 4].length) (baseStart_2746639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746639 prefixEnd_2746639 := by exact prefixLift 2746639
  have htrace : WordTrace (prefixWord ++ tailWord_2746639) baseStart_2746639 baseEnd_2746639 := by
    simpa [prefixWord, tailWord_2746639, baseEnd_2746639] using wordTrace_append hprefix tailTrace_2746639
  have hstable : (prefixWord ++ tailWord_2746639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746639).length < 2 ^ (prefixWord ++ tailWord_2746639).sum := by decide
  have hdescent : baseEnd_2746639 < baseStart_2746639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746686 : List Nat := [4, 2, 1, 2, 1, 2, 2, 3, 6]
def baseStart_2746686 : Nat := 118140960795 + 2746686 * 2 ^ 59
def prefixEnd_2746686 : Nat := 4983230072969 + 3 ^ 40 * 2746686 * 2
def baseEnd_2746686 : Nat := 156707791663927312454803

theorem tailTrace_2746686 : CollatzResearch.WordTrace tailWord_2746686 prefixEnd_2746686 156707791663927312454803 := by
  unfold tailWord_2746686
  simp only [CollatzResearch.WordTrace]
  refine ⟨12522483565904149183402489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66786579018155462311479941 12522483565904149183402489)
  ·
    refine ⟨9391862674428111887551867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12522483565904149183402489 9391862674428111887551867)
    ·
      refine ⟨14087794011642167831327801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9391862674428111887551867 14087794011642167831327801)
      ·
        refine ⟨10565845508731625873495851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14087794011642167831327801 10565845508731625873495851)
        ·
          refine ⟨15848768263097438810243777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10565845508731625873495851 15848768263097438810243777)
          ·
            refine ⟨11886576197323079107682833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15848768263097438810243777 11886576197323079107682833)
            ·
              refine ⟨8914932147992309330762125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11886576197323079107682833 8914932147992309330762125)
              ·
                refine ⟨3343099555497115999035797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8914932147992309330762125 3343099555497115999035797)
                ·
                  refine ⟨156707791663927312454803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3343099555497115999035797 156707791663927312454803)
                  ·
                    rfl

theorem cell23_2746686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_2746686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746686 prefixEnd_2746686 := by exact prefixLift 2746686
  have htrace : WordTrace (prefixWord ++ tailWord_2746686) baseStart_2746686 baseEnd_2746686 := by
    simpa [prefixWord, tailWord_2746686, baseEnd_2746686] using wordTrace_append hprefix tailTrace_2746686
  have hstable : (prefixWord ++ tailWord_2746686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746686).length < 2 ^ (prefixWord ++ tailWord_2746686).sum := by decide
  have hdescent : baseEnd_2746686 < baseStart_2746686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746696 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 5, 1, 3]
def baseStart_2746696 : Nat := 118140960795 + 2746696 * 2 ^ 59
def prefixEnd_2746696 : Nat := 4983230072969 + 3 ^ 40 * 2746696 * 2
def baseEnd_2746696 : Nat := 1410375259781890772968181

theorem tailTrace_2746696 : CollatzResearch.WordTrace tailWord_2746696 prefixEnd_2746696 1410375259781890772968181 := by
  unfold tailWord_2746696
  simp only [CollatzResearch.WordTrace]
  refine ⟨50090116628598482587541971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66786822171464643450055961 50090116628598482587541971)
  ·
    refine ⟨75135174942897723881312957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50090116628598482587541971 75135174942897723881312957)
    ·
      refine ⟨28175690603586646455492359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75135174942897723881312957 28175690603586646455492359)
      ·
        refine ⟨42263535905379969683238539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28175690603586646455492359 42263535905379969683238539)
        ·
          refine ⟨63395303858069954524857809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42263535905379969683238539 63395303858069954524857809)
          ·
            refine ⟨47546477893552465893643357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63395303858069954524857809 47546477893552465893643357)
            ·
              refine ⟨17829929210082174710116259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47546477893552465893643357 17829929210082174710116259)
              ·
                refine ⟨26744893815123262065174389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17829929210082174710116259 26744893815123262065174389)
                ·
                  refine ⟨2507333795167805818610099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26744893815123262065174389 2507333795167805818610099)
                  ·
                    refine ⟨3761000692751708727915149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2507333795167805818610099 3761000692751708727915149)
                    ·
                      refine ⟨1410375259781890772968181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3761000692751708727915149 1410375259781890772968181)
                      ·
                        rfl

theorem cell23_2746696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_2746696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746696 prefixEnd_2746696 := by exact prefixLift 2746696
  have htrace : WordTrace (prefixWord ++ tailWord_2746696) baseStart_2746696 baseEnd_2746696 := by
    simpa [prefixWord, tailWord_2746696, baseEnd_2746696] using wordTrace_append hprefix tailTrace_2746696
  have hstable : (prefixWord ++ tailWord_2746696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746696).length < 2 ^ (prefixWord ++ tailWord_2746696).sum := by decide
  have hdescent : baseEnd_2746696 < baseStart_2746696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746730 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_2746730 : Nat := 118140960795 + 2746730 * 2 ^ 59
def prefixEnd_2746730 : Nat := 4983230072969 + 3 ^ 40 * 2746730 * 2
def baseEnd_2746730 : Nat := 1410392718124143639943025

theorem tailTrace_2746730 : CollatzResearch.WordTrace tailWord_2746730 prefixEnd_2746730 1410392718124143639943025 := by
  unfold tailWord_2746730
  simp only [CollatzResearch.WordTrace]
  refine ⟨25045368334768447245455411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66787648892715859321214429 25045368334768447245455411)
  ·
    refine ⟨37568052502152670868183117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25045368334768447245455411 37568052502152670868183117)
    ·
      refine ⟨14088019688307251575568669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37568052502152670868183117 14088019688307251575568669)
      ·
        refine ⟨5283007383115219340838251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14088019688307251575568669 5283007383115219340838251)
        ·
          refine ⟨7924511074672829011257377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5283007383115219340838251 7924511074672829011257377)
          ·
            refine ⟨5943383306004621758443033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7924511074672829011257377 5943383306004621758443033)
            ·
              refine ⟨4457537479503466318832275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5943383306004621758443033 4457537479503466318832275)
              ·
                refine ⟨6686306219255199478248413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4457537479503466318832275 6686306219255199478248413)
                ·
                  refine ⟨2507364832220699804343155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6686306219255199478248413 2507364832220699804343155)
                  ·
                    refine ⟨3761047248331049706514733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2507364832220699804343155 3761047248331049706514733)
                    ·
                      refine ⟨1410392718124143639943025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3761047248331049706514733 1410392718124143639943025)
                      ·
                        rfl

theorem cell23_2746730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_2746730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746730 prefixEnd_2746730 := by exact prefixLift 2746730
  have htrace : WordTrace (prefixWord ++ tailWord_2746730) baseStart_2746730 baseEnd_2746730 := by
    simpa [prefixWord, tailWord_2746730, baseEnd_2746730] using wordTrace_append hprefix tailTrace_2746730
  have hstable : (prefixWord ++ tailWord_2746730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746730).length < 2 ^ (prefixWord ++ tailWord_2746730).sum := by decide
  have hdescent : baseEnd_2746730 < baseStart_2746730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746739 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 5]
def baseStart_2746739 : Nat := 118140960795 + 2746739 * 2 ^ 59
def prefixEnd_2746739 : Nat := 4983230072969 + 3 ^ 40 * 2746739 * 2
def baseEnd_2746739 : Nat := 1410397339450034104730483

theorem tailTrace_2746739 : CollatzResearch.WordTrace tailWord_2746739 prefixEnd_2746739 1410397339450034104730483 := by
  unfold tailWord_2746739
  simp only [CollatzResearch.WordTrace]
  refine ⟨100181801596041183518899271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66787867730694122345932847 100181801596041183518899271)
  ·
    refine ⟨150272702394061775278348907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100181801596041183518899271 150272702394061775278348907)
    ·
      refine ⟨225409053591092662917523361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150272702394061775278348907 225409053591092662917523361)
      ·
        refine ⟨169056790193319497188142521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225409053591092662917523361 169056790193319497188142521)
        ·
          refine ⟨126792592644989622891106891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169056790193319497188142521 126792592644989622891106891)
          ·
            refine ⟨190188888967484434336660337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126792592644989622891106891 190188888967484434336660337)
            ·
              refine ⟨142641666725613325752495253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190188888967484434336660337 142641666725613325752495253)
              ·
                refine ⟨6686328127763124644648215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142641666725613325752495253 6686328127763124644648215)
                ·
                  refine ⟨10029492191644686966972323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6686328127763124644648215 10029492191644686966972323)
                  ·
                    refine ⟨15044238287467030450458485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10029492191644686966972323 15044238287467030450458485)
                    ·
                      refine ⟨1410397339450034104730483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15044238287467030450458485 1410397339450034104730483)
                      ·
                        rfl

theorem cell23_2746739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 5].length) (baseStart_2746739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746739 prefixEnd_2746739 := by exact prefixLift 2746739
  have htrace : WordTrace (prefixWord ++ tailWord_2746739) baseStart_2746739 baseEnd_2746739 := by
    simpa [prefixWord, tailWord_2746739, baseEnd_2746739] using wordTrace_append hprefix tailTrace_2746739
  have hstable : (prefixWord ++ tailWord_2746739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746739).length < 2 ^ (prefixWord ++ tailWord_2746739).sum := by decide
  have hdescent : baseEnd_2746739 < baseStart_2746739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746753 : List Nat := [1, 2, 4, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_2746753 : Nat := 118140960795 + 2746753 * 2 ^ 59
def prefixEnd_2746753 : Nat := 4983230072969 + 3 ^ 40 * 2746753 * 2
def baseEnd_2746753 : Nat := 1410404528179197049955419

theorem tailTrace_2746753 : CollatzResearch.WordTrace tailWord_2746753 prefixEnd_2746753 1410404528179197049955419 := by
  unfold tailWord_2746753
  simp only [CollatzResearch.WordTrace]
  refine ⟨100182312217990463909908913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66788208145326975939939275 100182312217990463909908913)
  ·
    refine ⟨75136734163492847932431685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100182312217990463909908913 75136734163492847932431685)
    ·
      refine ⟨14088137655654908987330941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75136734163492847932431685 14088137655654908987330941)
      ·
        refine ⟨5283051620870590870249103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14088137655654908987330941 5283051620870590870249103)
        ·
          refine ⟨7924577431305886305373655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5283051620870590870249103 7924577431305886305373655)
          ·
            refine ⟨11886866146958829458060483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7924577431305886305373655 11886866146958829458060483)
            ·
              refine ⟨17830299220438244187090725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11886866146958829458060483 17830299220438244187090725)
              ·
                refine ⟨3343181103832170785079511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17830299220438244187090725 3343181103832170785079511)
                ·
                  refine ⟨5014771655748256177619267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3343181103832170785079511 5014771655748256177619267)
                  ·
                    refine ⟨7522157483622384266428901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5014771655748256177619267 7522157483622384266428901)
                    ·
                      refine ⟨1410404528179197049955419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7522157483622384266428901 1410404528179197049955419)
                      ·
                        rfl

theorem cell23_2746753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_2746753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746753 prefixEnd_2746753 := by exact prefixLift 2746753
  have htrace : WordTrace (prefixWord ++ tailWord_2746753) baseStart_2746753 baseEnd_2746753 := by
    simpa [prefixWord, tailWord_2746753, baseEnd_2746753] using wordTrace_append hprefix tailTrace_2746753
  have hstable : (prefixWord ++ tailWord_2746753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746753).length < 2 ^ (prefixWord ++ tailWord_2746753).sum := by decide
  have hdescent : baseEnd_2746753 < baseStart_2746753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746759 : List Nat := [1, 1, 4, 2, 2, 1, 3, 9]
def baseStart_2746759 : Nat := 118140960795 + 2746759 * 2 ^ 59
def prefixEnd_2746759 : Nat := 4983230072969 + 3 ^ 40 * 2746759 * 2
def baseEnd_2746759 : Nat := 52237318854189778758533

theorem tailTrace_2746759 : CollatzResearch.WordTrace tailWord_2746759 prefixEnd_2746759 52237318854189778758533 := by
  unfold tailWord_2746759
  simp only [CollatzResearch.WordTrace]
  refine ⟨100182531055968726934627331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66788354037312484623084887 100182531055968726934627331)
  ·
    refine ⟨150273796583953090401940997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100182531055968726934627331 150273796583953090401940997)
    ·
      refine ⟨28176336859491204450363937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150273796583953090401940997 28176336859491204450363937)
      ·
        refine ⟨21132252644618403337772953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28176336859491204450363937 21132252644618403337772953)
        ·
          refine ⟨15849189483463802503329715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21132252644618403337772953 15849189483463802503329715)
          ·
            refine ⟨23773784225195703754994573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15849189483463802503329715 23773784225195703754994573)
            ·
              refine ⟨8915169084448388908122965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23773784225195703754994573 8915169084448388908122965)
              ·
                refine ⟨52237318854189778758533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8915169084448388908122965 52237318854189778758533)
                ·
                  rfl

theorem cell23_2746759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 9].length) (baseStart_2746759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746759 prefixEnd_2746759 := by exact prefixLift 2746759
  have htrace : WordTrace (prefixWord ++ tailWord_2746759) baseStart_2746759 baseEnd_2746759 := by
    simpa [prefixWord, tailWord_2746759, baseEnd_2746759] using wordTrace_append hprefix tailTrace_2746759
  have hstable : (prefixWord ++ tailWord_2746759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746759).length < 2 ^ (prefixWord ++ tailWord_2746759).sum := by decide
  have hdescent : baseEnd_2746759 < baseStart_2746759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746776 : List Nat := [2, 1, 2, 5, 1, 3, 9]
def baseStart_2746776 : Nat := 118140960795 + 2746776 * 2 ^ 59
def prefixEnd_2746776 : Nat := 4983230072969 + 3 ^ 40 * 2746776 * 2
def baseEnd_2746776 : Nat := 17412547385608030369973

theorem tailTrace_2746776 : CollatzResearch.WordTrace tailWord_2746776 prefixEnd_2746776 17412547385608030369973 := by
  unfold tailWord_2746776
  simp only [CollatzResearch.WordTrace]
  refine ⟨50091575548453569418998091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66788767397938092558664121 50091575548453569418998091)
  ·
    refine ⟨75137363322680354128497137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50091575548453569418998091 75137363322680354128497137)
    ·
      refine ⟨56353022492010265596372853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75137363322680354128497137 56353022492010265596372853)
      ·
        refine ⟨5283095858625962399659955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56353022492010265596372853 5283095858625962399659955)
        ·
          refine ⟨7924643787938943599489933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5283095858625962399659955 7924643787938943599489933)
          ·
            refine ⟨2971741420477103849808725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7924643787938943599489933 2971741420477103849808725)
            ·
              refine ⟨17412547385608030369973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2971741420477103849808725 17412547385608030369973)
              ·
                rfl

theorem cell23_2746776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 9].length) (baseStart_2746776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746776 prefixEnd_2746776 := by exact prefixLift 2746776
  have htrace : WordTrace (prefixWord ++ tailWord_2746776) baseStart_2746776 baseEnd_2746776 := by
    simpa [prefixWord, tailWord_2746776, baseEnd_2746776] using wordTrace_append hprefix tailTrace_2746776
  have hstable : (prefixWord ++ tailWord_2746776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746776).length < 2 ^ (prefixWord ++ tailWord_2746776).sum := by decide
  have hdescent : baseEnd_2746776 < baseStart_2746776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746789 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 2, 7]
def baseStart_2746789 : Nat := 118140960795 + 2746789 * 2 ^ 59
def prefixEnd_2746789 : Nat := 4983230072969 + 3 ^ 40 * 2746789 * 2
def baseEnd_2746789 : Nat := 470141004494252969701751

theorem tailTrace_2746789 : CollatzResearch.WordTrace tailWord_2746789 prefixEnd_2746789 470141004494252969701751 := by
  unfold tailWord_2746789
  simp only [CollatzResearch.WordTrace]
  refine ⟨100183625245860042058219421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66789083497240028038812947 100183625245860042058219421)
  ·
    refine ⟨37568859467197515771832283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100183625245860042058219421 37568859467197515771832283)
    ·
      refine ⟨56353289200796273657748425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37568859467197515771832283 56353289200796273657748425)
      ·
        refine ⟨42264966900597205243311319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56353289200796273657748425 42264966900597205243311319)
        ·
          refine ⟨63397450350895807864966979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42264966900597205243311319 63397450350895807864966979)
          ·
            refine ⟨95096175526343711797450469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63397450350895807864966979 95096175526343711797450469)
            ·
              refine ⟨17830532911189445962021963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95096175526343711797450469 17830532911189445962021963)
              ·
                refine ⟨26745799366784168943032945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17830532911189445962021963 26745799366784168943032945)
                ·
                  refine ⟨20059349525088126707274709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26745799366784168943032945 20059349525088126707274709)
                  ·
                    refine ⟨470141004494252969701751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20059349525088126707274709 470141004494252969701751)
                    ·
                      rfl

theorem cell23_2746789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_2746789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746789 prefixEnd_2746789 := by exact prefixLift 2746789
  have htrace : WordTrace (prefixWord ++ tailWord_2746789) baseStart_2746789 baseEnd_2746789 := by
    simpa [prefixWord, tailWord_2746789, baseEnd_2746789] using wordTrace_append hprefix tailTrace_2746789
  have hstable : (prefixWord ++ tailWord_2746789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746789).length < 2 ^ (prefixWord ++ tailWord_2746789).sum := by decide
  have hdescent : baseEnd_2746789 < baseStart_2746789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746796 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 2, 7, 2]
def baseStart_2746796 : Nat := 118140960795 + 2746796 * 2 ^ 59
def prefixEnd_2746796 : Nat := 4983230072969 + 3 ^ 40 * 2746796 * 2
def baseEnd_2746796 : Nat := 1410426607847340381717721

theorem tailTrace_2746796 : CollatzResearch.WordTrace tailWord_2746796 prefixEnd_2746796 1410426607847340381717721 := by
  unfold tailWord_2746796
  simp only [CollatzResearch.WordTrace]
  refine ⟨50091940278417341126862121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66789253704556454835816161 50091940278417341126862121)
  ·
    refine ⟨37568955208813005845146591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50091940278417341126862121 37568955208813005845146591)
    ·
      refine ⟨56353432813219508767719887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37568955208813005845146591 56353432813219508767719887)
      ·
        refine ⟨84530149219829263151579831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56353432813219508767719887 84530149219829263151579831)
        ·
          refine ⟨126795223829743894727369747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84530149219829263151579831 126795223829743894727369747)
          ·
            refine ⟨190192835744615842091054621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126795223829743894727369747 190192835744615842091054621)
            ·
              refine ⟨71322313404230940784145483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190192835744615842091054621 71322313404230940784145483)
              ·
                refine ⟨106983470106346411176218225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71322313404230940784145483 106983470106346411176218225)
                ·
                  refine ⟨80237602579759808382163669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106983470106346411176218225 80237602579759808382163669)
                  ·
                    refine ⟨1880568810463120508956961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 80237602579759808382163669 1880568810463120508956961)
                    ·
                      refine ⟨1410426607847340381717721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1880568810463120508956961 1410426607847340381717721)
                      ·
                        rfl

theorem cell23_2746796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 7, 2].length) (baseStart_2746796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746796 prefixEnd_2746796 := by exact prefixLift 2746796
  have htrace : WordTrace (prefixWord ++ tailWord_2746796) baseStart_2746796 baseEnd_2746796 := by
    simpa [prefixWord, tailWord_2746796, baseEnd_2746796] using wordTrace_append hprefix tailTrace_2746796
  have hstable : (prefixWord ++ tailWord_2746796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746796).length < 2 ^ (prefixWord ++ tailWord_2746796).sum := by decide
  have hdescent : baseEnd_2746796 < baseStart_2746796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746804 : List Nat := [2, 5, 2, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_2746804 : Nat := 118140960795 + 2746804 * 2 ^ 59
def prefixEnd_2746804 : Nat := 4983230072969 + 3 ^ 40 * 2746804 * 2
def baseEnd_2746804 : Nat := 1410430715692576350417685

theorem tailTrace_2746804 : CollatzResearch.WordTrace tailWord_2746804 prefixEnd_2746804 1410430715692576350417685 := by
  unfold tailWord_2746804
  simp only [CollatzResearch.WordTrace]
  refine ⟨50092086170402849810007733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66789448227203799746676977 50092086170402849810007733)
  ·
    refine ⟨4696133078475267169688225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50092086170402849810007733 4696133078475267169688225)
    ·
      refine ⟨3522099808856450377266169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4696133078475267169688225 3522099808856450377266169)
      ·
        refine ⟨2641574856642337782949627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3522099808856450377266169 2641574856642337782949627)
        ·
          refine ⟨3962362284963506674424441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2641574856642337782949627 3962362284963506674424441)
          ·
            refine ⟨2971771713722630005818331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3962362284963506674424441 2971771713722630005818331)
            ·
              refine ⟨4457657570583945008727497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2971771713722630005818331 4457657570583945008727497)
              ·
                refine ⟨3343243177937958756545623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4457657570583945008727497 3343243177937958756545623)
                ·
                  refine ⟨5014864766906938134818435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3343243177937958756545623 5014864766906938134818435)
                  ·
                    refine ⟨7522297150360407202227653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5014864766906938134818435 7522297150360407202227653)
                    ·
                      refine ⟨1410430715692576350417685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7522297150360407202227653 1410430715692576350417685)
                      ·
                        rfl

theorem cell23_2746804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_2746804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746804 prefixEnd_2746804 := by exact prefixLift 2746804
  have htrace : WordTrace (prefixWord ++ tailWord_2746804) baseStart_2746804 baseEnd_2746804 := by
    simpa [prefixWord, tailWord_2746804, baseEnd_2746804] using wordTrace_append hprefix tailTrace_2746804
  have hstable : (prefixWord ++ tailWord_2746804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746804).length < 2 ^ (prefixWord ++ tailWord_2746804).sum := by decide
  have hdescent : baseEnd_2746804 < baseStart_2746804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746817 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2746817 : Nat := 118140960795 + 2746817 * 2 ^ 59
def prefixEnd_2746817 : Nat := 4983230072969 + 3 ^ 40 * 2746817 * 2
def baseEnd_2746817 : Nat := 1410437390941084799555125

theorem tailTrace_2746817 : CollatzResearch.WordTrace tailWord_2746817 prefixEnd_2746817 1410437390941084799555125 := by
  unfold tailWord_2746817
  simp only [CollatzResearch.WordTrace]
  refine ⟨100184646489758602840238705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66789764326505735226825803 100184646489758602840238705)
  ·
    refine ⟨75138484867318952130179029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100184646489758602840238705 75138484867318952130179029)
    ·
      refine ⟨1761058239077787940551071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 75138484867318952130179029 1761058239077787940551071)
      ·
        refine ⟨2641587358616681910826607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1761058239077787940551071 2641587358616681910826607)
        ·
          refine ⟨3962381037925022866239911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2641587358616681910826607 3962381037925022866239911)
          ·
            refine ⟨5943571556887534299359867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3962381037925022866239911 5943571556887534299359867)
            ·
              refine ⟨8915357335331301449039801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5943571556887534299359867 8915357335331301449039801)
              ·
                refine ⟨6686518001498476086779851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8915357335331301449039801 6686518001498476086779851)
                ·
                  refine ⟨10029777002247714130169777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6686518001498476086779851 10029777002247714130169777)
                  ·
                    refine ⟨7522332751685785597627333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10029777002247714130169777 7522332751685785597627333)
                    ·
                      refine ⟨1410437390941084799555125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7522332751685785597627333 1410437390941084799555125)
                      ·
                        rfl

theorem cell23_2746817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2746817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746817 prefixEnd_2746817 := by exact prefixLift 2746817
  have htrace : WordTrace (prefixWord ++ tailWord_2746817) baseStart_2746817 baseEnd_2746817 := by
    simpa [prefixWord, tailWord_2746817, baseEnd_2746817] using wordTrace_append hprefix tailTrace_2746817
  have hstable : (prefixWord ++ tailWord_2746817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746817).length < 2 ^ (prefixWord ++ tailWord_2746817).sum := by decide
  have hdescent : baseEnd_2746817 < baseStart_2746817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746819 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 4, 6]
def baseStart_2746819 : Nat := 118140960795 + 2746819 * 2 ^ 59
def prefixEnd_2746819 : Nat := 4983230072969 + 3 ^ 40 * 2746819 * 2
def baseEnd_2746819 : Nat := 470146139300797930576705

theorem tailTrace_2746819 : CollatzResearch.WordTrace tailWord_2746819 prefixEnd_2746819 470146139300797930576705 := by
  unfold tailWord_2746819
  simp only [CollatzResearch.WordTrace]
  refine ⟨100184719435751357181811511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66789812957167571454541007 100184719435751357181811511)
  ·
    refine ⟨150277079153627035772717267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100184719435751357181811511 150277079153627035772717267)
    ·
      refine ⟨225415618730440553659075901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150277079153627035772717267 225415618730440553659075901)
      ·
        refine ⟨84530857023915207622153463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225415618730440553659075901 84530857023915207622153463)
        ·
          refine ⟨126796285535872811433230195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84530857023915207622153463 126796285535872811433230195)
          ·
            refine ⟨190194428303809217149845293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126796285535872811433230195 190194428303809217149845293)
            ·
              refine ⟨71322910613928456431191985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190194428303809217149845293 71322910613928456431191985)
              ·
                refine ⟨53492182960446342323393989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71322910613928456431191985 53492182960446342323393989)
                ·
                  refine ⟨10029784305083689185636373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53492182960446342323393989 10029784305083689185636373)
                  ·
                    refine ⟨470146139300797930576705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10029784305083689185636373 470146139300797930576705)
                    ·
                      rfl

theorem cell23_2746819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 6].length) (baseStart_2746819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746819 prefixEnd_2746819 := by exact prefixLift 2746819
  have htrace : WordTrace (prefixWord ++ tailWord_2746819) baseStart_2746819 baseEnd_2746819 := by
    simpa [prefixWord, tailWord_2746819, baseEnd_2746819] using wordTrace_append hprefix tailTrace_2746819
  have hstable : (prefixWord ++ tailWord_2746819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746819).length < 2 ^ (prefixWord ++ tailWord_2746819).sum := by decide
  have hdescent : baseEnd_2746819 < baseStart_2746819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746820 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_2746820 : Nat := 118140960795 + 2746820 * 2 ^ 59
def prefixEnd_2746820 : Nat := 4983230072969 + 3 ^ 40 * 2746820 * 2
def baseEnd_2746820 : Nat := 1410438931383048287817611

theorem tailTrace_2746820 : CollatzResearch.WordTrace tailWord_2746820 prefixEnd_2746820 1410438931383048287817611 := by
  unfold tailWord_2746820
  simp only [CollatzResearch.WordTrace]
  refine ⟨50092377954373867176298957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66789837272498489568398609 50092377954373867176298957)
  ·
    refine ⟨18784641732890200191112109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50092377954373867176298957 18784641732890200191112109)
    ·
      refine ⟨7044240649833825071667041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18784641732890200191112109 7044240649833825071667041)
      ·
        refine ⟨5283180487375368803750281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7044240649833825071667041 5283180487375368803750281)
        ·
          refine ⟨3962385365531526602812711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5283180487375368803750281 3962385365531526602812711)
          ·
            refine ⟨5943578048297289904219067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3962385365531526602812711 5943578048297289904219067)
            ·
              refine ⟨8915367072445934856328601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5943578048297289904219067 8915367072445934856328601)
              ·
                refine ⟨6686525304334451142246451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8915367072445934856328601 6686525304334451142246451)
                ·
                  refine ⟨10029787956501676713369677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6686525304334451142246451 10029787956501676713369677)
                  ·
                    refine ⟨3761170483688128767513629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10029787956501676713369677 3761170483688128767513629)
                    ·
                      refine ⟨1410438931383048287817611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3761170483688128767513629 1410438931383048287817611)
                      ·
                        rfl

theorem cell23_2746820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_2746820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746820 prefixEnd_2746820 := by exact prefixLift 2746820
  have htrace : WordTrace (prefixWord ++ tailWord_2746820) baseStart_2746820 baseEnd_2746820 := by
    simpa [prefixWord, tailWord_2746820, baseEnd_2746820] using wordTrace_append hprefix tailTrace_2746820
  have hstable : (prefixWord ++ tailWord_2746820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746820).length < 2 ^ (prefixWord ++ tailWord_2746820).sum := by decide
  have hdescent : baseEnd_2746820 < baseStart_2746820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746839 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 6]
def baseStart_2746839 : Nat := 118140960795 + 2746839 * 2 ^ 59
def prefixEnd_2746839 : Nat := 4983230072969 + 3 ^ 40 * 2746839 * 2
def baseEnd_2746839 : Nat := 1410448687515483713480023

theorem tailTrace_2746839 : CollatzResearch.WordTrace tailWord_2746839 prefixEnd_2746839 1410448687515483713480023 := by
  unfold tailWord_2746839
  simp only [CollatzResearch.WordTrace]
  refine ⟨100185448895678900597539571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66790299263785933731693047 100185448895678900597539571)
  ·
    refine ⟨150278173343518350896309357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100185448895678900597539571 150278173343518350896309357)
    ·
      refine ⟨56354315003819381586116009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150278173343518350896309357 56354315003819381586116009)
      ·
        refine ⟨42265736252864536189587007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56354315003819381586116009 42265736252864536189587007)
        ·
          refine ⟨63398604379296804284380511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42265736252864536189587007 63398604379296804284380511)
          ·
            refine ⟨95097906568945206426570767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63398604379296804284380511 95097906568945206426570767)
            ·
              refine ⟨142646859853417809639856151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95097906568945206426570767 142646859853417809639856151)
              ·
                refine ⟨213970289780126714459784227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142646859853417809639856151 213970289780126714459784227)
                ·
                  refine ⟨320955434670190071689676341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213970289780126714459784227 320955434670190071689676341)
                  ·
                    refine ⟨30089572000330319220907157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 320955434670190071689676341 30089572000330319220907157)
                    ·
                      refine ⟨1410448687515483713480023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30089572000330319220907157 1410448687515483713480023)
                      ·
                        rfl

theorem cell23_2746839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_2746839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746839 prefixEnd_2746839 := by exact prefixLift 2746839
  have htrace : WordTrace (prefixWord ++ tailWord_2746839) baseStart_2746839 baseEnd_2746839 := by
    simpa [prefixWord, tailWord_2746839, baseEnd_2746839] using wordTrace_append hprefix tailTrace_2746839
  have hstable : (prefixWord ++ tailWord_2746839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746839).length < 2 ^ (prefixWord ++ tailWord_2746839).sum := by decide
  have hdescent : baseEnd_2746839 < baseStart_2746839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746853 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 2, 6]
def baseStart_2746853 : Nat := 118140960795 + 2746853 * 2 ^ 59
def prefixEnd_2746853 : Nat := 4983230072969 + 3 ^ 40 * 2746853 * 2
def baseEnd_2746853 : Nat := 470151958748215552901653

theorem tailTrace_2746853 : CollatzResearch.WordTrace tailWord_2746853 prefixEnd_2746853 470151958748215552901653 := by
  unfold tailWord_2746853
  simp only [CollatzResearch.WordTrace]
  refine ⟨100185959517628180988549213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66790639678418787325699475 100185959517628180988549213)
  ·
    refine ⟨37569734819110567870705955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100185959517628180988549213 37569734819110567870705955)
    ·
      refine ⟨56354602228665851806058933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37569734819110567870705955 56354602228665851806058933)
      ·
        refine ⟨5283243958937423606818025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56354602228665851806058933 5283243958937423606818025)
        ·
          refine ⟨3962432969203067705113519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5283243958937423606818025 3962432969203067705113519)
          ·
            refine ⟨5943649453804601557670279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3962432969203067705113519 5943649453804601557670279)
            ·
              refine ⟨8915474180706902336505419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5943649453804601557670279 8915474180706902336505419)
              ·
                refine ⟨13373211271060353504758129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8915474180706902336505419 13373211271060353504758129)
                ·
                  refine ⟨10029908453295265128568597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13373211271060353504758129 10029908453295265128568597)
                  ·
                    refine ⟨470151958748215552901653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10029908453295265128568597 470151958748215552901653)
                    ·
                      rfl

theorem cell23_2746853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_2746853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746853 prefixEnd_2746853 := by exact prefixLift 2746853
  have htrace : WordTrace (prefixWord ++ tailWord_2746853) baseStart_2746853 baseEnd_2746853 := by
    simpa [prefixWord, tailWord_2746853, baseEnd_2746853] using wordTrace_append hprefix tailTrace_2746853
  have hstable : (prefixWord ++ tailWord_2746853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746853).length < 2 ^ (prefixWord ++ tailWord_2746853).sum := by decide
  have hdescent : baseEnd_2746853 < baseStart_2746853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746856 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_2746856 : Nat := 118140960795 + 2746856 * 2 ^ 59
def prefixEnd_2746856 : Nat := 4983230072969 + 3 ^ 40 * 2746856 * 2
def baseEnd_2746856 : Nat := 1410457416686610146967445

theorem tailTrace_2746856 : CollatzResearch.WordTrace tailWord_2746856 prefixEnd_2746856 1410457416686610146967445 := by
  unfold tailWord_2746856
  simp only [CollatzResearch.WordTrace]
  refine ⟨50093034468308656250454211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66790712624411541667272281 50093034468308656250454211)
  ·
    refine ⟨75139551702462984375681317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50093034468308656250454211 75139551702462984375681317)
    ·
      refine ⟨14088665944211809570440247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75139551702462984375681317 14088665944211809570440247)
      ·
        refine ⟨21132998916317714355660371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14088665944211809570440247 21132998916317714355660371)
        ·
          refine ⟨31699498374476571533490557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21132998916317714355660371 31699498374476571533490557)
          ·
            refine ⟨11887311890428714325058959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31699498374476571533490557 11887311890428714325058959)
            ·
              refine ⟨17830967835643071487588439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11887311890428714325058959 17830967835643071487588439)
              ·
                refine ⟨26746451753464607231382659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17830967835643071487588439 26746451753464607231382659)
                ·
                  refine ⟨40119677630196910847073989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26746451753464607231382659 40119677630196910847073989)
                  ·
                    refine ⟨7522439555661920783826373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40119677630196910847073989 7522439555661920783826373)
                    ·
                      refine ⟨1410457416686610146967445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7522439555661920783826373 1410457416686610146967445)
                      ·
                        rfl

theorem cell23_2746856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_2746856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746856 prefixEnd_2746856 := by exact prefixLift 2746856
  have htrace : WordTrace (prefixWord ++ tailWord_2746856) baseStart_2746856 baseEnd_2746856 := by
    simpa [prefixWord, tailWord_2746856, baseEnd_2746856] using wordTrace_append hprefix tailTrace_2746856
  have hstable : (prefixWord ++ tailWord_2746856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746856).length < 2 ^ (prefixWord ++ tailWord_2746856).sum := by decide
  have hdescent : baseEnd_2746856 < baseStart_2746856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746860 : List Nat := [2, 2, 1, 1, 2, 1, 3, 5, 2, 2, 2]
def baseStart_2746860 : Nat := 118140960795 + 2746860 * 2 ^ 59
def prefixEnd_2746860 : Nat := 4983230072969 + 3 ^ 40 * 2746860 * 2
def baseEnd_2746860 : Nat := 1410459470609228131317427

theorem tailTrace_2746860 : CollatzResearch.WordTrace tailWord_2746860 prefixEnd_2746860 1410459470609228131317427 := by
  unfold tailWord_2746860
  simp only [CollatzResearch.WordTrace]
  refine ⟨50093107414301410592027017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66790809885735214122702689 50093107414301410592027017)
  ·
    refine ⟨37569830560726057944020263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50093107414301410592027017 37569830560726057944020263)
    ·
      refine ⟨56354745841089086916030395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37569830560726057944020263 56354745841089086916030395)
      ·
        refine ⟨84532118761633630374045593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56354745841089086916030395 84532118761633630374045593)
        ·
          refine ⟨63399089071225222780534195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84532118761633630374045593 63399089071225222780534195)
          ·
            refine ⟨95098633606837834170801293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63399089071225222780534195 95098633606837834170801293)
            ·
              refine ⟨35661987602564187814050485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95098633606837834170801293 35661987602564187814050485)
              ·
                refine ⟨3343311337740392607567233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35661987602564187814050485 3343311337740392607567233)
                ·
                  refine ⟨2507483503305294455675425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3343311337740392607567233 2507483503305294455675425)
                  ·
                    refine ⟨1880612627478970841756569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2507483503305294455675425 1880612627478970841756569)
                    ·
                      refine ⟨1410459470609228131317427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1880612627478970841756569 1410459470609228131317427)
                      ·
                        rfl

theorem cell23_2746860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 2, 2].length) (baseStart_2746860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746860 prefixEnd_2746860 := by exact prefixLift 2746860
  have htrace : WordTrace (prefixWord ++ tailWord_2746860) baseStart_2746860 baseEnd_2746860 := by
    simpa [prefixWord, tailWord_2746860, baseEnd_2746860] using wordTrace_append hprefix tailTrace_2746860
  have hstable : (prefixWord ++ tailWord_2746860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746860).length < 2 ^ (prefixWord ++ tailWord_2746860).sum := by decide
  have hdescent : baseEnd_2746860 < baseStart_2746860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746876 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 3, 5, 3]
def baseStart_2746876 : Nat := 118140960795 + 2746876 * 2 ^ 59
def prefixEnd_2746876 : Nat := 4983230072969 + 3 ^ 40 * 2746876 * 2
def baseEnd_2746876 : Nat := 1410467686299700068717353

theorem tailTrace_2746876 : CollatzResearch.WordTrace tailWord_2746876 prefixEnd_2746876 1410467686299700068717353 := by
  unfold tailWord_2746876
  simp only [CollatzResearch.WordTrace]
  refine ⟨50093399198272427958318241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66791198931029903944424321 50093399198272427958318241)
  ·
    refine ⟨37570049398704320968738681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50093399198272427958318241 37570049398704320968738681)
    ·
      refine ⟨28177537049028240726554011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37570049398704320968738681 28177537049028240726554011)
      ·
        refine ⟨42266305573542361089831017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28177537049028240726554011 42266305573542361089831017)
        ·
          refine ⟨31699729180156770817373263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42266305573542361089831017 31699729180156770817373263)
          ·
            refine ⟨47549593770235156226059895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31699729180156770817373263 47549593770235156226059895)
            ·
              refine ⟨71324390655352734339089843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47549593770235156226059895 71324390655352734339089843)
              ·
                refine ⟨106986585983029101508634765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71324390655352734339089843 106986585983029101508634765)
                ·
                  refine ⟨40119969743635913065738037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106986585983029101508634765 40119969743635913065738037)
                  ·
                    refine ⟨3761247163465866849912941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40119969743635913065738037 3761247163465866849912941)
                    ·
                      refine ⟨1410467686299700068717353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3761247163465866849912941 1410467686299700068717353)
                      ·
                        rfl

theorem cell23_2746876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_2746876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746876 prefixEnd_2746876 := by exact prefixLift 2746876
  have htrace : WordTrace (prefixWord ++ tailWord_2746876) baseStart_2746876 baseEnd_2746876 := by
    simpa [prefixWord, tailWord_2746876, baseEnd_2746876] using wordTrace_append hprefix tailTrace_2746876
  have hstable : (prefixWord ++ tailWord_2746876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746876).length < 2 ^ (prefixWord ++ tailWord_2746876).sum := by decide
  have hdescent : baseEnd_2746876 < baseStart_2746876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746883 : List Nat := [1, 1, 1, 3, 2, 1, 6, 3, 5]
def baseStart_2746883 : Nat := 118140960795 + 2746883 * 2 ^ 59
def prefixEnd_2746883 : Nat := 4983230072969 + 3 ^ 40 * 2746883 * 2
def baseEnd_2746883 : Nat := 156719031184920171258869

theorem tailTrace_2746883 : CollatzResearch.WordTrace tailWord_2746883 prefixEnd_2746883 156719031184920171258869 := by
  unfold tailWord_2746883
  simp only [CollatzResearch.WordTrace]
  refine ⟨100187053707519496112141303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66791369138346330741427535 100187053707519496112141303)
  ·
    refine ⟨150280580561279244168211955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100187053707519496112141303 150280580561279244168211955)
    ·
      refine ⟨225420870841918866252317933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150280580561279244168211955 225420870841918866252317933)
      ·
        refine ⟨84532826565719574844619225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225420870841918866252317933 84532826565719574844619225)
        ·
          refine ⟨63399619924289681133464419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84532826565719574844619225 63399619924289681133464419)
          ·
            refine ⟨95099429886434521700196629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63399619924289681133464419 95099429886434521700196629)
            ·
              refine ⟨4457785775926618204696717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95099429886434521700196629 4457785775926618204696717)
              ·
                refine ⟨1671669665972481826761269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4457785775926618204696717 1671669665972481826761269)
                ·
                  refine ⟨156719031184920171258869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1671669665972481826761269 156719031184920171258869)
                  ·
                    rfl

theorem cell23_2746883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 5].length) (baseStart_2746883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746883 prefixEnd_2746883 := by exact prefixLift 2746883
  have htrace : WordTrace (prefixWord ++ tailWord_2746883) baseStart_2746883 baseEnd_2746883 := by
    simpa [prefixWord, tailWord_2746883, baseEnd_2746883] using wordTrace_append hprefix tailTrace_2746883
  have hstable : (prefixWord ++ tailWord_2746883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746883).length < 2 ^ (prefixWord ++ tailWord_2746883).sum := by decide
  have hdescent : baseEnd_2746883 < baseStart_2746883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746894 : List Nat := [4, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2]
def baseStart_2746894 : Nat := 118140960795 + 2746894 * 2 ^ 59
def prefixEnd_2746894 : Nat := 4983230072969 + 3 ^ 40 * 2746894 * 2
def baseEnd_2746894 : Nat := 1410476928951480998292271

theorem tailTrace_2746894 : CollatzResearch.WordTrace tailWord_2746894 prefixEnd_2746894 1410476928951480998292271 := by
  unfold tailWord_2746894
  simp only [CollatzResearch.WordTrace]
  refine ⟨12523431863809955623848967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66791636606986429993861157 12523431863809955623848967)
  ·
    refine ⟨18785147795714933435773451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12523431863809955623848967 18785147795714933435773451)
    ·
      refine ⟨28177721693572400153660177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18785147795714933435773451 28177721693572400153660177)
      ·
        refine ⟨21133291270179300115245133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28177721693572400153660177 21133291270179300115245133)
        ·
          refine ⟨7924984226317237543216925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21133291270179300115245133 7924984226317237543216925)
          ·
            refine ⟨2971869084868964078706347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7924984226317237543216925 2971869084868964078706347)
            ·
              refine ⟨4457803627303446118059521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2971869084868964078706347 4457803627303446118059521)
              ·
                refine ⟨3343352720477584588544641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4457803627303446118059521 3343352720477584588544641)
                ·
                  refine ⟨2507514540358188441408481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3343352720477584588544641 2507514540358188441408481)
                  ·
                    refine ⟨1880635905268641331056361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2507514540358188441408481 1880635905268641331056361)
                    ·
                      refine ⟨1410476928951480998292271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1880635905268641331056361 1410476928951480998292271)
                      ·
                        rfl

theorem cell23_2746894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_2746894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746894 prefixEnd_2746894 := by exact prefixLift 2746894
  have htrace : WordTrace (prefixWord ++ tailWord_2746894) baseStart_2746894 baseEnd_2746894 := by
    simpa [prefixWord, tailWord_2746894, baseEnd_2746894] using wordTrace_append hprefix tailTrace_2746894
  have hstable : (prefixWord ++ tailWord_2746894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746894).length < 2 ^ (prefixWord ++ tailWord_2746894).sum := by decide
  have hdescent : baseEnd_2746894 < baseStart_2746894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746900 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 7]
def baseStart_2746900 : Nat := 118140960795 + 2746900 * 2 ^ 59
def prefixEnd_2746900 : Nat := 4983230072969 + 3 ^ 40 * 2746900 * 2
def baseEnd_2746900 : Nat := 156720001092823108313027

theorem tailTrace_2746900 : CollatzResearch.WordTrace tailWord_2746900 prefixEnd_2746900 156720001092823108313027 := by
  unfold tailWord_2746900
  simp only [CollatzResearch.WordTrace]
  refine ⟨50093836874228954007755077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66791782498971938677006769 50093836874228954007755077)
  ·
    refine ⟨9392594413917928876454077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50093836874228954007755077 9392594413917928876454077)
    ·
      refine ⟨3522222905219223328670279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9392594413917928876454077 3522222905219223328670279)
      ·
        refine ⟨5283334357828834993005419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3522222905219223328670279 5283334357828834993005419)
        ·
          refine ⟨7925001536743252489508129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5283334357828834993005419 7925001536743252489508129)
          ·
            refine ⟨5943751152557439367131097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7925001536743252489508129 5943751152557439367131097)
            ·
              refine ⟨4457813364418079525348323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5943751152557439367131097 4457813364418079525348323)
              ·
                refine ⟨6686720046627119288022485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4457813364418079525348323 6686720046627119288022485)
                ·
                  refine ⟨156720001092823108313027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6686720046627119288022485 156720001092823108313027)
                  ·
                    rfl

theorem cell23_2746900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_2746900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746900 prefixEnd_2746900 := by exact prefixLift 2746900
  have htrace : WordTrace (prefixWord ++ tailWord_2746900) baseStart_2746900 baseEnd_2746900 := by
    simpa [prefixWord, tailWord_2746900, baseEnd_2746900] using wordTrace_append hprefix tailTrace_2746900
  have hstable : (prefixWord ++ tailWord_2746900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746900).length < 2 ^ (prefixWord ++ tailWord_2746900).sum := by decide
  have hdescent : baseEnd_2746900 < baseStart_2746900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746906 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5]
def baseStart_2746906 : Nat := 118140960795 + 2746906 * 2 ^ 59
def prefixEnd_2746906 : Nat := 4983230072969 + 3 ^ 40 * 2746906 * 2
def baseEnd_2746906 : Nat := 1410483090719334951342215

theorem tailTrace_2746906 : CollatzResearch.WordTrace tailWord_2746906 prefixEnd_2746906 1410483090719334951342215 := by
  unfold tailWord_2746906
  simp only [CollatzResearch.WordTrace]
  refine ⟨25046973146609042760057143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66791928390957447360152381 25046973146609042760057143)
  ·
    refine ⟨37570459719913564140085715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25046973146609042760057143 37570459719913564140085715)
    ·
      refine ⟨56355689579870346210128573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37570459719913564140085715 56355689579870346210128573)
      ·
        refine ⟨21133383592451379828798215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56355689579870346210128573 21133383592451379828798215)
        ·
          refine ⟨31700075388677069743197323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21133383592451379828798215 31700075388677069743197323)
          ·
            refine ⟨47550113083015604614795985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31700075388677069743197323 47550113083015604614795985)
            ·
              refine ⟨35662584812261703461096989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47550113083015604614795985 35662584812261703461096989)
              ·
                refine ⟨13373469304598138797911371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35662584812261703461096989 13373469304598138797911371)
                ·
                  refine ⟨20060203956897208196867057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13373469304598138797911371 20060203956897208196867057)
                  ·
                    refine ⟨15045152967672906147650293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20060203956897208196867057 15045152967672906147650293)
                    ·
                      refine ⟨1410483090719334951342215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15045152967672906147650293 1410483090719334951342215)
                      ·
                        rfl

theorem cell23_2746906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_2746906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746906 prefixEnd_2746906 := by exact prefixLift 2746906
  have htrace : WordTrace (prefixWord ++ tailWord_2746906) baseStart_2746906 baseEnd_2746906 := by
    simpa [prefixWord, tailWord_2746906, baseEnd_2746906] using wordTrace_append hprefix tailTrace_2746906
  have hstable : (prefixWord ++ tailWord_2746906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746906).length < 2 ^ (prefixWord ++ tailWord_2746906).sum := by decide
  have hdescent : baseEnd_2746906 < baseStart_2746906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746933 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_2746933 : Nat := 118140960795 + 2746933 * 2 ^ 59
def prefixEnd_2746933 : Nat := 4983230072969 + 3 ^ 40 * 2746933 * 2
def baseEnd_2746933 : Nat := 1410496954697006345704591

theorem tailTrace_2746933 : CollatzResearch.WordTrace tailWord_2746933 prefixEnd_2746933 1410496954697006345704591 := by
  unfold tailWord_2746933
  simp only [CollatzResearch.WordTrace]
  refine ⟨100188877357338354651461453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66792584904892236434307635 100188877357338354651461453)
  ·
    refine ⟨37570829009001882994298045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100188877357338354651461453 37570829009001882994298045)
    ·
      refine ⟨14089060878375706122861767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37570829009001882994298045 14089060878375706122861767)
      ·
        refine ⟨21133591317563559184292651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14089060878375706122861767 21133591317563559184292651)
        ·
          refine ⟨31700386976345338776438977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21133591317563559184292651 31700386976345338776438977)
          ·
            refine ⟨23775290232259004082329233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31700386976345338776438977 23775290232259004082329233)
            ·
              refine ⟨17831467674194253061746925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23775290232259004082329233 17831467674194253061746925)
              ·
                refine ⟨6686800377822844898155097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17831467674194253061746925 6686800377822844898155097)
                ·
                  refine ⟨5015100283367133673616323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6686800377822844898155097 5015100283367133673616323)
                  ·
                    refine ⟨7522650425050700510424485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5015100283367133673616323 7522650425050700510424485)
                    ·
                      refine ⟨1410496954697006345704591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7522650425050700510424485 1410496954697006345704591)
                      ·
                        rfl

theorem cell23_2746933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_2746933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746933 prefixEnd_2746933 := by exact prefixLift 2746933
  have htrace : WordTrace (prefixWord ++ tailWord_2746933) baseStart_2746933 baseEnd_2746933 := by
    simpa [prefixWord, tailWord_2746933, baseEnd_2746933] using wordTrace_append hprefix tailTrace_2746933
  have hstable : (prefixWord ++ tailWord_2746933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746933).length < 2 ^ (prefixWord ++ tailWord_2746933).sum := by decide
  have hdescent : baseEnd_2746933 < baseStart_2746933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746956 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 8]
def baseStart_2746956 : Nat := 118140960795 + 2746956 * 2 ^ 59
def prefixEnd_2746956 : Nat := 4983230072969 + 3 ^ 40 * 2746956 * 2
def baseEnd_2746956 : Nat := 156723196083562195079665

theorem tailTrace_2746956 : CollatzResearch.WordTrace tailWord_2746956 prefixEnd_2746956 156723196083562195079665 := by
  unfold tailWord_2746956
  simp only [CollatzResearch.WordTrace]
  refine ⟨50094858118127514789774361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66793144157503353053032481 50094858118127514789774361)
  ·
    refine ⟨37571143588595636092330771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50094858118127514789774361 37571143588595636092330771)
    ·
      refine ⟨56356715382893454138496157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37571143588595636092330771 56356715382893454138496157)
      ·
        refine ⟨21133768268585045301936059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56356715382893454138496157 21133768268585045301936059)
        ·
          refine ⟨31700652402877567952904089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21133768268585045301936059 31700652402877567952904089)
          ·
            refine ⟨23775489302158175964678067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31700652402877567952904089 23775489302158175964678067)
            ·
              refine ⟨35663233953237263947017101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23775489302158175964678067 35663233953237263947017101)
              ·
                refine ⟨13373712732463973980131413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35663233953237263947017101 13373712732463973980131413)
                ·
                  refine ⟨156723196083562195079665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13373712732463973980131413 156723196083562195079665)
                  ·
                    rfl

theorem cell23_2746956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 8].length) (baseStart_2746956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746956 prefixEnd_2746956 := by exact prefixLift 2746956
  have htrace : WordTrace (prefixWord ++ tailWord_2746956) baseStart_2746956 baseEnd_2746956 := by
    simpa [prefixWord, tailWord_2746956, baseEnd_2746956] using wordTrace_append hprefix tailTrace_2746956
  have hstable : (prefixWord ++ tailWord_2746956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746956).length < 2 ^ (prefixWord ++ tailWord_2746956).sum := by decide
  have hdescent : baseEnd_2746956 < baseStart_2746956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746976 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 6]
def baseStart_2746976 : Nat := 118140960795 + 2746976 * 2 ^ 59
def prefixEnd_2746976 : Nat := 4983230072969 + 3 ^ 40 * 2746976 * 2
def baseEnd_2746976 : Nat := 1410519034365149677466893

theorem tailTrace_2746976 : CollatzResearch.WordTrace tailWord_2746976 prefixEnd_2746976 1410519034365149677466893 := by
  unfold tailWord_2746976
  simp only [CollatzResearch.WordTrace]
  refine ⟨50095222848091286497638391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66793630464121715330184521 50095222848091286497638391)
  ·
    refine ⟨75142834272136929746457587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50095222848091286497638391 75142834272136929746457587)
    ·
      refine ⟨112714251408205394619686381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75142834272136929746457587 112714251408205394619686381)
      ·
        refine ⟨42267844278077022982382393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112714251408205394619686381 42267844278077022982382393)
        ·
          refine ⟨31700883208557767236786795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42267844278077022982382393 31700883208557767236786795)
          ·
            refine ⟨47551324812836650855180193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31700883208557767236786795 47551324812836650855180193)
            ·
              refine ⟨35663493609627488141385145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47551324812836650855180193 35663493609627488141385145)
              ·
                refine ⟨26747620207220616106038859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35663493609627488141385145 26747620207220616106038859)
                ·
                  refine ⟨40121430310830924159058289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26747620207220616106038859 40121430310830924159058289)
                  ·
                    refine ⟨30091072733123193119293717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40121430310830924159058289 30091072733123193119293717)
                    ·
                      refine ⟨1410519034365149677466893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30091072733123193119293717 1410519034365149677466893)
                      ·
                        rfl

theorem cell23_2746976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_2746976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2746976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2746976 prefixEnd_2746976 := by exact prefixLift 2746976
  have htrace : WordTrace (prefixWord ++ tailWord_2746976) baseStart_2746976 baseEnd_2746976 := by
    simpa [prefixWord, tailWord_2746976, baseEnd_2746976] using wordTrace_append hprefix tailTrace_2746976
  have hstable : (prefixWord ++ tailWord_2746976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746976).length < 2 ^ (prefixWord ++ tailWord_2746976).sum := by decide
  have hdescent : baseEnd_2746976 < baseStart_2746976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747033 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 1, 6]
def baseStart_2747033 : Nat := 118140960795 + 2747033 * 2 ^ 59
def prefixEnd_2747033 : Nat := 4983230072969 + 3 ^ 40 * 2747033 * 2
def baseEnd_2747033 : Nat := 470182767587485318151377

theorem tailTrace_2747033 : CollatzResearch.WordTrace tailWord_2747033 prefixEnd_2747033 470182767587485318151377 := by
  unfold tailWord_2747033
  simp only [CollatzResearch.WordTrace]
  refine ⟨100192524656976071730101753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66795016437984047820067835 100192524656976071730101753)
  ·
    refine ⟨75144393492732053797576315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100192524656976071730101753 75144393492732053797576315)
    ·
      refine ⟨112716590239098080696364473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75144393492732053797576315 112716590239098080696364473)
      ·
        refine ⟨84537442679323560522273355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112716590239098080696364473 84537442679323560522273355)
        ·
          refine ⟨126806164018985340783410033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84537442679323560522273355 126806164018985340783410033)
          ·
            refine ⟨95104623014239005587557525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126806164018985340783410033 95104623014239005587557525)
            ·
              refine ⟨4458029203792453386916759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95104623014239005587557525 4458029203792453386916759)
              ·
                refine ⟨6687043805688680080375139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4458029203792453386916759 6687043805688680080375139)
                ·
                  refine ⟨10030565708533020120562709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6687043805688680080375139 10030565708533020120562709)
                  ·
                    refine ⟨470182767587485318151377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10030565708533020120562709 470182767587485318151377)
                    ·
                      rfl

theorem cell23_2747033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 6].length) (baseStart_2747033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747033 prefixEnd_2747033 := by exact prefixLift 2747033
  have htrace : WordTrace (prefixWord ++ tailWord_2747033) baseStart_2747033 baseEnd_2747033 := by
    simpa [prefixWord, tailWord_2747033, baseEnd_2747033] using wordTrace_append hprefix tailTrace_2747033
  have hstable : (prefixWord ++ tailWord_2747033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747033).length < 2 ^ (prefixWord ++ tailWord_2747033).sum := by decide
  have hdescent : baseEnd_2747033 < baseStart_2747033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747034 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2747034 : Nat := 118140960795 + 2747034 * 2 ^ 59
def prefixEnd_2747034 : Nat := 4983230072969 + 3 ^ 40 * 2747034 * 2
def baseEnd_2747034 : Nat := 1410548816243110450541627

theorem tailTrace_2747034 : CollatzResearch.WordTrace tailWord_2747034 prefixEnd_2747034 1410548816243110450541627 := by
  unfold tailWord_2747034
  simp only [CollatzResearch.WordTrace]
  refine ⟨25048140282493112225222039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66795040753314965933925437 25048140282493112225222039)
  ·
    refine ⟨37572210423739668337833059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25048140282493112225222039 37572210423739668337833059)
    ·
      refine ⟨56358315635609502506749589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37572210423739668337833059 56358315635609502506749589)
      ·
        refine ⟨2641796045419195430003887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56358315635609502506749589 2641796045419195430003887)
        ·
          refine ⟨3962694068128793145005831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2641796045419195430003887 3962694068128793145005831)
          ·
            refine ⟨5944041102193189717508747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3962694068128793145005831 5944041102193189717508747)
            ·
              refine ⟨8916061653289784576263121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5944041102193189717508747 8916061653289784576263121)
              ·
                refine ⟨6687046239967338432197341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8916061653289784576263121 6687046239967338432197341)
                ·
                  refine ⟨2507642339987751912074003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6687046239967338432197341 2507642339987751912074003)
                  ·
                    refine ⟨3761463509981627868111005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2507642339987751912074003 3761463509981627868111005)
                    ·
                      refine ⟨1410548816243110450541627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3761463509981627868111005 1410548816243110450541627)
                      ·
                        rfl

theorem cell23_2747034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2747034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747034 prefixEnd_2747034 := by exact prefixLift 2747034
  have htrace : WordTrace (prefixWord ++ tailWord_2747034) baseStart_2747034 baseEnd_2747034 := by
    simpa [prefixWord, tailWord_2747034, baseEnd_2747034] using wordTrace_append hprefix tailTrace_2747034
  have hstable : (prefixWord ++ tailWord_2747034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747034).length < 2 ^ (prefixWord ++ tailWord_2747034).sum := by decide
  have hdescent : baseEnd_2747034 < baseStart_2747034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747054 : List Nat := [4, 1, 4, 1, 1, 1, 4, 1, 1, 5]
def baseStart_2747054 : Nat := 118140960795 + 2747054 * 2 ^ 59
def prefixEnd_2747054 : Nat := 4983230072969 + 3 ^ 40 * 2747054 * 2
def baseEnd_2747054 : Nat := 470186361952066790763845

theorem tailTrace_2747054 : CollatzResearch.WordTrace tailWord_2747054 prefixEnd_2747054 470186361952066790763845 := by
  unfold tailWord_2747054
  simp only [CollatzResearch.WordTrace]
  refine ⟨12524161323737499039577027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66795527059933328211077477 12524161323737499039577027)
  ·
    refine ⟨18786241985606248559365541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12524161323737499039577027 18786241985606248559365541)
    ·
      refine ⟨3522420372301171604881039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18786241985606248559365541 3522420372301171604881039)
      ·
        refine ⟨5283630558451757407321559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3522420372301171604881039 5283630558451757407321559)
        ·
          refine ⟨7925445837677636110982339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5283630558451757407321559 7925445837677636110982339)
          ·
            refine ⟨11888168756516454166473509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7925445837677636110982339 11888168756516454166473509)
            ·
              refine ⟨2229031641846835156213783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11888168756516454166473509 2229031641846835156213783)
              ·
                refine ⟨3343547462770252734320675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2229031641846835156213783 3343547462770252734320675)
                ·
                  refine ⟨5015321194155379101481013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3343547462770252734320675 5015321194155379101481013)
                  ·
                    refine ⟨470186361952066790763845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5015321194155379101481013 470186361952066790763845)
                    ·
                      rfl

theorem cell23_2747054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_2747054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747054 prefixEnd_2747054 := by exact prefixLift 2747054
  have htrace : WordTrace (prefixWord ++ tailWord_2747054) baseStart_2747054 baseEnd_2747054 := by
    simpa [prefixWord, tailWord_2747054, baseEnd_2747054] using wordTrace_append hprefix tailTrace_2747054
  have hstable : (prefixWord ++ tailWord_2747054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747054).length < 2 ^ (prefixWord ++ tailWord_2747054).sum := by decide
  have hdescent : baseEnd_2747054 < baseStart_2747054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747063 : List Nat := [1, 1, 3, 1, 6, 1, 10]
def baseStart_2747063 : Nat := 118140960795 + 2747063 * 2 ^ 59
def prefixEnd_2747063 : Nat := 4983230072969 + 3 ^ 40 * 2747063 * 2
def baseEnd_2747063 : Nat := 17414366755334454778753

theorem tailTrace_2747063 : CollatzResearch.WordTrace tailWord_2747063 prefixEnd_2747063 17414366755334454778753 := by
  unfold tailWord_2747063
  simp only [CollatzResearch.WordTrace]
  refine ⟨100193618846867386853693843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66795745897911591235795895 100193618846867386853693843)
  ·
    refine ⟨150290428270301080280540765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100193618846867386853693843 150290428270301080280540765)
    ·
      refine ⟨56358910601362905105202787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150290428270301080280540765 56358910601362905105202787)
      ·
        refine ⟨84538365902044357657804181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56358910601362905105202787 84538365902044357657804181)
        ·
          refine ⟨3962735901658329265209571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84538365902044357657804181 3962735901658329265209571)
          ·
            refine ⟨5944103852487493897814357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3962735901658329265209571 5944103852487493897814357)
            ·
              refine ⟨17414366755334454778753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5944103852487493897814357 17414366755334454778753)
              ·
                rfl

theorem cell23_2747063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 10].length) (baseStart_2747063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747063 prefixEnd_2747063 := by exact prefixLift 2747063
  have htrace : WordTrace (prefixWord ++ tailWord_2747063) baseStart_2747063 baseEnd_2747063 := by
    simpa [prefixWord, tailWord_2747063, baseEnd_2747063] using wordTrace_append hprefix tailTrace_2747063
  have hstable : (prefixWord ++ tailWord_2747063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747063).length < 2 ^ (prefixWord ++ tailWord_2747063).sum := by decide
  have hdescent : baseEnd_2747063 < baseStart_2747063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747084 : List Nat := [2, 2, 1, 5, 1, 2, 3, 1, 2, 4]
def baseStart_2747084 : Nat := 118140960795 + 2747084 * 2 ^ 59
def prefixEnd_2747084 : Nat := 4983230072969 + 3 ^ 40 * 2747084 * 2
def baseEnd_2747084 : Nat := 470191496758611751638799

theorem tailTrace_2747084 : CollatzResearch.WordTrace tailWord_2747084 prefixEnd_2747084 470191496758611751638799 := by
  unfold tailWord_2747084
  simp only [CollatzResearch.WordTrace]
  refine ⟨50097192389895653720104153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66796256519860871626805537 50097192389895653720104153)
  ·
    refine ⟨37572894292421740290078115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50097192389895653720104153 37572894292421740290078115)
    ·
      refine ⟨56359341438632610435117173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37572894292421740290078115 56359341438632610435117173)
      ·
        refine ⟨5283688259871807228292235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56359341438632610435117173 5283688259871807228292235)
        ·
          refine ⟨7925532389807710842438353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5283688259871807228292235 7925532389807710842438353)
          ·
            refine ⟨5944149292355783131828765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7925532389807710842438353 5944149292355783131828765)
            ·
              refine ⟨2229055984633418674435787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5944149292355783131828765 2229055984633418674435787)
              ·
                refine ⟨3343583976950128011653681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2229055984633418674435787 3343583976950128011653681)
                ·
                  refine ⟨2507687982712596008740261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3343583976950128011653681 2507687982712596008740261)
                  ·
                    refine ⟨470191496758611751638799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2507687982712596008740261 470191496758611751638799)
                    ·
                      rfl

theorem cell23_2747084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 2, 4].length) (baseStart_2747084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747084 prefixEnd_2747084 := by exact prefixLift 2747084
  have htrace : WordTrace (prefixWord ++ tailWord_2747084) baseStart_2747084 baseEnd_2747084 := by
    simpa [prefixWord, tailWord_2747084, baseEnd_2747084] using wordTrace_append hprefix tailTrace_2747084
  have hstable : (prefixWord ++ tailWord_2747084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747084).length < 2 ^ (prefixWord ++ tailWord_2747084).sum := by decide
  have hdescent : baseEnd_2747084 < baseStart_2747084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747103 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 5]
def baseStart_2747103 : Nat := 118140960795 + 2747103 * 2 ^ 59
def prefixEnd_2747103 : Nat := 4983230072969 + 3 ^ 40 * 2747103 * 2
def baseEnd_2747103 : Nat := 1410584246408270680578809

theorem tailTrace_2747103 : CollatzResearch.WordTrace tailWord_2747103 prefixEnd_2747103 1410584246408270680578809 := by
  unfold tailWord_2747103
  simp only [CollatzResearch.WordTrace]
  refine ⟨100195077766722473685149963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66796718511148315790099975 100195077766722473685149963)
  ·
    refine ⟨150292616650083710527724945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100195077766722473685149963 150292616650083710527724945)
    ·
      refine ⟨112719462487562782895793709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150292616650083710527724945 112719462487562782895793709)
      ·
        refine ⟨42269798432836043585922641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112719462487562782895793709 42269798432836043585922641)
        ·
          refine ⟨31702348824627032689441981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42269798432836043585922641 31702348824627032689441981)
          ·
            refine ⟨11888380809235137258540743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31702348824627032689441981 11888380809235137258540743)
            ·
              refine ⟨17832571213852705887811115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11888380809235137258540743 17832571213852705887811115)
              ·
                refine ⟨26748856820779058831716673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17832571213852705887811115 26748856820779058831716673)
                ·
                  refine ⟨20061642615584294123787505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26748856820779058831716673 20061642615584294123787505)
                  ·
                    refine ⟨15046231961688220592840629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20061642615584294123787505 15046231961688220592840629)
                    ·
                      refine ⟨1410584246408270680578809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15046231961688220592840629 1410584246408270680578809)
                      ·
                        rfl

theorem cell23_2747103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_2747103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747103 prefixEnd_2747103 := by exact prefixLift 2747103
  have htrace : WordTrace (prefixWord ++ tailWord_2747103) baseStart_2747103 baseEnd_2747103 := by
    simpa [prefixWord, tailWord_2747103, baseEnd_2747103] using wordTrace_append hprefix tailTrace_2747103
  have hstable : (prefixWord ++ tailWord_2747103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747103).length < 2 ^ (prefixWord ++ tailWord_2747103).sum := by decide
  have hdescent : baseEnd_2747103 < baseStart_2747103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747107 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 4, 1, 3]
def baseStart_2747107 : Nat := 118140960795 + 2747107 * 2 ^ 59
def prefixEnd_2747107 : Nat := 4983230072969 + 3 ^ 40 * 2747107 * 2
def baseEnd_2747107 : Nat := 1410586300330888664928791

theorem tailTrace_2747107 : CollatzResearch.WordTrace tailWord_2747107 prefixEnd_2747107 1410586300330888664928791 := by
  unfold tailWord_2747107
  simp only [CollatzResearch.WordTrace]
  refine ⟨100195223658707982368295575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66796815772471988245530383 100195223658707982368295575)
  ·
    refine ⟨150292835488061973552443363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100195223658707982368295575 150292835488061973552443363)
    ·
      refine ⟨225439253232092960328665045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150292835488061973552443363 225439253232092960328665045)
      ·
        refine ⟨5283732497627178757703087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 225439253232092960328665045 5283732497627178757703087)
        ·
          refine ⟨7925598746440768136554631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5283732497627178757703087 7925598746440768136554631)
          ·
            refine ⟨11888398119661152204831947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7925598746440768136554631 11888398119661152204831947)
            ·
              refine ⟨17832597179491728307247921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11888398119661152204831947 17832597179491728307247921)
              ·
                refine ⟨13374447884618796230435941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17832597179491728307247921 13374447884618796230435941)
                ·
                  refine ⟨2507708978366024293206739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13374447884618796230435941 2507708978366024293206739)
                  ·
                    refine ⟨3761563467549036439810109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2507708978366024293206739 3761563467549036439810109)
                    ·
                      refine ⟨1410586300330888664928791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3761563467549036439810109 1410586300330888664928791)
                      ·
                        rfl

theorem cell23_2747107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_2747107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747107 prefixEnd_2747107 := by exact prefixLift 2747107
  have htrace : WordTrace (prefixWord ++ tailWord_2747107) baseStart_2747107 baseEnd_2747107 := by
    simpa [prefixWord, tailWord_2747107, baseEnd_2747107] using wordTrace_append hprefix tailTrace_2747107
  have hstable : (prefixWord ++ tailWord_2747107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747107).length < 2 ^ (prefixWord ++ tailWord_2747107).sum := by decide
  have hdescent : baseEnd_2747107 < baseStart_2747107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747125 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_2747125 : Nat := 118140960795 + 2747125 * 2 ^ 59
def prefixEnd_2747125 : Nat := 4983230072969 + 3 ^ 40 * 2747125 * 2
def baseEnd_2747125 : Nat := 1410595542982669594503709

theorem tailTrace_2747125 : CollatzResearch.WordTrace tailWord_2747125 prefixEnd_2747125 1410595542982669594503709 := by
  unfold tailWord_2747125
  simp only [CollatzResearch.WordTrace]
  refine ⟨100195880172642771442450829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66797253448428514294967219 100195880172642771442450829)
  ·
    refine ⟨37573455064741039290919061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100195880172642771442450829 37573455064741039290919061)
    ·
      refine ⟨1761255706159736216761831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37573455064741039290919061 1761255706159736216761831)
      ·
        refine ⟨2641883559239604325142747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1761255706159736216761831 2641883559239604325142747)
        ·
          refine ⟨3962825338859406487714121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2641883559239604325142747 3962825338859406487714121)
          ·
            refine ⟨2972119004144554865785591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3962825338859406487714121 2972119004144554865785591)
            ·
              refine ⟨4458178506216832298678387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2972119004144554865785591 4458178506216832298678387)
              ·
                refine ⟨6687267759325248448017581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4458178506216832298678387 6687267759325248448017581)
                ·
                  refine ⟨2507725409746968168006593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6687267759325248448017581 2507725409746968168006593)
                  ·
                    refine ⟨1880794057310226126004945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2507725409746968168006593 1880794057310226126004945)
                    ·
                      refine ⟨1410595542982669594503709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1880794057310226126004945 1410595542982669594503709)
                      ·
                        rfl

theorem cell23_2747125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_2747125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747125 prefixEnd_2747125 := by exact prefixLift 2747125
  have htrace : WordTrace (prefixWord ++ tailWord_2747125) baseStart_2747125 baseEnd_2747125 := by
    simpa [prefixWord, tailWord_2747125, baseEnd_2747125] using wordTrace_append hprefix tailTrace_2747125
  have hstable : (prefixWord ++ tailWord_2747125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747125).length < 2 ^ (prefixWord ++ tailWord_2747125).sum := by decide
  have hdescent : baseEnd_2747125 < baseStart_2747125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747133 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_2747133 : Nat := 118140960795 + 2747133 * 2 ^ 59
def prefixEnd_2747133 : Nat := 4983230072969 + 3 ^ 40 * 2747133 * 2
def baseEnd_2747133 : Nat := 1410599650827905563203671

theorem tailTrace_2747133 : CollatzResearch.WordTrace tailWord_2747133 prefixEnd_2747133 1410599650827905563203671 := by
  unfold tailWord_2747133
  simp only [CollatzResearch.WordTrace]
  refine ⟨100196171956613788808742053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66797447971075859205828035 100196171956613788808742053)
  ·
    refine ⟨18786782241865085401639135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100196171956613788808742053 18786782241865085401639135)
    ·
      refine ⟨28180173362797628102458703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18786782241865085401639135 28180173362797628102458703)
      ·
        refine ⟨42270260044196442153688055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28180173362797628102458703 42270260044196442153688055)
        ·
          refine ⟨63405390066294663230532083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42270260044196442153688055 63405390066294663230532083)
          ·
            refine ⟨95108085099441994845798125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63405390066294663230532083 95108085099441994845798125)
            ·
              refine ⟨35665531912290748067174297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95108085099441994845798125 35665531912290748067174297)
              ·
                refine ⟨26749148934218061050380723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35665531912290748067174297 26749148934218061050380723)
                ·
                  refine ⟨40123723401327091575571085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26749148934218061050380723 40123723401327091575571085)
                  ·
                    refine ⟨15046396275497659340839157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40123723401327091575571085 15046396275497659340839157)
                    ·
                      refine ⟨1410599650827905563203671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15046396275497659340839157 1410599650827905563203671)
                      ·
                        rfl

theorem cell23_2747133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_2747133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747133 prefixEnd_2747133 := by exact prefixLift 2747133
  have htrace : WordTrace (prefixWord ++ tailWord_2747133) baseStart_2747133 baseEnd_2747133 := by
    simpa [prefixWord, tailWord_2747133, baseEnd_2747133] using wordTrace_append hprefix tailTrace_2747133
  have hstable : (prefixWord ++ tailWord_2747133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747133).length < 2 ^ (prefixWord ++ tailWord_2747133).sum := by decide
  have hdescent : baseEnd_2747133 < baseStart_2747133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747153 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 7]
def baseStart_2747153 : Nat := 118140960795 + 2747153 * 2 ^ 59
def prefixEnd_2747153 : Nat := 4983230072969 + 3 ^ 40 * 2747153 * 2
def baseEnd_2747153 : Nat := 156734435604555053883731

theorem tailTrace_2747153 : CollatzResearch.WordTrace tailWord_2747153 prefixEnd_2747153 156734435604555053883731 := by
  unfold tailWord_2747153
  simp only [CollatzResearch.WordTrace]
  refine ⟨100196901416541332224470113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66797934277694221482980075 100196901416541332224470113)
  ·
    refine ⟨75147676062405999168352585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100196901416541332224470113 75147676062405999168352585)
    ·
      refine ⟨56360757046804499376264439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75147676062405999168352585 56360757046804499376264439)
      ·
        refine ⟨84541135570206749064396659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56360757046804499376264439 84541135570206749064396659)
        ·
          refine ⟨126811703355310123596594989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84541135570206749064396659 126811703355310123596594989)
          ·
            refine ⟨47554388758241296348723121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126811703355310123596594989 47554388758241296348723121)
            ·
              refine ⟨35665791568680972261542341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47554388758241296348723121 35665791568680972261542341)
              ·
                refine ⟨6687335919127682299039189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35665791568680972261542341 6687335919127682299039189)
                ·
                  refine ⟨156734435604555053883731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6687335919127682299039189 156734435604555053883731)
                  ·
                    rfl

theorem cell23_2747153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 7].length) (baseStart_2747153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747153 prefixEnd_2747153 := by exact prefixLift 2747153
  have htrace : WordTrace (prefixWord ++ tailWord_2747153) baseStart_2747153 baseEnd_2747153 := by
    simpa [prefixWord, tailWord_2747153, baseEnd_2747153] using wordTrace_append hprefix tailTrace_2747153
  have hstable : (prefixWord ++ tailWord_2747153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747153).length < 2 ^ (prefixWord ++ tailWord_2747153).sum := by decide
  have hdescent : baseEnd_2747153 < baseStart_2747153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747180 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 3]
def baseStart_2747180 : Nat := 118140960795 + 2747180 * 2 ^ 59
def prefixEnd_2747180 : Nat := 4983230072969 + 3 ^ 40 * 2747180 * 2
def baseEnd_2747180 : Nat := 1410623784418666879315955

theorem tailTrace_2747180 : CollatzResearch.WordTrace tailWord_2747180 prefixEnd_2747180 1410623784418666879315955 := by
  unfold tailWord_2747180
  simp only [CollatzResearch.WordTrace]
  refine ⟨50098943093721757917851497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66798590791629010557135329 50098943093721757917851497)
  ·
    refine ⟨37574207320291318438388623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50098943093721757917851497 37574207320291318438388623)
    ·
      refine ⟨56361310980436977657582935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37574207320291318438388623 56361310980436977657582935)
      ·
        refine ⟨84541966470655466486374403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56361310980436977657582935 84541966470655466486374403)
        ·
          refine ⟨126812949705983199729561605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84541966470655466486374403 126812949705983199729561605)
          ·
            refine ⟨23777428069871849949292801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126812949705983199729561605 23777428069871849949292801)
            ·
              refine ⟨17833071052403887461969601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23777428069871849949292801 17833071052403887461969601)
              ·
                refine ⟨13374803289302915596477201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17833071052403887461969601 13374803289302915596477201)
                ·
                  refine ⟨10031102466977186697357901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13374803289302915596477201 10031102466977186697357901)
                  ·
                    refine ⟨3761663425116445011509213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10031102466977186697357901 3761663425116445011509213)
                    ·
                      refine ⟨1410623784418666879315955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3761663425116445011509213 1410623784418666879315955)
                      ·
                        rfl

theorem cell23_2747180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_2747180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747180 prefixEnd_2747180 := by exact prefixLift 2747180
  have htrace : WordTrace (prefixWord ++ tailWord_2747180) baseStart_2747180 baseEnd_2747180 := by
    simpa [prefixWord, tailWord_2747180, baseEnd_2747180] using wordTrace_append hprefix tailTrace_2747180
  have hstable : (prefixWord ++ tailWord_2747180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747180).length < 2 ^ (prefixWord ++ tailWord_2747180).sum := by decide
  have hdescent : baseEnd_2747180 < baseStart_2747180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747187 : List Nat := [1, 1, 1, 2, 6, 2, 1, 4, 5]
def baseStart_2747187 : Nat := 118140960795 + 2747187 * 2 ^ 59
def prefixEnd_2747187 : Nat := 4983230072969 + 3 ^ 40 * 2747187 * 2
def baseEnd_2747187 : Nat := 156736375420360927992047

theorem tailTrace_2747187 : CollatzResearch.WordTrace tailWord_2747187 prefixEnd_2747187 156736375420360927992047 := by
  unfold tailWord_2747187
  simp only [CollatzResearch.WordTrace]
  refine ⟨100198141498418156031207815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66798760998945437354138543 100198141498418156031207815)
  ·
    refine ⟨150297212247627234046811723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100198141498418156031207815 150297212247627234046811723)
    ·
      refine ⟨225445818371440851070217585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150297212247627234046811723 225445818371440851070217585)
      ·
        refine ⟨169084363778580638302663189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225445818371440851070217585 169084363778580638302663189)
        ·
          refine ⟨7925829552120967420437337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 169084363778580638302663189 7925829552120967420437337)
          ·
            refine ⟨5944372164090725565328003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7925829552120967420437337 5944372164090725565328003)
            ·
              refine ⟨8916558246136088347992005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5944372164090725565328003 8916558246136088347992005)
              ·
                refine ⟨1671854671150516565248501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8916558246136088347992005 1671854671150516565248501)
                ·
                  refine ⟨156736375420360927992047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1671854671150516565248501 156736375420360927992047)
                  ·
                    rfl

theorem cell23_2747187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 5].length) (baseStart_2747187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747187 prefixEnd_2747187 := by exact prefixLift 2747187
  have htrace : WordTrace (prefixWord ++ tailWord_2747187) baseStart_2747187 baseEnd_2747187 := by
    simpa [prefixWord, tailWord_2747187, baseEnd_2747187] using wordTrace_append hprefix tailTrace_2747187
  have hstable : (prefixWord ++ tailWord_2747187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747187).length < 2 ^ (prefixWord ++ tailWord_2747187).sum := by decide
  have hdescent : baseEnd_2747187 < baseStart_2747187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747204 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 7]
def baseStart_2747204 : Nat := 118140960795 + 2747204 * 2 ^ 59
def prefixEnd_2747204 : Nat := 4983230072969 + 3 ^ 40 * 2747204 * 2
def baseEnd_2747204 : Nat := 156737345328263865046205

theorem tailTrace_2747204 : CollatzResearch.WordTrace tailWord_2747204 prefixEnd_2747204 156737345328263865046205 := by
  unfold tailWord_2747204
  simp only [CollatzResearch.WordTrace]
  refine ⟨50099380769678283967288333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66799174359571045289717777 50099380769678283967288333)
  ·
    refine ⟨18787267788629356487733125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50099380769678283967288333 18787267788629356487733125)
    ·
      refine ⟨3522612710368004341449961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18787267788629356487733125 3522612710368004341449961)
      ·
        refine ⟨2641959532776003256087471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3522612710368004341449961 2641959532776003256087471)
        ·
          refine ⟨3962939299164004884131207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2641959532776003256087471 3962939299164004884131207)
          ·
            refine ⟨5944408948746007326196811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3962939299164004884131207 5944408948746007326196811)
            ·
              refine ⟨8916613423119010989295217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5944408948746007326196811 8916613423119010989295217)
              ·
                refine ⟨6687460067339258241971413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8916613423119010989295217 6687460067339258241971413)
                ·
                  refine ⟨156737345328263865046205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6687460067339258241971413 156737345328263865046205)
                  ·
                    rfl

theorem cell23_2747204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_2747204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747204 prefixEnd_2747204 := by exact prefixLift 2747204
  have htrace : WordTrace (prefixWord ++ tailWord_2747204) baseStart_2747204 baseEnd_2747204 := by
    simpa [prefixWord, tailWord_2747204, baseEnd_2747204] using wordTrace_append hprefix tailTrace_2747204
  have hstable : (prefixWord ++ tailWord_2747204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747204).length < 2 ^ (prefixWord ++ tailWord_2747204).sum := by decide
  have hdescent : baseEnd_2747204 < baseStart_2747204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747237 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 2, 4, 2]
def baseStart_2747237 : Nat := 118140960795 + 2747237 * 2 ^ 59
def prefixEnd_2747237 : Nat := 4983230072969 + 3 ^ 40 * 2747237 * 2
def baseEnd_2747237 : Nat := 1410653052815973156303193

theorem tailTrace_2747237 : CollatzResearch.WordTrace tailWord_2747237 prefixEnd_2747237 1410653052815973156303193 := by
  unfold tailWord_2747237
  simp only [CollatzResearch.WordTrace]
  refine ⟨100199965148237014570527965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66799976765491343047018643 100199965148237014570527965)
  ·
    refine ⟨37574986930588880463947987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100199965148237014570527965 37574986930588880463947987)
    ·
      refine ⟨56362480395883320695921981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37574986930588880463947987 56362480395883320695921981)
      ·
        refine ⟨21135930148456245260970743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56362480395883320695921981 21135930148456245260970743)
        ·
          refine ⟨31703895222684367891456115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21135930148456245260970743 31703895222684367891456115)
          ·
            refine ⟨47555842834026551837184173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31703895222684367891456115 47555842834026551837184173)
            ·
              refine ⟨17833441062759956938944065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47555842834026551837184173 17833441062759956938944065)
              ·
                refine ⟨13375080797069967704208049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17833441062759956938944065 13375080797069967704208049)
                ·
                  refine ⟨10031310597802475778156037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13375080797069967704208049 10031310597802475778156037)
                  ·
                    refine ⟨1880870737087964208404257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10031310597802475778156037 1880870737087964208404257)
                    ·
                      refine ⟨1410653052815973156303193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1880870737087964208404257 1410653052815973156303193)
                      ·
                        rfl

theorem cell23_2747237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_2747237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747237 prefixEnd_2747237 := by exact prefixLift 2747237
  have htrace : WordTrace (prefixWord ++ tailWord_2747237) baseStart_2747237 baseEnd_2747237 := by
    simpa [prefixWord, tailWord_2747237, baseEnd_2747237] using wordTrace_append hprefix tailTrace_2747237
  have hstable : (prefixWord ++ tailWord_2747237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747237).length < 2 ^ (prefixWord ++ tailWord_2747237).sum := by decide
  have hdescent : baseEnd_2747237 < baseStart_2747237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747260 : List Nat := [2, 2, 2, 1, 1, 1, 1, 7, 6]
def baseStart_2747260 : Nat := 118140960795 + 2747260 * 2 ^ 59
def prefixEnd_2747260 : Nat := 4983230072969 + 3 ^ 40 * 2747260 * 2
def baseEnd_2747260 : Nat := 156740540319002951812843

theorem tailTrace_2747260 : CollatzResearch.WordTrace tailWord_2747260 prefixEnd_2747260 156740540319002951812843 := by
  unfold tailWord_2747260
  simp only [CollatzResearch.WordTrace]
  refine ⟨50100402013576844749307617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66800536018102459665743489 50100402013576844749307617)
  ·
    refine ⟨37575301510182633561980713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50100402013576844749307617 37575301510182633561980713)
    ·
      refine ⟨28181476132636975171485535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37575301510182633561980713 28181476132636975171485535)
      ·
        refine ⟨42272214198955462757228303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28181476132636975171485535 42272214198955462757228303)
        ·
          refine ⟨63408321298433194135842455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42272214198955462757228303 63408321298433194135842455)
          ·
            refine ⟨95112481947649791203763683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63408321298433194135842455 95112481947649791203763683)
            ·
              refine ⟨142668722921474686805645525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95112481947649791203763683 142668722921474686805645525)
              ·
                refine ⟨3343798193472062972007317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 142668722921474686805645525 3343798193472062972007317)
                ·
                  refine ⟨156740540319002951812843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3343798193472062972007317 156740540319002951812843)
                  ·
                    rfl

theorem cell23_2747260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 6].length) (baseStart_2747260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747260 prefixEnd_2747260 := by exact prefixLift 2747260
  have htrace : WordTrace (prefixWord ++ tailWord_2747260) baseStart_2747260 baseEnd_2747260 := by
    simpa [prefixWord, tailWord_2747260, baseEnd_2747260] using wordTrace_append hprefix tailTrace_2747260
  have hstable : (prefixWord ++ tailWord_2747260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747260).length < 2 ^ (prefixWord ++ tailWord_2747260).sum := by decide
  have hdescent : baseEnd_2747260 < baseStart_2747260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747298 : List Nat := [3, 3, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_2747298 : Nat := 118140960795 + 2747298 * 2 ^ 59
def prefixEnd_2747298 : Nat := 4983230072969 + 3 ^ 40 * 2747298 * 2
def baseEnd_2747298 : Nat := 470228125045299139213471

theorem tailTrace_2747298 : CollatzResearch.WordTrace tailWord_2747298 prefixEnd_2747298 470228125045299139213471 := by
  unfold tailWord_2747298
  simp only [CollatzResearch.WordTrace]
  refine ⟨25050547500254005497124637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66801460000677347992332365 25050547500254005497124637)
  ·
    refine ⟨9393955312595252061421739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25050547500254005497124637 9393955312595252061421739)
    ·
      refine ⟨14090932968892878092132609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9393955312595252061421739 14090932968892878092132609)
      ·
        refine ⟨10568199726669658569099457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14090932968892878092132609 10568199726669658569099457)
        ·
          refine ⟨7926149795002243926824593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10568199726669658569099457 7926149795002243926824593)
          ·
            refine ⟨5944612346251682945118445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7926149795002243926824593 5944612346251682945118445)
            ·
              refine ⟨2229229629844381104419417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5944612346251682945118445 2229229629844381104419417)
              ·
                refine ⟨1671922222383285828314563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2229229629844381104419417 1671922222383285828314563)
                ·
                  refine ⟨2507883333574928742471845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1671922222383285828314563 2507883333574928742471845)
                  ·
                    refine ⟨470228125045299139213471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2507883333574928742471845 470228125045299139213471)
                    ·
                      rfl

theorem cell23_2747298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_2747298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747298 prefixEnd_2747298 := by exact prefixLift 2747298
  have htrace : WordTrace (prefixWord ++ tailWord_2747298) baseStart_2747298 baseEnd_2747298 := by
    simpa [prefixWord, tailWord_2747298, baseEnd_2747298] using wordTrace_append hprefix tailTrace_2747298
  have hstable : (prefixWord ++ tailWord_2747298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747298).length < 2 ^ (prefixWord ++ tailWord_2747298).sum := by decide
  have hdescent : baseEnd_2747298 < baseStart_2747298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747327 : List Nat := [1, 1, 2, 2, 2, 1, 2, 6, 1, 1, 4]
def baseStart_2747327 : Nat := 118140960795 + 2747327 * 2 ^ 59
def prefixEnd_2747327 : Nat := 4983230072969 + 3 ^ 40 * 2747327 * 2
def baseEnd_2747327 : Nat := 1410699266074877804177779

theorem tailTrace_2747327 : CollatzResearch.WordTrace tailWord_2747327 prefixEnd_2747327 1410699266074877804177779 := by
  unfold tailWord_2747327
  simp only [CollatzResearch.WordTrace]
  refine ⟨100203247717910959941304235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66802165145273973294202823 100203247717910959941304235)
  ·
    refine ⟨150304871576866439911956353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100203247717910959941304235 150304871576866439911956353)
    ·
      refine ⟨112728653682649829933967265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150304871576866439911956353 112728653682649829933967265)
      ·
        refine ⟨84546490261987372450475449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112728653682649829933967265 84546490261987372450475449)
        ·
          refine ⟨63409867696490529337856587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84546490261987372450475449 63409867696490529337856587)
          ·
            refine ⟨95114801544735794006784881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63409867696490529337856587 95114801544735794006784881)
            ·
              refine ⟨71336101158551845505088661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95114801544735794006784881 71336101158551845505088661)
              ·
                refine ⟨3343879741807117758051031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71336101158551845505088661 3343879741807117758051031)
                ·
                  refine ⟨5015819612710676637076547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3343879741807117758051031 5015819612710676637076547)
                  ·
                    refine ⟨7523729419066014955614821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5015819612710676637076547 7523729419066014955614821)
                    ·
                      refine ⟨1410699266074877804177779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7523729419066014955614821 1410699266074877804177779)
                      ·
                        rfl

theorem cell23_2747327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_2747327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747327 prefixEnd_2747327 := by exact prefixLift 2747327
  have htrace : WordTrace (prefixWord ++ tailWord_2747327) baseStart_2747327 baseEnd_2747327 := by
    simpa [prefixWord, tailWord_2747327, baseEnd_2747327] using wordTrace_append hprefix tailTrace_2747327
  have hstable : (prefixWord ++ tailWord_2747327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747327).length < 2 ^ (prefixWord ++ tailWord_2747327).sum := by decide
  have hdescent : baseEnd_2747327 < baseStart_2747327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747354 : List Nat := [3, 1, 1, 2, 4, 1, 1, 4, 2, 4]
def baseStart_2747354 : Nat := 118140960795 + 2747354 * 2 ^ 59
def prefixEnd_2747354 : Nat := 4983230072969 + 3 ^ 40 * 2747354 * 2
def baseEnd_2747354 : Nat := 470237710017516399513385

theorem tailTrace_2747354 : CollatzResearch.WordTrace tailWord_2747354 prefixEnd_2747354 470237710017516399513385 := by
  unfold tailWord_2747354
  simp only [CollatzResearch.WordTrace]
  refine ⟨25051058122203285888134279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66802821659208762368358077 25051058122203285888134279)
  ·
    refine ⟨37576587183304928832201419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25051058122203285888134279 37576587183304928832201419)
    ·
      refine ⟨56364880774957393248302129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37576587183304928832201419 56364880774957393248302129)
      ·
        refine ⟨42273660581218044936226597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56364880774957393248302129 42273660581218044936226597)
        ·
          refine ⟨7926311358978383425542487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42273660581218044936226597 7926311358978383425542487)
          ·
            refine ⟨11889467038467575138313731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7926311358978383425542487 11889467038467575138313731)
            ·
              refine ⟨17834200557701362707470597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11889467038467575138313731 17834200557701362707470597)
              ·
                refine ⟨3343912604569005507650737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17834200557701362707470597 3343912604569005507650737)
                ·
                  refine ⟨2507934453426754130738053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3343912604569005507650737 2507934453426754130738053)
                  ·
                    refine ⟨470237710017516399513385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2507934453426754130738053 470237710017516399513385)
                    ·
                      rfl

theorem cell23_2747354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_2747354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747354 prefixEnd_2747354 := by exact prefixLift 2747354
  have htrace : WordTrace (prefixWord ++ tailWord_2747354) baseStart_2747354 baseEnd_2747354 := by
    simpa [prefixWord, tailWord_2747354, baseEnd_2747354] using wordTrace_append hprefix tailTrace_2747354
  have hstable : (prefixWord ++ tailWord_2747354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747354).length < 2 ^ (prefixWord ++ tailWord_2747354).sum := by decide
  have hdescent : baseEnd_2747354 < baseStart_2747354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747367 : List Nat := [1, 1, 5, 2, 2, 1, 3, 8]
def baseStart_2747367 : Nat := 118140960795 + 2747367 * 2 ^ 59
def prefixEnd_2747367 : Nat := 4983230072969 + 3 ^ 40 * 2747367 * 2
def baseEnd_2747367 : Nat := 52248881677816949913985

theorem tailTrace_2747367 : CollatzResearch.WordTrace tailWord_2747367 prefixEnd_2747367 52248881677816949913985 := by
  unfold tailWord_2747367
  simp only [CollatzResearch.WordTrace]
  refine ⟨100204706637766046772760355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66803137758510697848506903 100204706637766046772760355)
  ·
    refine ⟨150307059956649070159140533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100204706637766046772760355 150307059956649070159140533)
    ·
      refine ⟨14091286870935850327419425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150307059956649070159140533 14091286870935850327419425)
      ·
        refine ⟨10568465153201887745564569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14091286870935850327419425 10568465153201887745564569)
        ·
          refine ⟨7926348864901415809173427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10568465153201887745564569 7926348864901415809173427)
          ·
            refine ⟨11889523297352123713760141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7926348864901415809173427 11889523297352123713760141)
            ·
              refine ⟨4458571236507046392660053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11889523297352123713760141 4458571236507046392660053)
              ·
                refine ⟨52248881677816949913985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4458571236507046392660053 52248881677816949913985)
                ·
                  rfl

theorem cell23_2747367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 8].length) (baseStart_2747367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747367 prefixEnd_2747367 := by exact prefixLift 2747367
  have htrace : WordTrace (prefixWord ++ tailWord_2747367) baseStart_2747367 baseEnd_2747367 := by
    simpa [prefixWord, tailWord_2747367, baseEnd_2747367] using wordTrace_append hprefix tailTrace_2747367
  have hstable : (prefixWord ++ tailWord_2747367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747367).length < 2 ^ (prefixWord ++ tailWord_2747367).sum := by decide
  have hdescent : baseEnd_2747367 < baseStart_2747367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747427 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 2, 6]
def baseStart_2747427 : Nat := 118140960795 + 2747427 * 2 ^ 59
def prefixEnd_2747427 : Nat := 4983230072969 + 3 ^ 40 * 2747427 * 2
def baseEnd_2747427 : Nat := 470250204713442470975773

theorem tailTrace_2747427 : CollatzResearch.WordTrace tailWord_2747427 prefixEnd_2747427 470250204713442470975773 := by
  unfold tailWord_2747427
  simp only [CollatzResearch.WordTrace]
  refine ⟨100206895017548677019944535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66804596678365784679963023 100206895017548677019944535)
  ·
    refine ⟨150310342526323015529916803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100206895017548677019944535 150310342526323015529916803)
    ·
      refine ⟨225465513789484523294875205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150310342526323015529916803 225465513789484523294875205)
      ·
        refine ⟨42274783835528348117789101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225465513789484523294875205 42274783835528348117789101)
        ·
          refine ⟨15853043938323130544170913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42274783835528348117789101 15853043938323130544170913)
          ·
            refine ⟨11889782953742347908128185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15853043938323130544170913 11889782953742347908128185)
            ·
              refine ⟨8917337215306760931096139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11889782953742347908128185 8917337215306760931096139)
              ·
                refine ⟨13376005822960141396644209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8917337215306760931096139 13376005822960141396644209)
                ·
                  refine ⟨10032004367220106047483157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13376005822960141396644209 10032004367220106047483157)
                  ·
                    refine ⟨470250204713442470975773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10032004367220106047483157 470250204713442470975773)
                    ·
                      rfl

theorem cell23_2747427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 6].length) (baseStart_2747427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747427 prefixEnd_2747427 := by exact prefixLift 2747427
  have htrace : WordTrace (prefixWord ++ tailWord_2747427) baseStart_2747427 baseEnd_2747427 := by
    simpa [prefixWord, tailWord_2747427, baseEnd_2747427] using wordTrace_append hprefix tailTrace_2747427
  have hstable : (prefixWord ++ tailWord_2747427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747427).length < 2 ^ (prefixWord ++ tailWord_2747427).sum := by decide
  have hdescent : baseEnd_2747427 < baseStart_2747427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747438 : List Nat := [4, 1, 3, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_2747438 : Nat := 118140960795 + 2747438 * 2 ^ 59
def prefixEnd_2747438 : Nat := 4983230072969 + 3 ^ 40 * 2747438 * 2
def baseEnd_2747438 : Nat := 1410756262427526869889769

theorem tailTrace_2747438 : CollatzResearch.WordTrace tailWord_2747438 prefixEnd_2747438 1410756262427526869889769 := by
  unfold tailWord_2747438
  simp only [CollatzResearch.WordTrace]
  refine ⟨12525912027563603237324371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66804864147005883932396645 12525912027563603237324371)
  ·
    refine ⟨18788868041345404855986557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12525912027563603237324371 18788868041345404855986557)
    ·
      refine ⟨7045825515504526820994959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18788868041345404855986557 7045825515504526820994959)
      ·
        refine ⟨10568738273256790231492439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7045825515504526820994959 10568738273256790231492439)
        ·
          refine ⟨15853107409885185347238659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10568738273256790231492439 15853107409885185347238659)
          ·
            refine ⟨23779661114827778020857989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15853107409885185347238659 23779661114827778020857989)
            ·
              refine ⟨4458686459030208378910873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23779661114827778020857989 4458686459030208378910873)
              ·
                refine ⟨3344014844272656284183155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4458686459030208378910873 3344014844272656284183155)
                ·
                  refine ⟨5016022266408984426274733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3344014844272656284183155 5016022266408984426274733)
                  ·
                    refine ⟨1881008349903369159853025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5016022266408984426274733 1881008349903369159853025)
                    ·
                      refine ⟨1410756262427526869889769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1881008349903369159853025 1410756262427526869889769)
                      ·
                        rfl

theorem cell23_2747438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_2747438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747438 prefixEnd_2747438 := by exact prefixLift 2747438
  have htrace : WordTrace (prefixWord ++ tailWord_2747438) baseStart_2747438 baseEnd_2747438 := by
    simpa [prefixWord, tailWord_2747438, baseEnd_2747438] using wordTrace_append hprefix tailTrace_2747438
  have hstable : (prefixWord ++ tailWord_2747438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747438).length < 2 ^ (prefixWord ++ tailWord_2747438).sum := by decide
  have hdescent : baseEnd_2747438 < baseStart_2747438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747454 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_2747454 : Nat := 118140960795 + 2747454 * 2 ^ 59
def prefixEnd_2747454 : Nat := 4983230072969 + 3 ^ 40 * 2747454 * 2
def baseEnd_2747454 : Nat := 1410764478117998807289695

theorem tailTrace_2747454 : CollatzResearch.WordTrace tailWord_2747454 prefixEnd_2747454 1410764478117998807289695 := by
  unfold tailWord_2747454
  simp only [CollatzResearch.WordTrace]
  refine ⟨12525984973556357578897177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66805253192300573754118277 12525984973556357578897177)
  ·
    refine ⟨9394488730167268184172883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12525984973556357578897177 9394488730167268184172883)
    ·
      refine ⟨14091733095250902276259325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9394488730167268184172883 14091733095250902276259325)
      ·
        refine ⟨5284399910719088353597247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14091733095250902276259325 5284399910719088353597247)
        ·
          refine ⟨7926599866078632530395871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5284399910719088353597247 7926599866078632530395871)
          ·
            refine ⟨11889899799117948795593807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7926599866078632530395871 11889899799117948795593807)
            ·
              refine ⟨17834849698676923193390711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11889899799117948795593807 17834849698676923193390711)
              ·
                refine ⟨26752274548015384790086067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17834849698676923193390711 26752274548015384790086067)
                ·
                  refine ⟨40128411822023077185129101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26752274548015384790086067 40128411822023077185129101)
                  ·
                    refine ⟨15048154433258653944423413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40128411822023077185129101 15048154433258653944423413)
                    ·
                      refine ⟨1410764478117998807289695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15048154433258653944423413 1410764478117998807289695)
                      ·
                        rfl

theorem cell23_2747454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_2747454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747454 prefixEnd_2747454 := by exact prefixLift 2747454
  have htrace : WordTrace (prefixWord ++ tailWord_2747454) baseStart_2747454 baseEnd_2747454 := by
    simpa [prefixWord, tailWord_2747454, baseEnd_2747454] using wordTrace_append hprefix tailTrace_2747454
  have hstable : (prefixWord ++ tailWord_2747454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747454).length < 2 ^ (prefixWord ++ tailWord_2747454).sum := by decide
  have hdescent : baseEnd_2747454 < baseStart_2747454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747474 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 7]
def baseStart_2747474 : Nat := 118140960795 + 2747474 * 2 ^ 59
def prefixEnd_2747474 : Nat := 4983230072969 + 3 ^ 40 * 2747474 * 2
def baseEnd_2747474 : Nat := 156752749747898747671067

theorem tailTrace_2747474 : CollatzResearch.WordTrace tailWord_2747474 prefixEnd_2747474 156752749747898747671067 := by
  unfold tailWord_2747474
  simp only [CollatzResearch.WordTrace]
  refine ⟨25052152312094601011726369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66805739498918936031270317 25052152312094601011726369)
  ·
    refine ⟨18789114234070950758794777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25052152312094601011726369 18789114234070950758794777)
    ·
      refine ⟨14091835675553213069096083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18789114234070950758794777 14091835675553213069096083)
      ·
        refine ⟨21137753513329819603644125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14091835675553213069096083 21137753513329819603644125)
        ·
          refine ⟨7926657567498682351366547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21137753513329819603644125 7926657567498682351366547)
          ·
            refine ⟨11889986351248023527049821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7926657567498682351366547 11889986351248023527049821)
            ·
              refine ⟨4458744881718008822643683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11889986351248023527049821 4458744881718008822643683)
              ·
                refine ⟨6688117322577013233965525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4458744881718008822643683 6688117322577013233965525)
                ·
                  refine ⟨156752749747898747671067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6688117322577013233965525 156752749747898747671067)
                  ·
                    rfl

theorem cell23_2747474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_2747474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747474 prefixEnd_2747474 := by exact prefixLift 2747474
  have htrace : WordTrace (prefixWord ++ tailWord_2747474) baseStart_2747474 baseEnd_2747474 := by
    simpa [prefixWord, tailWord_2747474, baseEnd_2747474] using wordTrace_append hprefix tailTrace_2747474
  have hstable : (prefixWord ++ tailWord_2747474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747474).length < 2 ^ (prefixWord ++ tailWord_2747474).sum := by decide
  have hdescent : baseEnd_2747474 < baseStart_2747474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747484 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_2747484 : Nat := 118140960795 + 2747484 * 2 ^ 59
def prefixEnd_2747484 : Nat := 4983230072969 + 3 ^ 40 * 2747484 * 2
def baseEnd_2747484 : Nat := 1410779882537633689914557

theorem tailTrace_2747484 : CollatzResearch.WordTrace tailWord_2747484 prefixEnd_2747484 1410779882537633689914557 := by
  unfold tailWord_2747484
  simp only [CollatzResearch.WordTrace]
  refine ⟨50104486989171087877384753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66805982652228117169846337 50104486989171087877384753)
  ·
    refine ⟨37578365241878315908038565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50104486989171087877384753 37578365241878315908038565)
    ·
      refine ⟨7045943482852184232757231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37578365241878315908038565 7045943482852184232757231)
      ·
        refine ⟨10568915224278276349135847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7045943482852184232757231 10568915224278276349135847)
        ·
          refine ⟨15853372836417414523703771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10568915224278276349135847 15853372836417414523703771)
          ·
            refine ⟨23780059254626121785555657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15853372836417414523703771 23780059254626121785555657)
            ·
              refine ⟨17835044440969591339166743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23780059254626121785555657 17835044440969591339166743)
              ·
                refine ⟨26752566661454387008750115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17835044440969591339166743 26752566661454387008750115)
                ·
                  refine ⟨40128849992181580513125173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26752566661454387008750115 40128849992181580513125173)
                  ·
                    refine ⟨3762079686767023173105485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40128849992181580513125173 3762079686767023173105485)
                    ·
                      refine ⟨1410779882537633689914557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3762079686767023173105485 1410779882537633689914557)
                      ·
                        rfl

theorem cell23_2747484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_2747484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747484 prefixEnd_2747484 := by exact prefixLift 2747484
  have htrace : WordTrace (prefixWord ++ tailWord_2747484) baseStart_2747484 baseEnd_2747484 := by
    simpa [prefixWord, tailWord_2747484, baseEnd_2747484] using wordTrace_append hprefix tailTrace_2747484
  have hstable : (prefixWord ++ tailWord_2747484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747484).length < 2 ^ (prefixWord ++ tailWord_2747484).sum := by decide
  have hdescent : baseEnd_2747484 < baseStart_2747484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747487 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 4, 5]
def baseStart_2747487 : Nat := 118140960795 + 2747487 * 2 ^ 59
def prefixEnd_2747487 : Nat := 4983230072969 + 3 ^ 40 * 2747487 * 2
def baseEnd_2747487 : Nat := 470260474326532392725681

theorem tailTrace_2747487 : CollatzResearch.WordTrace tailWord_2747487 prefixEnd_2747487 470260474326532392725681 := by
  unfold tailWord_2747487
  simp only [CollatzResearch.WordTrace]
  refine ⟨100209083397331307267128715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66806055598220871511419143 100209083397331307267128715)
  ·
    refine ⟨150313625095996960900693073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100209083397331307267128715 150313625095996960900693073)
    ·
      refine ⟨112735218821997720675519805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150313625095996960900693073 112735218821997720675519805)
      ·
        refine ⟨42275707058249145253319927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112735218821997720675519805 42275707058249145253319927)
        ·
          refine ⟨63413560587373717879979891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42275707058249145253319927 63413560587373717879979891)
          ·
            refine ⟨95120340881060576819969837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63413560587373717879979891 95120340881060576819969837)
            ·
              refine ⟨35670127830397716307488689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95120340881060576819969837 35670127830397716307488689)
              ·
                refine ⟨26752595872798287230616517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35670127830397716307488689 26752595872798287230616517)
                ·
                  refine ⟨5016111726149678855740597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26752595872798287230616517 5016111726149678855740597)
                  ·
                    refine ⟨470260474326532392725681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5016111726149678855740597 470260474326532392725681)
                    ·
                      rfl

theorem cell23_2747487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 5].length) (baseStart_2747487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747487 prefixEnd_2747487 := by exact prefixLift 2747487
  have htrace : WordTrace (prefixWord ++ tailWord_2747487) baseStart_2747487 baseEnd_2747487 := by
    simpa [prefixWord, tailWord_2747487, baseEnd_2747487] using wordTrace_append hprefix tailTrace_2747487
  have hstable : (prefixWord ++ tailWord_2747487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747487).length < 2 ^ (prefixWord ++ tailWord_2747487).sum := by decide
  have hdescent : baseEnd_2747487 < baseStart_2747487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747504 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 2, 5]
def baseStart_2747504 : Nat := 118140960795 + 2747504 * 2 ^ 59
def prefixEnd_2747504 : Nat := 4983230072969 + 3 ^ 40 * 2747504 * 2
def baseEnd_2747504 : Nat := 470263384050241203888155

theorem tailTrace_2747504 : CollatzResearch.WordTrace tailWord_2747504 prefixEnd_2747504 470263384050241203888155 := by
  unfold tailWord_2747504
  simp only [CollatzResearch.WordTrace]
  refine ⟨50104851719134859585248783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66806468958846479446998377 50104851719134859585248783)
  ·
    refine ⟨75157277578702289377873175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50104851719134859585248783 75157277578702289377873175)
    ·
      refine ⟨112735916368053434066809763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75157277578702289377873175 112735916368053434066809763)
      ·
        refine ⟨169103874552080151100214645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112735916368053434066809763 169103874552080151100214645)
        ·
          refine ⟨15853488239257514165645123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169103874552080151100214645 15853488239257514165645123)
          ·
            refine ⟨23780232358886271248467685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15853488239257514165645123 23780232358886271248467685)
            ·
              refine ⟨4458793567291175859087691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23780232358886271248467685 4458793567291175859087691)
              ·
                refine ⟨6688190350936763788631537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4458793567291175859087691 6688190350936763788631537)
                ·
                  refine ⟨5016142763202572841473653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6688190350936763788631537 5016142763202572841473653)
                  ·
                    refine ⟨470263384050241203888155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5016142763202572841473653 470263384050241203888155)
                    ·
                      rfl

theorem cell23_2747504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 2, 5].length) (baseStart_2747504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747504 prefixEnd_2747504 := by exact prefixLift 2747504
  have htrace : WordTrace (prefixWord ++ tailWord_2747504) baseStart_2747504 baseEnd_2747504 := by
    simpa [prefixWord, tailWord_2747504, baseEnd_2747504] using wordTrace_append hprefix tailTrace_2747504
  have hstable : (prefixWord ++ tailWord_2747504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747504).length < 2 ^ (prefixWord ++ tailWord_2747504).sum := by decide
  have hdescent : baseEnd_2747504 < baseStart_2747504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747525 : List Nat := [1, 3, 1, 1, 7, 1, 2, 2, 5]
def baseStart_2747525 : Nat := 118140960795 + 2747525 * 2 ^ 59
def prefixEnd_2747525 : Nat := 4983230072969 + 3 ^ 40 * 2747525 * 2
def baseEnd_2747525 : Nat := 156755659471607558833541

theorem tailTrace_2747525 : CollatzResearch.WordTrace tailWord_2747525 prefixEnd_2747525 156755659471607558833541 := by
  unfold tailWord_2747525
  simp only [CollatzResearch.WordTrace]
  refine ⟨100210469371193639757012029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66806979580795759838008019 100210469371193639757012029)
  ·
    refine ⟨37578926014197614908879511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100210469371193639757012029 37578926014197614908879511)
    ·
      refine ⟨56368389021296422363319267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37578926014197614908879511 56368389021296422363319267)
      ·
        refine ⟨84552583531944633544978901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56368389021296422363319267 84552583531944633544978901)
        ·
          refine ⟨1981701176529952348710443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 84552583531944633544978901 1981701176529952348710443)
          ·
            refine ⟨2972551764794928523065665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1981701176529952348710443 2972551764794928523065665)
            ·
              refine ⟨2229413823596196392299249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2972551764794928523065665 2229413823596196392299249)
              ·
                refine ⟨1672060367697147294224437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2229413823596196392299249 1672060367697147294224437)
                ·
                  refine ⟨156755659471607558833541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1672060367697147294224437 156755659471607558833541)
                  ·
                    rfl

theorem cell23_2747525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 5].length) (baseStart_2747525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747525 prefixEnd_2747525 := by exact prefixLift 2747525
  have htrace : WordTrace (prefixWord ++ tailWord_2747525) baseStart_2747525 baseEnd_2747525 := by
    simpa [prefixWord, tailWord_2747525, baseEnd_2747525] using wordTrace_append hprefix tailTrace_2747525
  have hstable : (prefixWord ++ tailWord_2747525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747525).length < 2 ^ (prefixWord ++ tailWord_2747525).sum := by decide
  have hdescent : baseEnd_2747525 < baseStart_2747525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747527 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_2747527 : Nat := 118140960795 + 2747527 * 2 ^ 59
def prefixEnd_2747527 : Nat := 4983230072969 + 3 ^ 40 * 2747527 * 2
def baseEnd_2747527 : Nat := 1410801962205777021676859

theorem tailTrace_2747527 : CollatzResearch.WordTrace tailWord_2747527 prefixEnd_2747527 1410801962205777021676859 := by
  unfold tailWord_2747527
  simp only [CollatzResearch.WordTrace]
  refine ⟨100210542317186394098584835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66807028211457596065723223 100210542317186394098584835)
  ·
    refine ⟨150315813475779591147877253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100210542317186394098584835 150315813475779591147877253)
    ·
      refine ⟨28184215026708673340226985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150315813475779591147877253 28184215026708673340226985)
      ·
        refine ⟨21138161270031505005170239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28184215026708673340226985 21138161270031505005170239)
        ·
          refine ⟨31707241905047257507755359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21138161270031505005170239 31707241905047257507755359)
          ·
            refine ⟨47560862857570886261633039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31707241905047257507755359 47560862857570886261633039)
            ·
              refine ⟨71341294286356329392449559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47560862857570886261633039 71341294286356329392449559)
              ·
                refine ⟨107011941429534494088674339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71341294286356329392449559 107011941429534494088674339)
                ·
                  refine ⟨160517912144301741133011509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107011941429534494088674339 160517912144301741133011509)
                  ·
                    refine ⟨15048554263528288231219829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 160517912144301741133011509 15048554263528288231219829)
                    ·
                      refine ⟨1410801962205777021676859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15048554263528288231219829 1410801962205777021676859)
                      ·
                        rfl

theorem cell23_2747527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_2747527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747527 prefixEnd_2747527 := by exact prefixLift 2747527
  have htrace : WordTrace (prefixWord ++ tailWord_2747527) baseStart_2747527 baseEnd_2747527 := by
    simpa [prefixWord, tailWord_2747527, baseEnd_2747527] using wordTrace_append hprefix tailTrace_2747527
  have hstable : (prefixWord ++ tailWord_2747527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747527).length < 2 ^ (prefixWord ++ tailWord_2747527).sum := by decide
  have hdescent : baseEnd_2747527 < baseStart_2747527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747585 : List Nat := [1, 2, 6, 1, 1, 1, 2, 4, 1, 4]
def baseStart_2747585 : Nat := 118140960795 + 2747585 * 2 ^ 59
def prefixEnd_2747585 : Nat := 4983230072969 + 3 ^ 40 * 2747585 * 2
def baseEnd_2747585 : Nat := 470277248027912598250531

theorem tailTrace_2747585 : CollatzResearch.WordTrace tailWord_2747585 prefixEnd_2747585 470277248027912598250531 := by
  unfold tailWord_2747585
  simp only [CollatzResearch.WordTrace]
  refine ⟨100212657750976270004196209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66808438500650846669464139 100212657750976270004196209)
  ·
    refine ⟨75159493313232202503147157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100212657750976270004196209 75159493313232202503147157)
    ·
      refine ⟨3523101249057759492335023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 75159493313232202503147157 3523101249057759492335023)
      ·
        refine ⟨5284651873586639238502535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3523101249057759492335023 5284651873586639238502535)
        ·
          refine ⟨7926977810379958857753803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5284651873586639238502535 7926977810379958857753803)
          ·
            refine ⟨11890466715569938286630705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7926977810379958857753803 11890466715569938286630705)
            ·
              refine ⟨8917850036677453714973029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11890466715569938286630705 8917850036677453714973029)
              ·
                refine ⟨1672096881877022571557443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8917850036677453714973029 1672096881877022571557443)
                ·
                  refine ⟨2508145322815533857336165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672096881877022571557443 2508145322815533857336165)
                  ·
                    refine ⟨470277248027912598250531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2508145322815533857336165 470277248027912598250531)
                    ·
                      rfl

theorem cell23_2747585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_2747585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747585 prefixEnd_2747585 := by exact prefixLift 2747585
  have htrace : WordTrace (prefixWord ++ tailWord_2747585) baseStart_2747585 baseEnd_2747585 := by
    simpa [prefixWord, tailWord_2747585, baseEnd_2747585] using wordTrace_append hprefix tailTrace_2747585
  have hstable : (prefixWord ++ tailWord_2747585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747585).length < 2 ^ (prefixWord ++ tailWord_2747585).sum := by decide
  have hdescent : baseEnd_2747585 < baseStart_2747585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747587 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 7]
def baseStart_2747587 : Nat := 118140960795 + 2747587 * 2 ^ 59
def prefixEnd_2747587 : Nat := 4983230072969 + 3 ^ 40 * 2747587 * 2
def baseEnd_2747587 : Nat := 1410832771045046786926583

theorem tailTrace_2747587 : CollatzResearch.WordTrace tailWord_2747587 prefixEnd_2747587 1410832771045046786926583 := by
  unfold tailWord_2747587
  simp only [CollatzResearch.WordTrace]
  refine ⟨100212730696969024345769015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66808487131312682897179343 100212730696969024345769015)
  ·
    refine ⟨150319096045453536518653523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100212730696969024345769015 150319096045453536518653523)
    ·
      refine ⟨225478644068180304777980285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150319096045453536518653523 225478644068180304777980285)
      ·
        refine ⟨84554491525567614291742607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225478644068180304777980285 84554491525567614291742607)
        ·
          refine ⟨126831737288351421437613911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84554491525567614291742607 126831737288351421437613911)
          ·
            refine ⟨190247605932527132156420867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126831737288351421437613911 190247605932527132156420867)
            ·
              refine ⟨285371408898790698234631301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190247605932527132156420867 285371408898790698234631301)
              ·
                refine ⟨53507139168523255918993369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 285371408898790698234631301 53507139168523255918993369)
                ·
                  refine ⟨40130354376392441939245027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53507139168523255918993369 40130354376392441939245027)
                  ·
                    refine ⟨60195531564588662908867541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40130354376392441939245027 60195531564588662908867541)
                    ·
                      refine ⟨1410832771045046786926583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60195531564588662908867541 1410832771045046786926583)
                      ·
                        rfl

theorem cell23_2747587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_2747587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747587 prefixEnd_2747587 := by exact prefixLift 2747587
  have htrace : WordTrace (prefixWord ++ tailWord_2747587) baseStart_2747587 baseEnd_2747587 := by
    simpa [prefixWord, tailWord_2747587, baseEnd_2747587] using wordTrace_append hprefix tailTrace_2747587
  have hstable : (prefixWord ++ tailWord_2747587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747587).length < 2 ^ (prefixWord ++ tailWord_2747587).sum := by decide
  have hdescent : baseEnd_2747587 < baseStart_2747587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747598 : List Nat := [4, 1, 1, 1, 5, 1, 3, 1, 6]
def baseStart_2747598 : Nat := 118140960795 + 2747598 * 2 ^ 59
def prefixEnd_2747598 : Nat := 4983230072969 + 3 ^ 40 * 2747598 * 2
def baseEnd_2747598 : Nat := 156759824370249582654337

theorem tailTrace_2747598 : CollatzResearch.WordTrace tailWord_2747598 prefixEnd_2747598 156759824370249582654337 := by
  unfold tailWord_2747598
  simp only [CollatzResearch.WordTrace]
  refine ⟨12526641487491146653052431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66808754599952782149612965 12526641487491146653052431)
  ·
    refine ⟨18789962231236719979578647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12526641487491146653052431 18789962231236719979578647)
    ·
      refine ⟨28184943346855079969367971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18789962231236719979578647 28184943346855079969367971)
      ·
        refine ⟨42277415020282619954051957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28184943346855079969367971 42277415020282619954051957)
        ·
          refine ⟨3963507658151495620692371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42277415020282619954051957 3963507658151495620692371)
          ·
            refine ⟨5945261487227243431038557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3963507658151495620692371 5945261487227243431038557)
            ·
              refine ⟨2229473057710216286639459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5945261487227243431038557 2229473057710216286639459)
              ·
                refine ⟨3344209586565324429959189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2229473057710216286639459 3344209586565324429959189)
                ·
                  refine ⟨156759824370249582654337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3344209586565324429959189 156759824370249582654337)
                  ·
                    rfl

theorem cell23_2747598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_2747598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747598 prefixEnd_2747598 := by exact prefixLift 2747598
  have htrace : WordTrace (prefixWord ++ tailWord_2747598) baseStart_2747598 baseEnd_2747598 := by
    simpa [prefixWord, tailWord_2747598, baseEnd_2747598] using wordTrace_append hprefix tailTrace_2747598
  have hstable : (prefixWord ++ tailWord_2747598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747598).length < 2 ^ (prefixWord ++ tailWord_2747598).sum := by decide
  have hdescent : baseEnd_2747598 < baseStart_2747598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747624 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 3, 6]
def baseStart_2747624 : Nat := 118140960795 + 2747624 * 2 ^ 59
def prefixEnd_2747624 : Nat := 4983230072969 + 3 ^ 40 * 2747624 * 2
def baseEnd_2747624 : Nat := 470283923276421047387971

theorem tailTrace_2747624 : CollatzResearch.WordTrace tailWord_2747624 prefixEnd_2747624 470283923276421047387971 := by
  unfold tailWord_2747624
  simp only [CollatzResearch.WordTrace]
  refine ⟨50107040098917489832432963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66809386798556653109910617 50107040098917489832432963)
  ·
    refine ⟨75160560148376234748649445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50107040098917489832432963 75160560148376234748649445)
    ·
      refine ⟨14092605027820544015371771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75160560148376234748649445 14092605027820544015371771)
      ·
        refine ⟨21138907541730816023057657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14092605027820544015371771 21138907541730816023057657)
        ·
          refine ⟨15854180656298112017293243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21138907541730816023057657 15854180656298112017293243)
          ·
            refine ⟨23781270984447168025939865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15854180656298112017293243 23781270984447168025939865)
            ·
              refine ⟨17835953238335376019454899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23781270984447168025939865 17835953238335376019454899)
              ·
                refine ⟨26753929857503064029182349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17835953238335376019454899 26753929857503064029182349)
                ·
                  refine ⟨10032723696563649010943381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26753929857503064029182349 10032723696563649010943381)
                  ·
                    refine ⟨470283923276421047387971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10032723696563649010943381 470283923276421047387971)
                    ·
                      rfl

theorem cell23_2747624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_2747624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747624 prefixEnd_2747624 := by exact prefixLift 2747624
  have htrace : WordTrace (prefixWord ++ tailWord_2747624) baseStart_2747624 baseEnd_2747624 := by
    simpa [prefixWord, tailWord_2747624, baseEnd_2747624] using wordTrace_append hprefix tailTrace_2747624
  have hstable : (prefixWord ++ tailWord_2747624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747624).length < 2 ^ (prefixWord ++ tailWord_2747624).sum := by decide
  have hdescent : baseEnd_2747624 < baseStart_2747624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747636 : List Nat := [2, 6, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2747636 : Nat := 118140960795 + 2747636 * 2 ^ 59
def prefixEnd_2747636 : Nat := 4983230072969 + 3 ^ 40 * 2747636 * 2
def baseEnd_2747636 : Nat := 470285977199039031737953

theorem tailTrace_2747636 : CollatzResearch.WordTrace tailWord_2747636 prefixEnd_2747636 470285977199039031737953 := by
  unfold tailWord_2747636
  simp only [CollatzResearch.WordTrace]
  refine ⟨50107258936895752857151381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66809678582527670476201841 50107258936895752857151381)
  ·
    refine ⟨2348777762666988415178971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50107258936895752857151381 2348777762666988415178971)
    ·
      refine ⟨3523166644000482622768457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2348777762666988415178971 3523166644000482622768457)
      ·
        refine ⟨2642374983000361967076343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3523166644000482622768457 2642374983000361967076343)
        ·
          refine ⟨3963562474500542950614515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2642374983000361967076343 3963562474500542950614515)
          ·
            refine ⟨5945343711750814425921773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3963562474500542950614515 5945343711750814425921773)
            ·
              refine ⟨2229503891906555409720665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5945343711750814425921773 2229503891906555409720665)
              ·
                refine ⟨1672127918929916557290499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2229503891906555409720665 1672127918929916557290499)
                ·
                  refine ⟨2508191878394874835935749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672127918929916557290499 2508191878394874835935749)
                  ·
                    refine ⟨470285977199039031737953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2508191878394874835935749 470285977199039031737953)
                    ·
                      rfl

theorem cell23_2747636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2747636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747636 prefixEnd_2747636 := by exact prefixLift 2747636
  have htrace : WordTrace (prefixWord ++ tailWord_2747636) baseStart_2747636 baseEnd_2747636 := by
    simpa [prefixWord, tailWord_2747636, baseEnd_2747636] using wordTrace_append hprefix tailTrace_2747636
  have hstable : (prefixWord ++ tailWord_2747636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747636).length < 2 ^ (prefixWord ++ tailWord_2747636).sum := by decide
  have hdescent : baseEnd_2747636 < baseStart_2747636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747641 : List Nat := [1, 2, 1, 3, 1, 1, 4, 4, 2, 4]
def baseStart_2747641 : Nat := 118140960795 + 2747641 * 2 ^ 59
def prefixEnd_2747641 : Nat := 4983230072969 + 3 ^ 40 * 2747641 * 2
def baseEnd_2747641 : Nat := 470286833000129858550445

theorem tailTrace_2747641 : CollatzResearch.WordTrace tailWord_2747641 prefixEnd_2747641 470286833000129858550445 := by
  unfold tailWord_2747641
  simp only [CollatzResearch.WordTrace]
  refine ⟨100214700238773391568234777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66809800159182261045489851 100214700238773391568234777)
  ·
    refine ⟨75161025179080043676176083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100214700238773391568234777 75161025179080043676176083)
    ·
      refine ⟨112741537768620065514264125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75161025179080043676176083 112741537768620065514264125)
      ·
        refine ⟨42278076663232524567849047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112741537768620065514264125 42278076663232524567849047)
        ·
          refine ⟨63417114994848786851773571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42278076663232524567849047 63417114994848786851773571)
          ·
            refine ⟨95125672492273180277660357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63417114994848786851773571 95125672492273180277660357)
            ·
              refine ⟨17836063592301221302061317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95125672492273180277660357 17836063592301221302061317)
              ·
                refine ⟨3344261923556478994136497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17836063592301221302061317 3344261923556478994136497)
                ·
                  refine ⟨2508196442667359245602373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3344261923556478994136497 2508196442667359245602373)
                  ·
                    refine ⟨470286833000129858550445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2508196442667359245602373 470286833000129858550445)
                    ·
                      rfl

theorem cell23_2747641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 4].length) (baseStart_2747641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747641 prefixEnd_2747641 := by exact prefixLift 2747641
  have htrace : WordTrace (prefixWord ++ tailWord_2747641) baseStart_2747641 baseEnd_2747641 := by
    simpa [prefixWord, tailWord_2747641, baseEnd_2747641] using wordTrace_append hprefix tailTrace_2747641
  have hstable : (prefixWord ++ tailWord_2747641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747641).length < 2 ^ (prefixWord ++ tailWord_2747641).sum := by decide
  have hdescent : baseEnd_2747641 < baseStart_2747641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747685 : List Nat := [1, 3, 1, 2, 4, 2, 3, 1, 1, 2, 3]
def baseStart_2747685 : Nat := 118140960795 + 2747685 * 2 ^ 59
def prefixEnd_2747685 : Nat := 4983230072969 + 3 ^ 40 * 2747685 * 2
def baseEnd_2747685 : Nat := 1410883092149187403501133

theorem tailTrace_2747685 : CollatzResearch.WordTrace tailWord_2747685 prefixEnd_2747685 1410883092149187403501133 := by
  unfold tailWord_2747685
  simp only [CollatzResearch.WordTrace]
  refine ⟨100216305050613987082836509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66810870033742658055224339 100216305050613987082836509)
  ·
    refine ⟨37581114393980245156063691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100216305050613987082836509 37581114393980245156063691)
    ·
      refine ⟨56371671590970367734095537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37581114393980245156063691 56371671590970367734095537)
      ·
        refine ⟨42278753693227775800571653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56371671590970367734095537 42278753693227775800571653)
        ·
          refine ⟨7927266317480207962607185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42278753693227775800571653 7927266317480207962607185)
          ·
            refine ⟨5945449738110155971955389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7927266317480207962607185 5945449738110155971955389)
            ·
              refine ⟨2229543651791308489483271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5945449738110155971955389 2229543651791308489483271)
              ·
                refine ⟨3344315477686962734224907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2229543651791308489483271 3344315477686962734224907)
                ·
                  refine ⟨5016473216530444101337361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3344315477686962734224907 5016473216530444101337361)
                  ·
                    refine ⟨3762354912397833076003021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5016473216530444101337361 3762354912397833076003021)
                    ·
                      refine ⟨1410883092149187403501133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3762354912397833076003021 1410883092149187403501133)
                      ·
                        rfl

theorem cell23_2747685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_2747685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747685 prefixEnd_2747685 := by exact prefixLift 2747685
  have htrace : WordTrace (prefixWord ++ tailWord_2747685) baseStart_2747685 baseEnd_2747685 := by
    simpa [prefixWord, tailWord_2747685, baseEnd_2747685] using wordTrace_append hprefix tailTrace_2747685
  have hstable : (prefixWord ++ tailWord_2747685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747685).length < 2 ^ (prefixWord ++ tailWord_2747685).sum := by decide
  have hdescent : baseEnd_2747685 < baseStart_2747685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747699 : List Nat := [1, 1, 1, 2, 5, 4, 2, 2, 1, 2, 2]
def baseStart_2747699 : Nat := 118140960795 + 2747699 * 2 ^ 59
def prefixEnd_2747699 : Nat := 4983230072969 + 3 ^ 40 * 2747699 * 2
def baseEnd_2747699 : Nat := 1410890280878350348726069

theorem tailTrace_2747699 : CollatzResearch.WordTrace tailWord_2747699 prefixEnd_2747699 1410890280878350348726069 := by
  unfold tailWord_2747699
  simp only [CollatzResearch.WordTrace]
  refine ⟨100216815672563267473846151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66811210448375511649230767 100216815672563267473846151)
  ·
    refine ⟨150325223508844901210769227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100216815672563267473846151 150325223508844901210769227)
    ·
      refine ⟨225487835263267351816153841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150325223508844901210769227 225487835263267351816153841)
      ·
        refine ⟨169115876447450513862115381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225487835263267351816153841 169115876447450513862115381)
        ·
          refine ⟨15854613416948485674573317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169115876447450513862115381 15854613416948485674573317)
          ·
            refine ⟨2972740015677841063982497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15854613416948485674573317 2972740015677841063982497)
            ·
              refine ⟨2229555011758380797986873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2972740015677841063982497 2229555011758380797986873)
              ·
                refine ⟨1672166258818785598490155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2229555011758380797986873 1672166258818785598490155)
                ·
                  refine ⟨2508249388228178397735233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672166258818785598490155 2508249388228178397735233)
                  ·
                    refine ⟨1881187041171133798301425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2508249388228178397735233 1881187041171133798301425)
                    ·
                      refine ⟨1410890280878350348726069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1881187041171133798301425 1410890280878350348726069)
                      ·
                        rfl

theorem cell23_2747699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 1, 2, 2].length) (baseStart_2747699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747699 prefixEnd_2747699 := by exact prefixLift 2747699
  have htrace : WordTrace (prefixWord ++ tailWord_2747699) baseStart_2747699 baseEnd_2747699 := by
    simpa [prefixWord, tailWord_2747699, baseEnd_2747699] using wordTrace_append hprefix tailTrace_2747699
  have hstable : (prefixWord ++ tailWord_2747699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747699).length < 2 ^ (prefixWord ++ tailWord_2747699).sum := by decide
  have hdescent : baseEnd_2747699 < baseStart_2747699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747708 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 3, 3, 2]
def baseStart_2747708 : Nat := 118140960795 + 2747708 * 2 ^ 59
def prefixEnd_2747708 : Nat := 4983230072969 + 3 ^ 40 * 2747708 * 2
def baseEnd_2747708 : Nat := 1410894902204240813513527

theorem tailTrace_2747708 : CollatzResearch.WordTrace tailWord_2747708 prefixEnd_2747708 1410894902204240813513527 := by
  unfold tailWord_2747708
  simp only [CollatzResearch.WordTrace]
  refine ⟨50108571964765331005461889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66811429286353774673949185 50108571964765331005461889)
  ·
    refine ⟨37581428973573998254096417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50108571964765331005461889 37581428973573998254096417)
    ·
      refine ⟨28186071730180498690572313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37581428973573998254096417 28186071730180498690572313)
      ·
        refine ⟨21139553797635374017929235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28186071730180498690572313 21139553797635374017929235)
        ·
          refine ⟨31709330696453061026893853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21139553797635374017929235 31709330696453061026893853)
          ·
            refine ⟨11890999011169897885085195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31709330696453061026893853 11890999011169897885085195)
            ·
              refine ⟨17836498516754846827627793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11890999011169897885085195 17836498516754846827627793)
              ·
                refine ⟨13377373887566135120720845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17836498516754846827627793 13377373887566135120720845)
                ·
                  refine ⟨5016515207837300670270317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13377373887566135120720845 5016515207837300670270317)
                  ·
                    refine ⟨1881193202938987751351369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5016515207837300670270317 1881193202938987751351369)
                    ·
                      refine ⟨1410894902204240813513527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1881193202938987751351369 1410894902204240813513527)
                      ·
                        rfl

theorem cell23_2747708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_2747708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747708 prefixEnd_2747708 := by exact prefixLift 2747708
  have htrace : WordTrace (prefixWord ++ tailWord_2747708) baseStart_2747708 baseEnd_2747708 := by
    simpa [prefixWord, tailWord_2747708, baseEnd_2747708] using wordTrace_append hprefix tailTrace_2747708
  have hstable : (prefixWord ++ tailWord_2747708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747708).length < 2 ^ (prefixWord ++ tailWord_2747708).sum := by decide
  have hdescent : baseEnd_2747708 < baseStart_2747708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747738 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2]
def baseStart_2747738 : Nat := 118140960795 + 2747738 * 2 ^ 59
def prefixEnd_2747738 : Nat := 4983230072969 + 3 ^ 40 * 2747738 * 2
def baseEnd_2747738 : Nat := 1410910306623875696138389

theorem tailTrace_2747738 : CollatzResearch.WordTrace tailWord_2747738 prefixEnd_2747738 1410910306623875696138389 := by
  unfold tailWord_2747738
  simp only [CollatzResearch.WordTrace]
  refine ⟨25054559529855494283628967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66812158746281318089677245 25054559529855494283628967)
  ·
    refine ⟨37581839294783241425443451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25054559529855494283628967 37581839294783241425443451)
    ·
      refine ⟨56372758942174862138165177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37581839294783241425443451 56372758942174862138165177)
      ·
        refine ⟨42279569206631146603623883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56372758942174862138165177 42279569206631146603623883)
        ·
          refine ⟨63419353809946719905435825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42279569206631146603623883 63419353809946719905435825)
          ·
            refine ⟨47564515357460039929076869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63419353809946719905435825 47564515357460039929076869)
            ·
              refine ⟨8918346629523757486701913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47564515357460039929076869 8918346629523757486701913)
              ·
                refine ⟨6688759972142818115026435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8918346629523757486701913 6688759972142818115026435)
                ·
                  refine ⟨10033139958214227172539653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6688759972142818115026435 10033139958214227172539653)
                  ·
                    refine ⟨1881213742165167594851185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10033139958214227172539653 1881213742165167594851185)
                    ·
                      refine ⟨1410910306623875696138389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1881213742165167594851185 1410910306623875696138389)
                      ·
                        rfl

theorem cell23_2747738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_2747738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747738 prefixEnd_2747738 := by exact prefixLift 2747738
  have htrace : WordTrace (prefixWord ++ tailWord_2747738) baseStart_2747738 baseEnd_2747738 := by
    simpa [prefixWord, tailWord_2747738, baseEnd_2747738] using wordTrace_append hprefix tailTrace_2747738
  have hstable : (prefixWord ++ tailWord_2747738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747738).length < 2 ^ (prefixWord ++ tailWord_2747738).sum := by decide
  have hdescent : baseEnd_2747738 < baseStart_2747738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747771 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 3]
def baseStart_2747771 : Nat := 118140960795 + 2747771 * 2 ^ 59
def prefixEnd_2747771 : Nat := 4983230072969 + 3 ^ 40 * 2747771 * 2
def baseEnd_2747771 : Nat := 1410927251485474067025737

theorem tailTrace_2747771 : CollatzResearch.WordTrace tailWord_2747771 prefixEnd_2747771 1410927251485474067025737 := by
  unfold tailWord_2747771
  simp only [CollatzResearch.WordTrace]
  refine ⟨100219441728302423770467167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66812961152201615846978111 100219441728302423770467167)
  ·
    refine ⟨150329162592453635655700751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100219441728302423770467167 150329162592453635655700751)
    ·
      refine ⟨225493743888680453483551127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150329162592453635655700751 225493743888680453483551127)
      ·
        refine ⟨338240615833020680225326691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225493743888680453483551127 338240615833020680225326691)
        ·
          refine ⟨507360923749531020337990037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338240615833020680225326691 507360923749531020337990037)
          ·
            refine ⟨23782543300759266578343283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 507360923749531020337990037 23782543300759266578343283)
            ·
              refine ⟨35673814951138899867514925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23782543300759266578343283 35673814951138899867514925)
              ·
                refine ⟨13377680606677087450318097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35673814951138899867514925 13377680606677087450318097)
                ·
                  refine ⟨10033260455007815587738573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13377680606677087450318097 10033260455007815587738573)
                  ·
                    refine ⟨3762472670627930845401965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10033260455007815587738573 3762472670627930845401965)
                    ·
                      refine ⟨1410927251485474067025737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3762472670627930845401965 1410927251485474067025737)
                      ·
                        rfl

theorem cell23_2747771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 3].length) (baseStart_2747771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747771 prefixEnd_2747771 := by exact prefixLift 2747771
  have htrace : WordTrace (prefixWord ++ tailWord_2747771) baseStart_2747771 baseEnd_2747771 := by
    simpa [prefixWord, tailWord_2747771, baseEnd_2747771] using wordTrace_append hprefix tailTrace_2747771
  have hstable : (prefixWord ++ tailWord_2747771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747771).length < 2 ^ (prefixWord ++ tailWord_2747771).sum := by decide
  have hdescent : baseEnd_2747771 < baseStart_2747771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747772 : List Nat := [2, 2, 2, 1, 1, 1, 7, 1, 2, 2, 2]
def baseStart_2747772 : Nat := 118140960795 + 2747772 * 2 ^ 59
def prefixEnd_2747772 : Nat := 4983230072969 + 3 ^ 40 * 2747772 * 2
def baseEnd_2747772 : Nat := 1410927764966128563113233

theorem tailTrace_2747772 : CollatzResearch.WordTrace tailWord_2747772 prefixEnd_2747772 1410927764966128563113233 := by
  unfold tailWord_2747772
  simp only [CollatzResearch.WordTrace]
  refine ⟨50109739100649400470626785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66812985467532533960835713 50109739100649400470626785)
  ·
    refine ⟨37582304325487050352970089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50109739100649400470626785 37582304325487050352970089)
    ·
      refine ⟨28186728244115287764727567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37582304325487050352970089 28186728244115287764727567)
      ·
        refine ⟨42280092366172931647091351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28186728244115287764727567 42280092366172931647091351)
        ·
          refine ⟨63420138549259397470637027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42280092366172931647091351 63420138549259397470637027)
          ·
            refine ⟨95130207823889096205955541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63420138549259397470637027 95130207823889096205955541)
            ·
              refine ⟨2229614245872400692327083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 95130207823889096205955541 2229614245872400692327083)
              ·
                refine ⟨3344421368808601038490625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2229614245872400692327083 3344421368808601038490625)
                ·
                  refine ⟨2508316026606450778867969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3344421368808601038490625 2508316026606450778867969)
                  ·
                    refine ⟨1881237019954838084150977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2508316026606450778867969 1881237019954838084150977)
                    ·
                      refine ⟨1410927764966128563113233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1881237019954838084150977 1410927764966128563113233)
                      ·
                        rfl

theorem cell23_2747772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_2747772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747772 prefixEnd_2747772 := by exact prefixLift 2747772
  have htrace : WordTrace (prefixWord ++ tailWord_2747772) baseStart_2747772 baseEnd_2747772 := by
    simpa [prefixWord, tailWord_2747772, baseEnd_2747772] using wordTrace_append hprefix tailTrace_2747772
  have hstable : (prefixWord ++ tailWord_2747772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747772).length < 2 ^ (prefixWord ++ tailWord_2747772).sum := by decide
  have hdescent : baseEnd_2747772 < baseStart_2747772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747838 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_2747838 : Nat := 118140960795 + 2747838 * 2 ^ 59
def prefixEnd_2747838 : Nat := 4983230072969 + 3 ^ 40 * 2747838 * 2
def baseEnd_2747838 : Nat := 470320551563108434962643

theorem tailTrace_2747838 : CollatzResearch.WordTrace tailWord_2747838 prefixEnd_2747838 470320551563108434962643 := by
  unfold tailWord_2747838
  simp only [CollatzResearch.WordTrace]
  refine ⟨12527735677382461776644521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66814590279373129475437445 12527735677382461776644521)
  ·
    refine ⟨9395801758036846332483391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12527735677382461776644521 9395801758036846332483391)
    ·
      refine ⟨14093702637055269498725087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9395801758036846332483391 14093702637055269498725087)
      ·
        refine ⟨21140553955582904248087631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14093702637055269498725087 21140553955582904248087631)
        ·
          refine ⟨31710830933374356372131447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21140553955582904248087631 31710830933374356372131447)
          ·
            refine ⟨47566246400061534558197171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31710830933374356372131447 47566246400061534558197171)
            ·
              refine ⟨71349369600092301837295757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47566246400061534558197171 71349369600092301837295757)
              ·
                refine ⟨26756013600034613188985909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71349369600092301837295757 26756013600034613188985909)
                ·
                  refine ⟨2508376275003244986467429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26756013600034613188985909 2508376275003244986467429)
                  ·
                    refine ⟨470320551563108434962643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2508376275003244986467429 470320551563108434962643)
                    ·
                      rfl

theorem cell23_2747838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_2747838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747838 prefixEnd_2747838 := by exact prefixLift 2747838
  have htrace : WordTrace (prefixWord ++ tailWord_2747838) baseStart_2747838 baseEnd_2747838 := by
    simpa [prefixWord, tailWord_2747838, baseEnd_2747838] using wordTrace_append hprefix tailTrace_2747838
  have hstable : (prefixWord ++ tailWord_2747838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747838).length < 2 ^ (prefixWord ++ tailWord_2747838).sum := by decide
  have hdescent : baseEnd_2747838 < baseStart_2747838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747871 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 6]
def baseStart_2747871 : Nat := 118140960795 + 2747871 * 2 ^ 59
def prefixEnd_2747871 : Nat := 4983230072969 + 3 ^ 40 * 2747871 * 2
def baseEnd_2747871 : Nat := 1410978599550923675775277

theorem tailTrace_2747871 : CollatzResearch.WordTrace tailWord_2747871 prefixEnd_2747871 1410978599550923675775277 := by
  unfold tailWord_2747871
  simp only [CollatzResearch.WordTrace]
  refine ⟨100223089027940140849107467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66815392685293427232738311 100223089027940140849107467)
  ·
    refine ⟨150334633541910211273661201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100223089027940140849107467 150334633541910211273661201)
    ·
      refine ⟨112750975156432658455245901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150334633541910211273661201 112750975156432658455245901)
      ·
        refine ⟨42281615683662246920717213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112750975156432658455245901 42281615683662246920717213)
        ·
          refine ⟨15855605881373342595268955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42281615683662246920717213 15855605881373342595268955)
          ·
            refine ⟨23783408822060013892903433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15855605881373342595268955 23783408822060013892903433)
            ·
              refine ⟨17837556616545010419677575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23783408822060013892903433 17837556616545010419677575)
              ·
                refine ⟨26756334924817515629516363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17837556616545010419677575 26756334924817515629516363)
                ·
                  refine ⟨40134502387226273444274545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26756334924817515629516363 40134502387226273444274545)
                  ·
                    refine ⟨30100876790419705083205909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40134502387226273444274545 30100876790419705083205909)
                    ·
                      refine ⟨1410978599550923675775277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30100876790419705083205909 1410978599550923675775277)
                      ·
                        rfl

theorem cell23_2747871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_2747871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747871 prefixEnd_2747871 := by exact prefixLift 2747871
  have htrace : WordTrace (prefixWord ++ tailWord_2747871) baseStart_2747871 baseEnd_2747871 := by
    simpa [prefixWord, tailWord_2747871, baseEnd_2747871] using wordTrace_append hprefix tailTrace_2747871
  have hstable : (prefixWord ++ tailWord_2747871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747871).length < 2 ^ (prefixWord ++ tailWord_2747871).sum := by decide
  have hdescent : baseEnd_2747871 < baseStart_2747871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747898 : List Nat := [3, 1, 1, 1, 1, 2, 4, 4, 1, 5]
def baseStart_2747898 : Nat := 118140960795 + 2747898 * 2 ^ 59
def prefixEnd_2747898 : Nat := 4983230072969 + 3 ^ 40 * 2747898 * 2
def baseEnd_2747898 : Nat := 470330821176198356712551

theorem tailTrace_2747898 : CollatzResearch.WordTrace tailWord_2747898 prefixEnd_2747898 470330821176198356712551 := by
  unfold tailWord_2747898
  simp only [CollatzResearch.WordTrace]
  refine ⟨25056018449710581115085087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66816049199228216306893565 25056018449710581115085087)
  ·
    refine ⟨37584027674565871672627631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25056018449710581115085087 37584027674565871672627631)
    ·
      refine ⟨56376041511848807508941447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37584027674565871672627631 56376041511848807508941447)
      ·
        refine ⟨84564062267773211263412171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56376041511848807508941447 84564062267773211263412171)
        ·
          refine ⟨126846093401659816895118257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84564062267773211263412171 126846093401659816895118257)
          ·
            refine ⟨95134570051244862671338693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126846093401659816895118257 95134570051244862671338693)
            ·
              refine ⟨17837731884608411750876005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95134570051244862671338693 17837731884608411750876005)
              ·
                refine ⟨3344574728364077203289251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17837731884608411750876005 3344574728364077203289251)
                ·
                  refine ⟨5016862092546115804933877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3344574728364077203289251 5016862092546115804933877)
                  ·
                    refine ⟨470330821176198356712551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5016862092546115804933877 470330821176198356712551)
                    ·
                      rfl

theorem cell23_2747898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_2747898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747898 prefixEnd_2747898 := by exact prefixLift 2747898
  have htrace : WordTrace (prefixWord ++ tailWord_2747898) baseStart_2747898 baseEnd_2747898 := by
    simpa [prefixWord, tailWord_2747898, baseEnd_2747898] using wordTrace_append hprefix tailTrace_2747898
  have hstable : (prefixWord ++ tailWord_2747898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747898).length < 2 ^ (prefixWord ++ tailWord_2747898).sum := by decide
  have hdescent : baseEnd_2747898 < baseStart_2747898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747912 : List Nat := [2, 1, 3, 2, 1, 1, 3, 5, 1, 1, 3]
def baseStart_2747912 : Nat := 118140960795 + 2747912 * 2 ^ 59
def prefixEnd_2747912 : Nat := 4983230072969 + 3 ^ 40 * 2747912 * 2
def baseEnd_2747912 : Nat := 1410999652257758015362589

theorem tailTrace_2747912 : CollatzResearch.WordTrace tailWord_2747912 prefixEnd_2747912 1410999652257758015362589 := by
  unfold tailWord_2747912
  simp only [CollatzResearch.WordTrace]
  refine ⟨50112292210395802425674995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66816389613861069900899993 50112292210395802425674995)
  ·
    refine ⟨75168438315593703638512493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50112292210395802425674995 75168438315593703638512493)
    ·
      refine ⟨28188164368347638864442185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75168438315593703638512493 28188164368347638864442185)
      ·
        refine ⟨21141123276260729148331639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28188164368347638864442185 21141123276260729148331639)
        ·
          refine ⟨31711684914391093722497459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21141123276260729148331639 31711684914391093722497459)
          ·
            refine ⟨47567527371586640583746189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31711684914391093722497459 47567527371586640583746189)
            ·
              refine ⟨17837822764344990218904821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47567527371586640583746189 17837822764344990218904821)
              ·
                refine ⟨1672295884157342833022327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17837822764344990218904821 1672295884157342833022327)
                ·
                  refine ⟨2508443826236014249533491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672295884157342833022327 2508443826236014249533491)
                  ·
                    refine ⟨3762665739354021374300237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2508443826236014249533491 3762665739354021374300237)
                    ·
                      refine ⟨1410999652257758015362589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3762665739354021374300237 1410999652257758015362589)
                      ·
                        rfl

theorem cell23_2747912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_2747912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747912 prefixEnd_2747912 := by exact prefixLift 2747912
  have htrace : WordTrace (prefixWord ++ tailWord_2747912) baseStart_2747912 baseEnd_2747912 := by
    simpa [prefixWord, tailWord_2747912, baseEnd_2747912] using wordTrace_append hprefix tailTrace_2747912
  have hstable : (prefixWord ++ tailWord_2747912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747912).length < 2 ^ (prefixWord ++ tailWord_2747912).sum := by decide
  have hdescent : baseEnd_2747912 < baseStart_2747912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747915 : List Nat := [1, 1, 1, 1, 8, 1, 1, 3, 1, 5]
def baseStart_2747915 : Nat := 118140960795 + 2747915 * 2 ^ 59
def prefixEnd_2747915 : Nat := 4983230072969 + 3 ^ 40 * 2747915 * 2
def baseEnd_2747915 : Nat := 470333730899907167875025

theorem tailTrace_2747915 : CollatzResearch.WordTrace tailWord_2747915 prefixEnd_2747915 470333730899907167875025 := by
  unfold tailWord_2747915
  simp only [CollatzResearch.WordTrace]
  refine ⟨100224693839780736363709199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66816462559853824242472799 100224693839780736363709199)
  ·
    refine ⟨150337040759671104545563799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100224693839780736363709199 150337040759671104545563799)
    ·
      refine ⟨225505561139506656818345699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150337040759671104545563799 225505561139506656818345699)
      ·
        refine ⟨338258341709259985227518549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225505561139506656818345699 338258341709259985227518549)
        ·
          refine ⟨3963964941905390451884983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 338258341709259985227518549 3963964941905390451884983)
          ·
            refine ⟨5945947412858085677827475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3963964941905390451884983 5945947412858085677827475)
            ·
              refine ⟨8918921119287128516741213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5945947412858085677827475 8918921119287128516741213)
              ·
                refine ⟨3344595419732673193777955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8918921119287128516741213 3344595419732673193777955)
                ·
                  refine ⟨5016893129599009790666933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3344595419732673193777955 5016893129599009790666933)
                  ·
                    refine ⟨470333730899907167875025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5016893129599009790666933 470333730899907167875025)
                    ·
                      rfl

theorem cell23_2747915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 5].length) (baseStart_2747915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747915 prefixEnd_2747915 := by exact prefixLift 2747915
  have htrace : WordTrace (prefixWord ++ tailWord_2747915) baseStart_2747915 baseEnd_2747915 := by
    simpa [prefixWord, tailWord_2747915, baseEnd_2747915] using wordTrace_append hprefix tailTrace_2747915
  have hstable : (prefixWord ++ tailWord_2747915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747915).length < 2 ^ (prefixWord ++ tailWord_2747915).sum := by decide
  have hdescent : baseEnd_2747915 < baseStart_2747915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747931 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 4]
def baseStart_2747931 : Nat := 118140960795 + 2747931 * 2 ^ 59
def prefixEnd_2747931 : Nat := 4983230072969 + 3 ^ 40 * 2747931 * 2
def baseEnd_2747931 : Nat := 1411009408390193441025001

theorem tailTrace_2747931 : CollatzResearch.WordTrace tailWord_2747931 prefixEnd_2747931 1411009408390193441025001 := by
  unfold tailWord_2747931
  simp only [CollatzResearch.WordTrace]
  refine ⟨100225277407722771096291647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66816851605148514064194431 100225277407722771096291647)
  ·
    refine ⟨150337916111584156644437471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100225277407722771096291647 150337916111584156644437471)
    ·
      refine ⟨225506874167376234966656207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150337916111584156644437471 225506874167376234966656207)
      ·
        refine ⟨338260311251064352449984311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225506874167376234966656207 338260311251064352449984311)
        ·
          refine ⟨507390466876596528674976467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338260311251064352449984311 507390466876596528674976467)
          ·
            refine ⟨761085700314894793012464701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507390466876596528674976467 761085700314894793012464701)
            ·
              refine ⟨285407137618085547379674263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 761085700314894793012464701 285407137618085547379674263)
              ·
                refine ⟨428110706427128321069511395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285407137618085547379674263 428110706427128321069511395)
                ·
                  refine ⟨642166059640692481604267093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 428110706427128321069511395 642166059640692481604267093)
                  ·
                    refine ⟨7525383511414365018800005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 642166059640692481604267093 7525383511414365018800005)
                    ·
                      refine ⟨1411009408390193441025001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7525383511414365018800005 1411009408390193441025001)
                      ·
                        rfl

theorem cell23_2747931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 4].length) (baseStart_2747931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747931 prefixEnd_2747931 := by exact prefixLift 2747931
  have htrace : WordTrace (prefixWord ++ tailWord_2747931) baseStart_2747931 baseEnd_2747931 := by
    simpa [prefixWord, tailWord_2747931, baseEnd_2747931] using wordTrace_append hprefix tailTrace_2747931
  have hstable : (prefixWord ++ tailWord_2747931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747931).length < 2 ^ (prefixWord ++ tailWord_2747931).sum := by decide
  have hdescent : baseEnd_2747931 < baseStart_2747931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747938 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_2747938 : Nat := 118140960795 + 2747938 * 2 ^ 59
def prefixEnd_2747938 : Nat := 4983230072969 + 3 ^ 40 * 2747938 * 2
def baseEnd_2747938 : Nat := 1411013002754774913637469

theorem tailTrace_2747938 : CollatzResearch.WordTrace tailWord_2747938 prefixEnd_2747938 1411013002754774913637469 := by
  unfold tailWord_2747938
  simp only [CollatzResearch.WordTrace]
  refine ⟨25056383179674352822949117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66817021812464940861197645 25056383179674352822949117)
  ·
    refine ⟨9396143692377882308605919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25056383179674352822949117 9396143692377882308605919)
    ·
      refine ⟨14094215538566823462908879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9396143692377882308605919 14094215538566823462908879)
      ·
        refine ⟨21141323307850235194363319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14094215538566823462908879 21141323307850235194363319)
        ·
          refine ⟨31711984961775352791544979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21141323307850235194363319 31711984961775352791544979)
          ·
            refine ⟨47567977442663029187317469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31711984961775352791544979 47567977442663029187317469)
            ·
              refine ⟨17837991540998635945244051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47567977442663029187317469 17837991540998635945244051)
              ·
                refine ⟨26756987311497953917866077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17837991540998635945244051 26756987311497953917866077)
                ·
                  refine ⟨10033870241811732719199779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26756987311497953917866077 10033870241811732719199779)
                  ·
                    refine ⟨15050805362717599078799669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10033870241811732719199779 15050805362717599078799669)
                    ·
                      refine ⟨1411013002754774913637469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15050805362717599078799669 1411013002754774913637469)
                      ·
                        rfl

theorem cell23_2747938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_2747938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747938 prefixEnd_2747938 := by exact prefixLift 2747938
  have htrace : WordTrace (prefixWord ++ tailWord_2747938) baseStart_2747938 baseEnd_2747938 := by
    simpa [prefixWord, tailWord_2747938, baseEnd_2747938] using wordTrace_append hprefix tailTrace_2747938
  have hstable : (prefixWord ++ tailWord_2747938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747938).length < 2 ^ (prefixWord ++ tailWord_2747938).sum := by decide
  have hdescent : baseEnd_2747938 < baseStart_2747938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747941 : List Nat := [1, 3, 1, 2, 2, 1, 1, 12]
def baseStart_2747941 : Nat := 118140960795 + 2747941 * 2 ^ 59
def prefixEnd_2747941 : Nat := 4983230072969 + 3 ^ 40 * 2747941 * 2
def baseEnd_2747941 : Nat := 52259797896175496366665

theorem tailTrace_2747941 : CollatzResearch.WordTrace tailWord_2747941 prefixEnd_2747941 52259797896175496366665 := by
  unfold tailWord_2747941
  simp only [CollatzResearch.WordTrace]
  refine ⟨100225642137686542804155677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66817094758457695202770451 100225642137686542804155677)
  ·
    refine ⟨37584615801632453551558379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100225642137686542804155677 37584615801632453551558379)
    ·
      refine ⟨56376923702448680327337569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37584615801632453551558379 56376923702448680327337569)
      ·
        refine ⟨42282692776836510245503177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56376923702448680327337569 42282692776836510245503177)
        ·
          refine ⟨31712019582627382684127383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42282692776836510245503177 31712019582627382684127383)
          ·
            refine ⟨47568029373941074026191075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31712019582627382684127383 47568029373941074026191075)
            ·
              refine ⟨71352044060911611039286613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47568029373941074026191075 71352044060911611039286613)
              ·
                refine ⟨52259797896175496366665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 71352044060911611039286613 52259797896175496366665)
                ·
                  rfl

theorem cell23_2747941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 12].length) (baseStart_2747941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747941 prefixEnd_2747941 := by exact prefixLift 2747941
  have htrace : WordTrace (prefixWord ++ tailWord_2747941) baseStart_2747941 baseEnd_2747941 := by
    simpa [prefixWord, tailWord_2747941, baseEnd_2747941] using wordTrace_append hprefix tailTrace_2747941
  have hstable : (prefixWord ++ tailWord_2747941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747941).length < 2 ^ (prefixWord ++ tailWord_2747941).sum := by decide
  have hdescent : baseEnd_2747941 < baseStart_2747941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747955 : List Nat := [1, 1, 1, 2, 4, 3, 1, 4, 1, 2, 3]
def baseStart_2747955 : Nat := 118140960795 + 2747955 * 2 ^ 59
def prefixEnd_2747955 : Nat := 4983230072969 + 3 ^ 40 * 2747955 * 2
def baseEnd_2747955 : Nat := 1411021731925901347124891

theorem tailTrace_2747955 : CollatzResearch.WordTrace tailWord_2747955 prefixEnd_2747955 1411021731925901347124891 := by
  unfold tailWord_2747955
  simp only [CollatzResearch.WordTrace]
  refine ⟨100226152759635823195165319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66817435173090548796776879 100226152759635823195165319)
  ·
    refine ⟨150339229139453734792747979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100226152759635823195165319 150339229139453734792747979)
    ·
      refine ⟨225508843709180602189121969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150339229139453734792747979 225508843709180602189121969)
      ·
        refine ⟨169131632781885451641841477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225508843709180602189121969 169131632781885451641841477)
        ·
          refine ⟨31712181146603522182845277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169131632781885451641841477 31712181146603522182845277)
          ·
            refine ⟨11892067929976320818566979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31712181146603522182845277 11892067929976320818566979)
            ·
              refine ⟨17838101894964481227850469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11892067929976320818566979 17838101894964481227850469)
              ·
                refine ⟨3344644105305840230221963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17838101894964481227850469 3344644105305840230221963)
                ·
                  refine ⟨5016966157958760345332945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3344644105305840230221963 5016966157958760345332945)
                  ·
                    refine ⟨3762724618469070258999709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5016966157958760345332945 3762724618469070258999709)
                    ·
                      refine ⟨1411021731925901347124891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3762724618469070258999709 1411021731925901347124891)
                      ·
                        rfl

theorem cell23_2747955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 2, 3].length) (baseStart_2747955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747955 prefixEnd_2747955 := by exact prefixLift 2747955
  have htrace : WordTrace (prefixWord ++ tailWord_2747955) baseStart_2747955 baseEnd_2747955 := by
    simpa [prefixWord, tailWord_2747955, baseEnd_2747955] using wordTrace_append hprefix tailTrace_2747955
  have hstable : (prefixWord ++ tailWord_2747955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747955).length < 2 ^ (prefixWord ++ tailWord_2747955).sum := by decide
  have hdescent : baseEnd_2747955 < baseStart_2747955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747968 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 3]
def baseStart_2747968 : Nat := 118140960795 + 2747968 * 2 ^ 59
def prefixEnd_2747968 : Nat := 4983230072969 + 3 ^ 40 * 2747968 * 2
def baseEnd_2747968 : Nat := 1411028407174409796262331

theorem tailTrace_2747968 : CollatzResearch.WordTrace tailWord_2747968 prefixEnd_2747968 1411028407174409796262331 := by
  unfold tailWord_2747968
  simp only [CollatzResearch.WordTrace]
  refine ⟨50113313454294363207694279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66817751272392484276925705 50113313454294363207694279)
  ·
    refine ⟨75169970181441544811541419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50113313454294363207694279 75169970181441544811541419)
    ·
      refine ⟨112754955272162317217312129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75169970181441544811541419 112754955272162317217312129)
      ·
        refine ⟨84566216454121737912984097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112754955272162317217312129 84566216454121737912984097)
        ·
          refine ⟨63424662340591303434738073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84566216454121737912984097 63424662340591303434738073)
          ·
            refine ⟨47568496755443477576053555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63424662340591303434738073 47568496755443477576053555)
            ·
              refine ⟨71352745133165216364080333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47568496755443477576053555 71352745133165216364080333)
              ·
                refine ⟨26757279424936956136530125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71352745133165216364080333 26757279424936956136530125)
                ·
                  refine ⟨10033979784351358551198797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26757279424936956136530125 10033979784351358551198797)
                  ·
                    refine ⟨3762742419131759456699549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10033979784351358551198797 3762742419131759456699549)
                    ·
                      refine ⟨1411028407174409796262331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3762742419131759456699549 1411028407174409796262331)
                      ·
                        rfl

theorem cell23_2747968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_2747968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747968 prefixEnd_2747968 := by exact prefixLift 2747968
  have htrace : WordTrace (prefixWord ++ tailWord_2747968) baseStart_2747968 baseEnd_2747968 := by
    simpa [prefixWord, tailWord_2747968, baseEnd_2747968] using wordTrace_append hprefix tailTrace_2747968
  have hstable : (prefixWord ++ tailWord_2747968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747968).length < 2 ^ (prefixWord ++ tailWord_2747968).sum := by decide
  have hdescent : baseEnd_2747968 < baseStart_2747968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747971 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 3, 9]
def baseStart_2747971 : Nat := 118140960795 + 2747971 * 2 ^ 59
def prefixEnd_2747971 : Nat := 4983230072969 + 3 ^ 40 * 2747971 * 2
def baseEnd_2747971 : Nat := 470343315872124428174939

theorem tailTrace_2747971 : CollatzResearch.WordTrace tailWord_2747971 prefixEnd_2747971 470343315872124428174939 := by
  unfold tailWord_2747971
  simp only [CollatzResearch.WordTrace]
  refine ⟨100226736327577857927747767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66817824218385238618498511 100226736327577857927747767)
  ·
    refine ⟨150340104491366786891621651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100226736327577857927747767 150340104491366786891621651)
    ·
      refine ⟨225510156737050180337432477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150340104491366786891621651 225510156737050180337432477)
      ·
        refine ⟨84566308776393817626537179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225510156737050180337432477 84566308776393817626537179)
        ·
          refine ⟨126849463164590726439805769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84566308776393817626537179 126849463164590726439805769)
          ·
            refine ⟨95137097373443044829854327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126849463164590726439805769 95137097373443044829854327)
            ·
              refine ⟨142705646060164567244781491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95137097373443044829854327 142705646060164567244781491)
              ·
                refine ⟨214058469090246850867172237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142705646060164567244781491 214058469090246850867172237)
                ·
                  refine ⟨80271925908842569075189589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214058469090246850867172237 80271925908842569075189589)
                  ·
                    refine ⟨470343315872124428174939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 80271925908842569075189589 470343315872124428174939)
                    ·
                      rfl

theorem cell23_2747971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 9].length) (baseStart_2747971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747971 prefixEnd_2747971 := by exact prefixLift 2747971
  have htrace : WordTrace (prefixWord ++ tailWord_2747971) baseStart_2747971 baseEnd_2747971 := by
    simpa [prefixWord, tailWord_2747971, baseEnd_2747971] using wordTrace_append hprefix tailTrace_2747971
  have hstable : (prefixWord ++ tailWord_2747971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747971).length < 2 ^ (prefixWord ++ tailWord_2747971).sum := by decide
  have hdescent : baseEnd_2747971 < baseStart_2747971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747975 : List Nat := [1, 1, 4, 1, 6, 1, 9]
def baseStart_2747975 : Nat := 118140960795 + 2747975 * 2 ^ 59
def prefixEnd_2747975 : Nat := 4983230072969 + 3 ^ 40 * 2747975 * 2
def baseEnd_2747975 : Nat := 17420148167148040356479

theorem tailTrace_2747975 : CollatzResearch.WordTrace tailWord_2747975 prefixEnd_2747975 17420148167148040356479 := by
  unfold tailWord_2747975
  simp only [CollatzResearch.WordTrace]
  refine ⟨100226882219563366610893379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66817921479708911073928919 100226882219563366610893379)
  ·
    refine ⟨150340323329345049916340069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100226882219563366610893379 150340323329345049916340069)
    ·
      refine ⟨28188810624252196859313763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150340323329345049916340069 28188810624252196859313763)
      ·
        refine ⟨42283215936378295288970645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28188810624252196859313763 42283215936378295288970645)
        ·
          refine ⟨1982025747017732591670499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42283215936378295288970645 1982025747017732591670499)
          ·
            refine ⟨2973038620526598887505749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982025747017732591670499 2973038620526598887505749)
            ·
              refine ⟨17420148167148040356479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2973038620526598887505749 17420148167148040356479)
              ·
                rfl

theorem cell23_2747975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 9].length) (baseStart_2747975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747975 prefixEnd_2747975 := by exact prefixLift 2747975
  have htrace : WordTrace (prefixWord ++ tailWord_2747975) baseStart_2747975 baseEnd_2747975 := by
    simpa [prefixWord, tailWord_2747975, baseEnd_2747975] using wordTrace_append hprefix tailTrace_2747975
  have hstable : (prefixWord ++ tailWord_2747975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747975).length < 2 ^ (prefixWord ++ tailWord_2747975).sum := by decide
  have hdescent : baseEnd_2747975 < baseStart_2747975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747985 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 4, 1, 3]
def baseStart_2747985 : Nat := 118140960795 + 2747985 * 2 ^ 59
def prefixEnd_2747985 : Nat := 4983230072969 + 3 ^ 40 * 2747985 * 2
def baseEnd_2747985 : Nat := 1411037136345536229749753

theorem tailTrace_2747985 : CollatzResearch.WordTrace tailWord_2747985 prefixEnd_2747985 1411037136345536229749753 := by
  unfold tailWord_2747985
  simp only [CollatzResearch.WordTrace]
  refine ⟨100227246949527138318757409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66818164633018092212504939 100227246949527138318757409)
  ·
    refine ⟨75170435212145353739068057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100227246949527138318757409 75170435212145353739068057)
    ·
      refine ⟨56377826409109015304301043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75170435212145353739068057 56377826409109015304301043)
      ·
        refine ⟨84566739613663522956451565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56377826409109015304301043 84566739613663522956451565)
        ·
          refine ⟨31712527355123821108669337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84566739613663522956451565 31712527355123821108669337)
          ·
            refine ⟨23784395516342865831502003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31712527355123821108669337 23784395516342865831502003)
            ·
              refine ⟨35676593274514298747253005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23784395516342865831502003 35676593274514298747253005)
              ·
                refine ⟨13378722477942862030219877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35676593274514298747253005 13378722477942862030219877)
                ·
                  refine ⟨2508510464614286630666227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13378722477942862030219877 2508510464614286630666227)
                  ·
                    refine ⟨3762765696921429945999341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2508510464614286630666227 3762765696921429945999341)
                    ·
                      refine ⟨1411037136345536229749753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3762765696921429945999341 1411037136345536229749753)
                      ·
                        rfl

theorem cell23_2747985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 1, 3].length) (baseStart_2747985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747985 prefixEnd_2747985 := by exact prefixLift 2747985
  have htrace : WordTrace (prefixWord ++ tailWord_2747985) baseStart_2747985 baseEnd_2747985 := by
    simpa [prefixWord, tailWord_2747985, baseEnd_2747985] using wordTrace_append hprefix tailTrace_2747985
  have hstable : (prefixWord ++ tailWord_2747985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747985).length < 2 ^ (prefixWord ++ tailWord_2747985).sum := by decide
  have hdescent : baseEnd_2747985 < baseStart_2747985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747988 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_2747988 : Nat := 118140960795 + 2747988 * 2 ^ 59
def prefixEnd_2747988 : Nat := 4983230072969 + 3 ^ 40 * 2747988 * 2
def baseEnd_2747988 : Nat := 470346225595833239337413

theorem tailTrace_2747988 : CollatzResearch.WordTrace tailWord_2747988 prefixEnd_2747988 470346225595833239337413 := by
  unfold tailWord_2747988
  simp only [CollatzResearch.WordTrace]
  refine ⟨50113678184258134915558309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66818237579010846554077745 50113678184258134915558309)
  ·
    refine ⟨9396314659548400296667183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50113678184258134915558309 9396314659548400296667183)
    ·
      refine ⟨14094471989322600445000775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9396314659548400296667183 14094471989322600445000775)
      ·
        refine ⟨21141707983983900667501163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14094471989322600445000775 21141707983983900667501163)
        ·
          refine ⟨31712561975975851001251745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21141707983983900667501163 31712561975975851001251745)
          ·
            refine ⟨23784421481981888250938809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31712561975975851001251745 23784421481981888250938809)
            ·
              refine ⟨17838316111486416188204107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23784421481981888250938809 17838316111486416188204107)
              ·
                refine ⟨26757474167229624282306161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17838316111486416188204107 26757474167229624282306161)
                ·
                  refine ⟨20068105625422218211729621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26757474167229624282306161 20068105625422218211729621)
                  ·
                    refine ⟨470346225595833239337413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20068105625422218211729621 470346225595833239337413)
                    ·
                      rfl

theorem cell23_2747988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_2747988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2747988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2747988 prefixEnd_2747988 := by exact prefixLift 2747988
  have htrace : WordTrace (prefixWord ++ tailWord_2747988) baseStart_2747988 baseEnd_2747988 := by
    simpa [prefixWord, tailWord_2747988, baseEnd_2747988] using wordTrace_append hprefix tailTrace_2747988
  have hstable : (prefixWord ++ tailWord_2747988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747988).length < 2 ^ (prefixWord ++ tailWord_2747988).sum := by decide
  have hdescent : baseEnd_2747988 < baseStart_2747988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748052 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_2748052 : Nat := 118140960795 + 2748052 * 2 ^ 59
def prefixEnd_2748052 : Nat := 4983230072969 + 3 ^ 40 * 2748052 * 2
def baseEnd_2748052 : Nat := 470357179849795822537315

theorem tailTrace_2748052 : CollatzResearch.WordTrace tailWord_2748052 prefixEnd_2748052 470357179849795822537315 := by
  unfold tailWord_2748052
  simp only [CollatzResearch.WordTrace]
  refine ⟨50114845320142204380723205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66819793760189605840964273 50114845320142204380723205)
  ·
    refine ⟨9396533497526663321385601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50114845320142204380723205 9396533497526663321385601)
    ·
      refine ⟨7047400123144997491039201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9396533497526663321385601 7047400123144997491039201)
      ·
        refine ⟨5285550092358748118279401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7047400123144997491039201 5285550092358748118279401)
        ·
          refine ⟨3964162569269061088709551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5285550092358748118279401 3964162569269061088709551)
          ·
            refine ⟨5946243853903591633064327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3964162569269061088709551 5946243853903591633064327)
            ·
              refine ⟨8919365780855387449596491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5946243853903591633064327 8919365780855387449596491)
              ·
                refine ⟨13379048671283081174394737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8919365780855387449596491 13379048671283081174394737)
                ·
                  refine ⟨10034286503462310880796053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13379048671283081174394737 10034286503462310880796053)
                  ·
                    refine ⟨470357179849795822537315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10034286503462310880796053 470357179849795822537315)
                    ·
                      rfl

theorem cell23_2748052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_2748052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748052 prefixEnd_2748052 := by exact prefixLift 2748052
  have htrace : WordTrace (prefixWord ++ tailWord_2748052) baseStart_2748052 baseEnd_2748052 := by
    simpa [prefixWord, tailWord_2748052, baseEnd_2748052] using wordTrace_append hprefix tailTrace_2748052
  have hstable : (prefixWord ++ tailWord_2748052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748052).length < 2 ^ (prefixWord ++ tailWord_2748052).sum := by decide
  have hdescent : baseEnd_2748052 < baseStart_2748052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748055 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 4]
def baseStart_2748055 : Nat := 118140960795 + 2748055 * 2 ^ 59
def prefixEnd_2748055 : Nat := 4983230072969 + 3 ^ 40 * 2748055 * 2
def baseEnd_2748055 : Nat := 1411073079991350955874431

theorem tailTrace_2748055 : CollatzResearch.WordTrace tailWord_2748055 prefixEnd_2748055 1411073079991350955874431 := by
  unfold tailWord_2748055
  simp only [CollatzResearch.WordTrace]
  refine ⟨100229800059273540273805619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66819866706182360182537079 100229800059273540273805619)
  ·
    refine ⟨150344700088910310410708429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100229800059273540273805619 150344700088910310410708429)
    ·
      refine ⟨56379262533341366404015661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150344700088910310410708429 56379262533341366404015661)
      ·
        refine ⟨21142223450003012401505873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56379262533341366404015661 21142223450003012401505873)
        ·
          refine ⟨15856667587502259301129405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21142223450003012401505873 15856667587502259301129405)
          ·
            refine ⟨5946250345313347237923527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15856667587502259301129405 5946250345313347237923527)
            ·
              refine ⟨8919375517970020856885291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5946250345313347237923527 8919375517970020856885291)
              ·
                refine ⟨13379063276955031285327937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8919375517970020856885291 13379063276955031285327937)
                ·
                  refine ⟨10034297457716273463995953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13379063276955031285327937 10034297457716273463995953)
                  ·
                    refine ⟨7525723093287205097996965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10034297457716273463995953 7525723093287205097996965)
                    ·
                      refine ⟨1411073079991350955874431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7525723093287205097996965 1411073079991350955874431)
                      ·
                        rfl

theorem cell23_2748055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_2748055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748055 prefixEnd_2748055 := by exact prefixLift 2748055
  have htrace : WordTrace (prefixWord ++ tailWord_2748055) baseStart_2748055 baseEnd_2748055 := by
    simpa [prefixWord, tailWord_2748055, baseEnd_2748055] using wordTrace_append hprefix tailTrace_2748055
  have hstable : (prefixWord ++ tailWord_2748055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748055).length < 2 ^ (prefixWord ++ tailWord_2748055).sum := by decide
  have hdescent : baseEnd_2748055 < baseStart_2748055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748065 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 7]
def baseStart_2748065 : Nat := 118140960795 + 2748065 * 2 ^ 59
def prefixEnd_2748065 : Nat := 4983230072969 + 3 ^ 40 * 2748065 * 2
def baseEnd_2748065 : Nat := 156786468310877324083265

theorem tailTrace_2748065 : CollatzResearch.WordTrace tailWord_2748065 prefixEnd_2748065 156786468310877324083265 := by
  unfold tailWord_2748065
  simp only [CollatzResearch.WordTrace]
  refine ⟨100230164789237311981669649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66820109859491541321113099 100230164789237311981669649)
  ·
    refine ⟨75172623591927983986252237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100230164789237311981669649 75172623591927983986252237)
    ·
      refine ⟨28189733846972993994844589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75172623591927983986252237 28189733846972993994844589)
      ·
        refine ⟨10571150192614872748066721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28189733846972993994844589 10571150192614872748066721)
        ·
          refine ⟨7928362644461154561050041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10571150192614872748066721 7928362644461154561050041)
          ·
            refine ⟨5946271983345865920787531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7928362644461154561050041 5946271983345865920787531)
            ·
              refine ⟨8919407975018798881181297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5946271983345865920787531 8919407975018798881181297)
              ·
                refine ⟨6689555981264099160885973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8919407975018798881181297 6689555981264099160885973)
                ·
                  refine ⟨156786468310877324083265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6689555981264099160885973 156786468310877324083265)
                  ·
                    rfl

theorem cell23_2748065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 7].length) (baseStart_2748065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748065 prefixEnd_2748065 := by exact prefixLift 2748065
  have htrace : WordTrace (prefixWord ++ tailWord_2748065) baseStart_2748065 baseEnd_2748065 := by
    simpa [prefixWord, tailWord_2748065, baseEnd_2748065] using wordTrace_append hprefix tailTrace_2748065
  have hstable : (prefixWord ++ tailWord_2748065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748065).length < 2 ^ (prefixWord ++ tailWord_2748065).sum := by decide
  have hdescent : baseEnd_2748065 < baseStart_2748065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748088 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 3, 2, 5]
def baseStart_2748088 : Nat := 118140960795 + 2748088 * 2 ^ 59
def prefixEnd_2748088 : Nat := 4983230072969 + 3 ^ 40 * 2748088 * 2
def baseEnd_2748088 : Nat := 1411090024852949326761779

theorem tailTrace_2748088 : CollatzResearch.WordTrace tailWord_2748088 prefixEnd_2748088 1411090024852949326761779 := by
  unfold tailWord_2748088
  simp only [CollatzResearch.WordTrace]
  refine ⟨50115501834076993454878459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66820669112102657939837945 50115501834076993454878459)
  ·
    refine ⟨75173252751115490182317689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50115501834076993454878459 75173252751115490182317689)
    ·
      refine ⟨56379939563336617636738267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75173252751115490182317689 56379939563336617636738267)
      ·
        refine ⟨84569909345004926455107401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56379939563336617636738267 84569909345004926455107401)
        ·
          refine ⟨63427432008753694841330551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84569909345004926455107401 63427432008753694841330551)
          ·
            refine ⟨95141148013130542261995827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63427432008753694841330551 95141148013130542261995827)
            ·
              refine ⟨142711722019695813392993741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95141148013130542261995827 142711722019695813392993741)
              ·
                refine ⟨53516895757385930022372653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142711722019695813392993741 53516895757385930022372653)
                ·
                  refine ⟨20068835909019723758389745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53516895757385930022372653 20068835909019723758389745)
                  ·
                    refine ⟨15051626931764792818792309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20068835909019723758389745 15051626931764792818792309)
                    ·
                      refine ⟨1411090024852949326761779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15051626931764792818792309 1411090024852949326761779)
                      ·
                        rfl

theorem cell23_2748088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_2748088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748088 prefixEnd_2748088 := by exact prefixLift 2748088
  have htrace : WordTrace (prefixWord ++ tailWord_2748088) baseStart_2748088 baseEnd_2748088 := by
    simpa [prefixWord, tailWord_2748088, baseEnd_2748088] using wordTrace_append hprefix tailTrace_2748088
  have hstable : (prefixWord ++ tailWord_2748088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748088).length < 2 ^ (prefixWord ++ tailWord_2748088).sum := by decide
  have hdescent : baseEnd_2748088 < baseStart_2748088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748109 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_2748109 : Nat := 118140960795 + 2748109 * 2 ^ 59
def prefixEnd_2748109 : Nat := 4983230072969 + 3 ^ 40 * 2748109 * 2
def baseEnd_2748109 : Nat := 1411100807946693744599183

theorem tailTrace_2748109 : CollatzResearch.WordTrace tailWord_2748109 prefixEnd_2748109 1411100807946693744599183 := by
  unfold tailWord_2748109
  simp only [CollatzResearch.WordTrace]
  refine ⟨100231769601077907496271381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66821179734051938330847587 100231769601077907496271381)
  ·
    refine ⟨4698364200050526913887721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 100231769601077907496271381 4698364200050526913887721)
    ·
      refine ⟨3523773150037895185415791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4698364200050526913887721 3523773150037895185415791)
      ·
        refine ⟨5285659725056842778123687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3523773150037895185415791 5285659725056842778123687)
        ·
          refine ⟨7928489587585264167185531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5285659725056842778123687 7928489587585264167185531)
          ·
            refine ⟨11892734381377896250778297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7928489587585264167185531 11892734381377896250778297)
            ·
              refine ⟨8919550786033422188083723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11892734381377896250778297 8919550786033422188083723)
              ·
                refine ⟨13379326179050133282125585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8919550786033422188083723 13379326179050133282125585)
                ·
                  refine ⟨10034494634287599961594189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13379326179050133282125585 10034494634287599961594189)
                  ·
                    refine ⟨3762935487857849985597821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10034494634287599961594189 3762935487857849985597821)
                    ·
                      refine ⟨1411100807946693744599183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3762935487857849985597821 1411100807946693744599183)
                      ·
                        rfl

theorem cell23_2748109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_2748109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748109 prefixEnd_2748109 := by exact prefixLift 2748109
  have htrace : WordTrace (prefixWord ++ tailWord_2748109) baseStart_2748109 baseEnd_2748109 := by
    simpa [prefixWord, tailWord_2748109, baseEnd_2748109] using wordTrace_append hprefix tailTrace_2748109
  have hstable : (prefixWord ++ tailWord_2748109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748109).length < 2 ^ (prefixWord ++ tailWord_2748109).sum := by decide
  have hdescent : baseEnd_2748109 < baseStart_2748109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748115 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 5, 6, 2]
def baseStart_2748115 : Nat := 118140960795 + 2748115 * 2 ^ 59
def prefixEnd_2748115 : Nat := 4983230072969 + 3 ^ 40 * 2748115 * 2
def baseEnd_2748115 : Nat := 1411103888830620721124155

theorem tailTrace_2748115 : CollatzResearch.WordTrace tailWord_2748115 prefixEnd_2748115 1411103888830620721124155 := by
  unfold tailWord_2748115
  simp only [CollatzResearch.WordTrace]
  refine ⟨100231988439056170520989799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66821325626037447013993199 100231988439056170520989799)
  ·
    refine ⟨150347982658584255781484699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100231988439056170520989799 150347982658584255781484699)
    ·
      refine ⟨225521973987876383672227049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150347982658584255781484699 225521973987876383672227049)
      ·
        refine ⟨169141480490907287754170287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225521973987876383672227049 169141480490907287754170287)
        ·
          refine ⟨253712220736360931631255431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169141480490907287754170287 253712220736360931631255431)
          ·
            refine ⟨380568331104541397446883147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253712220736360931631255431 380568331104541397446883147)
            ·
              refine ⟨570852496656812096170324721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380568331104541397446883147 570852496656812096170324721)
              ·
                refine ⟨428139372492609072127743541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570852496656812096170324721 428139372492609072127743541)
                ·
                  refine ⟨40138066171182100511975957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 428139372492609072127743541 40138066171182100511975957)
                  ·
                    refine ⟨1881471851774160961498873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40138066171182100511975957 1881471851774160961498873)
                    ·
                      refine ⟨1411103888830620721124155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1881471851774160961498873 1411103888830620721124155)
                      ·
                        rfl

theorem cell23_2748115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 6, 2].length) (baseStart_2748115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748115 prefixEnd_2748115 := by exact prefixLift 2748115
  have htrace : WordTrace (prefixWord ++ tailWord_2748115) baseStart_2748115 baseEnd_2748115 := by
    simpa [prefixWord, tailWord_2748115, baseEnd_2748115] using wordTrace_append hprefix tailTrace_2748115
  have hstable : (prefixWord ++ tailWord_2748115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748115).length < 2 ^ (prefixWord ++ tailWord_2748115).sum := by decide
  have hdescent : baseEnd_2748115 < baseStart_2748115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748172 : List Nat := [2, 2, 1, 2, 2, 1, 6, 1, 6]
def baseStart_2748172 : Nat := 118140960795 + 2748172 * 2 ^ 59
def prefixEnd_2748172 : Nat := 4983230072969 + 3 ^ 40 * 2748172 * 2
def baseEnd_2748172 : Nat := 156792573025325222012377

theorem tailTrace_2748172 : CollatzResearch.WordTrace tailWord_2748172 prefixEnd_2748172 156792573025325222012377 := by
  unfold tailWord_2748172
  simp only [CollatzResearch.WordTrace]
  refine ⟨50117033699924834627907385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66822711599899779503876513 50117033699924834627907385)
  ·
    refine ⟨37587775274943625970930539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50117033699924834627907385 37587775274943625970930539)
    ·
      refine ⟨56381662912415438956395809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37587775274943625970930539 56381662912415438956395809)
      ·
        refine ⟨42286247184311579217296857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56381662912415438956395809 42286247184311579217296857)
        ·
          refine ⟨31714685388233684412972643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42286247184311579217296857 31714685388233684412972643)
          ·
            refine ⟨47572028082350526619458965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31714685388233684412972643 47572028082350526619458965)
            ·
              refine ⟨2229938816360180935287139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47572028082350526619458965 2229938816360180935287139)
              ·
                refine ⟨3344908224540271402930709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2229938816360180935287139 3344908224540271402930709)
                ·
                  refine ⟨156792573025325222012377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3344908224540271402930709 156792573025325222012377)
                  ·
                    rfl

theorem cell23_2748172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 6].length) (baseStart_2748172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748172 prefixEnd_2748172 := by exact prefixLift 2748172
  have htrace : WordTrace (prefixWord ++ tailWord_2748172) baseStart_2748172 baseEnd_2748172 := by
    simpa [prefixWord, tailWord_2748172, baseEnd_2748172] using wordTrace_append hprefix tailTrace_2748172
  have hstable : (prefixWord ++ tailWord_2748172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748172).length < 2 ^ (prefixWord ++ tailWord_2748172).sum := by decide
  have hdescent : baseEnd_2748172 < baseStart_2748172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748209 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 2, 3, 2]
def baseStart_2748209 : Nat := 118140960795 + 2748209 * 2 ^ 59
def prefixEnd_2748209 : Nat := 4983230072969 + 3 ^ 40 * 2748209 * 2
def baseEnd_2748209 : Nat := 1411152156012143353348723

theorem tailTrace_2748209 : CollatzResearch.WordTrace tailWord_2748209 prefixEnd_2748209 1411152156012143353348723 := by
  unfold tailWord_2748209
  simp only [CollatzResearch.WordTrace]
  refine ⟨100235416900715624574911681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66823611267143749716607787 100235416900715624574911681)
  ·
    refine ⟨75176562675536718431183761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100235416900715624574911681 75176562675536718431183761)
    ·
      refine ⟨56382422006652538823387821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75176562675536718431183761 56382422006652538823387821)
      ·
        refine ⟨21143408252494702058770433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56382422006652538823387821 21143408252494702058770433)
        ·
          refine ⟨15857556189371026544077825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21143408252494702058770433 15857556189371026544077825)
          ·
            refine ⟨11893167142028269908058369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15857556189371026544077825 11893167142028269908058369)
            ·
              refine ⟨8919875356521202431043777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11893167142028269908058369 8919875356521202431043777)
              ·
                refine ⟨6689906517390901823282833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8919875356521202431043777 6689906517390901823282833)
                ·
                  refine ⟨5017429888043176367462125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6689906517390901823282833 5017429888043176367462125)
                  ·
                    refine ⟨1881536208016191137798297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5017429888043176367462125 1881536208016191137798297)
                    ·
                      refine ⟨1411152156012143353348723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1881536208016191137798297 1411152156012143353348723)
                      ·
                        rfl

theorem cell23_2748209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_2748209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748209 prefixEnd_2748209 := by exact prefixLift 2748209
  have htrace : WordTrace (prefixWord ++ tailWord_2748209) baseStart_2748209 baseEnd_2748209 := by
    simpa [prefixWord, tailWord_2748209, baseEnd_2748209] using wordTrace_append hprefix tailTrace_2748209
  have hstable : (prefixWord ++ tailWord_2748209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748209).length < 2 ^ (prefixWord ++ tailWord_2748209).sum := by decide
  have hdescent : baseEnd_2748209 < baseStart_2748209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748216 : List Nat := [2, 1, 2, 1, 3, 4, 1, 4, 1, 1, 3]
def baseStart_2748216 : Nat := 118140960795 + 2748216 * 2 ^ 59
def prefixEnd_2748216 : Nat := 4983230072969 + 3 ^ 40 * 2748216 * 2
def baseEnd_2748216 : Nat := 1411155750376724825961191

theorem tailTrace_2748216 : CollatzResearch.WordTrace tailWord_2748216 prefixEnd_2748216 1411155750376724825961191 := by
  unfold tailWord_2748216
  simp only [CollatzResearch.WordTrace]
  refine ⟨50117836105845132385208251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66823781474460176513611001 50117836105845132385208251)
  ·
    refine ⟨75176754158767698577812377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50117836105845132385208251 75176754158767698577812377)
    ·
      refine ⟨56382565619075773933359283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75176754158767698577812377 56382565619075773933359283)
      ·
        refine ⟨84573848428613660900038925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56382565619075773933359283 84573848428613660900038925)
        ·
          refine ⟨31715193160730122837514597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84573848428613660900038925 31715193160730122837514597)
          ·
            refine ⟨5946598717636898032033987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31715193160730122837514597 5946598717636898032033987)
            ·
              refine ⟨8919898076455347048050981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5946598717636898032033987 8919898076455347048050981)
              ·
                refine ⟨1672480889335377571509559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8919898076455347048050981 1672480889335377571509559)
                ·
                  refine ⟨2508721334003066357264339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672480889335377571509559 2508721334003066357264339)
                  ·
                    refine ⟨3763082001004599535896509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2508721334003066357264339 3763082001004599535896509)
                    ·
                      refine ⟨1411155750376724825961191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3763082001004599535896509 1411155750376724825961191)
                      ·
                        rfl

theorem cell23_2748216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 1, 1, 3].length) (baseStart_2748216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748216 prefixEnd_2748216 := by exact prefixLift 2748216
  have htrace : WordTrace (prefixWord ++ tailWord_2748216) baseStart_2748216 baseEnd_2748216 := by
    simpa [prefixWord, tailWord_2748216, baseEnd_2748216] using wordTrace_append hprefix tailTrace_2748216
  have hstable : (prefixWord ++ tailWord_2748216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748216).length < 2 ^ (prefixWord ++ tailWord_2748216).sum := by decide
  have hdescent : baseEnd_2748216 < baseStart_2748216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748232 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 1, 6]
def baseStart_2748232 : Nat := 118140960795 + 2748232 * 2 ^ 59
def prefixEnd_2748232 : Nat := 4983230072969 + 3 ^ 40 * 2748232 * 2
def baseEnd_2748232 : Nat := 470387988689065587787039

theorem tailTrace_2748232 : CollatzResearch.WordTrace tailWord_2748232 prefixEnd_2748232 470387988689065587787039 := by
  unfold tailWord_2748232
  simp only [CollatzResearch.WordTrace]
  refine ⟨50118127889816149751499475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66824170519754866335332633 50118127889816149751499475)
  ·
    refine ⟨75177191834724224627249213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50118127889816149751499475 75177191834724224627249213)
    ·
      refine ⟨28191446938021584235218455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75177191834724224627249213 28191446938021584235218455)
      ·
        refine ⟨42287170407032376352827683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28191446938021584235218455 42287170407032376352827683)
        ·
          refine ⟨63430755610548564529241525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42287170407032376352827683 63430755610548564529241525)
          ·
            refine ⟨5946633338488927924616393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63430755610548564529241525 5946633338488927924616393)
            ·
              refine ⟨4459975003866695943462295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5946633338488927924616393 4459975003866695943462295)
              ·
                refine ⟨6689962505800043915193443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4459975003866695943462295 6689962505800043915193443)
                ·
                  refine ⟨10034943758700065872790165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6689962505800043915193443 10034943758700065872790165)
                  ·
                    refine ⟨470387988689065587787039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10034943758700065872790165 470387988689065587787039)
                    ·
                      rfl

theorem cell23_2748232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_2748232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748232 prefixEnd_2748232 := by exact prefixLift 2748232
  have htrace : WordTrace (prefixWord ++ tailWord_2748232) baseStart_2748232 baseEnd_2748232 := by
    simpa [prefixWord, tailWord_2748232, baseEnd_2748232] using wordTrace_append hprefix tailTrace_2748232
  have hstable : (prefixWord ++ tailWord_2748232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748232).length < 2 ^ (prefixWord ++ tailWord_2748232).sum := by decide
  have hdescent : baseEnd_2748232 < baseStart_2748232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748256 : List Nat := [2, 1, 1, 3, 3, 4, 2, 1, 1, 1, 4]
def baseStart_2748256 : Nat := 118140960795 + 2748256 * 2 ^ 59
def prefixEnd_2748256 : Nat := 4983230072969 + 3 ^ 40 * 2748256 * 2
def baseEnd_2748256 : Nat := 1411176289602904669461007

theorem tailTrace_2748256 : CollatzResearch.WordTrace tailWord_2748256 prefixEnd_2748256 1411176289602904669461007 := by
  unfold tailWord_2748256
  simp only [CollatzResearch.WordTrace]
  refine ⟨50118565565772675800936311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66824754087696901067915081 50118565565772675800936311)
  ·
    refine ⟨75177848348659013701404467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50118565565772675800936311 75177848348659013701404467)
    ·
      refine ⟨112766772522988520552106701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75177848348659013701404467 112766772522988520552106701)
      ·
        refine ⟨42287539696120695207040013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112766772522988520552106701 42287539696120695207040013)
        ·
          refine ⟨15857827386045260702640005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42287539696120695207040013 15857827386045260702640005)
          ·
            refine ⟨2973342634883486381745001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15857827386045260702640005 2973342634883486381745001)
            ·
              refine ⟨2230006976162614786308751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2973342634883486381745001 2230006976162614786308751)
              ·
                refine ⟨3345010464243922179463127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2230006976162614786308751 3345010464243922179463127)
                ·
                  refine ⟨5017515696365883269194691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345010464243922179463127 5017515696365883269194691)
                  ·
                    refine ⟨7526273544548824903792037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5017515696365883269194691 7526273544548824903792037)
                    ·
                      refine ⟨1411176289602904669461007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7526273544548824903792037 1411176289602904669461007)
                      ·
                        rfl

theorem cell23_2748256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_2748256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748256 prefixEnd_2748256 := by exact prefixLift 2748256
  have htrace : WordTrace (prefixWord ++ tailWord_2748256) baseStart_2748256 baseEnd_2748256 := by
    simpa [prefixWord, tailWord_2748256, baseEnd_2748256] using wordTrace_append hprefix tailTrace_2748256
  have hstable : (prefixWord ++ tailWord_2748256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748256).length < 2 ^ (prefixWord ++ tailWord_2748256).sum := by decide
  have hdescent : baseEnd_2748256 < baseStart_2748256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748266 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 4, 4]
def baseStart_2748266 : Nat := 118140960795 + 2748266 * 2 ^ 59
def prefixEnd_2748266 : Nat := 4983230072969 + 3 ^ 40 * 2748266 * 2
def baseEnd_2748266 : Nat := 470393808136483210111987

theorem tailTrace_2748266 : CollatzResearch.WordTrace tailWord_2748266 prefixEnd_2748266 470393808136483210111987 := by
  unfold tailWord_2748266
  simp only [CollatzResearch.WordTrace]
  refine ⟨25059373965377280827434163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66824997241006082206491101 25059373965377280827434163)
  ·
    refine ⟨37589060948065921241151245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25059373965377280827434163 37589060948065921241151245)
    ·
      refine ⟨14095897855524720465431717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37589060948065921241151245 14095897855524720465431717)
      ·
        refine ⟨2642980847910885087268447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14095897855524720465431717 2642980847910885087268447)
        ·
          refine ⟨3964471271866327630902671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2642980847910885087268447 3964471271866327630902671)
          ·
            refine ⟨5946706907799491446354007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3964471271866327630902671 5946706907799491446354007)
            ·
              refine ⟨8920060361699237169531011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5946706907799491446354007 8920060361699237169531011)
              ·
                refine ⟨13380090542548855754296517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8920060361699237169531011 13380090542548855754296517)
                ·
                  refine ⟨2508766976727910453930597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13380090542548855754296517 2508766976727910453930597)
                  ·
                    refine ⟨470393808136483210111987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2508766976727910453930597 470393808136483210111987)
                    ·
                      rfl

theorem cell23_2748266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_2748266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748266 prefixEnd_2748266 := by exact prefixLift 2748266
  have htrace : WordTrace (prefixWord ++ tailWord_2748266) baseStart_2748266 baseEnd_2748266 := by
    simpa [prefixWord, tailWord_2748266, baseEnd_2748266] using wordTrace_append hprefix tailTrace_2748266
  have hstable : (prefixWord ++ tailWord_2748266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748266).length < 2 ^ (prefixWord ++ tailWord_2748266).sum := by decide
  have hdescent : baseEnd_2748266 < baseStart_2748266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748286 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2748286 : Nat := 118140960795 + 2748286 * 2 ^ 59
def prefixEnd_2748286 : Nat := 4983230072969 + 3 ^ 40 * 2748286 * 2
def baseEnd_2748286 : Nat := 1411191694022539552085869

theorem tailTrace_2748286 : CollatzResearch.WordTrace tailWord_2748286 prefixEnd_2748286 1411191694022539552085869 := by
  unfold tailWord_2748286
  simp only [CollatzResearch.WordTrace]
  refine ⟨12529778165179583340683089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66825483547624444483643141 12529778165179583340683089)
  ·
    refine ⟨9397333623884687505512317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12529778165179583340683089 9397333623884687505512317)
    ·
      refine ⟨3524000108956757814567119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9397333623884687505512317 3524000108956757814567119)
      ·
        refine ⟨5286000163435136721850679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3524000108956757814567119 5286000163435136721850679)
        ·
          refine ⟨7929000245152705082776019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5286000163435136721850679 7929000245152705082776019)
          ·
            refine ⟨11893500367729057624164029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7929000245152705082776019 11893500367729057624164029)
            ·
              refine ⟨4460062637898396609061511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11893500367729057624164029 4460062637898396609061511)
              ·
                refine ⟨6690093956847594913592267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4460062637898396609061511 6690093956847594913592267)
                ·
                  refine ⟨10035140935271392370388401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6690093956847594913592267 10035140935271392370388401)
                  ·
                    refine ⟨7526355701453544277791301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10035140935271392370388401 7526355701453544277791301)
                    ·
                      refine ⟨1411191694022539552085869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7526355701453544277791301 1411191694022539552085869)
                      ·
                        rfl

theorem cell23_2748286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2748286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748286 prefixEnd_2748286 := by exact prefixLift 2748286
  have htrace : WordTrace (prefixWord ++ tailWord_2748286) baseStart_2748286 baseEnd_2748286 := by
    simpa [prefixWord, tailWord_2748286, baseEnd_2748286] using wordTrace_append hprefix tailTrace_2748286
  have hstable : (prefixWord ++ tailWord_2748286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748286).length < 2 ^ (prefixWord ++ tailWord_2748286).sum := by decide
  have hdescent : baseEnd_2748286 < baseStart_2748286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748296 : List Nat := [2, 1, 3, 3, 4, 1, 2, 7]
def baseStart_2748296 : Nat := 118140960795 + 2748296 * 2 ^ 59
def prefixEnd_2748296 : Nat := 4983230072969 + 3 ^ 40 * 2748296 * 2
def baseEnd_2748296 : Nat := 52266549215892018998549

theorem tailTrace_2748296 : CollatzResearch.WordTrace tailWord_2748296 prefixEnd_2748296 52266549215892018998549 := by
  unfold tailWord_2748296
  simp only [CollatzResearch.WordTrace]
  refine ⟨50119295025700219216664371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66825726700933625622219161 50119295025700219216664371)
  ·
    refine ⟨75178942538550328824996557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50119295025700219216664371 75178942538550328824996557)
    ·
      refine ⟨28192103451956373309373709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75178942538550328824996557 28192103451956373309373709)
      ·
        refine ⟨10572038794483639991015141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28192103451956373309373709 10572038794483639991015141)
        ·
          refine ⟨1982257273965682498315339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10572038794483639991015141 1982257273965682498315339)
          ·
            refine ⟨2973385910948523747473009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982257273965682498315339 2973385910948523747473009)
            ·
              refine ⟨2230039433211392810604757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2973385910948523747473009 2230039433211392810604757)
              ·
                refine ⟨52266549215892018998549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2230039433211392810604757 52266549215892018998549)
                ·
                  rfl

theorem cell23_2748296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 7].length) (baseStart_2748296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748296 prefixEnd_2748296 := by exact prefixLift 2748296
  have htrace : WordTrace (prefixWord ++ tailWord_2748296) baseStart_2748296 baseEnd_2748296 := by
    simpa [prefixWord, tailWord_2748296, baseEnd_2748296] using wordTrace_append hprefix tailTrace_2748296
  have hstable : (prefixWord ++ tailWord_2748296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748296).length < 2 ^ (prefixWord ++ tailWord_2748296).sum := by decide
  have hdescent : baseEnd_2748296 < baseStart_2748296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748305 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 1, 8]
def baseStart_2748305 : Nat := 118140960795 + 2748305 * 2 ^ 59
def prefixEnd_2748305 : Nat := 4983230072969 + 3 ^ 40 * 2748305 * 2
def baseEnd_2748305 : Nat := 470400483384991659249427

theorem tailTrace_2748305 : CollatzResearch.WordTrace tailWord_2748305 prefixEnd_2748305 470400483384991659249427 := by
  unfold tailWord_2748305
  simp only [CollatzResearch.WordTrace]
  refine ⟨100238918308367832970406369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66825945538911888646937579 100238918308367832970406369)
  ·
    refine ⟨75179188731275874727804777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100238918308367832970406369 75179188731275874727804777)
    ·
      refine ⟨56384391548456906045853583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75179188731275874727804777 56384391548456906045853583)
      ·
        refine ⟨84576587322685359068780375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56384391548456906045853583 84576587322685359068780375)
        ·
          refine ⟨126864880984028038603170563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84576587322685359068780375 126864880984028038603170563)
          ·
            refine ⟨190297321476042057904755845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126864880984028038603170563 190297321476042057904755845)
            ·
              refine ⟨35680747776757885857141721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190297321476042057904755845 35680747776757885857141721)
              ·
                refine ⟨26760560832568414392856291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35680747776757885857141721 26760560832568414392856291)
                ·
                  refine ⟨40140841248852621589284437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26760560832568414392856291 40140841248852621589284437)
                  ·
                    refine ⟨470400483384991659249427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40140841248852621589284437 470400483384991659249427)
                    ·
                      rfl

theorem cell23_2748305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_2748305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748305 prefixEnd_2748305 := by exact prefixLift 2748305
  have htrace : WordTrace (prefixWord ++ tailWord_2748305) baseStart_2748305 baseEnd_2748305 := by
    simpa [prefixWord, tailWord_2748305, baseEnd_2748305] using wordTrace_append hprefix tailTrace_2748305
  have hstable : (prefixWord ++ tailWord_2748305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748305).length < 2 ^ (prefixWord ++ tailWord_2748305).sum := by decide
  have hdescent : baseEnd_2748305 < baseStart_2748305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748306 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_2748306 : Nat := 118140960795 + 2748306 * 2 ^ 59
def prefixEnd_2748306 : Nat := 4983230072969 + 3 ^ 40 * 2748306 * 2
def baseEnd_2748306 : Nat := 1411201963635629473835777

theorem tailTrace_2748306 : CollatzResearch.WordTrace tailWord_2748306 prefixEnd_2748306 1411201963635629473835777 := by
  unfold tailWord_2748306
  simp only [CollatzResearch.WordTrace]
  refine ⟨25059738695341052535298193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66825969854242806760795181 25059738695341052535298193)
  ·
    refine ⟨18794804021505789401473645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25059738695341052535298193 18794804021505789401473645)
    ·
      refine ⟨7048051508064671025552617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18794804021505789401473645 7048051508064671025552617)
      ·
        refine ⟨5286038631048503269164463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7048051508064671025552617 5286038631048503269164463)
        ·
          refine ⟨7929057946572754903746695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5286038631048503269164463 7929057946572754903746695)
          ·
            refine ⟨11893586919859132355620043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7929057946572754903746695 11893586919859132355620043)
            ·
              refine ⟨17840380379788698533430065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11893586919859132355620043 17840380379788698533430065)
              ·
                refine ⟨13380285284841523900072549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17840380379788698533430065 13380285284841523900072549)
                ·
                  refine ⟨2508803490907785731263603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13380285284841523900072549 2508803490907785731263603)
                  ·
                    refine ⟨3763205236361678596895405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2508803490907785731263603 3763205236361678596895405)
                    ·
                      refine ⟨1411201963635629473835777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3763205236361678596895405 1411201963635629473835777)
                      ·
                        rfl

theorem cell23_2748306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_2748306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748306 prefixEnd_2748306 := by exact prefixLift 2748306
  have htrace : WordTrace (prefixWord ++ tailWord_2748306) baseStart_2748306 baseEnd_2748306 := by
    simpa [prefixWord, tailWord_2748306, baseEnd_2748306] using wordTrace_append hprefix tailTrace_2748306
  have hstable : (prefixWord ++ tailWord_2748306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748306).length < 2 ^ (prefixWord ++ tailWord_2748306).sum := by decide
  have hdescent : baseEnd_2748306 < baseStart_2748306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748334 : List Nat := [4, 1, 5, 1, 2, 1, 2, 1, 2, 4]
def baseStart_2748334 : Nat := 118140960795 + 2748334 * 2 ^ 59
def prefixEnd_2748334 : Nat := 4983230072969 + 3 ^ 40 * 2748334 * 2
def baseEnd_2748334 : Nat := 470405447031318454761883

theorem tailTrace_2748334 : CollatzResearch.WordTrace tailWord_2748334 prefixEnd_2748334 470405447031318454761883 := by
  unfold tailWord_2748334
  simp only [CollatzResearch.WordTrace]
  refine ⟨12529997003157846365401507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66826650683508513948808037 12529997003157846365401507)
  ·
    refine ⟨18794995504736769548102261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12529997003157846365401507 18794995504736769548102261)
    ·
      refine ⟨1762030828569072145134587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18794995504736769548102261 1762030828569072145134587)
      ·
        refine ⟨2643046242853608217701881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1762030828569072145134587 2643046242853608217701881)
        ·
          refine ⟨1982284682140206163276411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2643046242853608217701881 1982284682140206163276411)
          ·
            refine ⟨2973427023210309244914617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982284682140206163276411 2973427023210309244914617)
            ·
              refine ⟨2230070267407731933685963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2973427023210309244914617 2230070267407731933685963)
              ·
                refine ⟨3345105401111597900528945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2230070267407731933685963 3345105401111597900528945)
                ·
                  refine ⟨2508829050833698425396709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3345105401111597900528945 2508829050833698425396709)
                  ·
                    refine ⟨470405447031318454761883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2508829050833698425396709 470405447031318454761883)
                    ·
                      rfl

theorem cell23_2748334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_2748334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748334 prefixEnd_2748334 := by exact prefixLift 2748334
  have htrace : WordTrace (prefixWord ++ tailWord_2748334) baseStart_2748334 baseEnd_2748334 := by
    simpa [prefixWord, tailWord_2748334, baseEnd_2748334] using wordTrace_append hprefix tailTrace_2748334
  have hstable : (prefixWord ++ tailWord_2748334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748334).length < 2 ^ (prefixWord ++ tailWord_2748334).sum := by decide
  have hdescent : baseEnd_2748334 < baseStart_2748334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748340 : List Nat := [2, 5, 2, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_2748340 : Nat := 118140960795 + 2748340 * 2 ^ 59
def prefixEnd_2748340 : Nat := 4983230072969 + 3 ^ 40 * 2748340 * 2
def baseEnd_2748340 : Nat := 1411219421977882340810621

theorem tailTrace_2748340 : CollatzResearch.WordTrace tailWord_2748340 prefixEnd_2748340 1411219421977882340810621 := by
  unfold tailWord_2748340
  simp only [CollatzResearch.WordTrace]
  refine ⟨50120097431620516973965237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66826796575494022631953649 50120097431620516973965237)
  ·
    refine ⟨4698759134214423466309241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50120097431620516973965237 4698759134214423466309241)
    ·
      refine ⟨3524069350660817599731931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4698759134214423466309241 3524069350660817599731931)
      ·
        refine ⟨5286104025991226399597897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3524069350660817599731931 5286104025991226399597897)
        ·
          refine ⟨3964578019493419799698423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5286104025991226399597897 3964578019493419799698423)
          ·
            refine ⟨5946867029240129699547635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3964578019493419799698423 5946867029240129699547635)
            ·
              refine ⟨8920300543860194549321453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5946867029240129699547635 8920300543860194549321453)
              ·
                refine ⟨3345112703947572955995545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8920300543860194549321453 3345112703947572955995545)
                ·
                  refine ⟨2508834527960679716996659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3345112703947572955995545 2508834527960679716996659)
                  ·
                    refine ⟨3763251791941019575494989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2508834527960679716996659 3763251791941019575494989)
                    ·
                      refine ⟨1411219421977882340810621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3763251791941019575494989 1411219421977882340810621)
                      ·
                        rfl

theorem cell23_2748340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_2748340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748340 prefixEnd_2748340 := by exact prefixLift 2748340
  have htrace : WordTrace (prefixWord ++ tailWord_2748340) baseStart_2748340 baseEnd_2748340 := by
    simpa [prefixWord, tailWord_2748340, baseEnd_2748340] using wordTrace_append hprefix tailTrace_2748340
  have hstable : (prefixWord ++ tailWord_2748340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748340).length < 2 ^ (prefixWord ++ tailWord_2748340).sum := by decide
  have hdescent : baseEnd_2748340 < baseStart_2748340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748489 : List Nat := [1, 2, 1, 1, 2, 2, 3, 5, 1, 5]
def baseStart_2748489 : Nat := 118140960795 + 2748489 * 2 ^ 59
def prefixEnd_2748489 : Nat := 4983230072969 + 3 ^ 40 * 2748489 * 2
def baseEnd_2748489 : Nat := 470431976865134085949145

theorem tailTrace_2748489 : CollatzResearch.WordTrace tailWord_2748489 prefixEnd_2748489 470431976865134085949145 := by
  unfold tailWord_2748489
  simp only [CollatzResearch.WordTrace]
  refine ⟨100245629339701232395104521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66830419559800821596736347 100245629339701232395104521)
  ·
    refine ⟨75184222004775924296328391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100245629339701232395104521 75184222004775924296328391)
    ·
      refine ⟨112776333007163886444492587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75184222004775924296328391 112776333007163886444492587)
      ·
        refine ⟨169164499510745829666738881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112776333007163886444492587 169164499510745829666738881)
        ·
          refine ⟨126873374633059372250054161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169164499510745829666738881 126873374633059372250054161)
          ·
            refine ⟨95155030974794529187540621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126873374633059372250054161 95155030974794529187540621)
            ·
              refine ⟨35683136615547948445327733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95155030974794529187540621 35683136615547948445327733)
              ·
                refine ⟨3345294057707620166749475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35683136615547948445327733 3345294057707620166749475)
                ·
                  refine ⟨5017941086561430250124213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345294057707620166749475 5017941086561430250124213)
                  ·
                    refine ⟨470431976865134085949145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5017941086561430250124213 470431976865134085949145)
                    ·
                      rfl

theorem cell23_2748489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 5].length) (baseStart_2748489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748489 prefixEnd_2748489 := by exact prefixLift 2748489
  have htrace : WordTrace (prefixWord ++ tailWord_2748489) baseStart_2748489 baseEnd_2748489 := by
    simpa [prefixWord, tailWord_2748489, baseEnd_2748489] using wordTrace_append hprefix tailTrace_2748489
  have hstable : (prefixWord ++ tailWord_2748489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748489).length < 2 ^ (prefixWord ++ tailWord_2748489).sum := by decide
  have hdescent : baseEnd_2748489 < baseStart_2748489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748503 : List Nat := [1, 1, 3, 2, 2, 1, 2, 6, 1, 1, 3]
def baseStart_2748503 : Nat := 118140960795 + 2748503 * 2 ^ 59
def prefixEnd_2748503 : Nat := 4983230072969 + 3 ^ 40 * 2748503 * 2
def baseEnd_2748503 : Nat := 1411303119324565203072371

theorem tailTrace_2748503 : CollatzResearch.WordTrace tailWord_2748503 prefixEnd_2748503 1411303119324565203072371 := by
  unfold tailWord_2748503
  simp only [CollatzResearch.WordTrace]
  refine ⟨100246139961650512786114163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66830759974433675190742775 100246139961650512786114163)
  ·
    refine ⟨150369209942475769179171245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100246139961650512786114163 150369209942475769179171245)
    ·
      refine ⟨56388453728428413442189217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150369209942475769179171245 56388453728428413442189217)
      ·
        refine ⟨42291340296321310081641913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56388453728428413442189217 42291340296321310081641913)
        ·
          refine ⟨31718505222240982561231435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42291340296321310081641913 31718505222240982561231435)
          ·
            refine ⟨47577757833361473841847153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31718505222240982561231435 47577757833361473841847153)
            ·
              refine ⟨35683318375021105381385365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47577757833361473841847153 35683318375021105381385365)
              ·
                refine ⟨1672655548829114314752439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35683318375021105381385365 1672655548829114314752439)
                ·
                  refine ⟨2508983323243671472128659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672655548829114314752439 2508983323243671472128659)
                  ·
                    refine ⟨3763474984865507208192989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2508983323243671472128659 3763474984865507208192989)
                    ·
                      refine ⟨1411303119324565203072371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3763474984865507208192989 1411303119324565203072371)
                      ·
                        rfl

theorem cell23_2748503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_2748503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748503 prefixEnd_2748503 := by exact prefixLift 2748503
  have htrace : WordTrace (prefixWord ++ tailWord_2748503) baseStart_2748503 baseEnd_2748503 := by
    simpa [prefixWord, tailWord_2748503, baseEnd_2748503] using wordTrace_append hprefix tailTrace_2748503
  have hstable : (prefixWord ++ tailWord_2748503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748503).length < 2 ^ (prefixWord ++ tailWord_2748503).sum := by decide
  have hdescent : baseEnd_2748503 < baseStart_2748503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748510 : List Nat := [4, 4, 1, 1, 2, 1, 1, 3, 6]
def baseStart_2748510 : Nat := 118140960795 + 2748510 * 2 ^ 59
def prefixEnd_2748510 : Nat := 4983230072969 + 3 ^ 40 * 2748510 * 2
def baseEnd_2748510 : Nat := 156811857076571852853871

theorem tailTrace_2748510 : CollatzResearch.WordTrace tailWord_2748510 prefixEnd_2748510 156811857076571852853871 := by
  unfold tailWord_2748510
  simp only [CollatzResearch.WordTrace]
  refine ⟨12530799409078144122702373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66830930181750101987745989 12530799409078144122702373)
  ·
    refine ⟨2349524889202152023006695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12530799409078144122702373 2349524889202152023006695)
    ·
      refine ⟨3524287333803228034510043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2349524889202152023006695 3524287333803228034510043)
      ·
        refine ⟨5286431000704842051765065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3524287333803228034510043 5286431000704842051765065)
        ·
          refine ⟨3964823250528631538823799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5286431000704842051765065 3964823250528631538823799)
          ·
            refine ⟨5947234875792947308235699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3964823250528631538823799 5947234875792947308235699)
            ·
              refine ⟨8920852313689420962353549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5947234875792947308235699 8920852313689420962353549)
              ·
                refine ⟨3345319617633532860882581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8920852313689420962353549 3345319617633532860882581)
                ·
                  refine ⟨156811857076571852853871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3345319617633532860882581 156811857076571852853871)
                  ·
                    rfl

theorem cell23_2748510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_2748510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748510 prefixEnd_2748510 := by exact prefixLift 2748510
  have htrace : WordTrace (prefixWord ++ tailWord_2748510) baseStart_2748510 baseEnd_2748510 := by
    simpa [prefixWord, tailWord_2748510, baseEnd_2748510] using wordTrace_append hprefix tailTrace_2748510
  have hstable : (prefixWord ++ tailWord_2748510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748510).length < 2 ^ (prefixWord ++ tailWord_2748510).sum := by decide
  have hdescent : baseEnd_2748510 < baseStart_2748510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748519 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 1, 6]
def baseStart_2748519 : Nat := 118140960795 + 2748519 * 2 ^ 59
def prefixEnd_2748519 : Nat := 4983230072969 + 3 ^ 40 * 2748519 * 2
def baseEnd_2748519 : Nat := 470437111671679046824099

theorem tailTrace_2748519 : CollatzResearch.WordTrace tailWord_2748519 prefixEnd_2748519 470437111671679046824099 := by
  unfold tailWord_2748519
  simp only [CollatzResearch.WordTrace]
  refine ⟨100246723529592547518696611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66831149019728365012464407 100246723529592547518696611)
  ·
    refine ⟨150370085294388821278044917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100246723529592547518696611 150370085294388821278044917)
    ·
      refine ⟨14097195496348951994816711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150370085294388821278044917 14097195496348951994816711)
      ·
        refine ⟨21145793244523427992225067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14097195496348951994816711 21145793244523427992225067)
        ·
          refine ⟨31718689866785141988337601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21145793244523427992225067 31718689866785141988337601)
          ·
            refine ⟨23789017400088856491253201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31718689866785141988337601 23789017400088856491253201)
            ·
              refine ⟨17841763050066642368439901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23789017400088856491253201 17841763050066642368439901)
              ·
                refine ⟨6690661143774990888164963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17841763050066642368439901 6690661143774990888164963)
                ·
                  refine ⟨10035991715662486332247445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6690661143774990888164963 10035991715662486332247445)
                  ·
                    refine ⟨470437111671679046824099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10035991715662486332247445 470437111671679046824099)
                    ·
                      rfl

theorem cell23_2748519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_2748519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748519 prefixEnd_2748519 := by exact prefixLift 2748519
  have htrace : WordTrace (prefixWord ++ tailWord_2748519) baseStart_2748519 baseEnd_2748519 := by
    simpa [prefixWord, tailWord_2748519, baseEnd_2748519] using wordTrace_append hprefix tailTrace_2748519
  have hstable : (prefixWord ++ tailWord_2748519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748519).length < 2 ^ (prefixWord ++ tailWord_2748519).sum := by decide
  have hdescent : baseEnd_2748519 < baseStart_2748519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748526 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_2748526 : Nat := 118140960795 + 2748526 * 2 ^ 59
def prefixEnd_2748526 : Nat := 4983230072969 + 3 ^ 40 * 2748526 * 2
def baseEnd_2748526 : Nat := 1411314929379618613084765

theorem tailTrace_2748526 : CollatzResearch.WordTrace tailWord_2748526 prefixEnd_2748526 1411314929379618613084765 := by
  unfold tailWord_2748526
  simp only [CollatzResearch.WordTrace]
  refine ⟨12530872355070898464275179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66831319227044791809467621 12530872355070898464275179)
  ·
    refine ⟨18796308532606347696412769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12530872355070898464275179 18796308532606347696412769)
    ·
      refine ⟨14097231399454760772309577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18796308532606347696412769 14097231399454760772309577)
      ·
        refine ⟨10572923549591070579232183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14097231399454760772309577 10572923549591070579232183)
        ·
          refine ⟨15859385324386605868848275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10572923549591070579232183 15859385324386605868848275)
          ·
            refine ⟨23789077986579908803272413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15859385324386605868848275 23789077986579908803272413)
            ·
              refine ⟨8920904244967465801227155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23789077986579908803272413 8920904244967465801227155)
              ·
                refine ⟨13381356367451198701840733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8920904244967465801227155 13381356367451198701840733)
                ·
                  refine ⟨5018008637794199513190275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13381356367451198701840733 5018008637794199513190275)
                  ·
                    refine ⟨7527012956691299269785413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5018008637794199513190275 7527012956691299269785413)
                    ·
                      refine ⟨1411314929379618613084765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7527012956691299269785413 1411314929379618613084765)
                      ·
                        rfl

theorem cell23_2748526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_2748526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748526 prefixEnd_2748526 := by exact prefixLift 2748526
  have htrace : WordTrace (prefixWord ++ tailWord_2748526) baseStart_2748526 baseEnd_2748526 := by
    simpa [prefixWord, tailWord_2748526, baseEnd_2748526] using wordTrace_append hprefix tailTrace_2748526
  have hstable : (prefixWord ++ tailWord_2748526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748526).length < 2 ^ (prefixWord ++ tailWord_2748526).sum := by decide
  have hdescent : baseEnd_2748526 < baseStart_2748526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748560 : List Nat := [2, 1, 1, 1, 1, 1, 7, 4, 1, 2, 2]
def baseStart_2748560 : Nat := 118140960795 + 2748560 * 2 ^ 59
def prefixEnd_2748560 : Nat := 4983230072969 + 3 ^ 40 * 2748560 * 2
def baseEnd_2748560 : Nat := 1411332387721871480059609

theorem tailTrace_2748560 : CollatzResearch.WordTrace tailWord_2748560 prefixEnd_2748560 1411332387721871480059609 := by
  unfold tailWord_2748560
  simp only [CollatzResearch.WordTrace]
  refine ⟨50124109461222005760469567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66832145948296007680626089 50124109461222005760469567)
  ·
    refine ⟨75186164191833008640704351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50124109461222005760469567 75186164191833008640704351)
    ·
      refine ⟨112779246287749512961056527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75186164191833008640704351 112779246287749512961056527)
      ·
        refine ⟨169168869431624269441584791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112779246287749512961056527 169168869431624269441584791)
        ·
          refine ⟨253753304147436404162377187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169168869431624269441584791 253753304147436404162377187)
          ·
            refine ⟨380629956221154606243565781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253753304147436404162377187 380629956221154606243565781)
            ·
              refine ⟨8921014598933311083833573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 380629956221154606243565781 8921014598933311083833573)
              ·
                refine ⟨1672690237299995828218795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8921014598933311083833573 1672690237299995828218795)
                ·
                  refine ⟨2509035355949993742328193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672690237299995828218795 2509035355949993742328193)
                  ·
                    refine ⟨1881776516962495306746145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2509035355949993742328193 1881776516962495306746145)
                    ·
                      refine ⟨1411332387721871480059609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1881776516962495306746145 1411332387721871480059609)
                      ·
                        rfl

theorem cell23_2748560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 1, 2, 2].length) (baseStart_2748560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748560 prefixEnd_2748560 := by exact prefixLift 2748560
  have htrace : WordTrace (prefixWord ++ tailWord_2748560) baseStart_2748560 baseEnd_2748560 := by
    simpa [prefixWord, tailWord_2748560, baseEnd_2748560] using wordTrace_append hprefix tailTrace_2748560
  have hstable : (prefixWord ++ tailWord_2748560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748560).length < 2 ^ (prefixWord ++ tailWord_2748560).sum := by decide
  have hdescent : baseEnd_2748560 < baseStart_2748560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748576 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 3]
def baseStart_2748576 : Nat := 118140960795 + 2748576 * 2 ^ 59
def prefixEnd_2748576 : Nat := 4983230072969 + 3 ^ 40 * 2748576 * 2
def baseEnd_2748576 : Nat := 1411340603412343417459535

theorem tailTrace_2748576 : CollatzResearch.WordTrace tailWord_2748576 prefixEnd_2748576 1411340603412343417459535 := by
  unfold tailWord_2748576
  simp only [CollatzResearch.WordTrace]
  refine ⟨50124401245193023126760791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66832534993590697502347721 50124401245193023126760791)
  ·
    refine ⟨75186601867789534690141187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50124401245193023126760791 75186601867789534690141187)
    ·
      refine ⟨112779902801684302035211781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75186601867789534690141187 112779902801684302035211781)
      ·
        refine ⟨21146231775315806631602209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112779902801684302035211781 21146231775315806631602209)
        ·
          refine ⟨15859673831486854973701657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21146231775315806631602209 15859673831486854973701657)
          ·
            refine ⟨11894755373615141230276243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15859673831486854973701657 11894755373615141230276243)
            ·
              refine ⟨17842133060422711845414365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11894755373615141230276243 17842133060422711845414365)
              ·
                refine ⟨6690799897658516942030387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17842133060422711845414365 6690799897658516942030387)
                ·
                  refine ⟨10036199846487775413045581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6690799897658516942030387 10036199846487775413045581)
                  ·
                    refine ⟨3763574942432915779892093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10036199846487775413045581 3763574942432915779892093)
                    ·
                      refine ⟨1411340603412343417459535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3763574942432915779892093 1411340603412343417459535)
                      ·
                        rfl

theorem cell23_2748576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_2748576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748576 prefixEnd_2748576 := by exact prefixLift 2748576
  have htrace : WordTrace (prefixWord ++ tailWord_2748576) baseStart_2748576 baseEnd_2748576 := by
    simpa [prefixWord, tailWord_2748576, baseEnd_2748576] using wordTrace_append hprefix tailTrace_2748576
  have hstable : (prefixWord ++ tailWord_2748576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748576).length < 2 ^ (prefixWord ++ tailWord_2748576).sum := by decide
  have hdescent : baseEnd_2748576 < baseStart_2748576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748583 : List Nat := [1, 1, 6, 2, 2, 1, 3, 7]
def baseStart_2748583 : Nat := 118140960795 + 2748583 * 2 ^ 59
def prefixEnd_2748583 : Nat := 4983230072969 + 3 ^ 40 * 2748583 * 2
def baseEnd_2748583 : Nat := 52272007325071292224889

theorem tailTrace_2748583 : CollatzResearch.WordTrace tailWord_2748583 prefixEnd_2748583 52272007325071292224889 := by
  unfold tailWord_2748583
  simp only [CollatzResearch.WordTrace]
  refine ⟨100249057801360686449026403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66832705200907124299350935 100249057801360686449026403)
  ·
    refine ⟨150373586702041029673539605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100249057801360686449026403 150373586702041029673539605)
    ·
      refine ⟨7048761876658173265947169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 150373586702041029673539605 7048761876658173265947169)
      ·
        refine ⟨5286571407493629949460377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7048761876658173265947169 5286571407493629949460377)
        ·
          refine ⟨3964928555620222462095283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5286571407493629949460377 3964928555620222462095283)
          ·
            refine ⟨5947392833430333693142925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3964928555620222462095283 5947392833430333693142925)
            ·
              refine ⟨2230272312536375134928597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5947392833430333693142925 2230272312536375134928597)
              ·
                refine ⟨52272007325071292224889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2230272312536375134928597 52272007325071292224889)
                ·
                  rfl

theorem cell23_2748583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 7].length) (baseStart_2748583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748583 prefixEnd_2748583 := by exact prefixLift 2748583
  have htrace : WordTrace (prefixWord ++ tailWord_2748583) baseStart_2748583 baseEnd_2748583 := by
    simpa [prefixWord, tailWord_2748583, baseEnd_2748583] using wordTrace_append hprefix tailTrace_2748583
  have hstable : (prefixWord ++ tailWord_2748583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748583).length < 2 ^ (prefixWord ++ tailWord_2748583).sum := by decide
  have hdescent : baseEnd_2748583 < baseStart_2748583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748603 : List Nat := [1, 1, 1, 1, 1, 2, 7, 3, 1, 3, 2]
def baseStart_2748603 : Nat := 118140960795 + 2748603 * 2 ^ 59
def prefixEnd_2748603 : Nat := 4983230072969 + 3 ^ 40 * 2748603 * 2
def baseEnd_2748603 : Nat := 1411354467390014811821911

theorem tailTrace_2748603 : CollatzResearch.WordTrace tailWord_2748603 prefixEnd_2748603 1411354467390014811821911 := by
  unfold tailWord_2748603
  simp only [CollatzResearch.WordTrace]
  refine ⟨100249787261288229864754463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66833191507525486576502975 100249787261288229864754463)
  ·
    refine ⟨150374680891932344797131695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100249787261288229864754463 150374680891932344797131695)
    ·
      refine ⟨225562021337898517195697543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150374680891932344797131695 225562021337898517195697543)
      ·
        refine ⟨338343032006847775793546315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225562021337898517195697543 338343032006847775793546315)
        ·
          refine ⟨507514548010271663690319473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338343032006847775793546315 507514548010271663690319473)
          ·
            refine ⟨380635911007703747767739605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 507514548010271663690319473 380635911007703747767739605)
            ·
              refine ⟨8921154164243056588306397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 380635911007703747767739605 8921154164243056588306397)
              ·
                refine ⟨3345432811591146220614899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8921154164243056588306397 3345432811591146220614899)
                ·
                  refine ⟨5018149217386719330922349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345432811591146220614899 5018149217386719330922349)
                  ·
                    refine ⟨1881805956520019749095881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5018149217386719330922349 1881805956520019749095881)
                    ·
                      refine ⟨1411354467390014811821911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1881805956520019749095881 1411354467390014811821911)
                      ·
                        rfl

theorem cell23_2748603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 3, 2].length) (baseStart_2748603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748603 prefixEnd_2748603 := by exact prefixLift 2748603
  have htrace : WordTrace (prefixWord ++ tailWord_2748603) baseStart_2748603 baseEnd_2748603 := by
    simpa [prefixWord, tailWord_2748603, baseEnd_2748603] using wordTrace_append hprefix tailTrace_2748603
  have hstable : (prefixWord ++ tailWord_2748603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748603).length < 2 ^ (prefixWord ++ tailWord_2748603).sum := by decide
  have hdescent : baseEnd_2748603 < baseStart_2748603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748626 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 2, 6]
def baseStart_2748626 : Nat := 118140960795 + 2748626 * 2 ^ 59
def prefixEnd_2748626 : Nat := 4983230072969 + 3 ^ 40 * 2748626 * 2
def baseEnd_2748626 : Nat := 470455425815022740611435

theorem tailTrace_2748626 : CollatzResearch.WordTrace tailWord_2748626 prefixEnd_2748626 470455425815022740611435 := by
  unfold tailWord_2748626
  simp only [CollatzResearch.WordTrace]
  refine ⟨25062656535051226198210433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66833750760136603195227821 25062656535051226198210433)
  ·
    refine ⟨18796992401288419648657825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25062656535051226198210433 18796992401288419648657825)
    ·
      refine ⟨14097744300966314736493369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18796992401288419648657825 14097744300966314736493369)
      ·
        refine ⟨10573308225724736052370027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14097744300966314736493369 10573308225724736052370027)
        ·
          refine ⟨15859962338587104078555041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10573308225724736052370027 15859962338587104078555041)
          ·
            refine ⟨11894971753940328058916281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15859962338587104078555041 11894971753940328058916281)
            ·
              refine ⟨8921228815455246044187211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11894971753940328058916281 8921228815455246044187211)
              ·
                refine ⟨13381843223182869066280817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8921228815455246044187211 13381843223182869066280817)
                ·
                  refine ⟨10036382417387151799710613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13381843223182869066280817 10036382417387151799710613)
                  ·
                    refine ⟨470455425815022740611435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10036382417387151799710613 470455425815022740611435)
                    ·
                      rfl

theorem cell23_2748626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_2748626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748626 prefixEnd_2748626 := by exact prefixLift 2748626
  have htrace : WordTrace (prefixWord ++ tailWord_2748626) baseStart_2748626 baseEnd_2748626 := by
    simpa [prefixWord, tailWord_2748626, baseEnd_2748626] using wordTrace_append hprefix tailTrace_2748626
  have hstable : (prefixWord ++ tailWord_2748626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748626).length < 2 ^ (prefixWord ++ tailWord_2748626).sum := by decide
  have hdescent : baseEnd_2748626 < baseStart_2748626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748633 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 1, 4, 2]
def baseStart_2748633 : Nat := 118140960795 + 2748633 * 2 ^ 59
def prefixEnd_2748633 : Nat := 4983230072969 + 3 ^ 40 * 2748633 * 2
def baseEnd_2748633 : Nat := 1411369871809649694446773

theorem tailTrace_2748633 : CollatzResearch.WordTrace tailWord_2748633 prefixEnd_2748633 1411369871809649694446773 := by
  unfold tailWord_2748633
  simp only [CollatzResearch.WordTrace]
  refine ⟨100250881451179544988346553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66833920967453029992231035 100250881451179544988346553)
  ·
    refine ⟨75188161088384658741259915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100250881451179544988346553 75188161088384658741259915)
    ·
      refine ⟨112782241632576988111889873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75188161088384658741259915 112782241632576988111889873)
      ·
        refine ⟨84586681224432741083917405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112782241632576988111889873 84586681224432741083917405)
        ·
          refine ⟨31720005459162277906469027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84586681224432741083917405 31720005459162277906469027)
          ·
            refine ⟨47580008188743416859703541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31720005459162277906469027 47580008188743416859703541)
            ·
              refine ⟨4460625767694695330597207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47580008188743416859703541 4460625767694695330597207)
              ·
                refine ⟨6690938651542042995895811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4460625767694695330597207 6690938651542042995895811)
                ·
                  refine ⟨10036407977313064493843717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6690938651542042995895811 10036407977313064493843717)
                  ·
                    refine ⟨1881826495746199592595697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10036407977313064493843717 1881826495746199592595697)
                    ·
                      refine ⟨1411369871809649694446773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1881826495746199592595697 1411369871809649694446773)
                      ·
                        rfl

theorem cell23_2748633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 4, 2].length) (baseStart_2748633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748633 prefixEnd_2748633 := by exact prefixLift 2748633
  have htrace : WordTrace (prefixWord ++ tailWord_2748633) baseStart_2748633 baseEnd_2748633 := by
    simpa [prefixWord, tailWord_2748633, baseEnd_2748633] using wordTrace_append hprefix tailTrace_2748633
  have hstable : (prefixWord ++ tailWord_2748633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748633).length < 2 ^ (prefixWord ++ tailWord_2748633).sum := by decide
  have hdescent : baseEnd_2748633 < baseStart_2748633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748637 : List Nat := [1, 4, 3, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_2748637 : Nat := 118140960795 + 2748637 * 2 ^ 59
def prefixEnd_2748637 : Nat := 4983230072969 + 3 ^ 40 * 2748637 * 2
def baseEnd_2748637 : Nat := 1411371925732267678796755

theorem tailTrace_2748637 : CollatzResearch.WordTrace tailWord_2748637 prefixEnd_2748637 1411371925732267678796755 := by
  unfold tailWord_2748637
  simp only [CollatzResearch.WordTrace]
  refine ⟨100251027343165053671492165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66834018228776702447661443 100251027343165053671492165)
  ·
    refine ⟨18797067626843447563404781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100251027343165053671492165 18797067626843447563404781)
    ·
      refine ⟨7048900360066292836276793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18797067626843447563404781 7048900360066292836276793)
      ·
        refine ⟨5286675270049719627207595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7048900360066292836276793 5286675270049719627207595)
        ·
          refine ⟨7930012905074579440811393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5286675270049719627207595 7930012905074579440811393)
          ·
            refine ⟨5947509678805934580608545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7930012905074579440811393 5947509678805934580608545)
            ·
              refine ⟨4460632259104450935456409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5947509678805934580608545 4460632259104450935456409)
              ·
                refine ⟨3345474194328338201592307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4460632259104450935456409 3345474194328338201592307)
                ·
                  refine ⟨5018211291492507302388461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345474194328338201592307 5018211291492507302388461)
                  ·
                    refine ⟨1881829234309690238395673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5018211291492507302388461 1881829234309690238395673)
                    ·
                      refine ⟨1411371925732267678796755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1881829234309690238395673 1411371925732267678796755)
                      ·
                        rfl

theorem cell23_2748637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_2748637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748637 prefixEnd_2748637 := by exact prefixLift 2748637
  have htrace : WordTrace (prefixWord ++ tailWord_2748637) baseStart_2748637 baseEnd_2748637 := by
    simpa [prefixWord, tailWord_2748637, baseEnd_2748637] using wordTrace_append hprefix tailTrace_2748637
  have hstable : (prefixWord ++ tailWord_2748637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748637).length < 2 ^ (prefixWord ++ tailWord_2748637).sum := by decide
  have hdescent : baseEnd_2748637 < baseStart_2748637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748653 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_2748653 : Nat := 118140960795 + 2748653 * 2 ^ 59
def prefixEnd_2748653 : Nat := 4983230072969 + 3 ^ 40 * 2748653 * 2
def baseEnd_2748653 : Nat := 1411380141422739616196681

theorem tailTrace_2748653 : CollatzResearch.WordTrace tailWord_2748653 prefixEnd_2748653 1411380141422739616196681 := by
  unfold tailWord_2748653
  simp only [CollatzResearch.WordTrace]
  refine ⟨100251610911107088404074613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66834407274071392269383075 100251610911107088404074613)
  ·
    refine ⟨9398588522916289537881995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100251610911107088404074613 9398588522916289537881995)
    ·
      refine ⟨14097882784374434306822993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9398588522916289537881995 14097882784374434306822993)
      ·
        refine ⟨10573412088280825730117245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14097882784374434306822993 10573412088280825730117245)
        ·
          refine ⟨3965029533105309648793967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10573412088280825730117245 3965029533105309648793967)
          ·
            refine ⟨5947544299657964473190951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3965029533105309648793967 5947544299657964473190951)
            ·
              refine ⟨8921316449486946709786427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5947544299657964473190951 8921316449486946709786427)
              ·
                refine ⟨13381974674230420064679641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8921316449486946709786427 13381974674230420064679641)
                ·
                  refine ⟨10036481005672815048509731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13381974674230420064679641 10036481005672815048509731)
                  ·
                    refine ⟨15054721508509222572764597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10036481005672815048509731 15054721508509222572764597)
                    ·
                      refine ⟨1411380141422739616196681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15054721508509222572764597 1411380141422739616196681)
                      ·
                        rfl

theorem cell23_2748653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_2748653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748653 prefixEnd_2748653 := by exact prefixLift 2748653
  have htrace : WordTrace (prefixWord ++ tailWord_2748653) baseStart_2748653 baseEnd_2748653 := by
    simpa [prefixWord, tailWord_2748653, baseEnd_2748653] using wordTrace_append hprefix tailTrace_2748653
  have hstable : (prefixWord ++ tailWord_2748653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748653).length < 2 ^ (prefixWord ++ tailWord_2748653).sum := by decide
  have hdescent : baseEnd_2748653 < baseStart_2748653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748686 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 4, 5]
def baseStart_2748686 : Nat := 118140960795 + 2748686 * 2 ^ 59
def prefixEnd_2748686 : Nat := 4983230072969 + 3 ^ 40 * 2748686 * 2
def baseEnd_2748686 : Nat := 470465695428112662361343

theorem tailTrace_2748686 : CollatzResearch.WordTrace tailWord_2748686 prefixEnd_2748686 470465695428112662361343 := by
  unfold tailWord_2748686
  simp only [CollatzResearch.WordTrace]
  refine ⟨12531601814998441880003239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66835209679991690026683941 12531601814998441880003239)
  ·
    refine ⟨18797402722497662820004859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12531601814998441880003239 18797402722497662820004859)
    ·
      refine ⟨28196104083746494230007289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18797402722497662820004859 28196104083746494230007289)
      ·
        refine ⟨21147078062809870672505467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28196104083746494230007289 21147078062809870672505467)
        ·
          refine ⟨31720617094214806008758201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21147078062809870672505467 31720617094214806008758201)
          ·
            refine ⟨23790462820661104506568651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31720617094214806008758201 23790462820661104506568651)
            ·
              refine ⟨35685694230991656759852977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23790462820661104506568651 35685694230991656759852977)
              ·
                refine ⟨26764270673243742569889733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35685694230991656759852977 26764270673243742569889733)
                ·
                  refine ⟨5018300751233201731854325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26764270673243742569889733 5018300751233201731854325)
                  ·
                    refine ⟨470465695428112662361343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5018300751233201731854325 470465695428112662361343)
                    ·
                      rfl

theorem cell23_2748686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_2748686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748686 prefixEnd_2748686 := by exact prefixLift 2748686
  have htrace : WordTrace (prefixWord ++ tailWord_2748686) baseStart_2748686 baseEnd_2748686 := by
    simpa [prefixWord, tailWord_2748686, baseEnd_2748686] using wordTrace_append hprefix tailTrace_2748686
  have hstable : (prefixWord ++ tailWord_2748686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748686).length < 2 ^ (prefixWord ++ tailWord_2748686).sum := by decide
  have hdescent : baseEnd_2748686 < baseStart_2748686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748699 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 2, 8]
def baseStart_2748699 : Nat := 118140960795 + 2748699 * 2 ^ 59
def prefixEnd_2748699 : Nat := 4983230072969 + 3 ^ 40 * 2748699 * 2
def baseEnd_2748699 : Nat := 470467920510948812073823

theorem tailTrace_2748699 : CollatzResearch.WordTrace tailWord_2748699 prefixEnd_2748699 470467920510948812073823 := by
  unfold tailWord_2748699
  simp only [CollatzResearch.WordTrace]
  refine ⟨100253288668940438260249151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66835525779293625506832767 100253288668940438260249151)
  ·
    refine ⟨150379933003410657390373727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100253288668940438260249151 150379933003410657390373727)
    ·
      refine ⟨225569899505115986085560591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150379933003410657390373727 225569899505115986085560591)
      ·
        refine ⟨338354849257673979128340887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225569899505115986085560591 338354849257673979128340887)
        ·
          refine ⟨507532273886510968692511331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338354849257673979128340887 507532273886510968692511331)
          ·
            refine ⟨761298410829766453038766997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507532273886510968692511331 761298410829766453038766997)
            ·
              refine ⟨35685863007645302486192203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 761298410829766453038766997 35685863007645302486192203)
              ·
                refine ⟨53528794511467953729288305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35685863007645302486192203 53528794511467953729288305)
                ·
                  refine ⟨40146595883600965296966229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53528794511467953729288305 40146595883600965296966229)
                  ·
                    refine ⟨470467920510948812073823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40146595883600965296966229 470467920510948812073823)
                    ·
                      rfl

theorem cell23_2748699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 8].length) (baseStart_2748699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748699 prefixEnd_2748699 := by exact prefixLift 2748699
  have htrace : WordTrace (prefixWord ++ tailWord_2748699) baseStart_2748699 baseEnd_2748699 := by
    simpa [prefixWord, tailWord_2748699, baseEnd_2748699] using wordTrace_append hprefix tailTrace_2748699
  have hstable : (prefixWord ++ tailWord_2748699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748699).length < 2 ^ (prefixWord ++ tailWord_2748699).sum := by decide
  have hdescent : baseEnd_2748699 < baseStart_2748699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748703 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 2, 5]
def baseStart_2748703 : Nat := 118140960795 + 2748703 * 2 ^ 59
def prefixEnd_2748703 : Nat := 4983230072969 + 3 ^ 40 * 2748703 * 2
def baseEnd_2748703 : Nat := 470468605151821473523817

theorem tailTrace_2748703 : CollatzResearch.WordTrace tailWord_2748703 prefixEnd_2748703 470468605151821473523817 := by
  unfold tailWord_2748703
  simp only [CollatzResearch.WordTrace]
  refine ⟨100253434560925946943394763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66835623040617297962263175 100253434560925946943394763)
  ·
    refine ⟨150380151841388920415092145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100253434560925946943394763 150380151841388920415092145)
    ·
      refine ⟨112785113881041690311319109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150380151841388920415092145 112785113881041690311319109)
      ·
        refine ⟨21147208852695316933372333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112785113881041690311319109 21147208852695316933372333)
        ·
          refine ⟨7930203319760743850014625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21147208852695316933372333 7930203319760743850014625)
          ·
            refine ⟨5947652489820557887510969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7930203319760743850014625 5947652489820557887510969)
            ·
              refine ⟨4460739367365418415633227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5947652489820557887510969 4460739367365418415633227)
              ·
                refine ⟨6691109051048127623449841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4460739367365418415633227 6691109051048127623449841)
                ·
                  refine ⟨5018331788286095717587381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6691109051048127623449841 5018331788286095717587381)
                  ·
                    refine ⟨470468605151821473523817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5018331788286095717587381 470468605151821473523817)
                    ·
                      rfl

theorem cell23_2748703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 5].length) (baseStart_2748703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748703 prefixEnd_2748703 := by exact prefixLift 2748703
  have htrace : WordTrace (prefixWord ++ tailWord_2748703) baseStart_2748703 baseEnd_2748703 := by
    simpa [prefixWord, tailWord_2748703, baseEnd_2748703] using wordTrace_append hprefix tailTrace_2748703
  have hstable : (prefixWord ++ tailWord_2748703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748703).length < 2 ^ (prefixWord ++ tailWord_2748703).sum := by decide
  have hdescent : baseEnd_2748703 < baseStart_2748703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748723 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 2, 4, 2]
def baseStart_2748723 : Nat := 118140960795 + 2748723 * 2 ^ 59
def prefixEnd_2748723 : Nat := 4983230072969 + 3 ^ 40 * 2748723 * 2
def baseEnd_2748723 : Nat := 1411416085068554342321359

theorem tailTrace_2748723 : CollatzResearch.WordTrace tailWord_2748723 prefixEnd_2748723 1411416085068554342321359 := by
  unfold tailWord_2748723
  simp only [CollatzResearch.WordTrace]
  refine ⟨100254164020853490359122823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66836109347235660239415215 100254164020853490359122823)
  ·
    refine ⟨150381246031280235538684235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100254164020853490359122823 150381246031280235538684235)
    ·
      refine ⟨225571869046920353308026353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150381246031280235538684235 225571869046920353308026353)
      ·
        refine ⟨169178901785190264981019765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225571869046920353308026353 169178901785190264981019765)
        ·
          refine ⟨15860522042361587341970603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169178901785190264981019765 15860522042361587341970603)
          ·
            refine ⟨23790783063542381012955905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15860522042361587341970603 23790783063542381012955905)
            ·
              refine ⟨17843087297656785759716929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23790783063542381012955905 17843087297656785759716929)
              ·
                refine ⟨13382315473242589319787697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17843087297656785759716929 13382315473242589319787697)
                ·
                  refine ⟨10036736604931941989840773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13382315473242589319787697 10036736604931941989840773)
                  ·
                    refine ⟨1881888113424739123095145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10036736604931941989840773 1881888113424739123095145)
                    ·
                      refine ⟨1411416085068554342321359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1881888113424739123095145 1411416085068554342321359)
                      ·
                        rfl

theorem cell23_2748723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 4, 2].length) (baseStart_2748723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748723 prefixEnd_2748723 := by exact prefixLift 2748723
  have htrace : WordTrace (prefixWord ++ tailWord_2748723) baseStart_2748723 baseEnd_2748723 := by
    simpa [prefixWord, tailWord_2748723, baseEnd_2748723] using wordTrace_append hprefix tailTrace_2748723
  have hstable : (prefixWord ++ tailWord_2748723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748723).length < 2 ^ (prefixWord ++ tailWord_2748723).sum := by decide
  have hdescent : baseEnd_2748723 < baseStart_2748723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748757 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 2, 1, 4]
def baseStart_2748757 : Nat := 118140960795 + 2748757 * 2 ^ 59
def prefixEnd_2748757 : Nat := 4983230072969 + 3 ^ 40 * 2748757 * 2
def baseEnd_2748757 : Nat := 1411433543410807209296203

theorem tailTrace_2748757 : CollatzResearch.WordTrace tailWord_2748757 prefixEnd_2748757 1411433543410807209296203 := by
  unfold tailWord_2748757
  simp only [CollatzResearch.WordTrace]
  refine ⟨100255404102730314165860525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66836936068486876110573683 100255404102730314165860525)
  ·
    refine ⟨37595776538523867812197697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100255404102730314165860525 37595776538523867812197697)
    ·
      refine ⟨28196832403892900859148273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37595776538523867812197697 28196832403892900859148273)
      ·
        refine ⟨21147624302919675644361205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28196832403892900859148273 21147624302919675644361205)
        ·
          refine ⟨1982589778398719591658863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21147624302919675644361205 1982589778398719591658863)
          ·
            refine ⟨2973884667598079387488295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982589778398719591658863 2973884667598079387488295)
            ·
              refine ⟨4460827001397119081232443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2973884667598079387488295 4460827001397119081232443)
              ·
                refine ⟨6691240502095678621848665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4460827001397119081232443 6691240502095678621848665)
                ·
                  refine ⟨5018430376571758966386499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6691240502095678621848665 5018430376571758966386499)
                  ·
                    refine ⟨7527645564857638449579749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5018430376571758966386499 7527645564857638449579749)
                    ·
                      refine ⟨1411433543410807209296203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7527645564857638449579749 1411433543410807209296203)
                      ·
                        rfl

theorem cell23_2748757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_2748757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748757 prefixEnd_2748757 := by exact prefixLift 2748757
  have htrace : WordTrace (prefixWord ++ tailWord_2748757) baseStart_2748757 baseEnd_2748757 := by
    simpa [prefixWord, tailWord_2748757, baseEnd_2748757] using wordTrace_append hprefix tailTrace_2748757
  have hstable : (prefixWord ++ tailWord_2748757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748757).length < 2 ^ (prefixWord ++ tailWord_2748757).sum := by decide
  have hdescent : baseEnd_2748757 < baseStart_2748757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748780 : List Nat := [2, 2, 1, 1, 6, 2, 1, 2, 6]
def baseStart_2748780 : Nat := 118140960795 + 2748780 * 2 ^ 59
def prefixEnd_2748780 : Nat := 4983230072969 + 3 ^ 40 * 2748780 * 2
def baseEnd_2748780 : Nat := 156827261496206735478733

theorem tailTrace_2748780 : CollatzResearch.WordTrace tailWord_2748780 prefixEnd_2748780 156827261496206735478733 := by
  unfold tailWord_2748780
  simp only [CollatzResearch.WordTrace]
  refine ⟨50128121490823494546973897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66837495321097992729298529 50128121490823494546973897)
  ·
    refine ⟨37596091118117620910230423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50128121490823494546973897 37596091118117620910230423)
    ·
      refine ⟨56394136677176431365345635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37596091118117620910230423 56394136677176431365345635)
      ·
        refine ⟨84591205015764647048018453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56394136677176431365345635 84591205015764647048018453)
        ·
          refine ⟨3965212735113967830375865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84591205015764647048018453 3965212735113967830375865)
          ·
            refine ⟨2973909551335475872781899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3965212735113967830375865 2973909551335475872781899)
            ·
              refine ⟨4460864327003213809172849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2973909551335475872781899 4460864327003213809172849)
              ·
                refine ⟨3345648245252410356879637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4460864327003213809172849 3345648245252410356879637)
                ·
                  refine ⟨156827261496206735478733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3345648245252410356879637 156827261496206735478733)
                  ·
                    rfl

theorem cell23_2748780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 6].length) (baseStart_2748780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748780 prefixEnd_2748780 := by exact prefixLift 2748780
  have htrace : WordTrace (prefixWord ++ tailWord_2748780) baseStart_2748780 baseEnd_2748780 := by
    simpa [prefixWord, tailWord_2748780, baseEnd_2748780] using wordTrace_append hprefix tailTrace_2748780
  have hstable : (prefixWord ++ tailWord_2748780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748780).length < 2 ^ (prefixWord ++ tailWord_2748780).sum := by decide
  have hdescent : baseEnd_2748780 < baseStart_2748780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748796 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_2748796 : Nat := 118140960795 + 2748796 * 2 ^ 59
def prefixEnd_2748796 : Nat := 4983230072969 + 3 ^ 40 * 2748796 * 2
def baseEnd_2748796 : Nat := 1411453569156332556708523

theorem tailTrace_2748796 : CollatzResearch.WordTrace tailWord_2748796 prefixEnd_2748796 1411453569156332556708523 := by
  unfold tailWord_2748796
  simp only [CollatzResearch.WordTrace]
  refine ⟨50128413274794511913265121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66837884366392682551020161 50128413274794511913265121)
  ·
    refine ⟨37596309956095883934948841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50128413274794511913265121 37596309956095883934948841)
    ·
      refine ⟨28197232467071912951211631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37596309956095883934948841 28197232467071912951211631)
      ·
        refine ⟨42295848700607869426817447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28197232467071912951211631 42295848700607869426817447)
        ·
          refine ⟨63443773050911804140226171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42295848700607869426817447 63443773050911804140226171)
          ·
            refine ⟨95165659576367706210339257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63443773050911804140226171 95165659576367706210339257)
            ·
              refine ⟨71374244682275779657754443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95165659576367706210339257 71374244682275779657754443)
              ·
                refine ⟨107061367023413669486631665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71374244682275779657754443 107061367023413669486631665)
                ·
                  refine ⟨80296025267560252114973749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107061367023413669486631665 80296025267560252114973749)
                  ·
                    refine ⟨7527752368833773635778789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80296025267560252114973749 7527752368833773635778789)
                    ·
                      refine ⟨1411453569156332556708523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7527752368833773635778789 1411453569156332556708523)
                      ·
                        rfl

theorem cell23_2748796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_2748796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748796 prefixEnd_2748796 := by exact prefixLift 2748796
  have htrace : WordTrace (prefixWord ++ tailWord_2748796) baseStart_2748796 baseEnd_2748796 := by
    simpa [prefixWord, tailWord_2748796, baseEnd_2748796] using wordTrace_append hprefix tailTrace_2748796
  have hstable : (prefixWord ++ tailWord_2748796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748796).length < 2 ^ (prefixWord ++ tailWord_2748796).sum := by decide
  have hdescent : baseEnd_2748796 < baseStart_2748796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748823 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 4, 4]
def baseStart_2748823 : Nat := 118140960795 + 2748823 * 2 ^ 59
def prefixEnd_2748823 : Nat := 4983230072969 + 3 ^ 40 * 2748823 * 2
def baseEnd_2748823 : Nat := 470489144378001317023633

theorem tailTrace_2748823 : CollatzResearch.WordTrace tailWord_2748823 prefixEnd_2748823 470489144378001317023633 := by
  unfold tailWord_2748823
  simp only [CollatzResearch.WordTrace]
  refine ⟨100257811320491207437763123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66838540880327471625175415 100257811320491207437763123)
  ·
    refine ⟨150386716980736811156644685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100257811320491207437763123 150386716980736811156644685)
    ·
      refine ⟨56395018867776304183741757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150386716980736811156644685 56395018867776304183741757)
      ·
        refine ⟨21148132075416114068903159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56395018867776304183741757 21148132075416114068903159)
        ·
          refine ⟨31722198113124171103354739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21148132075416114068903159 31722198113124171103354739)
          ·
            refine ⟨47583297169686256655032109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31722198113124171103354739 47583297169686256655032109)
            ·
              refine ⟨17843736438632346245637041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47583297169686256655032109 17843736438632346245637041)
              ·
                refine ⟨13382802328974259684227781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17843736438632346245637041 13382802328974259684227781)
                ·
                  refine ⟨2509275436682673690792709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13382802328974259684227781 2509275436682673690792709)
                  ·
                    refine ⟨470489144378001317023633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2509275436682673690792709 470489144378001317023633)
                    ·
                      rfl

theorem cell23_2748823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_2748823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748823 prefixEnd_2748823 := by exact prefixLift 2748823
  have htrace : WordTrace (prefixWord ++ tailWord_2748823) baseStart_2748823 baseEnd_2748823 := by
    simpa [prefixWord, tailWord_2748823, baseEnd_2748823] using wordTrace_append hprefix tailTrace_2748823
  have hstable : (prefixWord ++ tailWord_2748823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748823).length < 2 ^ (prefixWord ++ tailWord_2748823).sum := by decide
  have hdescent : baseEnd_2748823 < baseStart_2748823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748824 : List Nat := [2, 1, 2, 5, 1, 1, 3, 3, 1, 1, 3]
def baseStart_2748824 : Nat := 118140960795 + 2748824 * 2 ^ 59
def prefixEnd_2748824 : Nat := 4983230072969 + 3 ^ 40 * 2748824 * 2
def baseEnd_2748824 : Nat := 1411467946614658447158395

theorem tailTrace_2748824 : CollatzResearch.WordTrace tailWord_2748824 prefixEnd_2748824 1411467946614658447158395 := by
  unfold tailWord_2748824
  simp only [CollatzResearch.WordTrace]
  refine ⟨50128923896743792304274763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66838565195658389739033017 50128923896743792304274763)
  ·
    refine ⟨75193385845115688456412145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50128923896743792304274763 75193385845115688456412145)
    ·
      refine ⟨56395039383836766342309109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75193385845115688456412145 56395039383836766342309109)
      ·
        refine ⟨5287034942234696844591479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56395039383836766342309109 5287034942234696844591479)
        ·
          refine ⟨7930552413352045266887219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5287034942234696844591479 7930552413352045266887219)
          ·
            refine ⟨11895828620028067900330829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7930552413352045266887219 11895828620028067900330829)
            ·
              refine ⟨4460935732510525462624061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11895828620028067900330829 4460935732510525462624061)
              ·
                refine ⟨1672850899691447048484023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4460935732510525462624061 1672850899691447048484023)
                ·
                  refine ⟨2509276349537170572726035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672850899691447048484023 2509276349537170572726035)
                  ·
                    refine ⟨3763914524305755859089053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2509276349537170572726035 3763914524305755859089053)
                    ·
                      refine ⟨1411467946614658447158395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3763914524305755859089053 1411467946614658447158395)
                      ·
                        rfl

theorem cell23_2748824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_2748824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748824 prefixEnd_2748824 := by exact prefixLift 2748824
  have htrace : WordTrace (prefixWord ++ tailWord_2748824) baseStart_2748824 baseEnd_2748824 := by
    simpa [prefixWord, tailWord_2748824, baseEnd_2748824] using wordTrace_append hprefix tailTrace_2748824
  have hstable : (prefixWord ++ tailWord_2748824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748824).length < 2 ^ (prefixWord ++ tailWord_2748824).sum := by decide
  have hdescent : baseEnd_2748824 < baseStart_2748824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748836 : List Nat := [2, 3, 1, 2, 1, 1, 13]
def baseStart_2748836 : Nat := 118140960795 + 2748836 * 2 ^ 59
def prefixEnd_2748836 : Nat := 4983230072969 + 3 ^ 40 * 2748836 * 2
def baseEnd_2748836 : Nat := 17425606276327313582819

theorem tailTrace_2748836 : CollatzResearch.WordTrace tailWord_2748836 prefixEnd_2748836 17425606276327313582819 := by
  unfold tailWord_2748836
  simp only [CollatzResearch.WordTrace]
  refine ⟨50129142734722055328993181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66838856979629407105324241 50129142734722055328993181)
  ·
    refine ⟨18798428525520770748372443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50129142734722055328993181 18798428525520770748372443)
    ·
      refine ⟨28197642788281156122558665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18798428525520770748372443 28197642788281156122558665)
      ·
        refine ⟨21148232091210867091918999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28197642788281156122558665 21148232091210867091918999)
        ·
          refine ⟨31722348136816300637878499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21148232091210867091918999 31722348136816300637878499)
          ·
            refine ⟨47583522205224450956817749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31722348136816300637878499 47583522205224450956817749)
            ·
              refine ⟨17425606276327313582819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 47583522205224450956817749 17425606276327313582819)
              ·
                rfl

theorem cell23_2748836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 13].length) (baseStart_2748836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748836 prefixEnd_2748836 := by exact prefixLift 2748836
  have htrace : WordTrace (prefixWord ++ tailWord_2748836) baseStart_2748836 baseEnd_2748836 := by
    simpa [prefixWord, tailWord_2748836, baseEnd_2748836] using wordTrace_append hprefix tailTrace_2748836
  have hstable : (prefixWord ++ tailWord_2748836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748836).length < 2 ^ (prefixWord ++ tailWord_2748836).sum := by decide
  have hdescent : baseEnd_2748836 < baseStart_2748836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748856 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 1, 4, 6]
def baseStart_2748856 : Nat := 118140960795 + 2748856 * 2 ^ 59
def prefixEnd_2748856 : Nat := 4983230072969 + 3 ^ 40 * 2748856 * 2
def baseEnd_2748856 : Nat := 1411484377995602321958247

theorem tailTrace_2748856 : CollatzResearch.WordTrace tailWord_2748856 prefixEnd_2748856 1411484377995602321958247 := by
  unfold tailWord_2748856
  simp only [CollatzResearch.WordTrace]
  refine ⟨50129507464685827036857211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66839343286247769382476281 50129507464685827036857211)
  ·
    refine ⟨75194261197028740555285817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50129507464685827036857211 75194261197028740555285817)
    ·
      refine ⟨56395695897771555416464363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75194261197028740555285817 56395695897771555416464363)
      ·
        refine ⟨84593543846657333124696545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56395695897771555416464363 84593543846657333124696545)
        ·
          refine ⟨63445157884992999843522409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84593543846657333124696545 63445157884992999843522409)
          ·
            refine ⟨47583868413744749882641807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63445157884992999843522409 47583868413744749882641807)
            ·
              refine ⟨71375802620617124823962711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47583868413744749882641807 71375802620617124823962711)
              ·
                refine ⟨107063703930925687235944067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71375802620617124823962711 107063703930925687235944067)
                ·
                  refine ⟨160595555896388530853916101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107063703930925687235944067 160595555896388530853916101)
                  ·
                    refine ⟨30111666730572849535109269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 160595555896388530853916101 30111666730572849535109269)
                    ·
                      refine ⟨1411484377995602321958247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30111666730572849535109269 1411484377995602321958247)
                      ·
                        rfl

theorem cell23_2748856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_2748856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748856 prefixEnd_2748856 := by exact prefixLift 2748856
  have htrace : WordTrace (prefixWord ++ tailWord_2748856) baseStart_2748856 baseEnd_2748856 := by
    simpa [prefixWord, tailWord_2748856, baseEnd_2748856] using wordTrace_append hprefix tailTrace_2748856
  have hstable : (prefixWord ++ tailWord_2748856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748856).length < 2 ^ (prefixWord ++ tailWord_2748856).sum := by decide
  have hdescent : baseEnd_2748856 < baseStart_2748856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748857 : List Nat := [1, 2, 1, 4, 3, 1, 4, 1, 2, 4]
def baseStart_2748857 : Nat := 118140960795 + 2748857 * 2 ^ 59
def prefixEnd_2748857 : Nat := 4983230072969 + 3 ^ 40 * 2748857 * 2
def baseEnd_2748857 : Nat := 470494963825418939348581

theorem tailTrace_2748857 : CollatzResearch.WordTrace tailWord_2748857 prefixEnd_2748857 470494963825418939348581 := by
  unfold tailWord_2748857
  simp only [CollatzResearch.WordTrace]
  refine ⟨100259051402368031244500825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66839367601578687496333883 100259051402368031244500825)
  ·
    refine ⟨75194288551776023433375619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100259051402368031244500825 75194288551776023433375619)
    ·
      refine ⟨112791432827664035150063429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75194288551776023433375619 112791432827664035150063429)
      ·
        refine ⟨21148393655187006590636893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112791432827664035150063429 21148393655187006590636893)
        ·
          refine ⟨7930647620695127471488835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21148393655187006590636893 7930647620695127471488835)
          ·
            refine ⟨11895971431042691207233253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7930647620695127471488835 11895971431042691207233253)
            ·
              refine ⟨2230494643320504601356235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11895971431042691207233253 2230494643320504601356235)
              ·
                refine ⟨3345741964980756902034353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2230494643320504601356235 3345741964980756902034353)
                ·
                  refine ⟨2509306473735567676525765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3345741964980756902034353 2509306473735567676525765)
                  ·
                    refine ⟨470494963825418939348581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2509306473735567676525765 470494963825418939348581)
                    ·
                      rfl

theorem cell23_2748857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 2, 4].length) (baseStart_2748857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748857 prefixEnd_2748857 := by exact prefixLift 2748857
  have htrace : WordTrace (prefixWord ++ tailWord_2748857) baseStart_2748857 baseEnd_2748857 := by
    simpa [prefixWord, tailWord_2748857, baseEnd_2748857] using wordTrace_append hprefix tailTrace_2748857
  have hstable : (prefixWord ++ tailWord_2748857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748857).length < 2 ^ (prefixWord ++ tailWord_2748857).sum := by decide
  have hdescent : baseEnd_2748857 < baseStart_2748857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748884 : List Nat := [2, 4, 1, 2, 2, 2, 3, 1, 1, 2, 3]
def baseStart_2748884 : Nat := 118140960795 + 2748884 * 2 ^ 59
def prefixEnd_2748884 : Nat := 4983230072969 + 3 ^ 40 * 2748884 * 2
def baseEnd_2748884 : Nat := 1411498755453928212408119

theorem tailTrace_2748884 : CollatzResearch.WordTrace tailWord_2748884 prefixEnd_2748884 1411498755453928212408119 := by
  unfold tailWord_2748884
  simp only [CollatzResearch.WordTrace]
  refine ⟨50130018086635107427866853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66840024115513476570489137 50130018086635107427866853)
  ·
    refine ⟨9399378391244082642725035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50130018086635107427866853 9399378391244082642725035)
    ·
      refine ⟨14099067586866123964087553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9399378391244082642725035 14099067586866123964087553)
      ·
        refine ⟨10574300690149592973065665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14099067586866123964087553 10574300690149592973065665)
        ·
          refine ⟨7930725517612194729799249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10574300690149592973065665 7930725517612194729799249)
          ·
            refine ⟨5948044138209146047349437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7930725517612194729799249 5948044138209146047349437)
            ·
              refine ⟨2230516551828429767756039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5948044138209146047349437 2230516551828429767756039)
              ·
                refine ⟨3345774827742644651634059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2230516551828429767756039 3345774827742644651634059)
                ·
                  refine ⟨5018662241613966977451089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345774827742644651634059 5018662241613966977451089)
                  ·
                    refine ⟨3763996681210475233088317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5018662241613966977451089 3763996681210475233088317)
                    ·
                      refine ⟨1411498755453928212408119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3763996681210475233088317 1411498755453928212408119)
                      ·
                        rfl

theorem cell23_2748884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_2748884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748884 prefixEnd_2748884 := by exact prefixLift 2748884
  have htrace : WordTrace (prefixWord ++ tailWord_2748884) baseStart_2748884 baseEnd_2748884 := by
    simpa [prefixWord, tailWord_2748884, baseEnd_2748884] using wordTrace_append hprefix tailTrace_2748884
  have hstable : (prefixWord ++ tailWord_2748884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748884).length < 2 ^ (prefixWord ++ tailWord_2748884).sum := by decide
  have hdescent : baseEnd_2748884 < baseStart_2748884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748897 : List Nat := [1, 2, 3, 1, 2, 2, 4, 2, 2, 1, 3]
def baseStart_2748897 : Nat := 118140960795 + 2748897 * 2 ^ 59
def prefixEnd_2748897 : Nat := 4983230072969 + 3 ^ 40 * 2748897 * 2
def baseEnd_2748897 : Nat := 1411505430702436661545559

theorem tailTrace_2748897 : CollatzResearch.WordTrace tailWord_2748897 prefixEnd_2748897 1411505430702436661545559 := by
  unfold tailWord_2748897
  simp only [CollatzResearch.WordTrace]
  refine ⟨100260510322223118075956945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66840340214815412050637963 100260510322223118075956945)
  ·
    refine ⟨75195382741667338556967709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100260510322223118075956945 75195382741667338556967709)
    ·
      refine ⟨28198268528125251958862891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75195382741667338556967709 28198268528125251958862891)
      ·
        refine ⟨42297402792187877938294337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28198268528125251958862891 42297402792187877938294337)
        ·
          refine ⟨31723052094140908453720753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42297402792187877938294337 31723052094140908453720753)
          ·
            refine ⟨23792289070605681340290565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31723052094140908453720753 23792289070605681340290565)
            ·
              refine ⟨4461054200738565251304481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23792289070605681340290565 4461054200738565251304481)
              ·
                refine ⟨3345790650553923938478361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4461054200738565251304481 3345790650553923938478361)
                ·
                  refine ⟨2509342987915442953858771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3345790650553923938478361 2509342987915442953858771)
                  ·
                    refine ⟨3764014481873164430788157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2509342987915442953858771 3764014481873164430788157)
                    ·
                      refine ⟨1411505430702436661545559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3764014481873164430788157 1411505430702436661545559)
                      ·
                        rfl

theorem cell23_2748897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_2748897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748897 prefixEnd_2748897 := by exact prefixLift 2748897
  have htrace : WordTrace (prefixWord ++ tailWord_2748897) baseStart_2748897 baseEnd_2748897 := by
    simpa [prefixWord, tailWord_2748897, baseEnd_2748897] using wordTrace_append hprefix tailTrace_2748897
  have hstable : (prefixWord ++ tailWord_2748897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748897).length < 2 ^ (prefixWord ++ tailWord_2748897).sum := by decide
  have hdescent : baseEnd_2748897 < baseStart_2748897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748903 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_2748903 : Nat := 118140960795 + 2748903 * 2 ^ 59
def prefixEnd_2748903 : Nat := 4983230072969 + 3 ^ 40 * 2748903 * 2
def baseEnd_2748903 : Nat := 1411508511586363638070531

theorem tailTrace_2748903 : CollatzResearch.WordTrace tailWord_2748903 prefixEnd_2748903 1411508511586363638070531 := by
  unfold tailWord_2748903
  simp only [CollatzResearch.WordTrace]
  refine ⟨100260729160201381100675363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66840486106800920733783575 100260729160201381100675363)
  ·
    refine ⟨150391093740302071651013045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100260729160201381100675363 150391093740302071651013045)
    ·
      refine ⟨14099165038153319217282473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150391093740302071651013045 14099165038153319217282473)
      ·
        refine ⟨10574373778614989412961855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14099165038153319217282473 10574373778614989412961855)
        ·
          refine ⟨15861560667922484119442783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10574373778614989412961855 15861560667922484119442783)
          ·
            refine ⟨23792341001883726179164175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15861560667922484119442783 23792341001883726179164175)
            ·
              refine ⟨35688511502825589268746263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23792341001883726179164175 35688511502825589268746263)
              ·
                refine ⟨53532767254238383903119395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35688511502825589268746263 53532767254238383903119395)
                ·
                  refine ⟨80299150881357575854679093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53532767254238383903119395 80299150881357575854679093)
                  ·
                    refine ⟨7528045395127272736376165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80299150881357575854679093 7528045395127272736376165)
                    ·
                      refine ⟨1411508511586363638070531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7528045395127272736376165 1411508511586363638070531)
                      ·
                        rfl

theorem cell23_2748903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_2748903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748903 prefixEnd_2748903 := by exact prefixLift 2748903
  have htrace : WordTrace (prefixWord ++ tailWord_2748903) baseStart_2748903 baseEnd_2748903 := by
    simpa [prefixWord, tailWord_2748903, baseEnd_2748903] using wordTrace_append hprefix tailTrace_2748903
  have hstable : (prefixWord ++ tailWord_2748903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748903).length < 2 ^ (prefixWord ++ tailWord_2748903).sum := by decide
  have hdescent : baseEnd_2748903 < baseStart_2748903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748913 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 2, 6]
def baseStart_2748913 : Nat := 118140960795 + 2748913 * 2 ^ 59
def prefixEnd_2748913 : Nat := 4983230072969 + 3 ^ 40 * 2748913 * 2
def baseEnd_2748913 : Nat := 470504548797636199648495

theorem tailTrace_2748913 : CollatzResearch.WordTrace tailWord_2748913 prefixEnd_2748913 470504548797636199648495 := by
  unfold tailWord_2748913
  simp only [CollatzResearch.WordTrace]
  refine ⟨100261093890165152808539393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66840729260110101872359595 100261093890165152808539393)
  ·
    refine ⟨75195820417623864606404545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100261093890165152808539393 75195820417623864606404545)
    ·
      refine ⟨56396865313217898454803409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75195820417623864606404545 56396865313217898454803409)
      ·
        refine ⟨42297648984913423841102557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56396865313217898454803409 42297648984913423841102557)
        ·
          refine ⟨15861618369342533940413459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42297648984913423841102557 15861618369342533940413459)
          ·
            refine ⟨23792427554013800910620189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15861618369342533940413459 23792427554013800910620189)
            ·
              refine ⟨8922160332755175341482571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23792427554013800910620189 8922160332755175341482571)
              ·
                refine ⟨13383240499132763012223857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8922160332755175341482571 13383240499132763012223857)
                ·
                  refine ⟨10037430374349572259167893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13383240499132763012223857 10037430374349572259167893)
                  ·
                    refine ⟨470504548797636199648495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10037430374349572259167893 470504548797636199648495)
                    ·
                      rfl

theorem cell23_2748913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_2748913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748913 prefixEnd_2748913 := by exact prefixLift 2748913
  have htrace : WordTrace (prefixWord ++ tailWord_2748913) baseStart_2748913 baseEnd_2748913 := by
    simpa [prefixWord, tailWord_2748913, baseEnd_2748913] using wordTrace_append hprefix tailTrace_2748913
  have hstable : (prefixWord ++ tailWord_2748913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748913).length < 2 ^ (prefixWord ++ tailWord_2748913).sum := by decide
  have hdescent : baseEnd_2748913 < baseStart_2748913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748953 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 3, 5, 3]
def baseStart_2748953 : Nat := 118140960795 + 2748953 * 2 ^ 59
def prefixEnd_2748953 : Nat := 4983230072969 + 3 ^ 40 * 2748953 * 2
def baseEnd_2748953 : Nat := 1411534185619088442445301

theorem tailTrace_2748953 : CollatzResearch.WordTrace tailWord_2748953 prefixEnd_2748953 1411534185619088442445301 := by
  unfold tailWord_2748953
  simp only [CollatzResearch.WordTrace]
  refine ⟨100262552810020239639995513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66841701873346826426663675 100262552810020239639995513)
  ·
    refine ⟨75196914607515179729996635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100262552810020239639995513 75196914607515179729996635)
    ·
      refine ⟨112795371911272769594994953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75196914607515179729996635 112795371911272769594994953)
      ·
        refine ⟨84596528933454577196246215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112795371911272769594994953 84596528933454577196246215)
        ·
          refine ⟨126894793400181865794369323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84596528933454577196246215 126894793400181865794369323)
          ·
            refine ⟨190342190100272798691553985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126894793400181865794369323 190342190100272798691553985)
            ·
              refine ⟨142756642575204599018665489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190342190100272798691553985 142756642575204599018665489)
              ·
                refine ⟨107067481931403449263999117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142756642575204599018665489 107067481931403449263999117)
                ·
                  refine ⟨40150305724276293473999669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107067481931403449263999117 40150305724276293473999669)
                  ·
                    refine ⟨3764091161650902513187469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40150305724276293473999669 3764091161650902513187469)
                    ·
                      refine ⟨1411534185619088442445301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3764091161650902513187469 1411534185619088442445301)
                      ·
                        rfl

theorem cell23_2748953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_2748953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748953 prefixEnd_2748953 := by exact prefixLift 2748953
  have htrace : WordTrace (prefixWord ++ tailWord_2748953) baseStart_2748953 baseEnd_2748953 := by
    simpa [prefixWord, tailWord_2748953, baseEnd_2748953] using wordTrace_append hprefix tailTrace_2748953
  have hstable : (prefixWord ++ tailWord_2748953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748953).length < 2 ^ (prefixWord ++ tailWord_2748953).sum := by decide
  have hdescent : baseEnd_2748953 < baseStart_2748953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748954 : List Nat := [3, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2]
def baseStart_2748954 : Nat := 118140960795 + 2748954 * 2 ^ 59
def prefixEnd_2748954 : Nat := 4983230072969 + 3 ^ 40 * 2748954 * 2
def baseEnd_2748954 : Nat := 1411534699099742938532797

theorem tailTrace_2748954 : CollatzResearch.WordTrace tailWord_2748954 prefixEnd_2748954 1411534699099742938532797 := by
  unfold tailWord_2748954
  simp only [CollatzResearch.WordTrace]
  refine ⟨25065647320754154202695479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66841726188677744540521277 25065647320754154202695479)
  ·
    refine ⟨37598470981131231304043219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25065647320754154202695479 37598470981131231304043219)
    ·
      refine ⟨56397706471696846956064829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37598470981131231304043219 56397706471696846956064829)
      ·
        refine ⟨21149139926886317608524311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56397706471696846956064829 21149139926886317608524311)
        ·
          refine ⟨31723709890329476412786467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21149139926886317608524311 31723709890329476412786467)
          ·
            refine ⟨47585564835494214619179701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31723709890329476412786467 47585564835494214619179701)
            ·
              refine ⟨4461146703327582620548097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47585564835494214619179701 4461146703327582620548097)
              ·
                refine ⟨3345860027495686965411073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4461146703327582620548097 3345860027495686965411073)
                ·
                  refine ⟨2509395020621765224058305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3345860027495686965411073 2509395020621765224058305)
                  ·
                    refine ⟨1882046265466323918043729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2509395020621765224058305 1882046265466323918043729)
                    ·
                      refine ⟨1411534699099742938532797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1882046265466323918043729 1411534699099742938532797)
                      ·
                        rfl

theorem cell23_2748954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_2748954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2748954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2748954 prefixEnd_2748954 := by exact prefixLift 2748954
  have htrace : WordTrace (prefixWord ++ tailWord_2748954) baseStart_2748954 baseEnd_2748954 := by
    simpa [prefixWord, tailWord_2748954, baseEnd_2748954] using wordTrace_append hprefix tailTrace_2748954
  have hstable : (prefixWord ++ tailWord_2748954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748954).length < 2 ^ (prefixWord ++ tailWord_2748954).sum := by decide
  have hdescent : baseEnd_2748954 < baseStart_2748954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749023 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 6]
def baseStart_2749023 : Nat := 118140960795 + 2749023 * 2 ^ 59
def prefixEnd_2749023 : Nat := 4983230072969 + 3 ^ 40 * 2749023 * 2
def baseEnd_2749023 : Nat := 1411570129264903168569979

theorem tailTrace_2749023 : CollatzResearch.WordTrace tailWord_2749023 prefixEnd_2749023 1411570129264903168569979 := by
  unfold tailWord_2749023
  simp only [CollatzResearch.WordTrace]
  refine ⟨100265105919766641595043723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66843403946511094396695815 100265105919766641595043723)
  ·
    refine ⟨150397658879649962392565585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100265105919766641595043723 150397658879649962392565585)
    ·
      refine ⟨112798244159737471794424189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150397658879649962392565585 112798244159737471794424189)
      ·
        refine ⟨42299341559901551922909071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112798244159737471794424189 42299341559901551922909071)
        ·
          refine ⟨63449012339852327884363607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42299341559901551922909071 63449012339852327884363607)
          ·
            refine ⟨95173518509778491826545411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63449012339852327884363607 95173518509778491826545411)
            ·
              refine ⟨142760277764667737739818117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95173518509778491826545411 142760277764667737739818117)
              ·
                refine ⟨26767552080875200826215897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142760277764667737739818117 26767552080875200826215897)
                ·
                  refine ⟨20075664060656400619661923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26767552080875200826215897 20075664060656400619661923)
                  ·
                    refine ⟨30113496090984600929492885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20075664060656400619661923 30113496090984600929492885)
                    ·
                      refine ⟨1411570129264903168569979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30113496090984600929492885 1411570129264903168569979)
                      ·
                        rfl

theorem cell23_2749023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_2749023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749023 prefixEnd_2749023 := by exact prefixLift 2749023
  have htrace : WordTrace (prefixWord ++ tailWord_2749023) baseStart_2749023 baseEnd_2749023 := by
    simpa [prefixWord, tailWord_2749023, baseEnd_2749023] using wordTrace_append hprefix tailTrace_2749023
  have hstable : (prefixWord ++ tailWord_2749023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749023).length < 2 ^ (prefixWord ++ tailWord_2749023).sum := by decide
  have hdescent : baseEnd_2749023 < baseStart_2749023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749070 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_2749070 : Nat := 118140960795 + 2749070 * 2 ^ 59
def prefixEnd_2749070 : Nat := 4983230072969 + 3 ^ 40 * 2749070 * 2
def baseEnd_2749070 : Nat := 1411594262855664484682263

theorem tailTrace_2749070 : CollatzResearch.WordTrace tailWord_2749070 prefixEnd_2749070 1411594262855664484682263 := by
  unfold tailWord_2749070
  simp only [CollatzResearch.WordTrace]
  refine ⟨12533352518824546077750583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66844546767064245748003109 12533352518824546077750583)
  ·
    refine ⟨18800028778236819116625875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12533352518824546077750583 18800028778236819116625875)
    ·
      refine ⟨28200043167355228674938813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18800028778236819116625875 28200043167355228674938813)
      ·
        refine ⟨10575016187758210753102055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28200043167355228674938813 10575016187758210753102055)
        ·
          refine ⟨15862524281637316129653083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10575016187758210753102055 15862524281637316129653083)
          ·
            refine ⟨23793786422455974194479625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15862524281637316129653083 23793786422455974194479625)
            ·
              refine ⟨17845339816841980645859719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23793786422455974194479625 17845339816841980645859719)
              ·
                refine ⟨26768009725262970968789579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17845339816841980645859719 26768009725262970968789579)
                ·
                  refine ⟨40152014587894456453184369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26768009725262970968789579 40152014587894456453184369)
                  ·
                    refine ⟨30114010940920842339888277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40152014587894456453184369 30114010940920842339888277)
                    ·
                      refine ⟨1411594262855664484682263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30114010940920842339888277 1411594262855664484682263)
                      ·
                        rfl

theorem cell23_2749070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_2749070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749070 prefixEnd_2749070 := by exact prefixLift 2749070
  have htrace : WordTrace (prefixWord ++ tailWord_2749070) baseStart_2749070 baseEnd_2749070 := by
    simpa [prefixWord, tailWord_2749070, baseEnd_2749070] using wordTrace_append hprefix tailTrace_2749070
  have hstable : (prefixWord ++ tailWord_2749070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749070).length < 2 ^ (prefixWord ++ tailWord_2749070).sum := by decide
  have hdescent : baseEnd_2749070 < baseStart_2749070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749080 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 5, 5]
def baseStart_2749080 : Nat := 118140960795 + 2749080 * 2 ^ 59
def prefixEnd_2749080 : Nat := 4983230072969 + 3 ^ 40 * 2749080 * 2
def baseEnd_2749080 : Nat := 470533132554069815185739

theorem tailTrace_2749080 : CollatzResearch.WordTrace tailWord_2749080 prefixEnd_2749080 470533132554069815185739 := by
  unfold tailWord_2749080
  simp only [CollatzResearch.WordTrace]
  refine ⟨50133592440280070164934347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66844789920373426886579129 50133592440280070164934347)
  ·
    refine ⟨75200388660420105247401521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50133592440280070164934347 75200388660420105247401521)
    ·
      refine ⟨56400291495315078935551141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75200388660420105247401521 56400291495315078935551141)
      ·
        refine ⟨10575054655371577300415839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56400291495315078935551141 10575054655371577300415839)
        ·
          refine ⟨15862581983057365950623759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10575054655371577300415839 15862581983057365950623759)
          ·
            refine ⟨23793872974586048925935639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15862581983057365950623759 23793872974586048925935639)
            ·
              refine ⟨35690809461879073388903459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23793872974586048925935639 35690809461879073388903459)
              ·
                refine ⟨53536214192818610083355189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35690809461879073388903459 53536214192818610083355189)
                ·
                  refine ⟨5019020080576744695314549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53536214192818610083355189 5019020080576744695314549)
                  ·
                    refine ⟨470533132554069815185739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5019020080576744695314549 470533132554069815185739)
                    ·
                      rfl

theorem cell23_2749080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_2749080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749080 prefixEnd_2749080 := by exact prefixLift 2749080
  have htrace : WordTrace (prefixWord ++ tailWord_2749080) baseStart_2749080 baseEnd_2749080 := by
    simpa [prefixWord, tailWord_2749080, baseEnd_2749080] using wordTrace_append hprefix tailTrace_2749080
  have hstable : (prefixWord ++ tailWord_2749080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749080).length < 2 ^ (prefixWord ++ tailWord_2749080).sum := by decide
  have hdescent : baseEnd_2749080 < baseStart_2749080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749098 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2749098 : Nat := 118140960795 + 2749098 * 2 ^ 59
def prefixEnd_2749098 : Nat := 4983230072969 + 3 ^ 40 * 2749098 * 2
def baseEnd_2749098 : Nat := 1411608640313990375132135

theorem tailTrace_2749098 : CollatzResearch.WordTrace tailWord_2749098 prefixEnd_2749098 1411608640313990375132135 := by
  unfold tailWord_2749098
  simp only [CollatzResearch.WordTrace]
  refine ⟨25066960348623732351005987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66845227596329952936015965 25066960348623732351005987)
  ·
    refine ⟨37600440522935598526508981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25066960348623732351005987 37600440522935598526508981)
    ·
      refine ⟨3525041299025212361860217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37600440522935598526508981 3525041299025212361860217)
      ·
        refine ⟨2643780974268909271395163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3525041299025212361860217 2643780974268909271395163)
        ·
          refine ⟨3965671461403363907092745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2643780974268909271395163 3965671461403363907092745)
          ·
            refine ⟨2974253596052522930319559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3965671461403363907092745 2974253596052522930319559)
            ·
              refine ⟨4461380394078784395479339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2974253596052522930319559 4461380394078784395479339)
              ·
                refine ⟨6692070591118176593219009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4461380394078784395479339 6692070591118176593219009)
                ·
                  refine ⟨5019052943338632444914257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6692070591118176593219009 5019052943338632444914257)
                  ·
                    refine ⟨3764289707503974333685693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5019052943338632444914257 3764289707503974333685693)
                    ·
                      refine ⟨1411608640313990375132135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3764289707503974333685693 1411608640313990375132135)
                      ·
                        rfl

theorem cell23_2749098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2749098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749098 prefixEnd_2749098 := by exact prefixLift 2749098
  have htrace : WordTrace (prefixWord ++ tailWord_2749098) baseStart_2749098 baseEnd_2749098 := by
    simpa [prefixWord, tailWord_2749098, baseEnd_2749098] using wordTrace_append hprefix tailTrace_2749098
  have hstable : (prefixWord ++ tailWord_2749098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749098).length < 2 ^ (prefixWord ++ tailWord_2749098).sum := by decide
  have hdescent : baseEnd_2749098 < baseStart_2749098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749127 : List Nat := [1, 1, 4, 1, 1, 1, 2, 6, 2, 4]
def baseStart_2749127 : Nat := 118140960795 + 2749127 * 2 ^ 59
def prefixEnd_2749127 : Nat := 4983230072969 + 3 ^ 40 * 2749127 * 2
def baseEnd_2749127 : Nat := 470541177084323587223167

theorem tailTrace_2749127 : CollatzResearch.WordTrace tailWord_2749127 prefixEnd_2749127 470541177084323587223167 := by
  unfold tailWord_2749127
  simp only [CollatzResearch.WordTrace]
  refine ⟨100268899111389867356829635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66845932740926578237886423 100268899111389867356829635)
  ·
    refine ⟨150403348667084801035244453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100268899111389867356829635 150403348667084801035244453)
    ·
      refine ⟨28200627875078400194108335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150403348667084801035244453 28200627875078400194108335)
      ·
        refine ⟨42300941812617600291162503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28200627875078400194108335 42300941812617600291162503)
        ·
          refine ⟨63451412718926400436743755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42300941812617600291162503 63451412718926400436743755)
          ·
            refine ⟨95177119078389600655115633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63451412718926400436743755 95177119078389600655115633)
            ·
              refine ⟨71382839308792200491336725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95177119078389600655115633 71382839308792200491336725)
              ·
                refine ⟨3346070592599634398031409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71382839308792200491336725 3346070592599634398031409)
                ·
                  refine ⟨2509552944449725798523557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3346070592599634398031409 2509552944449725798523557)
                  ·
                    refine ⟨470541177084323587223167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2509552944449725798523557 470541177084323587223167)
                    ·
                      rfl

theorem cell23_2749127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_2749127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749127 prefixEnd_2749127 := by exact prefixLift 2749127
  have htrace : WordTrace (prefixWord ++ tailWord_2749127) baseStart_2749127 baseEnd_2749127 := by
    simpa [prefixWord, tailWord_2749127, baseEnd_2749127] using wordTrace_append hprefix tailTrace_2749127
  have hstable : (prefixWord ++ tailWord_2749127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749127).length < 2 ^ (prefixWord ++ tailWord_2749127).sum := by decide
  have hdescent : baseEnd_2749127 < baseStart_2749127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749157 : List Nat := [1, 3, 1, 4, 1, 2, 4, 7]
def baseStart_2749157 : Nat := 118140960795 + 2749157 * 2 ^ 59
def prefixEnd_2749157 : Nat := 4983230072969 + 3 ^ 40 * 2749157 * 2
def baseEnd_2749157 : Nat := 52282923543429838677569

theorem tailTrace_2749157 : CollatzResearch.WordTrace tailWord_2749157 prefixEnd_2749157 52282923543429838677569 := by
  unfold tailWord_2749157
  simp only [CollatzResearch.WordTrace]
  refine ⟨100269993301281182480421725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66846662200854121653614483 100269993301281182480421725)
  ·
    refine ⟨37601247487980443430158147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100269993301281182480421725 37601247487980443430158147)
    ·
      refine ⟨56401871231970665145237221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37601247487980443430158147 56401871231970665145237221)
      ·
        refine ⟨10575350855994499714731979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56401871231970665145237221 10575350855994499714731979)
        ·
          refine ⟨15863026283991749572097969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10575350855994499714731979 15863026283991749572097969)
          ·
            refine ⟨11897269712993812179073477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15863026283991749572097969 11897269712993812179073477)
            ·
              refine ⟨2230738071186339783576277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11897269712993812179073477 2230738071186339783576277)
              ·
                refine ⟨52282923543429838677569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2230738071186339783576277 52282923543429838677569)
                ·
                  rfl

theorem cell23_2749157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 7].length) (baseStart_2749157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749157 prefixEnd_2749157 := by exact prefixLift 2749157
  have htrace : WordTrace (prefixWord ++ tailWord_2749157) baseStart_2749157 baseEnd_2749157 := by
    simpa [prefixWord, tailWord_2749157, baseEnd_2749157] using wordTrace_append hprefix tailTrace_2749157
  have hstable : (prefixWord ++ tailWord_2749157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749157).length < 2 ^ (prefixWord ++ tailWord_2749157).sum := by decide
  have hdescent : baseEnd_2749157 < baseStart_2749157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749194 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 3, 3, 2]
def baseStart_2749194 : Nat := 118140960795 + 2749194 * 2 ^ 59
def prefixEnd_2749194 : Nat := 4983230072969 + 3 ^ 40 * 2749194 * 2
def baseEnd_2749194 : Nat := 1411657934456821999531693

theorem tailTrace_2749194 : CollatzResearch.WordTrace tailWord_2749194 prefixEnd_2749194 1411657934456821999531693 := by
  unfold tailWord_2749194
  simp only [CollatzResearch.WordTrace]
  refine ⟨25067835700536784449879659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66847561868098091866345757 25067835700536784449879659)
  ·
    refine ⟨37601753550805176674819489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25067835700536784449879659 37601753550805176674819489)
    ·
      refine ⟨28201315163103882506114617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37601753550805176674819489 28201315163103882506114617)
      ·
        refine ⟨21150986372327911879585963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28201315163103882506114617 21150986372327911879585963)
        ·
          refine ⟨31726479558491867819378945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21150986372327911879585963 31726479558491867819378945)
          ·
            refine ⟨23794859668868900864534209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31726479558491867819378945 23794859668868900864534209)
            ·
              refine ⟨17846144751651675648400657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23794859668868900864534209 17846144751651675648400657)
              ·
                refine ⟨13384608563738756736300493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17846144751651675648400657 13384608563738756736300493)
                ·
                  refine ⟨5019228211402033776112685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13384608563738756736300493 5019228211402033776112685)
                  ·
                    refine ⟨1882210579275762666042257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5019228211402033776112685 1882210579275762666042257)
                    ·
                      refine ⟨1411657934456821999531693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1882210579275762666042257 1411657934456821999531693)
                      ·
                        rfl

theorem cell23_2749194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_2749194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749194 prefixEnd_2749194 := by exact prefixLift 2749194
  have htrace : WordTrace (prefixWord ++ tailWord_2749194) baseStart_2749194 baseEnd_2749194 := by
    simpa [prefixWord, tailWord_2749194, baseEnd_2749194] using wordTrace_append hprefix tailTrace_2749194
  have hstable : (prefixWord ++ tailWord_2749194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749194).length < 2 ^ (prefixWord ++ tailWord_2749194).sum := by decide
  have hdescent : baseEnd_2749194 < baseStart_2749194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749201 : List Nat := [1, 2, 2, 1, 1, 3, 6, 1, 2, 1, 3]
def baseStart_2749201 : Nat := 118140960795 + 2749201 * 2 ^ 59
def prefixEnd_2749201 : Nat := 4983230072969 + 3 ^ 40 * 2749201 * 2
def baseEnd_2749201 : Nat := 1411661528821403472144161

theorem tailTrace_2749201 : CollatzResearch.WordTrace tailWord_2749201 prefixEnd_2749201 1411661528821403472144161 := by
  unfold tailWord_2749201
  simp only [CollatzResearch.WordTrace]
  refine ⟨100271598113121777995023457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66847732075414518663348971 100271598113121777995023457)
  ·
    refine ⟨75203698584841333496267593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100271598113121777995023457 75203698584841333496267593)
    ·
      refine ⟨56402773938631000122200695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75203698584841333496267593 56402773938631000122200695)
      ·
        refine ⟨84604160907946500183301043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56402773938631000122200695 84604160907946500183301043)
        ·
          refine ⟨126906241361919750274951565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84604160907946500183301043 126906241361919750274951565)
          ·
            refine ⟨47589840510719906353106837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126906241361919750274951565 47589840510719906353106837)
            ·
              refine ⟨2230773773939995610301883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47589840510719906353106837 2230773773939995610301883)
              ·
                refine ⟨3346160660909993415452825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2230773773939995610301883 3346160660909993415452825)
                ·
                  refine ⟨2509620495682495061589619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3346160660909993415452825 2509620495682495061589619)
                  ·
                    refine ⟨3764430743523742592384429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2509620495682495061589619 3764430743523742592384429)
                    ·
                      refine ⟨1411661528821403472144161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3764430743523742592384429 1411661528821403472144161)
                      ·
                        rfl

theorem cell23_2749201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 2, 1, 3].length) (baseStart_2749201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749201 prefixEnd_2749201 := by exact prefixLift 2749201
  have htrace : WordTrace (prefixWord ++ tailWord_2749201) baseStart_2749201 baseEnd_2749201 := by
    simpa [prefixWord, tailWord_2749201, baseEnd_2749201] using wordTrace_append hprefix tailTrace_2749201
  have hstable : (prefixWord ++ tailWord_2749201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749201).length < 2 ^ (prefixWord ++ tailWord_2749201).sum := by decide
  have hdescent : baseEnd_2749201 < baseStart_2749201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749257 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 1, 5, 3]
def baseStart_2749257 : Nat := 118140960795 + 2749257 * 2 ^ 59
def prefixEnd_2749257 : Nat := 4983230072969 + 3 ^ 40 * 2749257 * 2
def baseEnd_2749257 : Nat := 1411690283738055253043903

theorem tailTrace_2749257 : CollatzResearch.WordTrace tailWord_2749257 prefixEnd_2749257 1411690283738055253043903 := by
  unfold tailWord_2749257
  simp only [CollatzResearch.WordTrace]
  refine ⟨100273640600918899559062025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66849093733945933039374683 100273640600918899559062025)
  ·
    refine ⟨75205230450689174669296519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100273640600918899559062025 75205230450689174669296519)
    ·
      refine ⟨112807845676033762003944779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75205230450689174669296519 112807845676033762003944779)
      ·
        refine ⟨169211768514050643005917169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112807845676033762003944779 169211768514050643005917169)
        ·
          refine ⟨126908826385537982254437877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169211768514050643005917169 126908826385537982254437877)
          ·
            refine ⟨11897702473644185836353551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126908826385537982254437877 11897702473644185836353551)
            ·
              refine ⟨17846553710466278754530327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11897702473644185836353551 17846553710466278754530327)
              ·
                refine ⟨26769830565699418131795491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17846553710466278754530327 26769830565699418131795491)
                ·
                  refine ⟨40154745848549127197693237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26769830565699418131795491 40154745848549127197693237)
                  ·
                    refine ⟨3764507423301480674783741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40154745848549127197693237 3764507423301480674783741)
                    ·
                      refine ⟨1411690283738055253043903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3764507423301480674783741 1411690283738055253043903)
                      ·
                        rfl

theorem cell23_2749257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 5, 3].length) (baseStart_2749257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749257 prefixEnd_2749257 := by exact prefixLift 2749257
  have htrace : WordTrace (prefixWord ++ tailWord_2749257) baseStart_2749257 baseEnd_2749257 := by
    simpa [prefixWord, tailWord_2749257, baseEnd_2749257] using wordTrace_append hprefix tailTrace_2749257
  have hstable : (prefixWord ++ tailWord_2749257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749257).length < 2 ^ (prefixWord ++ tailWord_2749257).sum := by decide
  have hdescent : baseEnd_2749257 < baseStart_2749257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749324 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 3, 4]
def baseStart_2749324 : Nat := 118140960795 + 2749324 * 2 ^ 59
def prefixEnd_2749324 : Nat := 4983230072969 + 3 ^ 40 * 2749324 * 2
def baseEnd_2749324 : Nat := 470574895647302163635365

theorem tailTrace_2749324 : CollatzResearch.WordTrace tailWord_2749324 prefixEnd_2749324 470574895647302163635365 := by
  unfold tailWord_2749324
  simp only [CollatzResearch.WordTrace]
  refine ⟨50138042145838085000875513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66850722861117446667834017 50138042145838085000875513)
  ·
    refine ⟨37603531609378563750656635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50138042145838085000875513 37603531609378563750656635)
    ·
      refine ⟨56405297414067845625984953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37603531609378563750656635 56405297414067845625984953)
      ·
        refine ⟨42303973060550884219488715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56405297414067845625984953 42303973060550884219488715)
        ·
          refine ⟨63455959590826326329233073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42303973060550884219488715 63455959590826326329233073)
          ·
            refine ⟨47591969693119744746924805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63455959590826326329233073 47591969693119744746924805)
            ·
              refine ⟨8923494317459952140048401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47591969693119744746924805 8923494317459952140048401)
              ·
                refine ⟨6692620738094964105036301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8923494317459952140048401 6692620738094964105036301)
                ·
                  refine ⟨2509732776785611539388613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6692620738094964105036301 2509732776785611539388613)
                  ·
                    refine ⟨470574895647302163635365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2509732776785611539388613 470574895647302163635365)
                    ·
                      rfl

theorem cell23_2749324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_2749324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749324 prefixEnd_2749324 := by exact prefixLift 2749324
  have htrace : WordTrace (prefixWord ++ tailWord_2749324) baseStart_2749324 baseEnd_2749324 := by
    simpa [prefixWord, tailWord_2749324, baseEnd_2749324] using wordTrace_append hprefix tailTrace_2749324
  have hstable : (prefixWord ++ tailWord_2749324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749324).length < 2 ^ (prefixWord ++ tailWord_2749324).sum := by decide
  have hdescent : baseEnd_2749324 < baseStart_2749324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749391 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 2, 3, 2]
def baseStart_2749391 : Nat := 118140960795 + 2749391 * 2 ^ 59
def prefixEnd_2749391 : Nat := 4983230072969 + 3 ^ 40 * 2749391 * 2
def baseEnd_2749391 : Nat := 1411759090145757728768287

theorem tailTrace_2749391 : CollatzResearch.WordTrace tailWord_2749391 prefixEnd_2749391 1411759090145757728768287 := by
  unfold tailWord_2749391
  simp only [CollatzResearch.WordTrace]
  refine ⟨100278527982433440444440027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66852351988288960296293351 100278527982433440444440027)
  ·
    refine ⟨150417791973650160666660041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100278527982433440444440027 150417791973650160666660041)
    ·
      refine ⟨112813343980237620499995031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150417791973650160666660041 112813343980237620499995031)
      ·
        refine ⟨169220015970356430749992547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112813343980237620499995031 169220015970356430749992547)
        ·
          refine ⟨253830023955534646124988821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169220015970356430749992547 253830023955534646124988821)
          ·
            refine ⟨11898282372915686537108851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 253830023955534646124988821 11898282372915686537108851)
            ·
              refine ⟨17847423559373529805663277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11898282372915686537108851 17847423559373529805663277)
              ·
                refine ⟨6692783834765073677123729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17847423559373529805663277 6692783834765073677123729)
                ·
                  refine ⟨5019587876073805257842797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6692783834765073677123729 5019587876073805257842797)
                  ·
                    refine ⟨1882345453527676971691049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5019587876073805257842797 1882345453527676971691049)
                    ·
                      refine ⟨1411759090145757728768287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1882345453527676971691049 1411759090145757728768287)
                      ·
                        rfl

theorem cell23_2749391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 3, 2].length) (baseStart_2749391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749391 prefixEnd_2749391 := by exact prefixLift 2749391
  have htrace : WordTrace (prefixWord ++ tailWord_2749391) baseStart_2749391 baseEnd_2749391 := by
    simpa [prefixWord, tailWord_2749391, baseEnd_2749391] using wordTrace_append hprefix tailTrace_2749391
  have hstable : (prefixWord ++ tailWord_2749391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749391).length < 2 ^ (prefixWord ++ tailWord_2749391).sum := by decide
  have hdescent : baseEnd_2749391 < baseStart_2749391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749415 : List Nat := [1, 1, 5, 2, 2, 2, 1, 4, 1, 1, 3]
def baseStart_2749415 : Nat := 118140960795 + 2749415 * 2 ^ 59
def prefixEnd_2749415 : Nat := 4983230072969 + 3 ^ 40 * 2749415 * 2
def baseEnd_2749415 : Nat := 1411771413681465634868177

theorem tailTrace_2749415 : CollatzResearch.WordTrace tailWord_2749415 prefixEnd_2749415 1411771413681465634868177 := by
  unfold tailWord_2749415
  simp only [CollatzResearch.WordTrace]
  refine ⟨100279403334346492543313699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66852935556230995028875799 100279403334346492543313699)
  ·
    refine ⟨150419105001519738814970549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100279403334346492543313699 150419105001519738814970549)
    ·
      refine ⟨14101791093892475513903489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150419105001519738814970549 14101791093892475513903489)
      ·
        refine ⟨10576343320419356635427617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14101791093892475513903489 10576343320419356635427617)
        ·
          refine ⟨7932257490314517476570713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10576343320419356635427617 7932257490314517476570713)
          ·
            refine ⟨5949193117735888107428035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7932257490314517476570713 5949193117735888107428035)
            ·
              refine ⟨8923789676603832161142053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5949193117735888107428035 8923789676603832161142053)
              ·
                refine ⟨1673210564363218530214135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8923789676603832161142053 1673210564363218530214135)
                ·
                  refine ⟨2509815846544827795321203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1673210564363218530214135 2509815846544827795321203)
                  ·
                    refine ⟨3764723769817241692981805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2509815846544827795321203 3764723769817241692981805)
                    ·
                      refine ⟨1411771413681465634868177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3764723769817241692981805 1411771413681465634868177)
                      ·
                        rfl

theorem cell23_2749415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_2749415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749415 prefixEnd_2749415 := by exact prefixLift 2749415
  have htrace : WordTrace (prefixWord ++ tailWord_2749415) baseStart_2749415 baseEnd_2749415 := by
    simpa [prefixWord, tailWord_2749415, baseEnd_2749415] using wordTrace_append hprefix tailTrace_2749415
  have hstable : (prefixWord ++ tailWord_2749415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749415).length < 2 ^ (prefixWord ++ tailWord_2749415).sum := by decide
  have hdescent : baseEnd_2749415 < baseStart_2749415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749441 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_2749441 : Nat := 118140960795 + 2749441 * 2 ^ 59
def prefixEnd_2749441 : Nat := 4983230072969 + 3 ^ 40 * 2749441 * 2
def baseEnd_2749441 : Nat := 1411784764178482533143057

theorem tailTrace_2749441 : CollatzResearch.WordTrace tailWord_2749441 prefixEnd_2749441 1411784764178482533143057 := by
  unfold tailWord_2749441
  simp only [CollatzResearch.WordTrace]
  refine ⟨100280351632252298983760177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66853567754834865989173451 100280351632252298983760177)
  ·
    refine ⟨75210263724189224237820133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100280351632252298983760177 75210263724189224237820133)
    ·
      refine ⟨14101924448285479544591275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75210263724189224237820133 14101924448285479544591275)
      ·
        refine ⟨21152886672428219316886913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14101924448285479544591275 21152886672428219316886913)
        ·
          refine ⟨15864665004321164487665185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21152886672428219316886913 15864665004321164487665185)
          ·
            refine ⟨11898498753240873365748889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15864665004321164487665185 11898498753240873365748889)
            ·
              refine ⟨8923874064930655024311667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11898498753240873365748889 8923874064930655024311667)
              ·
                refine ⟨13385811097395982536467501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8923874064930655024311667 13385811097395982536467501)
                ·
                  refine ⟨5019679161523493451175313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13385811097395982536467501 5019679161523493451175313)
                  ·
                    refine ⟨3764759371142620088381485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5019679161523493451175313 3764759371142620088381485)
                    ·
                      refine ⟨1411784764178482533143057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3764759371142620088381485 1411784764178482533143057)
                      ·
                        rfl

theorem cell23_2749441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_2749441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749441 prefixEnd_2749441 := by exact prefixLift 2749441
  have htrace : WordTrace (prefixWord ++ tailWord_2749441) baseStart_2749441 baseEnd_2749441 := by
    simpa [prefixWord, tailWord_2749441, baseEnd_2749441] using wordTrace_append hprefix tailTrace_2749441
  have hstable : (prefixWord ++ tailWord_2749441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749441).length < 2 ^ (prefixWord ++ tailWord_2749441).sum := by decide
  have hdescent : baseEnd_2749441 < baseStart_2749441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749472 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 3, 2, 2]
def baseStart_2749472 : Nat := 118140960795 + 2749472 * 2 ^ 59
def prefixEnd_2749472 : Nat := 4983230072969 + 3 ^ 40 * 2749472 * 2
def baseEnd_2749472 : Nat := 1411800682078771911855415

theorem tailTrace_2749472 : CollatzResearch.WordTrace tailWord_2749472 prefixEnd_2749472 1411800682078771911855415 := by
  unfold tailWord_2749472
  simp only [CollatzResearch.WordTrace]
  refine ⟨50140741147569995639069335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66854321530093327518759113 50140741147569995639069335)
  ·
    refine ⟨75211111721354993458604003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50140741147569995639069335 75211111721354993458604003)
    ·
      refine ⟨112816667582032490187906005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75211111721354993458604003 112816667582032490187906005)
      ·
        refine ⟨2644140646453886488779047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 112816667582032490187906005 2644140646453886488779047)
        ·
          refine ⟨3966210969680829733168571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2644140646453886488779047 3966210969680829733168571)
          ·
            refine ⟨5949316454521244599752857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3966210969680829733168571 5949316454521244599752857)
            ·
              refine ⟨4461987340890933449814643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5949316454521244599752857 4461987340890933449814643)
              ·
                refine ⟨6692981011336400174721965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4461987340890933449814643 6692981011336400174721965)
                ·
                  refine ⟨2509867879251150065520737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6692981011336400174721965 2509867879251150065520737)
                  ·
                    refine ⟨1882400909438362549140553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2509867879251150065520737 1882400909438362549140553)
                    ·
                      refine ⟨1411800682078771911855415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1882400909438362549140553 1411800682078771911855415)
                      ·
                        rfl

theorem cell23_2749472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_2749472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749472 prefixEnd_2749472 := by exact prefixLift 2749472
  have htrace : WordTrace (prefixWord ++ tailWord_2749472) baseStart_2749472 baseEnd_2749472 := by
    simpa [prefixWord, tailWord_2749472, baseEnd_2749472] using wordTrace_append hprefix tailTrace_2749472
  have hstable : (prefixWord ++ tailWord_2749472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749472).length < 2 ^ (prefixWord ++ tailWord_2749472).sum := by decide
  have hdescent : baseEnd_2749472 < baseStart_2749472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749498 : List Nat := [3, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2]
def baseStart_2749498 : Nat := 118140960795 + 2749498 * 2 ^ 59
def prefixEnd_2749498 : Nat := 4983230072969 + 3 ^ 40 * 2749498 * 2
def baseEnd_2749498 : Nat := 1411814032575788810130295

theorem tailTrace_2749498 : CollatzResearch.WordTrace tailWord_2749498 prefixEnd_2749498 1411814032575788810130295 := by
  unfold tailWord_2749498
  simp only [CollatzResearch.WordTrace]
  refine ⟨25070607648261449429646287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66854953728697198479056765 25070607648261449429646287)
  ·
    refine ⟨37605911472392174144469431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25070607648261449429646287 37605911472392174144469431)
    ·
      refine ⟨56408867208588261216704147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37605911472392174144469431 56408867208588261216704147)
      ·
        refine ⟨84613300812882391825056221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56408867208588261216704147 84613300812882391825056221)
        ·
          refine ⟨31729987804830896934396083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84613300812882391825056221 31729987804830896934396083)
          ·
            refine ⟨47594981707246345401594125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31729987804830896934396083 47594981707246345401594125)
            ·
              refine ⟨17848118140217379525597797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47594981707246345401594125 17848118140217379525597797)
              ·
                refine ⟨3346522151290758661049587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17848118140217379525597797 3346522151290758661049587)
                ·
                  refine ⟨5019783226936137991574381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3346522151290758661049587 5019783226936137991574381)
                  ·
                    refine ⟨1882418710101051746840393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5019783226936137991574381 1882418710101051746840393)
                    ·
                      refine ⟨1411814032575788810130295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1882418710101051746840393 1411814032575788810130295)
                      ·
                        rfl

theorem cell23_2749498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2].length) (baseStart_2749498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749498 prefixEnd_2749498 := by exact prefixLift 2749498
  have htrace : WordTrace (prefixWord ++ tailWord_2749498) baseStart_2749498 baseEnd_2749498 := by
    simpa [prefixWord, tailWord_2749498, baseEnd_2749498] using wordTrace_append hprefix tailTrace_2749498
  have hstable : (prefixWord ++ tailWord_2749498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749498).length < 2 ^ (prefixWord ++ tailWord_2749498).sum := by decide
  have hdescent : baseEnd_2749498 < baseStart_2749498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749514 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_2749514 : Nat := 118140960795 + 2749514 * 2 ^ 59
def prefixEnd_2749514 : Nat := 4983230072969 + 3 ^ 40 * 2749514 * 2
def baseEnd_2749514 : Nat := 1411822248266260747530221

theorem tailTrace_2749514 : CollatzResearch.WordTrace tailWord_2749514 prefixEnd_2749514 1411822248266260747530221 := by
  unfold tailWord_2749514
  simp only [CollatzResearch.WordTrace]
  refine ⟨25070753540246958112791899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66855342773991888300778397 25070753540246958112791899)
  ·
    refine ⟨37606130310370437169187849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25070753540246958112791899 37606130310370437169187849)
    ·
      refine ⟨28204597732777827876890887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37606130310370437169187849 28204597732777827876890887)
      ·
        refine ⟨42306896599166741815336331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28204597732777827876890887 42306896599166741815336331)
        ·
          refine ⟨63460344898750112723004497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42306896599166741815336331 63460344898750112723004497)
          ·
            refine ⟨47595258674062584542253373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63460344898750112723004497 47595258674062584542253373)
            ·
              refine ⟨17848222002773469203345015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47595258674062584542253373 17848222002773469203345015)
              ·
                refine ⟨26772333004160203805017523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17848222002773469203345015 26772333004160203805017523)
                ·
                  refine ⟨40158499506240305707526285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26772333004160203805017523 40158499506240305707526285)
                  ·
                    refine ⟨15059437314840114640322357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40158499506240305707526285 15059437314840114640322357)
                    ·
                      refine ⟨1411822248266260747530221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15059437314840114640322357 1411822248266260747530221)
                      ·
                        rfl

theorem cell23_2749514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_2749514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749514 prefixEnd_2749514 := by exact prefixLift 2749514
  have htrace : WordTrace (prefixWord ++ tailWord_2749514) baseStart_2749514 baseEnd_2749514 := by
    simpa [prefixWord, tailWord_2749514, baseEnd_2749514] using wordTrace_append hprefix tailTrace_2749514
  have hstable : (prefixWord ++ tailWord_2749514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749514).length < 2 ^ (prefixWord ++ tailWord_2749514).sum := by decide
  have hdescent : baseEnd_2749514 < baseStart_2749514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749528 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 4, 2, 2]
def baseStart_2749528 : Nat := 118140960795 + 2749528 * 2 ^ 59
def prefixEnd_2749528 : Nat := 4983230072969 + 3 ^ 40 * 2749528 * 2
def baseEnd_2749528 : Nat := 1411829436995423692755157

theorem tailTrace_2749528 : CollatzResearch.WordTrace tailWord_2749528 prefixEnd_2749528 1411829436995423692755157 := by
  unfold tailWord_2749528
  simp only [CollatzResearch.WordTrace]
  refine ⟨50141762391468556421088619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66855683188624741894784825 50141762391468556421088619)
  ·
    refine ⟨75212643587202834631632929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50141762391468556421088619 75212643587202834631632929)
    ·
      refine ⟨56409482690402125973724697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75212643587202834631632929 56409482690402125973724697)
      ·
        refine ⟨42307112017801594480293523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56409482690402125973724697 42307112017801594480293523)
        ·
          refine ⟨63460668026702391720440285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42307112017801594480293523 63460668026702391720440285)
          ·
            refine ⟨23797750510013396895165107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63460668026702391720440285 23797750510013396895165107)
            ·
              refine ⟨35696625765020095342747661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23797750510013396895165107 35696625765020095342747661)
              ·
                refine ⟨13386234661882535753530373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35696625765020095342747661 13386234661882535753530373)
                ·
                  refine ⟨2509918999102975453786945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13386234661882535753530373 2509918999102975453786945)
                  ·
                    refine ⟨1882439249327231590340209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2509918999102975453786945 1882439249327231590340209)
                    ·
                      refine ⟨1411829436995423692755157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1882439249327231590340209 1411829436995423692755157)
                      ·
                        rfl

theorem cell23_2749528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_2749528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749528 prefixEnd_2749528 := by exact prefixLift 2749528
  have htrace : WordTrace (prefixWord ++ tailWord_2749528) baseStart_2749528 baseEnd_2749528 := by
    simpa [prefixWord, tailWord_2749528, baseEnd_2749528] using wordTrace_append hprefix tailTrace_2749528
  have hstable : (prefixWord ++ tailWord_2749528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749528).length < 2 ^ (prefixWord ++ tailWord_2749528).sum := by decide
  have hdescent : baseEnd_2749528 < baseStart_2749528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749545 : List Nat := [1, 2, 1, 1, 1, 7, 1, 3, 2, 2, 2]
def baseStart_2749545 : Nat := 118140960795 + 2749545 * 2 ^ 59
def prefixEnd_2749545 : Nat := 4983230072969 + 3 ^ 40 * 2749545 * 2
def baseEnd_2749545 : Nat := 1411838166166550126242579

theorem tailTrace_2749545 : CollatzResearch.WordTrace tailWord_2749545 prefixEnd_2749545 1411838166166550126242579 := by
  unfold tailWord_2749545
  simp only [CollatzResearch.WordTrace]
  refine ⟨100284144823875524745546089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66856096549250349830364059 100284144823875524745546089)
  ·
    refine ⟨75213108617906643559159567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100284144823875524745546089 75213108617906643559159567)
    ·
      refine ⟨112819662926859965338739351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75213108617906643559159567 112819662926859965338739351)
      ·
        refine ⟨169229494390289948008109027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112819662926859965338739351 169229494390289948008109027)
        ·
          refine ⟨253844241585434922012163541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169229494390289948008109027 253844241585434922012163541)
          ·
            refine ⟨5949474412158630984660083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 253844241585434922012163541 5949474412158630984660083)
            ·
              refine ⟨8924211618237946476990125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5949474412158630984660083 8924211618237946476990125)
              ·
                refine ⟨3346579356839229928871297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8924211618237946476990125 3346579356839229928871297)
                ·
                  refine ⟨2509934517629422446653473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3346579356839229928871297 2509934517629422446653473)
                  ·
                    refine ⟨1882450888222066834990105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2509934517629422446653473 1882450888222066834990105)
                    ·
                      refine ⟨1411838166166550126242579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1882450888222066834990105 1411838166166550126242579)
                      ·
                        rfl

theorem cell23_2749545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 2, 2].length) (baseStart_2749545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749545 prefixEnd_2749545 := by exact prefixLift 2749545
  have htrace : WordTrace (prefixWord ++ tailWord_2749545) baseStart_2749545 baseEnd_2749545 := by
    simpa [prefixWord, tailWord_2749545, baseEnd_2749545] using wordTrace_append hprefix tailTrace_2749545
  have hstable : (prefixWord ++ tailWord_2749545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749545).length < 2 ^ (prefixWord ++ tailWord_2749545).sum := by decide
  have hdescent : baseEnd_2749545 < baseStart_2749545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749591 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 5]
def baseStart_2749591 : Nat := 118140960795 + 2749591 * 2 ^ 59
def prefixEnd_2749591 : Nat := 4983230072969 + 3 ^ 40 * 2749591 * 2
def baseEnd_2749591 : Nat := 1411861786276656946267367

theorem tailTrace_2749591 : CollatzResearch.WordTrace tailWord_2749591 prefixEnd_2749591 1411861786276656946267367 := by
  unfold tailWord_2749591
  simp only [CollatzResearch.WordTrace]
  refine ⟨100285822581708874601720627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66857215054472583067813751 100285822581708874601720627)
  ·
    refine ⟨150428733872563311902580941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100285822581708874601720627 150428733872563311902580941)
    ·
      refine ⟨56410775202211241963467853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150428733872563311902580941 56410775202211241963467853)
      ·
        refine ⟨21154040700829215736300445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56410775202211241963467853 21154040700829215736300445)
        ·
          refine ⟨7932765262810955901112667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21154040700829215736300445 7932765262810955901112667)
          ·
            refine ⟨11899147894216433851669001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7932765262810955901112667 11899147894216433851669001)
            ·
              refine ⟨8924360920662325388751751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11899147894216433851669001 8924360920662325388751751)
              ·
                refine ⟨13386541380993488083127627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8924360920662325388751751 13386541380993488083127627)
                ·
                  refine ⟨20079812071490232124691441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13386541380993488083127627 20079812071490232124691441)
                  ·
                    refine ⟨15059859053617674093518581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20079812071490232124691441 15059859053617674093518581)
                    ·
                      refine ⟨1411861786276656946267367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15059859053617674093518581 1411861786276656946267367)
                      ·
                        rfl

theorem cell23_2749591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_2749591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749591 prefixEnd_2749591 := by exact prefixLift 2749591
  have htrace : WordTrace (prefixWord ++ tailWord_2749591) baseStart_2749591 baseEnd_2749591 := by
    simpa [prefixWord, tailWord_2749591, baseEnd_2749591] using wordTrace_append hprefix tailTrace_2749591
  have hstable : (prefixWord ++ tailWord_2749591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749591).length < 2 ^ (prefixWord ++ tailWord_2749591).sum := by decide
  have hdescent : baseEnd_2749591 < baseStart_2749591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749601 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2749601 : Nat := 118140960795 + 2749601 * 2 ^ 59
def prefixEnd_2749601 : Nat := 4983230072969 + 3 ^ 40 * 2749601 * 2
def baseEnd_2749601 : Nat := 1411866921083201907142321

theorem tailTrace_2749601 : CollatzResearch.WordTrace tailWord_2749601 prefixEnd_2749601 1411866921083201907142321 := by
  unfold tailWord_2749601
  simp only [CollatzResearch.WordTrace]
  refine ⟨100286187311672646309584657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66857458207781764206389771 100286187311672646309584657)
  ·
    refine ⟨75214640483754484732188493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100286187311672646309584657 75214640483754484732188493)
    ·
      refine ⟨28205490181407931774570685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75214640483754484732188493 28205490181407931774570685)
      ·
        refine ⟨10577058818027974415464007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28205490181407931774570685 10577058818027974415464007)
        ·
          refine ⟨15865588227041961623196011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10577058818027974415464007 15865588227041961623196011)
          ·
            refine ⟨23798382340562942434794017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15865588227041961623196011 23798382340562942434794017)
            ·
              refine ⟨17848786755422206826095513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23798382340562942434794017 17848786755422206826095513)
              ·
                refine ⟨13386590066566655119571635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17848786755422206826095513 13386590066566655119571635)
                ·
                  refine ⟨20079885099849982679357453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13386590066566655119571635 20079885099849982679357453)
                  ·
                    refine ⟨7529956912443743504759045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20079885099849982679357453 7529956912443743504759045)
                    ·
                      refine ⟨1411866921083201907142321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7529956912443743504759045 1411866921083201907142321)
                      ·
                        rfl

theorem cell23_2749601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2749601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749601 prefixEnd_2749601 := by exact prefixLift 2749601
  have htrace : WordTrace (prefixWord ++ tailWord_2749601) baseStart_2749601 baseEnd_2749601 := by
    simpa [prefixWord, tailWord_2749601, baseEnd_2749601] using wordTrace_append hprefix tailTrace_2749601
  have hstable : (prefixWord ++ tailWord_2749601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749601).length < 2 ^ (prefixWord ++ tailWord_2749601).sum := by decide
  have hdescent : baseEnd_2749601 < baseStart_2749601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749618 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4]
def baseStart_2749618 : Nat := 118140960795 + 2749618 * 2 ^ 59
def prefixEnd_2749618 : Nat := 4983230072969 + 3 ^ 40 * 2749618 * 2
def baseEnd_2749618 : Nat := 1411875650254328340629743

theorem tailTrace_2749618 : CollatzResearch.WordTrace tailWord_2749618 prefixEnd_2749618 1411875650254328340629743 := by
  unfold tailWord_2749618
  simp only [CollatzResearch.WordTrace]
  refine ⟨25071701838152764553238377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66857871568407372141969005 25071701838152764553238377)
  ·
    refine ⟨18803776378614573414928783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25071701838152764553238377 18803776378614573414928783)
    ·
      refine ⟨28205664567921860122393175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18803776378614573414928783 28205664567921860122393175)
      ·
        refine ⟨42308496851882790183589763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28205664567921860122393175 42308496851882790183589763)
        ·
          refine ⟨63462745277824185275384645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42308496851882790183589763 63462745277824185275384645)
          ·
            refine ⟨11899264739592034739134621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63462745277824185275384645 11899264739592034739134621)
            ·
              refine ⟨4462224277347013027175483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11899264739592034739134621 4462224277347013027175483)
              ·
                refine ⟨6693336416020519540763225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4462224277347013027175483 6693336416020519540763225)
                ·
                  refine ⟨5020002312015389655572419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6693336416020519540763225 5020002312015389655572419)
                  ·
                    refine ⟨7530003468023084483358629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5020002312015389655572419 7530003468023084483358629)
                    ·
                      refine ⟨1411875650254328340629743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7530003468023084483358629 1411875650254328340629743)
                      ·
                        rfl

theorem cell23_2749618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_2749618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749618 prefixEnd_2749618 := by exact prefixLift 2749618
  have htrace : WordTrace (prefixWord ++ tailWord_2749618) baseStart_2749618 baseEnd_2749618 := by
    simpa [prefixWord, tailWord_2749618, baseEnd_2749618] using wordTrace_append hprefix tailTrace_2749618
  have hstable : (prefixWord ++ tailWord_2749618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749618).length < 2 ^ (prefixWord ++ tailWord_2749618).sum := by decide
  have hdescent : baseEnd_2749618 < baseStart_2749618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749679 : List Nat := [1, 1, 2, 1, 8, 1, 1, 3, 1, 4]
def baseStart_2749679 : Nat := 118140960795 + 2749679 * 2 ^ 59
def prefixEnd_2749679 : Nat := 4983230072969 + 3 ^ 40 * 2749679 * 2
def baseEnd_2749679 : Nat := 470635657524750867322321

theorem tailTrace_2749679 : CollatzResearch.WordTrace tailWord_2749679 prefixEnd_2749679 470635657524750867322321 := by
  unfold tailWord_2749679
  simp only [CollatzResearch.WordTrace]
  refine ⟨100289032205390065630924091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66859354803593377087282727 100289032205390065630924091)
  ·
    refine ⟨150433548308085098446386137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100289032205390065630924091 150433548308085098446386137)
    ·
      refine ⟨112825161231063823834789603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150433548308085098446386137 112825161231063823834789603)
      ·
        refine ⟨169237741846595735752184405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112825161231063823834789603 169237741846595735752184405)
        ·
          refine ⟨1983254787264793778345911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 169237741846595735752184405 1983254787264793778345911)
          ·
            refine ⟨2974882180897190667518867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1983254787264793778345911 2974882180897190667518867)
            ·
              refine ⟨4462323271345786001278301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2974882180897190667518867 4462323271345786001278301)
              ·
                refine ⟨1673371226754669750479363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4462323271345786001278301 1673371226754669750479363)
                ·
                  refine ⟨2510056840132004625719045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1673371226754669750479363 2510056840132004625719045)
                  ·
                    refine ⟨470635657524750867322321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2510056840132004625719045 470635657524750867322321)
                    ·
                      rfl

theorem cell23_2749679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 1, 4].length) (baseStart_2749679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749679 prefixEnd_2749679 := by exact prefixLift 2749679
  have htrace : WordTrace (prefixWord ++ tailWord_2749679) baseStart_2749679 baseEnd_2749679 := by
    simpa [prefixWord, tailWord_2749679, baseEnd_2749679] using wordTrace_append hprefix tailTrace_2749679
  have hstable : (prefixWord ++ tailWord_2749679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749679).length < 2 ^ (prefixWord ++ tailWord_2749679).sum := by decide
  have hdescent : baseEnd_2749679 < baseStart_2749679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749695 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 2, 3, 2]
def baseStart_2749695 : Nat := 118140960795 + 2749695 * 2 ^ 59
def prefixEnd_2749695 : Nat := 4983230072969 + 3 ^ 40 * 2749695 * 2
def baseEnd_2749695 : Nat := 1411915188264724539366889

theorem tailTrace_2749695 : CollatzResearch.WordTrace tailWord_2749695 prefixEnd_2749695 1411915188264724539366889 := by
  unfold tailWord_2749695
  simp only [CollatzResearch.WordTrace]
  refine ⟨100289615773332100363506539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66859743848888066909004359 100289615773332100363506539)
  ·
    refine ⟨150434423659998150545259809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100289615773332100363506539 150434423659998150545259809)
    ·
      refine ⟨112825817744998612908944857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150434423659998150545259809 112825817744998612908944857)
      ·
        refine ⟨84619363308748959681708643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112825817744998612908944857 84619363308748959681708643)
        ·
          refine ⟨126929044963123439522562965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84619363308748959681708643 126929044963123439522562965)
          ·
            refine ⟨5949798982646411227620139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 126929044963123439522562965 5949798982646411227620139)
            ·
              refine ⟨8924698473969616841430209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5949798982646411227620139 8924698473969616841430209)
              ·
                refine ⟨6693523855477212631072657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8924698473969616841430209 6693523855477212631072657)
                ·
                  refine ⟨5020142891607909473304493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6693523855477212631072657 5020142891607909473304493)
                  ·
                    refine ⟨1882553584352966052489185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5020142891607909473304493 1882553584352966052489185)
                    ·
                      refine ⟨1411915188264724539366889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1882553584352966052489185 1411915188264724539366889)
                      ·
                        rfl

theorem cell23_2749695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 3, 2].length) (baseStart_2749695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749695 prefixEnd_2749695 := by exact prefixLift 2749695
  have htrace : WordTrace (prefixWord ++ tailWord_2749695) baseStart_2749695 baseEnd_2749695 := by
    simpa [prefixWord, tailWord_2749695, baseEnd_2749695] using wordTrace_append hprefix tailTrace_2749695
  have hstable : (prefixWord ++ tailWord_2749695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749695).length < 2 ^ (prefixWord ++ tailWord_2749695).sum := by decide
  have hdescent : baseEnd_2749695 < baseStart_2749695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749711 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 3]
def baseStart_2749711 : Nat := 118140960795 + 2749711 * 2 ^ 59
def prefixEnd_2749711 : Nat := 4983230072969 + 3 ^ 40 * 2749711 * 2
def baseEnd_2749711 : Nat := 1411923403955196476766815

theorem tailTrace_2749711 : CollatzResearch.WordTrace tailWord_2749711 prefixEnd_2749711 1411923403955196476766815 := by
  unfold tailWord_2749711
  simp only [CollatzResearch.WordTrace]
  refine ⟨100290199341274135096088987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66860132894182756730725991 100290199341274135096088987)
  ·
    refine ⟨150435299011911202644133481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100290199341274135096088987 150435299011911202644133481)
    ·
      refine ⟨112826474258933401983100111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150435299011911202644133481 112826474258933401983100111)
      ·
        refine ⟨169239711388400102974650167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112826474258933401983100111 169239711388400102974650167)
        ·
          refine ⟨253859567082600154461975251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169239711388400102974650167 253859567082600154461975251)
          ·
            refine ⟨380789350623900231692962877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253859567082600154461975251 380789350623900231692962877)
            ·
              refine ⟨142796006483962586884861079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 380789350623900231692962877 142796006483962586884861079)
              ·
                refine ⟨214194009725943880327291619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142796006483962586884861079 214194009725943880327291619)
                ·
                  refine ⟨321291014588915820490937429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214194009725943880327291619 321291014588915820490937429)
                  ·
                    refine ⟨3765129077213857271378173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 321291014588915820490937429 3765129077213857271378173)
                    ·
                      refine ⟨1411923403955196476766815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3765129077213857271378173 1411923403955196476766815)
                      ·
                        rfl

theorem cell23_2749711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 3].length) (baseStart_2749711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749711 prefixEnd_2749711 := by exact prefixLift 2749711
  have htrace : WordTrace (prefixWord ++ tailWord_2749711) baseStart_2749711 baseEnd_2749711 := by
    simpa [prefixWord, tailWord_2749711, baseEnd_2749711] using wordTrace_append hprefix tailTrace_2749711
  have hstable : (prefixWord ++ tailWord_2749711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749711).length < 2 ^ (prefixWord ++ tailWord_2749711).sum := by decide
  have hdescent : baseEnd_2749711 < baseStart_2749711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749721 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 7, 2, 4]
def baseStart_2749721 : Nat := 118140960795 + 2749721 * 2 ^ 59
def prefixEnd_2749721 : Nat := 4983230072969 + 3 ^ 40 * 2749721 * 2
def baseEnd_2749721 : Nat := 1411928538761741437641769

theorem tailTrace_2749721 : CollatzResearch.WordTrace tailWord_2749721 prefixEnd_2749721 1411928538761741437641769 := by
  unfold tailWord_2749721
  simp only [CollatzResearch.WordTrace]
  refine ⟨100290564071237906803953017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66860376047491937869302011 100290564071237906803953017)
  ·
    refine ⟨75217923053428430102964763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100290564071237906803953017 75217923053428430102964763)
    ·
      refine ⟨112826884580142645154447145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75217923053428430102964763 112826884580142645154447145)
      ·
        refine ⟨84620163435106983865835359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112826884580142645154447145 84620163435106983865835359)
        ·
          refine ⟨126930245152660475798753039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84620163435106983865835359 126930245152660475798753039)
          ·
            refine ⟨190395367728990713698129559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126930245152660475798753039 190395367728990713698129559)
            ·
              refine ⟨285593051593486070547194339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190395367728990713698129559 285593051593486070547194339)
              ·
                refine ⟨428389577390229105820791509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285593051593486070547194339 428389577390229105820791509)
                ·
                  refine ⟨10040380720083494667674801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 428389577390229105820791509 10040380720083494667674801)
                  ·
                    refine ⟨7530285540062621000756101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10040380720083494667674801 7530285540062621000756101)
                    ·
                      refine ⟨1411928538761741437641769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7530285540062621000756101 1411928538761741437641769)
                      ·
                        rfl

theorem cell23_2749721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_2749721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749721 prefixEnd_2749721 := by exact prefixLift 2749721
  have htrace : WordTrace (prefixWord ++ tailWord_2749721) baseStart_2749721 baseEnd_2749721 := by
    simpa [prefixWord, tailWord_2749721, baseEnd_2749721] using wordTrace_append hprefix tailTrace_2749721
  have hstable : (prefixWord ++ tailWord_2749721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749721).length < 2 ^ (prefixWord ++ tailWord_2749721).sum := by decide
  have hdescent : baseEnd_2749721 < baseStart_2749721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749725 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2749725 : Nat := 118140960795 + 2749725 * 2 ^ 59
def prefixEnd_2749725 : Nat := 4983230072969 + 3 ^ 40 * 2749725 * 2
def baseEnd_2749725 : Nat := 1411930592684359421991751

theorem tailTrace_2749725 : CollatzResearch.WordTrace tailWord_2749725 prefixEnd_2749725 1411930592684359421991751 := by
  unfold tailWord_2749725
  simp only [CollatzResearch.WordTrace]
  refine ⟨100290709963223415487098629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66860473308815610324732419 100290709963223415487098629)
  ·
    refine ⟨18804508118104390403830993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100290709963223415487098629 18804508118104390403830993)
    ·
      refine ⟨14103381088578292802873245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18804508118104390403830993 14103381088578292802873245)
      ·
        refine ⟨5288767908216859801077467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14103381088578292802873245 5288767908216859801077467)
        ·
          refine ⟨7933151862325289701616201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5288767908216859801077467 7933151862325289701616201)
          ·
            refine ⟨5949863896743967276212151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7933151862325289701616201 5949863896743967276212151)
            ·
              refine ⟨8924795845115950914318227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5949863896743967276212151 8924795845115950914318227)
              ·
                refine ⟨13387193767673926371477341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8924795845115950914318227 13387193767673926371477341)
                ·
                  refine ⟨5020197662877722389304003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13387193767673926371477341 5020197662877722389304003)
                  ·
                    refine ⟨7530296494316583583956005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5020197662877722389304003 7530296494316583583956005)
                    ·
                      refine ⟨1411930592684359421991751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7530296494316583583956005 1411930592684359421991751)
                      ·
                        rfl

theorem cell23_2749725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2749725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749725 prefixEnd_2749725 := by exact prefixLift 2749725
  have htrace : WordTrace (prefixWord ++ tailWord_2749725) baseStart_2749725 baseEnd_2749725 := by
    simpa [prefixWord, tailWord_2749725, baseEnd_2749725] using wordTrace_append hprefix tailTrace_2749725
  have hstable : (prefixWord ++ tailWord_2749725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749725).length < 2 ^ (prefixWord ++ tailWord_2749725).sum := by decide
  have hdescent : baseEnd_2749725 < baseStart_2749725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749731 : List Nat := [1, 1, 1, 4, 2, 3, 2, 9]
def baseStart_2749731 : Nat := 118140960795 + 2749731 * 2 ^ 59
def prefixEnd_2749731 : Nat := 4983230072969 + 3 ^ 40 * 2749731 * 2
def baseEnd_2749731 : Nat := 52293839761788385130249

theorem tailTrace_2749731 : CollatzResearch.WordTrace tailWord_2749731 prefixEnd_2749731 52293839761788385130249 := by
  unfold tailWord_2749731
  simp only [CollatzResearch.WordTrace]
  refine ⟨100290928801201678511817047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66860619200801119007878031 100290928801201678511817047)
  ·
    refine ⟨150436393201802517767725571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100290928801201678511817047 150436393201802517767725571)
    ·
      refine ⟨225654589802703776651588357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150436393201802517767725571 225654589802703776651588357)
      ·
        refine ⟨42310235588006958122172817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225654589802703776651588357 42310235588006958122172817)
        ·
          refine ⟨31732676691005218591629613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42310235588006958122172817 31732676691005218591629613)
          ·
            refine ⟨11899753759126956971861105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31732676691005218591629613 11899753759126956971861105)
            ·
              refine ⟨8924815319345217728895829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11899753759126956971861105 8924815319345217728895829)
              ·
                refine ⟨52293839761788385130249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8924815319345217728895829 52293839761788385130249)
                ·
                  rfl

theorem cell23_2749731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 9].length) (baseStart_2749731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749731 prefixEnd_2749731 := by exact prefixLift 2749731
  have htrace : WordTrace (prefixWord ++ tailWord_2749731) baseStart_2749731 baseEnd_2749731 := by
    simpa [prefixWord, tailWord_2749731, baseEnd_2749731] using wordTrace_append hprefix tailTrace_2749731
  have hstable : (prefixWord ++ tailWord_2749731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749731).length < 2 ^ (prefixWord ++ tailWord_2749731).sum := by decide
  have hdescent : baseEnd_2749731 < baseStart_2749731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749745 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 1, 1, 5]
def baseStart_2749745 : Nat := 118140960795 + 2749745 * 2 ^ 59
def prefixEnd_2749745 : Nat := 4983230072969 + 3 ^ 40 * 2749745 * 2
def baseEnd_2749745 : Nat := 1411940862297449343741659

theorem tailTrace_2749745 : CollatzResearch.WordTrace tailWord_2749745 prefixEnd_2749745 1411940862297449343741659 := by
  unfold tailWord_2749745
  simp only [CollatzResearch.WordTrace]
  refine ⟨100291439423150958902826689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66860959615433972601884459 100291439423150958902826689)
  ·
    refine ⟨75218579567363219177120017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100291439423150958902826689 75218579567363219177120017)
    ·
      refine ⟨56413934675522414382840013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75218579567363219177120017 56413934675522414382840013)
      ·
        refine ⟨21155225503320905393565005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56413934675522414382840013 21155225503320905393565005)
        ·
          refine ⟨7933209563745339522586877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21155225503320905393565005 7933209563745339522586877)
          ·
            refine ⟨2974953586404502320970079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7933209563745339522586877 2974953586404502320970079)
            ·
              refine ⟨4462430379606753481455119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2974953586404502320970079 4462430379606753481455119)
              ·
                refine ⟨6693645569410130222182679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4462430379606753481455119 6693645569410130222182679)
                ·
                  refine ⟨10040468354115195333274019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6693645569410130222182679 10040468354115195333274019)
                  ·
                    refine ⟨15060702531172792999911029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10040468354115195333274019 15060702531172792999911029)
                    ·
                      refine ⟨1411940862297449343741659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15060702531172792999911029 1411940862297449343741659)
                      ·
                        rfl

theorem cell23_2749745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_2749745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749745 prefixEnd_2749745 := by exact prefixLift 2749745
  have htrace : WordTrace (prefixWord ++ tailWord_2749745) baseStart_2749745 baseEnd_2749745 := by
    simpa [prefixWord, tailWord_2749745, baseEnd_2749745] using wordTrace_append hprefix tailTrace_2749745
  have hstable : (prefixWord ++ tailWord_2749745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749745).length < 2 ^ (prefixWord ++ tailWord_2749745).sum := by decide
  have hdescent : baseEnd_2749745 < baseStart_2749745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749753 : List Nat := [1, 2, 1, 6, 3, 1, 2, 2, 1, 1, 3]
def baseStart_2749753 : Nat := 118140960795 + 2749753 * 2 ^ 59
def prefixEnd_2749753 : Nat := 4983230072969 + 3 ^ 40 * 2749753 * 2
def baseEnd_2749753 : Nat := 1411944970142685312441623

theorem tailTrace_2749753 : CollatzResearch.WordTrace tailWord_2749753 prefixEnd_2749753 1411944970142685312441623 := by
  unfold tailWord_2749753
  simp only [CollatzResearch.WordTrace]
  refine ⟨100291731207121976269117913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66861154138081317512745275 100291731207121976269117913)
  ·
    refine ⟨75218798405341482201838435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100291731207121976269117913 75218798405341482201838435)
    ·
      refine ⟨112828197608012223302757653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75218798405341482201838435 112828197608012223302757653)
      ·
        refine ⟨5288821762875572967316765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 112828197608012223302757653 5288821762875572967316765)
        ·
          refine ⟨1983308161078339862743787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5288821762875572967316765 1983308161078339862743787)
          ·
            refine ⟨2974962241617509794115681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1983308161078339862743787 2974962241617509794115681)
            ·
              refine ⟨2231221681213132345586761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2974962241617509794115681 2231221681213132345586761)
              ·
                refine ⟨1673416260909849259190071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2231221681213132345586761 1673416260909849259190071)
                ·
                  refine ⟨2510124391364773888785107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1673416260909849259190071 2510124391364773888785107)
                  ·
                    refine ⟨3765186587047160833177661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2510124391364773888785107 3765186587047160833177661)
                    ·
                      refine ⟨1411944970142685312441623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3765186587047160833177661 1411944970142685312441623)
                      ·
                        rfl

theorem cell23_2749753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_2749753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749753 prefixEnd_2749753 := by exact prefixLift 2749753
  have htrace : WordTrace (prefixWord ++ tailWord_2749753) baseStart_2749753 baseEnd_2749753 := by
    simpa [prefixWord, tailWord_2749753, baseEnd_2749753] using wordTrace_append hprefix tailTrace_2749753
  have hstable : (prefixWord ++ tailWord_2749753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749753).length < 2 ^ (prefixWord ++ tailWord_2749753).sum := by decide
  have hdescent : baseEnd_2749753 < baseStart_2749753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749759 : List Nat := [1, 1, 2, 2, 4, 3, 1, 4, 1, 2, 2]
def baseStart_2749759 : Nat := 118140960795 + 2749759 * 2 ^ 59
def prefixEnd_2749759 : Nat := 4983230072969 + 3 ^ 40 * 2749759 * 2
def baseEnd_2749759 : Nat := 1411948051026612288966595

theorem tailTrace_2749759 : CollatzResearch.WordTrace tailWord_2749759 prefixEnd_2749759 1411948051026612288966595 := by
  unfold tailWord_2749759
  simp only [CollatzResearch.WordTrace]
  refine ⟨100291950045100239293836331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66861300030066826195890887 100291950045100239293836331)
  ·
    refine ⟨150437925067650358940754497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100291950045100239293836331 150437925067650358940754497)
    ·
      refine ⟨112828443800737769205565873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150437925067650358940754497 112828443800737769205565873)
      ·
        refine ⟨84621332850553326904174405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112828443800737769205565873 84621332850553326904174405)
        ·
          refine ⟨15866499909478748794532701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84621332850553326904174405 15866499909478748794532701)
          ·
            refine ⟨5949937466054530797949763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15866499909478748794532701 5949937466054530797949763)
            ·
              refine ⟨8924906199081796196924645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5949937466054530797949763 8924906199081796196924645)
              ·
                refine ⟨1673419912327836786923371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8924906199081796196924645 1673419912327836786923371)
                ·
                  refine ⟨2510129868491755180385057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1673419912327836786923371 2510129868491755180385057)
                  ·
                    refine ⟨1882597401368816385288793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2510129868491755180385057 1882597401368816385288793)
                    ·
                      refine ⟨1411948051026612288966595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1882597401368816385288793 1411948051026612288966595)
                      ·
                        rfl

theorem cell23_2749759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 1, 2, 2].length) (baseStart_2749759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749759 prefixEnd_2749759 := by exact prefixLift 2749759
  have htrace : WordTrace (prefixWord ++ tailWord_2749759) baseStart_2749759 baseEnd_2749759 := by
    simpa [prefixWord, tailWord_2749759, baseEnd_2749759] using wordTrace_append hprefix tailTrace_2749759
  have hstable : (prefixWord ++ tailWord_2749759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749759).length < 2 ^ (prefixWord ++ tailWord_2749759).sum := by decide
  have hdescent : baseEnd_2749759 < baseStart_2749759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749785 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 3, 3, 2]
def baseStart_2749785 : Nat := 118140960795 + 2749785 * 2 ^ 59
def prefixEnd_2749785 : Nat := 4983230072969 + 3 ^ 40 * 2749785 * 2
def baseEnd_2749785 : Nat := 1411961401523629187241475

theorem tailTrace_2749785 : CollatzResearch.WordTrace tailWord_2749785 prefixEnd_2749785 1411961401523629187241475 := by
  unfold tailWord_2749785
  simp only [CollatzResearch.WordTrace]
  refine ⟨100292898343006045734282809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66861932228670697156188539 100292898343006045734282809)
  ·
    refine ⟨75219673757254534300712107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100292898343006045734282809 75219673757254534300712107)
    ·
      refine ⟨112829510635881801451068161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75219673757254534300712107 112829510635881801451068161)
      ·
        refine ⟨84622132976911351088301121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112829510635881801451068161 84622132976911351088301121)
        ·
          refine ⟨63466599732683513316225841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84622132976911351088301121 63466599732683513316225841)
          ·
            refine ⟨47599949799512634987169381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63466599732683513316225841 47599949799512634987169381)
            ·
              refine ⟨8924990587408619060094259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47599949799512634987169381 8924990587408619060094259)
              ·
                refine ⟨13387485881112928590141389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8924990587408619060094259 13387485881112928590141389)
                ·
                  refine ⟨5020307205417348221303021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13387485881112928590141389 5020307205417348221303021)
                  ·
                    refine ⟨1882615202031505582988633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5020307205417348221303021 1882615202031505582988633)
                    ·
                      refine ⟨1411961401523629187241475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1882615202031505582988633 1411961401523629187241475)
                      ·
                        rfl

theorem cell23_2749785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 3, 2].length) (baseStart_2749785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749785 prefixEnd_2749785 := by exact prefixLift 2749785
  have htrace : WordTrace (prefixWord ++ tailWord_2749785) baseStart_2749785 baseEnd_2749785 := by
    simpa [prefixWord, tailWord_2749785, baseEnd_2749785] using wordTrace_append hprefix tailTrace_2749785
  have hstable : (prefixWord ++ tailWord_2749785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749785).length < 2 ^ (prefixWord ++ tailWord_2749785).sum := by decide
  have hdescent : baseEnd_2749785 < baseStart_2749785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749791 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 3, 8]
def baseStart_2749791 : Nat := 118140960795 + 2749791 * 2 ^ 59
def prefixEnd_2749791 : Nat := 4983230072969 + 3 ^ 40 * 2749791 * 2
def baseEnd_2749791 : Nat := 470654827469185387922149

theorem tailTrace_2749791 : CollatzResearch.WordTrace tailWord_2749791 prefixEnd_2749791 470654827469185387922149 := by
  unfold tailWord_2749791
  simp only [CollatzResearch.WordTrace]
  refine ⟨100293117180984308759001227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66862078120656205839334151 100293117180984308759001227)
  ·
    refine ⟨150439675771476463138501841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100293117180984308759001227 150439675771476463138501841)
    ·
      refine ⟨112829756828607347353876381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150439675771476463138501841 112829756828607347353876381)
      ·
        refine ⟨42311158810727755257703643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112829756828607347353876381 42311158810727755257703643)
        ·
          refine ⟨63466738216091632886555465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42311158810727755257703643 63466738216091632886555465)
          ·
            refine ⟨47600053662068724664916599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63466738216091632886555465 47600053662068724664916599)
            ·
              refine ⟨71400080493103086997374899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47600053662068724664916599 71400080493103086997374899)
              ·
                refine ⟨107100120739654630496062349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71400080493103086997374899 107100120739654630496062349)
                ·
                  refine ⟨40162545277370486436023381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107100120739654630496062349 40162545277370486436023381)
                  ·
                    refine ⟨470654827469185387922149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40162545277370486436023381 470654827469185387922149)
                    ·
                      rfl

theorem cell23_2749791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 8].length) (baseStart_2749791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749791 prefixEnd_2749791 := by exact prefixLift 2749791
  have htrace : WordTrace (prefixWord ++ tailWord_2749791) baseStart_2749791 baseEnd_2749791 := by
    simpa [prefixWord, tailWord_2749791, baseEnd_2749791] using wordTrace_append hprefix tailTrace_2749791
  have hstable : (prefixWord ++ tailWord_2749791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749791).length < 2 ^ (prefixWord ++ tailWord_2749791).sum := by decide
  have hdescent : baseEnd_2749791 < baseStart_2749791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749811 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 6]
def baseStart_2749811 : Nat := 118140960795 + 2749811 * 2 ^ 59
def prefixEnd_2749811 : Nat := 4983230072969 + 3 ^ 40 * 2749811 * 2
def baseEnd_2749811 : Nat := 1411974752020646085516355

theorem tailTrace_2749811 : CollatzResearch.WordTrace tailWord_2749811 prefixEnd_2749811 1411974752020646085516355 := by
  unfold tailWord_2749811
  simp only [CollatzResearch.WordTrace]
  refine ⟨100293846640911852174729287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66862564427274568116486191 100293846640911852174729287)
  ·
    refine ⟨150440769961367778262093931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100293846640911852174729287 150440769961367778262093931)
    ·
      refine ⟨225661154942051667393140897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150440769961367778262093931 225661154942051667393140897)
      ·
        refine ⟨169245866206538750544855673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225661154942051667393140897 169245866206538750544855673)
        ·
          refine ⟨126934399654904062908641755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169245866206538750544855673 126934399654904062908641755)
          ·
            refine ⟨190401599482356094362962633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126934399654904062908641755 190401599482356094362962633)
            ·
              refine ⟨142801199611767070772221975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190401599482356094362962633 142801199611767070772221975)
              ·
                refine ⟨214201799417650606158332963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142801199611767070772221975 214201799417650606158332963)
                ·
                  refine ⟨321302699126475909237499445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214201799417650606158332963 321302699126475909237499445)
                  ·
                    refine ⟨30122128043107116491015573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 321302699126475909237499445 30122128043107116491015573)
                    ·
                      refine ⟨1411974752020646085516355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30122128043107116491015573 1411974752020646085516355)
                      ·
                        rfl

theorem cell23_2749811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_2749811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749811 prefixEnd_2749811 := by exact prefixLift 2749811
  have htrace : WordTrace (prefixWord ++ tailWord_2749811) baseStart_2749811 baseEnd_2749811 := by
    simpa [prefixWord, tailWord_2749811, baseEnd_2749811] using wordTrace_append hprefix tailTrace_2749811
  have hstable : (prefixWord ++ tailWord_2749811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749811).length < 2 ^ (prefixWord ++ tailWord_2749811).sum := by decide
  have hdescent : baseEnd_2749811 < baseStart_2749811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749832 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 1, 4, 2]
def baseStart_2749832 : Nat := 118140960795 + 2749832 * 2 ^ 59
def prefixEnd_2749832 : Nat := 4983230072969 + 3 ^ 40 * 2749832 * 2
def baseEnd_2749832 : Nat := 1411985535114390503353759

theorem tailTrace_2749832 : CollatzResearch.WordTrace tailWord_2749832 prefixEnd_2749832 1411985535114390503353759 := by
  unfold tailWord_2749832
  simp only [CollatzResearch.WordTrace]
  refine ⟨50147306286917886380621875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66863075049223848507495833 50147306286917886380621875)
  ·
    refine ⟨75220959430376829570932813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50147306286917886380621875 75220959430376829570932813)
    ·
      refine ⟨28207859786391311089099805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75220959430376829570932813 28207859786391311089099805)
      ·
        refine ⟨10577947419896741658412427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28207859786391311089099805 10577947419896741658412427)
        ·
          refine ⟨15866921129845112487618641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10577947419896741658412427 15866921129845112487618641)
          ·
            refine ⟨11900190847383834365713981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15866921129845112487618641 11900190847383834365713981)
            ·
              refine ⟨4462571567768937887142743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11900190847383834365713981 4462571567768937887142743)
              ·
                refine ⟨6693857351653406830714115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4462571567768937887142743 6693857351653406830714115)
                ·
                  refine ⟨10040786027480110246071173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6693857351653406830714115 10040786027480110246071173)
                  ·
                    refine ⟨1882647380152520671138345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10040786027480110246071173 1882647380152520671138345)
                    ·
                      refine ⟨1411985535114390503353759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1882647380152520671138345 1411985535114390503353759)
                      ·
                        rfl

theorem cell23_2749832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_2749832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749832 prefixEnd_2749832 := by exact prefixLift 2749832
  have htrace : WordTrace (prefixWord ++ tailWord_2749832) baseStart_2749832 baseEnd_2749832 := by
    simpa [prefixWord, tailWord_2749832, baseEnd_2749832] using wordTrace_append hprefix tailTrace_2749832
  have hstable : (prefixWord ++ tailWord_2749832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749832).length < 2 ^ (prefixWord ++ tailWord_2749832).sum := by decide
  have hdescent : baseEnd_2749832 < baseStart_2749832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749852 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2749852 : Nat := 118140960795 + 2749852 * 2 ^ 59
def prefixEnd_2749852 : Nat := 4983230072969 + 3 ^ 40 * 2749852 * 2
def baseEnd_2749852 : Nat := 1411995804727480425103667

theorem tailTrace_2749852 : CollatzResearch.WordTrace tailWord_2749852 prefixEnd_2749852 1411995804727480425103667 := by
  unfold tailWord_2749852
  simp only [CollatzResearch.WordTrace]
  refine ⟨50147671016881658088485905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66863561355842210784647873 50147671016881658088485905)
  ·
    refine ⟨37610753262661243566364429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50147671016881658088485905 37610753262661243566364429)
    ·
      refine ⟨14104032473497966337386661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37610753262661243566364429 14104032473497966337386661)
      ·
        refine ⟨2644506088780868688259999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14104032473497966337386661 2644506088780868688259999)
        ·
          refine ⟨3966759133171303032389999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2644506088780868688259999 3966759133171303032389999)
          ·
            refine ⟨5950138699756954548584999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3966759133171303032389999 5950138699756954548584999)
            ·
              refine ⟨8925208049635431822877499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5950138699756954548584999 8925208049635431822877499)
              ·
                refine ⟨13387812074453147734316249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8925208049635431822877499 13387812074453147734316249)
                ·
                  refine ⟨10040859055839860800737187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13387812074453147734316249 10040859055839860800737187)
                  ·
                    refine ⟨15061288583759791201105781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10040859055839860800737187 15061288583759791201105781)
                    ·
                      refine ⟨1411995804727480425103667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15061288583759791201105781 1411995804727480425103667)
                      ·
                        rfl

theorem cell23_2749852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2749852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749852 prefixEnd_2749852 := by exact prefixLift 2749852
  have htrace : WordTrace (prefixWord ++ tailWord_2749852) baseStart_2749852 baseEnd_2749852 := by
    simpa [prefixWord, tailWord_2749852, baseEnd_2749852] using wordTrace_append hprefix tailTrace_2749852
  have hstable : (prefixWord ++ tailWord_2749852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749852).length < 2 ^ (prefixWord ++ tailWord_2749852).sum := by decide
  have hdescent : baseEnd_2749852 < baseStart_2749852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749868 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 4, 5]
def baseStart_2749868 : Nat := 118140960795 + 2749868 * 2 ^ 59
def prefixEnd_2749868 : Nat := 4983230072969 + 3 ^ 40 * 2749868 * 2
def baseEnd_2749868 : Nat := 470668006805984120834531

theorem tailTrace_2749868 : CollatzResearch.WordTrace tailWord_2749868 prefixEnd_2749868 470668006805984120834531 := by
  unfold tailWord_2749868
  simp only [CollatzResearch.WordTrace]
  refine ⟨50147962800852675454777129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66863950401136900606369505 50147962800852675454777129)
  ·
    refine ⟨37610972100639506591082847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50147962800852675454777129 37610972100639506591082847)
    ·
      refine ⟨56416458150959259886624271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37610972100639506591082847 56416458150959259886624271)
      ·
        refine ⟨84624687226438889829936407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56416458150959259886624271 84624687226438889829936407)
        ·
          refine ⟨126937030839658334744904611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84624687226438889829936407 126937030839658334744904611)
          ·
            refine ⟨190405546259487502117356917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126937030839658334744904611 190405546259487502117356917)
            ·
              refine ⟨17850519961826953323502211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 190405546259487502117356917 17850519961826953323502211)
              ·
                refine ⟨26775779942740429985253317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17850519961826953323502211 26775779942740429985253317)
                ·
                  refine ⟨5020458739263830622234997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26775779942740429985253317 5020458739263830622234997)
                  ·
                    refine ⟨470668006805984120834531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5020458739263830622234997 470668006805984120834531)
                    ·
                      rfl

theorem cell23_2749868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_2749868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749868 prefixEnd_2749868 := by exact prefixLift 2749868
  have htrace : WordTrace (prefixWord ++ tailWord_2749868) baseStart_2749868 baseEnd_2749868 := by
    simpa [prefixWord, tailWord_2749868, baseEnd_2749868] using wordTrace_append hprefix tailTrace_2749868
  have hstable : (prefixWord ++ tailWord_2749868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749868).length < 2 ^ (prefixWord ++ tailWord_2749868).sum := by decide
  have hdescent : baseEnd_2749868 < baseStart_2749868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749888 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 4]
def baseStart_2749888 : Nat := 118140960795 + 2749888 * 2 ^ 59
def prefixEnd_2749888 : Nat := 4983230072969 + 3 ^ 40 * 2749888 * 2
def baseEnd_2749888 : Nat := 1412014290031042284253501

theorem tailTrace_2749888 : CollatzResearch.WordTrace tailWord_2749888 prefixEnd_2749888 1412014290031042284253501 := by
  unfold tailWord_2749888
  simp only [CollatzResearch.WordTrace]
  refine ⟨50148327530816447162641159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66864436707755262883521545 50148327530816447162641159)
  ·
    refine ⟨75222491296224670743961739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50148327530816447162641159 75222491296224670743961739)
    ·
      refine ⟨112833736944337006115942609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75222491296224670743961739 112833736944337006115942609)
      ·
        refine ⟨84625302708252754586956957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112833736944337006115942609 84625302708252754586956957)
        ·
          refine ⟨31734488515594782970108859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84625302708252754586956957 31734488515594782970108859)
          ·
            refine ⟨47601732773392174455163289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31734488515594782970108859 47601732773392174455163289)
            ·
              refine ⟨35701299580044130841372467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47601732773392174455163289 35701299580044130841372467)
              ·
                refine ⟨53551949370066196262058701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35701299580044130841372467 53551949370066196262058701)
                ·
                  refine ⟨20081981013774823598272013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53551949370066196262058701 20081981013774823598272013)
                  ·
                    refine ⟨7530742880165558849352005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20081981013774823598272013 7530742880165558849352005)
                    ·
                      refine ⟨1412014290031042284253501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7530742880165558849352005 1412014290031042284253501)
                      ·
                        rfl

theorem cell23_2749888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_2749888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749888 prefixEnd_2749888 := by exact prefixLift 2749888
  have htrace : WordTrace (prefixWord ++ tailWord_2749888) baseStart_2749888 baseEnd_2749888 := by
    simpa [prefixWord, tailWord_2749888, baseEnd_2749888] using wordTrace_append hprefix tailTrace_2749888
  have hstable : (prefixWord ++ tailWord_2749888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749888).length < 2 ^ (prefixWord ++ tailWord_2749888).sum := by decide
  have hdescent : baseEnd_2749888 < baseStart_2749888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749905 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 6, 4, 2]
def baseStart_2749905 : Nat := 118140960795 + 2749905 * 2 ^ 59
def prefixEnd_2749905 : Nat := 4983230072969 + 3 ^ 40 * 2749905 * 2
def baseEnd_2749905 : Nat := 1412023019202168717740923

theorem tailTrace_2749905 : CollatzResearch.WordTrace tailWord_2749905 prefixEnd_2749905 1412023019202168717740923 := by
  unfold tailWord_2749905
  simp only [CollatzResearch.WordTrace]
  refine ⟨100297275102571306228651169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66864850068380870819100779 100297275102571306228651169)
  ·
    refine ⟨75222956326928479671488377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100297275102571306228651169 75222956326928479671488377)
    ·
      refine ⟨56417217245196359753616283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75222956326928479671488377 56417217245196359753616283)
      ·
        refine ⟨84625825867794539630424425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56417217245196359753616283 84625825867794539630424425)
        ·
          refine ⟨63469369400845904722818319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84625825867794539630424425 63469369400845904722818319)
          ·
            refine ⟨95204054101268857084227479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63469369400845904722818319 95204054101268857084227479)
            ·
              refine ⟨142806081151903285626341219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95204054101268857084227479 142806081151903285626341219)
              ·
                refine ⟨214209121727854928439511829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142806081151903285626341219 214209121727854928439511829)
                ·
                  refine ⟨10041052580993199770602117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 214209121727854928439511829 10041052580993199770602117)
                  ·
                    refine ⟨1882697358936224956987897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10041052580993199770602117 1882697358936224956987897)
                    ·
                      refine ⟨1412023019202168717740923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1882697358936224956987897 1412023019202168717740923)
                      ·
                        rfl

theorem cell23_2749905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 4, 2].length) (baseStart_2749905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749905 prefixEnd_2749905 := by exact prefixLift 2749905
  have htrace : WordTrace (prefixWord ++ tailWord_2749905) baseStart_2749905 baseEnd_2749905 := by
    simpa [prefixWord, tailWord_2749905, baseEnd_2749905] using wordTrace_append hprefix tailTrace_2749905
  have hstable : (prefixWord ++ tailWord_2749905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749905).length < 2 ^ (prefixWord ++ tailWord_2749905).sum := by decide
  have hdescent : baseEnd_2749905 < baseStart_2749905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749956 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 2, 1, 4]
def baseStart_2749956 : Nat := 118140960795 + 2749956 * 2 ^ 59
def prefixEnd_2749956 : Nat := 4983230072969 + 3 ^ 40 * 2749956 * 2
def baseEnd_2749956 : Nat := 1412049206715548018203189

theorem tailTrace_2749956 : CollatzResearch.WordTrace tailWord_2749956 prefixEnd_2749956 1412049206715548018203189 := by
  unfold tailWord_2749956
  simp only [CollatzResearch.WordTrace]
  refine ⟨50149567612693270969378861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66866090150257694625838481 50149567612693270969378861)
  ·
    refine ⟨18806087854759976613517073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50149567612693270969378861 18806087854759976613517073)
    ·
      refine ⟨14104565891069982460137805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18806087854759976613517073 14104565891069982460137805)
      ·
        refine ⟨5289212209151243422551677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14104565891069982460137805 5289212209151243422551677)
        ·
          refine ⟨1983454578431716283456879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5289212209151243422551677 1983454578431716283456879)
          ·
            refine ⟨2975181867647574425185319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1983454578431716283456879 2975181867647574425185319)
            ·
              refine ⟨4462772801471361637777979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2975181867647574425185319 4462772801471361637777979)
              ·
                refine ⟨6694159202207042456666969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4462772801471361637777979 6694159202207042456666969)
                ·
                  refine ⟨5020619401655281842500227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6694159202207042456666969 5020619401655281842500227)
                  ·
                    refine ⟨7530929102482922763750341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5020619401655281842500227 7530929102482922763750341)
                    ·
                      refine ⟨1412049206715548018203189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7530929102482922763750341 1412049206715548018203189)
                      ·
                        rfl

theorem cell23_2749956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_2749956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749956 prefixEnd_2749956 := by exact prefixLift 2749956
  have htrace : WordTrace (prefixWord ++ tailWord_2749956) baseStart_2749956 baseEnd_2749956 := by
    simpa [prefixWord, tailWord_2749956, baseEnd_2749956] using wordTrace_append hprefix tailTrace_2749956
  have hstable : (prefixWord ++ tailWord_2749956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749956).length < 2 ^ (prefixWord ++ tailWord_2749956).sum := by decide
  have hdescent : baseEnd_2749956 < baseStart_2749956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749959 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 2, 2, 3]
def baseStart_2749959 : Nat := 118140960795 + 2749959 * 2 ^ 59
def prefixEnd_2749959 : Nat := 4983230072969 + 3 ^ 40 * 2749959 * 2
def baseEnd_2749959 : Nat := 1412050747157511506465675

theorem tailTrace_2749959 : CollatzResearch.WordTrace tailWord_2749959 prefixEnd_2749959 1412050747157511506465675 := by
  unfold tailWord_2749959
  simp only [CollatzResearch.WordTrace]
  refine ⟨100299244644375673451116931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66866163096250448967411287 100299244644375673451116931)
  ·
    refine ⟨150448866966563510176675397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100299244644375673451116931 150448866966563510176675397)
    ·
      refine ⟨28209162556230658158126637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150448866966563510176675397 28209162556230658158126637)
      ·
        refine ⟨10578435958586496809297489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28209162556230658158126637 10578435958586496809297489)
        ·
          refine ⟨7933826968939872606973117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10578435958586496809297489 7933826968939872606973117)
          ·
            refine ⟨2975185113352452227614919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7933826968939872606973117 2975185113352452227614919)
            ·
              refine ⟨4462777670028678341422379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2975185113352452227614919 4462777670028678341422379)
              ·
                refine ⟨6694166505043017512133569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4462777670028678341422379 6694166505043017512133569)
                ·
                  refine ⟨5020624878782263134100177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6694166505043017512133569 5020624878782263134100177)
                  ·
                    refine ⟨3765468659086697350575133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5020624878782263134100177 3765468659086697350575133)
                    ·
                      refine ⟨1412050747157511506465675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3765468659086697350575133 1412050747157511506465675)
                      ·
                        rfl

theorem cell23_2749959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_2749959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749959 prefixEnd_2749959 := by exact prefixLift 2749959
  have htrace : WordTrace (prefixWord ++ tailWord_2749959) baseStart_2749959 baseEnd_2749959 := by
    simpa [prefixWord, tailWord_2749959, baseEnd_2749959] using wordTrace_append hprefix tailTrace_2749959
  have hstable : (prefixWord ++ tailWord_2749959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749959).length < 2 ^ (prefixWord ++ tailWord_2749959).sum := by decide
  have hdescent : baseEnd_2749959 < baseStart_2749959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749966 : List Nat := [4, 1, 1, 2, 4, 1, 2, 3, 1, 4]
def baseStart_2749966 : Nat := 118140960795 + 2749966 * 2 ^ 59
def prefixEnd_2749966 : Nat := 4983230072969 + 3 ^ 40 * 2749966 * 2
def baseEnd_2749966 : Nat := 470684780507364326359381

theorem tailTrace_2749966 : CollatzResearch.WordTrace tailWord_2749966 prefixEnd_2749966 470684780507364326359381 := by
  unfold tailWord_2749966
  simp only [CollatzResearch.WordTrace]
  refine ⟨12537437494418789205827719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66866333303566875764414501 12537437494418789205827719)
  ·
    refine ⟨18806156241628183808741579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12537437494418789205827719 18806156241628183808741579)
    ·
      refine ⟨28209234362442275713112369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18806156241628183808741579 28209234362442275713112369)
      ·
        refine ⟨21156925771831706784834277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28209234362442275713112369 21156925771831706784834277)
        ·
          refine ⟨3966923582218445022156427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21156925771831706784834277 3966923582218445022156427)
          ·
            refine ⟨5950385373327667533234641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3966923582218445022156427 5950385373327667533234641)
            ·
              refine ⟨4462789029995750649925981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5950385373327667533234641 4462789029995750649925981)
              ·
                refine ⟨1673545886248406493722243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4462789029995750649925981 1673545886248406493722243)
                ·
                  refine ⟨2510318829372609740583365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1673545886248406493722243 2510318829372609740583365)
                  ·
                    refine ⟨470684780507364326359381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2510318829372609740583365 470684780507364326359381)
                    ·
                      rfl

theorem cell23_2749966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_2749966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2749966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2749966 prefixEnd_2749966 := by exact prefixLift 2749966
  have htrace : WordTrace (prefixWord ++ tailWord_2749966) baseStart_2749966 baseEnd_2749966 := by
    simpa [prefixWord, tailWord_2749966, baseEnd_2749966] using wordTrace_append hprefix tailTrace_2749966
  have hstable : (prefixWord ++ tailWord_2749966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749966).length < 2 ^ (prefixWord ++ tailWord_2749966).sum := by decide
  have hdescent : baseEnd_2749966 < baseStart_2749966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750023 : List Nat := [1, 1, 4, 1, 5, 2, 1, 3, 1, 1, 3]
def baseStart_2750023 : Nat := 118140960795 + 2750023 * 2 ^ 59
def prefixEnd_2750023 : Nat := 4983230072969 + 3 ^ 40 * 2750023 * 2
def baseEnd_2750023 : Nat := 1412083609919399256065381

theorem tailTrace_2750023 : CollatzResearch.WordTrace tailWord_2750023 prefixEnd_2750023 1412083609919399256065381 := by
  unfold tailWord_2750023
  simp only [CollatzResearch.WordTrace]
  refine ⟨100301578916143812381446723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66867719277429208254297815 100301578916143812381446723)
  ·
    refine ⟨150452368374215718572170085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100301578916143812381446723 150452368374215718572170085)
    ·
      refine ⟨28209819070165447232281891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150452368374215718572170085 28209819070165447232281891)
      ·
        refine ⟨42314728605248170848422837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28209819070165447232281891 42314728605248170848422837)
        ·
          refine ⟨3967005806742016017039641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42314728605248170848422837 3967005806742016017039641)
          ·
            refine ⟨2975254355056512012779731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3967005806742016017039641 2975254355056512012779731)
            ·
              refine ⟨4462881532584768019169597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2975254355056512012779731 4462881532584768019169597)
              ·
                refine ⟨1673580574719288007188599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4462881532584768019169597 1673580574719288007188599)
                ·
                  refine ⟨2510370862078932010782899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1673580574719288007188599 2510370862078932010782899)
                  ·
                    refine ⟨3765556293118398016174349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2510370862078932010782899 3765556293118398016174349)
                    ·
                      refine ⟨1412083609919399256065381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3765556293118398016174349 1412083609919399256065381)
                      ·
                        rfl

theorem cell23_2750023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_2750023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750023 prefixEnd_2750023 := by exact prefixLift 2750023
  have htrace : WordTrace (prefixWord ++ tailWord_2750023) baseStart_2750023 baseEnd_2750023 := by
    simpa [prefixWord, tailWord_2750023, baseEnd_2750023] using wordTrace_append hprefix tailTrace_2750023
  have hstable : (prefixWord ++ tailWord_2750023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750023).length < 2 ^ (prefixWord ++ tailWord_2750023).sum := by decide
  have hdescent : baseEnd_2750023 < baseStart_2750023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750025 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 1, 2, 4]
def baseStart_2750025 : Nat := 118140960795 + 2750025 * 2 ^ 59
def prefixEnd_2750025 : Nat := 4983230072969 + 3 ^ 40 * 2750025 * 2
def baseEnd_2750025 : Nat := 1412084636880708248240371

theorem tailTrace_2750025 : CollatzResearch.WordTrace tailWord_2750025 prefixEnd_2750025 1412084636880708248240371 := by
  unfold tailWord_2750025
  simp only [CollatzResearch.WordTrace]
  refine ⟨100301651862136566723019529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66867767908091044482013019 100301651862136566723019529)
  ·
    refine ⟨75226238896602425042264647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100301651862136566723019529 75226238896602425042264647)
    ·
      refine ⟨112839358344903637563396971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75226238896602425042264647 112839358344903637563396971)
      ·
        refine ⟨169259037517355456345095457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112839358344903637563396971 169259037517355456345095457)
        ·
          refine ⟨126944278138016592258821593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169259037517355456345095457 126944278138016592258821593)
          ·
            refine ⟨95208208603512444194116195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126944278138016592258821593 95208208603512444194116195)
            ·
              refine ⟨142812312905268666291174293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95208208603512444194116195 142812312905268666291174293)
              ·
                refine ⟨6694327167434468732398795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142812312905268666291174293 6694327167434468732398795)
                ·
                  refine ⟨10041490751151703098598193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6694327167434468732398795 10041490751151703098598193)
                  ·
                    refine ⟨7531118063363777323948645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10041490751151703098598193 7531118063363777323948645)
                    ·
                      refine ⟨1412084636880708248240371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7531118063363777323948645 1412084636880708248240371)
                      ·
                        rfl

theorem cell23_2750025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 2, 4].length) (baseStart_2750025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750025 prefixEnd_2750025 := by exact prefixLift 2750025
  have htrace : WordTrace (prefixWord ++ tailWord_2750025) baseStart_2750025 baseEnd_2750025 := by
    simpa [prefixWord, tailWord_2750025, baseEnd_2750025] using wordTrace_append hprefix tailTrace_2750025
  have hstable : (prefixWord ++ tailWord_2750025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750025).length < 2 ^ (prefixWord ++ tailWord_2750025).sum := by decide
  have hdescent : baseEnd_2750025 < baseStart_2750025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750032 : List Nat := [2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 3]
def baseStart_2750032 : Nat := 118140960795 + 2750032 * 2 ^ 59
def prefixEnd_2750032 : Nat := 4983230072969 + 3 ^ 40 * 2750032 * 2
def baseEnd_2750032 : Nat := 1412088231245289720852839

theorem tailTrace_2750032 : CollatzResearch.WordTrace tailWord_2750032 prefixEnd_2750032 1412088231245289720852839 := by
  unfold tailWord_2750032
  simp only [CollatzResearch.WordTrace]
  refine ⟨50150953586555603459262175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66867938115407471279016233 50150953586555603459262175)
  ·
    refine ⟨75226430379833405188893263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50150953586555603459262175 75226430379833405188893263)
    ·
      refine ⟨112839645569750107783339895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75226430379833405188893263 112839645569750107783339895)
      ·
        refine ⟨169259468354625161675009843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112839645569750107783339895 169259468354625161675009843)
        ·
          refine ⟨253889202531937742512514765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169259468354625161675009843 253889202531937742512514765)
          ·
            refine ⟨95208450949476653442193037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253889202531937742512514765 95208450949476653442193037)
            ·
              refine ⟨35703169106053745040822389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95208450949476653442193037 35703169106053745040822389)
              ·
                refine ⟨3347172103692538597577099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35703169106053745040822389 3347172103692538597577099)
                ·
                  refine ⟨5020758155538807896365649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3347172103692538597577099 5020758155538807896365649)
                  ·
                    refine ⟨3765568616654105922274237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5020758155538807896365649 3765568616654105922274237)
                    ·
                      refine ⟨1412088231245289720852839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3765568616654105922274237 1412088231245289720852839)
                      ·
                        rfl

theorem cell23_2750032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 3].length) (baseStart_2750032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750032 prefixEnd_2750032 := by exact prefixLift 2750032
  have htrace : WordTrace (prefixWord ++ tailWord_2750032) baseStart_2750032 baseEnd_2750032 := by
    simpa [prefixWord, tailWord_2750032, baseEnd_2750032] using wordTrace_append hprefix tailTrace_2750032
  have hstable : (prefixWord ++ tailWord_2750032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750032).length < 2 ^ (prefixWord ++ tailWord_2750032).sum := by decide
  have hdescent : baseEnd_2750032 < baseStart_2750032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750056 : List Nat := [2, 1, 4, 3, 1, 1, 4, 1, 2, 4]
def baseStart_2750056 : Nat := 118140960795 + 2750056 * 2 ^ 59
def prefixEnd_2750056 : Nat := 4983230072969 + 3 ^ 40 * 2750056 * 2
def baseEnd_2750056 : Nat := 470700184926999208984243

theorem tailTrace_2750056 : CollatzResearch.WordTrace tailWord_2750056 prefixEnd_2750056 470700184926999208984243 := by
  unfold tailWord_2750056
  simp only [CollatzResearch.WordTrace]
  refine ⟨50151391262512129508699011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66868521683349506011598681 50151391262512129508699011)
  ·
    refine ⟨75227086893768194263048517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50151391262512129508699011 75227086893768194263048517)
    ·
      refine ⟨14105078792581536424321597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75227086893768194263048517 14105078792581536424321597)
      ·
        refine ⟨5289404547218076159120599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14105078792581536424321597 5289404547218076159120599)
        ·
          refine ⟨7934106820827114238680899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5289404547218076159120599 7934106820827114238680899)
          ·
            refine ⟨11901160231240671358021349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7934106820827114238680899 11901160231240671358021349)
            ·
              refine ⟨2231467543357625879629003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11901160231240671358021349 2231467543357625879629003)
              ·
                refine ⟨3347201315036438819443505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2231467543357625879629003 3347201315036438819443505)
                ·
                  refine ⟨2510400986277329114582629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3347201315036438819443505 2510400986277329114582629)
                  ·
                    refine ⟨470700184926999208984243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2510400986277329114582629 470700184926999208984243)
                    ·
                      rfl

theorem cell23_2750056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_2750056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750056 prefixEnd_2750056 := by exact prefixLift 2750056
  have htrace : WordTrace (prefixWord ++ tailWord_2750056) baseStart_2750056 baseEnd_2750056 := by
    simpa [prefixWord, tailWord_2750056, baseEnd_2750056] using wordTrace_append hprefix tailTrace_2750056
  have hstable : (prefixWord ++ tailWord_2750056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750056).length < 2 ^ (prefixWord ++ tailWord_2750056).sum := by decide
  have hdescent : baseEnd_2750056 < baseStart_2750056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750066 : List Nat := [3, 2, 1, 2, 3, 3, 1, 2, 1, 2, 3]
def baseStart_2750066 : Nat := 118140960795 + 2750066 * 2 ^ 59
def prefixEnd_2750066 : Nat := 4983230072969 + 3 ^ 40 * 2750066 * 2
def baseEnd_2750066 : Nat := 1412105689587542587827683

theorem tailTrace_2750066 : CollatzResearch.WordTrace tailWord_2750066 prefixEnd_2750066 1412105689587542587827683 := by
  unfold tailWord_2750066
  simp only [CollatzResearch.WordTrace]
  refine ⟨25075786813747007681315513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66868764836658687150174701 25075786813747007681315513)
  ·
    refine ⟨18806840110310255760986635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25075786813747007681315513 18806840110310255760986635)
    ·
      refine ⟨28210260165465383641479953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18806840110310255760986635 28210260165465383641479953)
      ·
        refine ⟨21157695124099037731109965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28210260165465383641479953 21157695124099037731109965)
        ·
          refine ⟨7934135671537139149166237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21157695124099037731109965 7934135671537139149166237)
          ·
            refine ⟨2975300876826427180937339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7934135671537139149166237 2975300876826427180937339)
            ·
              refine ⟨4462951315239640771406009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2975300876826427180937339 4462951315239640771406009)
              ·
                refine ⟨3347213486429730578554507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4462951315239640771406009 3347213486429730578554507)
                ·
                  refine ⟨5020820229644595867831761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3347213486429730578554507 5020820229644595867831761)
                  ·
                    refine ⟨3765615172233446900873821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5020820229644595867831761 3765615172233446900873821)
                    ·
                      refine ⟨1412105689587542587827683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3765615172233446900873821 1412105689587542587827683)
                      ·
                        rfl

theorem cell23_2750066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_2750066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750066 prefixEnd_2750066 := by exact prefixLift 2750066
  have htrace : WordTrace (prefixWord ++ tailWord_2750066) baseStart_2750066 baseEnd_2750066 := by
    simpa [prefixWord, tailWord_2750066, baseEnd_2750066] using wordTrace_append hprefix tailTrace_2750066
  have hstable : (prefixWord ++ tailWord_2750066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750066).length < 2 ^ (prefixWord ++ tailWord_2750066).sum := by decide
  have hdescent : baseEnd_2750066 < baseStart_2750066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750089 : List Nat := [1, 2, 1, 1, 4, 1, 2, 5, 1, 3, 2]
def baseStart_2750089 : Nat := 118140960795 + 2750089 * 2 ^ 59
def prefixEnd_2750089 : Nat := 4983230072969 + 3 ^ 40 * 2750089 * 2
def baseEnd_2750089 : Nat := 1412117499642595997840077

theorem tailTrace_2750089 : CollatzResearch.WordTrace tailWord_2750089 prefixEnd_2750089 1412117499642595997840077 := by
  unfold tailWord_2750089
  simp only [CollatzResearch.WordTrace]
  refine ⟨100303986133904705653349321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66869324089269803768899547 100303986133904705653349321)
  ·
    refine ⟨75227989600428529240011991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100303986133904705653349321 75227989600428529240011991)
    ·
      refine ⟨112841984400642793860017987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75227989600428529240011991 112841984400642793860017987)
      ·
        refine ⟨169262976600964190790026981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112841984400642793860017987 169262976600964190790026981)
        ·
          refine ⟨31736808112680785773130059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169262976600964190790026981 31736808112680785773130059)
          ·
            refine ⟨47605212169021178659695089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31736808112680785773130059 47605212169021178659695089)
            ·
              refine ⟨35703909126765883994771317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47605212169021178659695089 35703909126765883994771317)
              ·
                refine ⟨3347241480634301624509811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35703909126765883994771317 3347241480634301624509811)
                ·
                  refine ⟨5020862220951452436764717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3347241480634301624509811 5020862220951452436764717)
                  ·
                    refine ⟨1882823332856794663786769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5020862220951452436764717 1882823332856794663786769)
                    ·
                      refine ⟨1412117499642595997840077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1882823332856794663786769 1412117499642595997840077)
                      ·
                        rfl

theorem cell23_2750089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 3, 2].length) (baseStart_2750089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750089 prefixEnd_2750089 := by exact prefixLift 2750089
  have htrace : WordTrace (prefixWord ++ tailWord_2750089) baseStart_2750089 baseEnd_2750089 := by
    simpa [prefixWord, tailWord_2750089, baseEnd_2750089] using wordTrace_append hprefix tailTrace_2750089
  have hstable : (prefixWord ++ tailWord_2750089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750089).length < 2 ^ (prefixWord ++ tailWord_2750089).sum := by decide
  have hdescent : baseEnd_2750089 < baseStart_2750089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750105 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 4, 1, 5]
def baseStart_2750105 : Nat := 118140960795 + 2750105 * 2 ^ 59
def prefixEnd_2750105 : Nat := 4983230072969 + 3 ^ 40 * 2750105 * 2
def baseEnd_2750105 : Nat := 1412125715333067935240003

theorem tailTrace_2750105 : CollatzResearch.WordTrace tailWord_2750105 prefixEnd_2750105 1412125715333067935240003 := by
  unfold tailWord_2750105
  simp only [CollatzResearch.WordTrace]
  refine ⟨100304569701846740385931769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66869713134564493590621179 100304569701846740385931769)
  ·
    refine ⟨75228427276385055289448827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100304569701846740385931769 75228427276385055289448827)
    ·
      refine ⟨112842640914577582934173241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75228427276385055289448827 112842640914577582934173241)
      ·
        refine ⟨84631980685933187200629931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112842640914577582934173241 84631980685933187200629931)
        ·
          refine ⟨126947971028899780800944897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84631980685933187200629931 126947971028899780800944897)
          ·
            refine ⟨95210978271674835600708673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126947971028899780800944897 95210978271674835600708673)
            ·
              refine ⟨71408233703756126700531505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95210978271674835600708673 71408233703756126700531505)
              ·
                refine ⟨53556175277817095025398629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71408233703756126700531505 53556175277817095025398629)
                ·
                  refine ⟨10041782864590705317262243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53556175277817095025398629 10041782864590705317262243)
                  ·
                    refine ⟨15062674296886057975893365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10041782864590705317262243 15062674296886057975893365)
                    ·
                      refine ⟨1412125715333067935240003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15062674296886057975893365 1412125715333067935240003)
                      ·
                        rfl

theorem cell23_2750105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_2750105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750105 prefixEnd_2750105 := by exact prefixLift 2750105
  have htrace : WordTrace (prefixWord ++ tailWord_2750105) baseStart_2750105 baseEnd_2750105 := by
    simpa [prefixWord, tailWord_2750105, baseEnd_2750105] using wordTrace_append hprefix tailTrace_2750105
  have hstable : (prefixWord ++ tailWord_2750105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750105).length < 2 ^ (prefixWord ++ tailWord_2750105).sum := by decide
  have hdescent : baseEnd_2750105 < baseStart_2750105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750112 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 2, 6]
def baseStart_2750112 : Nat := 118140960795 + 2750112 * 2 ^ 59
def prefixEnd_2750112 : Nat := 4983230072969 + 3 ^ 40 * 2750112 * 2
def baseEnd_2750112 : Nat := 470709769899216469284157

theorem tailTrace_2750112 : CollatzResearch.WordTrace tailWord_2750112 prefixEnd_2750112 470709769899216469284157 := by
  unfold tailWord_2750112
  simp only [CollatzResearch.WordTrace]
  refine ⟨50152412506410690290718295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66869883341880920387624393 50152412506410690290718295)
  ·
    refine ⟨75228618759616035436077443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50152412506410690290718295 75228618759616035436077443)
    ·
      refine ⟨112842928139424053154116165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75228618759616035436077443 112842928139424053154116165)
      ·
        refine ⟨21158049026142009966396781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112842928139424053154116165 21158049026142009966396781)
        ·
          refine ⟨7934268384803253737398793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21158049026142009966396781 7934268384803253737398793)
          ·
            refine ⟨5950701288602440303049095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7934268384803253737398793 5950701288602440303049095)
            ·
              refine ⟨8926051932903660454573643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5950701288602440303049095 8926051932903660454573643)
              ·
                refine ⟨13389077899355490681860465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8926051932903660454573643 13389077899355490681860465)
                ·
                  refine ⟨10041808424516618011395349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13389077899355490681860465 10041808424516618011395349)
                  ·
                    refine ⟨470709769899216469284157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10041808424516618011395349 470709769899216469284157)
                    ·
                      rfl

theorem cell23_2750112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 2, 6].length) (baseStart_2750112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750112 prefixEnd_2750112 := by exact prefixLift 2750112
  have htrace : WordTrace (prefixWord ++ tailWord_2750112) baseStart_2750112 baseEnd_2750112 := by
    simpa [prefixWord, tailWord_2750112, baseEnd_2750112] using wordTrace_append hprefix tailTrace_2750112
  have hstable : (prefixWord ++ tailWord_2750112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750112).length < 2 ^ (prefixWord ++ tailWord_2750112).sum := by decide
  have hdescent : baseEnd_2750112 < baseStart_2750112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750152 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 4, 3, 3]
def baseStart_2750152 : Nat := 118140960795 + 2750152 * 2 ^ 59
def prefixEnd_2750152 : Nat := 4983230072969 + 3 ^ 40 * 2750152 * 2
def baseEnd_2750152 : Nat := 1412149848923829251352287

theorem tailTrace_2750152 : CollatzResearch.WordTrace tailWord_2750152 prefixEnd_2750152 1412149848923829251352287 := by
  unfold tailWord_2750152
  simp only [CollatzResearch.WordTrace]
  refine ⟨50153141966338233706446355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66870855955117644941928473 50153141966338233706446355)
  ·
    refine ⟨75229712949507350559669533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50153141966338233706446355 75229712949507350559669533)
    ·
      refine ⟨28211142356065256459876075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75229712949507350559669533 28211142356065256459876075)
      ·
        refine ⟨42316713534097884689814113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28211142356065256459876075 42316713534097884689814113)
        ·
          refine ⟨31737535150573413517360585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42316713534097884689814113 31737535150573413517360585)
          ·
            refine ⟨23803151362930060138020439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31737535150573413517360585 23803151362930060138020439)
            ·
              refine ⟨35704727044395090207030659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23803151362930060138020439 35704727044395090207030659)
              ·
                refine ⟨53557090566592635310545989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35704727044395090207030659 53557090566592635310545989)
                ·
                  refine ⟨10041954481236119120727373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53557090566592635310545989 10041954481236119120727373)
                  ·
                    refine ⟨3765732930463544670272765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10041954481236119120727373 3765732930463544670272765)
                    ·
                      refine ⟨1412149848923829251352287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3765732930463544670272765 1412149848923829251352287)
                      ·
                        rfl

theorem cell23_2750152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_2750152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750152 prefixEnd_2750152 := by exact prefixLift 2750152
  have htrace : WordTrace (prefixWord ++ tailWord_2750152) baseStart_2750152 baseEnd_2750152 := by
    simpa [prefixWord, tailWord_2750152, baseEnd_2750152] using wordTrace_append hprefix tailTrace_2750152
  have hstable : (prefixWord ++ tailWord_2750152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750152).length < 2 ^ (prefixWord ++ tailWord_2750152).sum := by decide
  have hdescent : baseEnd_2750152 < baseStart_2750152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750185 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 1, 10]
def baseStart_2750185 : Nat := 118140960795 + 2750185 * 2 ^ 59
def prefixEnd_2750185 : Nat := 4983230072969 + 3 ^ 40 * 2750185 * 2
def baseEnd_2750185 : Nat := 470722264595142540746545

theorem tailTrace_2750185 : CollatzResearch.WordTrace tailWord_2750185 prefixEnd_2750185 470722264595142540746545 := by
  unfold tailWord_2750185
  simp only [CollatzResearch.WordTrace]
  refine ⟨100307487541556914048844009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66871658361037942699229339 100307487541556914048844009)
  ·
    refine ⟨75230615656167685536633007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100307487541556914048844009 75230615656167685536633007)
    ·
      refine ⟨112845923484251528304949511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75230615656167685536633007 112845923484251528304949511)
      ·
        refine ⟨169268885226377292457424267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112845923484251528304949511 169268885226377292457424267)
        ·
          refine ⟨253903327839565938686136401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169268885226377292457424267 253903327839565938686136401)
          ·
            refine ⟨190427495879674454014602301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253903327839565938686136401 190427495879674454014602301)
            ·
              refine ⟨71410310954877920255475863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190427495879674454014602301 71410310954877920255475863)
              ·
                refine ⟨107115466432316880383213795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71410310954877920255475863 107115466432316880383213795)
                ·
                  refine ⟨160673199648475320574820693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107115466432316880383213795 160673199648475320574820693)
                  ·
                    refine ⟨470722264595142540746545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 160673199648475320574820693 470722264595142540746545)
                    ·
                      rfl

theorem cell23_2750185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 10].length) (baseStart_2750185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750185 prefixEnd_2750185 := by exact prefixLift 2750185
  have htrace : WordTrace (prefixWord ++ tailWord_2750185) baseStart_2750185 baseEnd_2750185 := by
    simpa [prefixWord, tailWord_2750185, baseEnd_2750185] using wordTrace_append hprefix tailTrace_2750185
  have hstable : (prefixWord ++ tailWord_2750185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750185).length < 2 ^ (prefixWord ++ tailWord_2750185).sum := by decide
  have hdescent : baseEnd_2750185 < baseStart_2750185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750206 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_2750206 : Nat := 118140960795 + 2750206 * 2 ^ 59
def prefixEnd_2750206 : Nat := 4983230072969 + 3 ^ 40 * 2750206 * 2
def baseEnd_2750206 : Nat := 470725858959724013359013

theorem tailTrace_2750206 : CollatzResearch.WordTrace tailWord_2750206 prefixEnd_2750206 470725858959724013359013 := by
  unfold tailWord_2750206
  simp only [CollatzResearch.WordTrace]
  refine ⟨12538531684310104329419809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66872168982987223090238981 12538531684310104329419809)
  ·
    refine ⟨9403898763232578247064857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12538531684310104329419809 9403898763232578247064857)
    ·
      refine ⟨7052924072424433685298643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9403898763232578247064857 7052924072424433685298643)
      ·
        refine ⟨10579386108636650527947965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7052924072424433685298643 10579386108636650527947965)
        ·
          refine ⟨3967269790738743947980487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10579386108636650527947965 3967269790738743947980487)
          ·
            refine ⟨5950904686108115921970731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3967269790738743947980487 5950904686108115921970731)
            ·
              refine ⟨8926357029162173882956097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5950904686108115921970731 8926357029162173882956097)
              ·
                refine ⟨6694767771871630412217073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8926357029162173882956097 6694767771871630412217073)
                ·
                  refine ⟨5021075828903722809162805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6694767771871630412217073 5021075828903722809162805)
                  ·
                    refine ⟨470725858959724013359013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5021075828903722809162805 470725858959724013359013)
                    ·
                      rfl

theorem cell23_2750206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_2750206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750206 prefixEnd_2750206 := by exact prefixLift 2750206
  have htrace : WordTrace (prefixWord ++ tailWord_2750206) baseStart_2750206 baseEnd_2750206 := by
    simpa [prefixWord, tailWord_2750206, baseEnd_2750206] using wordTrace_append hprefix tailTrace_2750206
  have hstable : (prefixWord ++ tailWord_2750206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750206).length < 2 ^ (prefixWord ++ tailWord_2750206).sum := by decide
  have hdescent : baseEnd_2750206 < baseStart_2750206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750209 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 4, 4, 2]
def baseStart_2750209 : Nat := 118140960795 + 2750209 * 2 ^ 59
def prefixEnd_2750209 : Nat := 4983230072969 + 3 ^ 40 * 2750209 * 2
def baseEnd_2750209 : Nat := 1412179117321135528339525

theorem tailTrace_2750209 : CollatzResearch.WordTrace tailWord_2750209 prefixEnd_2750209 1412179117321135528339525 := by
  unfold tailWord_2750209
  simp only [CollatzResearch.WordTrace]
  refine ⟨100308362893469966147717681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66872241928979977431811787 100308362893469966147717681)
  ·
    refine ⟨75231272170102474610788261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100308362893469966147717681 75231272170102474610788261)
    ·
      refine ⟨14105863531894213989522799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75231272170102474610788261 14105863531894213989522799)
      ·
        refine ⟨21158795297841320984284199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14105863531894213989522799 21158795297841320984284199)
        ·
          refine ⟨31738192946761981476426299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21158795297841320984284199 31738192946761981476426299)
          ·
            refine ⟨47607289420142972214639449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31738192946761981476426299 47607289420142972214639449)
            ·
              refine ⟨35705467065107229160979587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47607289420142972214639449 35705467065107229160979587)
              ·
                refine ⟨53558200597660843741469381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35705467065107229160979587 53558200597660843741469381)
                ·
                  refine ⟨10042162612061408201525509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53558200597660843741469381 10042162612061408201525509)
                  ·
                    refine ⟨1882905489761514037786033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10042162612061408201525509 1882905489761514037786033)
                    ·
                      refine ⟨1412179117321135528339525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1882905489761514037786033 1412179117321135528339525)
                      ·
                        rfl

theorem cell23_2750209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_2750209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750209 prefixEnd_2750209 := by exact prefixLift 2750209
  have htrace : WordTrace (prefixWord ++ tailWord_2750209) baseStart_2750209 baseEnd_2750209 := by
    simpa [prefixWord, tailWord_2750209, baseEnd_2750209] using wordTrace_append hprefix tailTrace_2750209
  have hstable : (prefixWord ++ tailWord_2750209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750209).length < 2 ^ (prefixWord ++ tailWord_2750209).sum := by decide
  have hdescent : baseEnd_2750209 < baseStart_2750209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750219 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 3, 4]
def baseStart_2750219 : Nat := 118140960795 + 2750219 * 2 ^ 59
def prefixEnd_2750219 : Nat := 4983230072969 + 3 ^ 40 * 2750219 * 2
def baseEnd_2750219 : Nat := 470728084042560163071493

theorem tailTrace_2750219 : CollatzResearch.WordTrace tailWord_2750219 prefixEnd_2750219 470728084042560163071493 := by
  unfold tailWord_2750219
  simp only [CollatzResearch.WordTrace]
  refine ⟨100308727623433737855581711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66872485082289158570387807 100308727623433737855581711)
  ·
    refine ⟨150463091435150606783372567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100308727623433737855581711 150463091435150606783372567)
    ·
      refine ⟨225694637152725910175058851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150463091435150606783372567 225694637152725910175058851)
      ·
        refine ⟨338541955729088865262588277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225694637152725910175058851 338541955729088865262588277)
        ·
          refine ⟨31738308349602081118367651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 338541955729088865262588277 31738308349602081118367651)
          ·
            refine ⟨47607462524403121677551477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31738308349602081118367651 47607462524403121677551477)
            ·
              refine ⟨4463199611662792657270451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47607462524403121677551477 4463199611662792657270451)
              ·
                refine ⟨6694799417494188985905677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4463199611662792657270451 6694799417494188985905677)
                ·
                  refine ⟨2510549781560320869714629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6694799417494188985905677 2510549781560320869714629)
                  ·
                    refine ⟨470728084042560163071493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2510549781560320869714629 470728084042560163071493)
                    ·
                      rfl

theorem cell23_2750219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 4].length) (baseStart_2750219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750219 prefixEnd_2750219 := by exact prefixLift 2750219
  have htrace : WordTrace (prefixWord ++ tailWord_2750219) baseStart_2750219 baseEnd_2750219 := by
    simpa [prefixWord, tailWord_2750219, baseEnd_2750219] using wordTrace_append hprefix tailTrace_2750219
  have hstable : (prefixWord ++ tailWord_2750219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750219).length < 2 ^ (prefixWord ++ tailWord_2750219).sum := by decide
  have hdescent : baseEnd_2750219 < baseStart_2750219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750222 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_2750222 : Nat := 118140960795 + 2750222 * 2 ^ 59
def prefixEnd_2750222 : Nat := 4983230072969 + 3 ^ 40 * 2750222 * 2
def baseEnd_2750222 : Nat := 1412185792569643977476965

theorem tailTrace_2750222 : CollatzResearch.WordTrace tailWord_2750222 prefixEnd_2750222 1412185792569643977476965 := by
  unfold tailWord_2750222
  simp only [CollatzResearch.WordTrace]
  refine ⟨12538604630302858670992615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66872558028281912911960613 12538604630302858670992615)
  ·
    refine ⟨18807906945454288006488923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12538604630302858670992615 18807906945454288006488923)
    ·
      refine ⟨28211860418181432009733385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18807906945454288006488923 28211860418181432009733385)
      ·
        refine ⟨21158895313636074007300039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28211860418181432009733385 21158895313636074007300039)
        ·
          refine ⟨31738342970454111010950059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21158895313636074007300039 31738342970454111010950059)
          ·
            refine ⟨47607514455681166516425089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31738342970454111010950059 47607514455681166516425089)
            ·
              refine ⟨35705635841760874887318817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47607514455681166516425089 35705635841760874887318817)
              ·
                refine ⟨26779226881320656165489113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35705635841760874887318817 26779226881320656165489113)
                ·
                  refine ⟨20084420160990492124116835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26779226881320656165489113 20084420160990492124116835)
                  ·
                    refine ⟨30126630241485738186175253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20084420160990492124116835 30126630241485738186175253)
                    ·
                      refine ⟨1412185792569643977476965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30126630241485738186175253 1412185792569643977476965)
                      ·
                        rfl

theorem cell23_2750222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_2750222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750222 prefixEnd_2750222 := by exact prefixLift 2750222
  have htrace : WordTrace (prefixWord ++ tailWord_2750222) baseStart_2750222 baseEnd_2750222 := by
    simpa [prefixWord, tailWord_2750222, baseEnd_2750222] using wordTrace_append hprefix tailTrace_2750222
  have hstable : (prefixWord ++ tailWord_2750222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750222).length < 2 ^ (prefixWord ++ tailWord_2750222).sum := by decide
  have hdescent : baseEnd_2750222 < baseStart_2750222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750270 : List Nat := [4, 2, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_2750270 : Nat := 118140960795 + 2750270 * 2 ^ 59
def prefixEnd_2750270 : Nat := 4983230072969 + 3 ^ 40 * 2750270 * 2
def baseEnd_2750270 : Nat := 470736813213686596558915

theorem tailTrace_2750270 : CollatzResearch.WordTrace tailWord_2750270 prefixEnd_2750270 470736813213686596558915 := by
  unfold tailWord_2750270
  simp only [CollatzResearch.WordTrace]
  refine ⟨12538823468281121695711033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66873725164165982377125509 12538823468281121695711033)
  ·
    refine ⟨9404117601210841271783275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12538823468281121695711033 9404117601210841271783275)
    ·
      refine ⟨14106176401816261907674913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9404117601210841271783275 14106176401816261907674913)
      ·
        refine ⟨10579632301362196430756185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14106176401816261907674913 10579632301362196430756185)
        ·
          refine ⟨7934724226021647323067139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10579632301362196430756185 7934724226021647323067139)
          ·
            refine ⟨11902086339032470984600709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7934724226021647323067139 11902086339032470984600709)
            ·
              refine ⟨2231641188568588309612633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11902086339032470984600709 2231641188568588309612633)
              ·
                refine ⟨1673730891426441232209475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2231641188568588309612633 1673730891426441232209475)
                ·
                  refine ⟨2510596337139661848314213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1673730891426441232209475 2510596337139661848314213)
                  ·
                    refine ⟨470736813213686596558915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2510596337139661848314213 470736813213686596558915)
                    ·
                      rfl

theorem cell23_2750270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_2750270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750270 prefixEnd_2750270 := by exact prefixLift 2750270
  have htrace : WordTrace (prefixWord ++ tailWord_2750270) baseStart_2750270 baseEnd_2750270 := by
    simpa [prefixWord, tailWord_2750270, baseEnd_2750270] using wordTrace_append hprefix tailTrace_2750270
  have hstable : (prefixWord ++ tailWord_2750270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750270).length < 2 ^ (prefixWord ++ tailWord_2750270).sum := by decide
  have hdescent : baseEnd_2750270 < baseStart_2750270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750303 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 2, 3, 2]
def baseStart_2750303 : Nat := 118140960795 + 2750303 * 2 ^ 59
def prefixEnd_2750303 : Nat := 4983230072969 + 3 ^ 40 * 2750303 * 2
def baseEnd_2750303 : Nat := 1412227384502658160564093

theorem tailTrace_2750303 : CollatzResearch.WordTrace tailWord_2750303 prefixEnd_2750303 1412227384502658160564093 := by
  unfold tailWord_2750303
  simp only [CollatzResearch.WordTrace]
  refine ⟨100311791355129420201639563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66874527570086280134426375 100311791355129420201639563)
  ·
    refine ⟨150467687032694130302459345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100311791355129420201639563 150467687032694130302459345)
    ·
      refine ⟨112850765274520597726844509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150467687032694130302459345 112850765274520597726844509)
      ·
        refine ⟨42319036977945224147566691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112850765274520597726844509 42319036977945224147566691)
        ·
          refine ⟨63478555466917836221350037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42319036977945224147566691 63478555466917836221350037)
          ·
            refine ⟨2975557287511773572875783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 63478555466917836221350037 2975557287511773572875783)
            ·
              refine ⟨4463335931267660359313675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2975557287511773572875783 4463335931267660359313675)
              ·
                refine ⟨6695003896901490538970513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4463335931267660359313675 6695003896901490538970513)
                ·
                  refine ⟨5021252922676117904227885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6695003896901490538970513 5021252922676117904227885)
                  ·
                    refine ⟨1882969846003544214085457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5021252922676117904227885 1882969846003544214085457)
                    ·
                      refine ⟨1412227384502658160564093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1882969846003544214085457 1412227384502658160564093)
                      ·
                        rfl

theorem cell23_2750303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_2750303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750303 prefixEnd_2750303 := by exact prefixLift 2750303
  have htrace : WordTrace (prefixWord ++ tailWord_2750303) baseStart_2750303 baseEnd_2750303 := by
    simpa [prefixWord, tailWord_2750303, baseEnd_2750303] using wordTrace_append hprefix tailTrace_2750303
  have hstable : (prefixWord ++ tailWord_2750303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750303).length < 2 ^ (prefixWord ++ tailWord_2750303).sum := by decide
  have hdescent : baseEnd_2750303 < baseStart_2750303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750309 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 4, 4]
def baseStart_2750309 : Nat := 118140960795 + 2750309 * 2 ^ 59
def prefixEnd_2750309 : Nat := 4983230072969 + 3 ^ 40 * 2750309 * 2
def baseEnd_2750309 : Nat := 470743488462195045696355

theorem tailTrace_2750309 : CollatzResearch.WordTrace tailWord_2750309 prefixEnd_2750309 470743488462195045696355 := by
  unfold tailWord_2750309
  simp only [CollatzResearch.WordTrace]
  refine ⟨100312010193107683226357981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66874673462071788817571987 100312010193107683226357981)
  ·
    refine ⟨37617003822415381209884243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100312010193107683226357981 37617003822415381209884243)
    ·
      refine ⟨56425505733623071814826365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37617003822415381209884243 56425505733623071814826365)
      ·
        refine ⟨21159564650108651930559887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56425505733623071814826365 21159564650108651930559887)
        ·
          refine ⟨31739346975162977895839831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21159564650108651930559887 31739346975162977895839831)
          ·
            refine ⟨47609020462744466843759747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31739346975162977895839831 47609020462744466843759747)
            ·
              refine ⟨71413530694116700265639621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47609020462744466843759747 71413530694116700265639621)
              ·
                refine ⟨13390037005146881299807429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71413530694116700265639621 13390037005146881299807429)
                ·
                  refine ⟨2510631938465040243713893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13390037005146881299807429 2510631938465040243713893)
                  ·
                    refine ⟨470743488462195045696355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2510631938465040243713893 470743488462195045696355)
                    ·
                      rfl

theorem cell23_2750309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_2750309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750309 prefixEnd_2750309 := by exact prefixLift 2750309
  have htrace : WordTrace (prefixWord ++ tailWord_2750309) baseStart_2750309 baseEnd_2750309 := by
    simpa [prefixWord, tailWord_2750309, baseEnd_2750309] using wordTrace_append hprefix tailTrace_2750309
  have hstable : (prefixWord ++ tailWord_2750309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750309).length < 2 ^ (prefixWord ++ tailWord_2750309).sum := by decide
  have hdescent : baseEnd_2750309 < baseStart_2750309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750316 : List Nat := [2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 4]
def baseStart_2750316 : Nat := 118140960795 + 2750316 * 2 ^ 59
def prefixEnd_2750316 : Nat := 4983230072969 + 3 ^ 40 * 2750316 * 2
def baseEnd_2750316 : Nat := 1412234059751166609701533

theorem tailTrace_2750316 : CollatzResearch.WordTrace tailWord_2750316 prefixEnd_2750316 1412234059751166609701533 := by
  unfold tailWord_2750316
  simp only [CollatzResearch.WordTrace]
  refine ⟨50156132752041161710931401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66874843669388215614575201 50156132752041161710931401)
  ·
    refine ⟨37617099564030871283198551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50156132752041161710931401 37617099564030871283198551)
    ·
      refine ⟨56425649346046306924797827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37617099564030871283198551 56425649346046306924797827)
      ·
        refine ⟨84638474019069460387196741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56425649346046306924797827 84638474019069460387196741)
        ·
          refine ⟨15869713878575523822599389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84638474019069460387196741 15869713878575523822599389)
          ·
            refine ⟨5951142704465821433474771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15869713878575523822599389 5951142704465821433474771)
            ·
              refine ⟨8926714056698732150212157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5951142704465821433474771 8926714056698732150212157)
              ·
                refine ⟨3347517771262024556329559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8926714056698732150212157 3347517771262024556329559)
                ·
                  refine ⟨5021276656893036834494339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3347517771262024556329559 5021276656893036834494339)
                  ·
                    refine ⟨7531914985339555251741509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5021276656893036834494339 7531914985339555251741509)
                    ·
                      refine ⟨1412234059751166609701533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7531914985339555251741509 1412234059751166609701533)
                      ·
                        rfl

theorem cell23_2750316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_2750316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750316 prefixEnd_2750316 := by exact prefixLift 2750316
  have htrace : WordTrace (prefixWord ++ tailWord_2750316) baseStart_2750316 baseEnd_2750316 := by
    simpa [prefixWord, tailWord_2750316, baseEnd_2750316] using wordTrace_append hprefix tailTrace_2750316
  have hstable : (prefixWord ++ tailWord_2750316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750316).length < 2 ^ (prefixWord ++ tailWord_2750316).sum := by decide
  have hdescent : baseEnd_2750316 < baseStart_2750316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750332 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_2750332 : Nat := 118140960795 + 2750332 * 2 ^ 59
def prefixEnd_2750332 : Nat := 4983230072969 + 3 ^ 40 * 2750332 * 2
def baseEnd_2750332 : Nat := 1412242275441638547101459

theorem tailTrace_2750332 : CollatzResearch.WordTrace tailWord_2750332 prefixEnd_2750332 1412242275441638547101459 := by
  unfold tailWord_2750332
  simp only [CollatzResearch.WordTrace]
  refine ⟨50156424536012179077222625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66875232714682905436296833 50156424536012179077222625)
  ·
    refine ⟨37617318402009134307916969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50156424536012179077222625 37617318402009134307916969)
    ·
      refine ⟨28212988801506850730937727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37617318402009134307916969 28212988801506850730937727)
      ·
        refine ⟨42319483202260276096406591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28212988801506850730937727 42319483202260276096406591)
        ·
          refine ⟨63479224803390414144609887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42319483202260276096406591 63479224803390414144609887)
          ·
            refine ⟨95218837205085621216914831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63479224803390414144609887 95218837205085621216914831)
            ·
              refine ⟨142828255807628431825372247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95218837205085621216914831 142828255807628431825372247)
              ·
                refine ⟨214242383711442647738058371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142828255807628431825372247 214242383711442647738058371)
                ·
                  refine ⟨321363575567163971607087557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214242383711442647738058371 321363575567163971607087557)
                  ·
                    refine ⟨60255670418843244676328917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 321363575567163971607087557 60255670418843244676328917)
                    ·
                      refine ⟨1412242275441638547101459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60255670418843244676328917 1412242275441638547101459)
                      ·
                        rfl

theorem cell23_2750332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_2750332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750332 prefixEnd_2750332 := by exact prefixLift 2750332
  have htrace : WordTrace (prefixWord ++ tailWord_2750332) baseStart_2750332 baseEnd_2750332 := by
    simpa [prefixWord, tailWord_2750332, baseEnd_2750332] using wordTrace_append hprefix tailTrace_2750332
  have hstable : (prefixWord ++ tailWord_2750332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750332).length < 2 ^ (prefixWord ++ tailWord_2750332).sum := by decide
  have hdescent : baseEnd_2750332 < baseStart_2750332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750343 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 1, 6]
def baseStart_2750343 : Nat := 118140960795 + 2750343 * 2 ^ 59
def prefixEnd_2750343 : Nat := 4983230072969 + 3 ^ 40 * 2750343 * 2
def baseEnd_2750343 : Nat := 470749307909612668021303

theorem tailTrace_2750343 : CollatzResearch.WordTrace tailWord_2750343 prefixEnd_2750343 470749307909612668021303 := by
  unfold tailWord_2750343
  simp only [CollatzResearch.WordTrace]
  refine ⟨100313250274984507033095683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66875500183323004688730455 100313250274984507033095683)
  ·
    refine ⟨150469875412476760549643525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100313250274984507033095683 150469875412476760549643525)
    ·
      refine ⟨28213101639839392603058161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150469875412476760549643525 28213101639839392603058161)
      ·
        refine ⟨21159826229879544452293621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28213101639839392603058161 21159826229879544452293621)
        ·
          refine ⟨1983733709051207292402527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21159826229879544452293621 1983733709051207292402527)
          ·
            refine ⟨2975600563576810938603791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1983733709051207292402527 2975600563576810938603791)
            ·
              refine ⟨4463400845365216407905687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2975600563576810938603791 4463400845365216407905687)
              ·
                refine ⟨6695101268047824611858531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4463400845365216407905687 6695101268047824611858531)
                ·
                  refine ⟨10042651902071736917787797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6695101268047824611858531 10042651902071736917787797)
                  ·
                    refine ⟨470749307909612668021303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10042651902071736917787797 470749307909612668021303)
                    ·
                      rfl

theorem cell23_2750343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_2750343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750343 prefixEnd_2750343 := by exact prefixLift 2750343
  have htrace : WordTrace (prefixWord ++ tailWord_2750343) baseStart_2750343 baseEnd_2750343 := by
    simpa [prefixWord, tailWord_2750343, baseEnd_2750343] using wordTrace_append hprefix tailTrace_2750343
  have hstable : (prefixWord ++ tailWord_2750343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750343).length < 2 ^ (prefixWord ++ tailWord_2750343).sum := by decide
  have hdescent : baseEnd_2750343 < baseStart_2750343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750346 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 1, 1, 6]
def baseStart_2750346 : Nat := 118140960795 + 2750346 * 2 ^ 59
def prefixEnd_2750346 : Nat := 4983230072969 + 3 ^ 40 * 2750346 * 2
def baseEnd_2750346 : Nat := 1412249464170801492326395

theorem tailTrace_2750346 : CollatzResearch.WordTrace tailWord_2750346 prefixEnd_2750346 1412249464170801492326395 := by
  unfold tailWord_2750346
  simp only [CollatzResearch.WordTrace]
  refine ⟨25078339923493409636363723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66875573129315759030303261 25078339923493409636363723)
  ·
    refine ⟨37617509885240114454545585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25078339923493409636363723 37617509885240114454545585)
    ·
      refine ⟨28213132413930085840909189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37617509885240114454545585 28213132413930085840909189)
      ·
        refine ⟨5289962327611891095170473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28213132413930085840909189 5289962327611891095170473)
        ·
          refine ⟨3967471745708918321377855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5289962327611891095170473 3967471745708918321377855)
          ·
            refine ⟨5951207618563377482066783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3967471745708918321377855 5951207618563377482066783)
            ·
              refine ⟨8926811427845066223100175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5951207618563377482066783 8926811427845066223100175)
              ·
                refine ⟨13390217141767599334650263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8926811427845066223100175 13390217141767599334650263)
                ·
                  refine ⟨20085325712651399001975395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13390217141767599334650263 20085325712651399001975395)
                  ·
                    refine ⟨30127988568977098502963093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20085325712651399001975395 30127988568977098502963093)
                    ·
                      refine ⟨1412249464170801492326395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30127988568977098502963093 1412249464170801492326395)
                      ·
                        rfl

theorem cell23_2750346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_2750346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750346 prefixEnd_2750346 := by exact prefixLift 2750346
  have htrace : WordTrace (prefixWord ++ tailWord_2750346) baseStart_2750346 baseEnd_2750346 := by
    simpa [prefixWord, tailWord_2750346, baseEnd_2750346] using wordTrace_append hprefix tailTrace_2750346
  have hstable : (prefixWord ++ tailWord_2750346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750346).length < 2 ^ (prefixWord ++ tailWord_2750346).sum := by decide
  have hdescent : baseEnd_2750346 < baseStart_2750346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750350 : List Nat := [4, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2750350 : Nat := 118140960795 + 2750350 * 2 ^ 59
def prefixEnd_2750350 : Nat := 4983230072969 + 3 ^ 40 * 2750350 * 2
def baseEnd_2750350 : Nat := 1412251518093419476676377

theorem tailTrace_2750350 : CollatzResearch.WordTrace tailWord_2750350 prefixEnd_2750350 1412251518093419476676377 := by
  unfold tailWord_2750350
  simp only [CollatzResearch.WordTrace]
  refine ⟨12539188198244893403575063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66875670390639431485733669 12539188198244893403575063)
  ·
    refine ⟨18808782297367340105362595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12539188198244893403575063 18808782297367340105362595)
    ·
      refine ⟨28213173446051010158043893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18808782297367340105362595 28213173446051010158043893)
      ·
        refine ⟨2644985010567282202316615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28213173446051010158043893 2644985010567282202316615)
        ·
          refine ⟨3967477515850923303474923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2644985010567282202316615 3967477515850923303474923)
          ·
            refine ⟨5951216273776384955212385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3967477515850923303474923 5951216273776384955212385)
            ·
              refine ⟨4463412205332288716409289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5951216273776384955212385 4463412205332288716409289)
              ·
                refine ⟨3347559153999216537306967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4463412205332288716409289 3347559153999216537306967)
                ·
                  refine ⟨5021338730998824805960451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3347559153999216537306967 5021338730998824805960451)
                  ·
                    refine ⟨7532008096498237208940677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5021338730998824805960451 7532008096498237208940677)
                    ·
                      refine ⟨1412251518093419476676377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7532008096498237208940677 1412251518093419476676377)
                      ·
                        rfl

theorem cell23_2750350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2750350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750350 prefixEnd_2750350 := by exact prefixLift 2750350
  have htrace : WordTrace (prefixWord ++ tailWord_2750350) baseStart_2750350 baseEnd_2750350 := by
    simpa [prefixWord, tailWord_2750350, baseEnd_2750350] using wordTrace_append hprefix tailTrace_2750350
  have hstable : (prefixWord ++ tailWord_2750350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750350).length < 2 ^ (prefixWord ++ tailWord_2750350).sum := by decide
  have hdescent : baseEnd_2750350 < baseStart_2750350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750352 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 4, 7]
def baseStart_2750352 : Nat := 118140960795 + 2750352 * 2 ^ 59
def prefixEnd_2750352 : Nat := 4983230072969 + 3 ^ 40 * 2750352 * 2
def baseEnd_2750352 : Nat := 470750848351576156283789

theorem tailTrace_2750352 : CollatzResearch.WordTrace tailWord_2750352 prefixEnd_2750352 470750848351576156283789 := by
  unfold tailWord_2750352
  simp only [CollatzResearch.WordTrace]
  refine ⟨50156789265975950785086655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66875719021301267713448873 50156789265975950785086655)
  ·
    refine ⟨75235183898963926177629983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50156789265975950785086655 75235183898963926177629983)
    ·
      refine ⟨112852775848445889266444975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75235183898963926177629983 112852775848445889266444975)
      ·
        refine ⟨169279163772668833899667463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112852775848445889266444975 169279163772668833899667463)
        ·
          refine ⟨253918745659003250849501195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169279163772668833899667463 253918745659003250849501195)
          ·
            refine ⟨380878118488504876274251793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253918745659003250849501195 380878118488504876274251793)
            ·
              refine ⟨285658588866378657205688845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380878118488504876274251793 285658588866378657205688845)
              ·
                refine ⟨107121970824891996452133317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285658588866378657205688845 107121970824891996452133317)
                ·
                  refine ⟨20085369529667249334774997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107121970824891996452133317 20085369529667249334774997)
                  ·
                    refine ⟨470750848351576156283789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20085369529667249334774997 470750848351576156283789)
                    ·
                      rfl

theorem cell23_2750352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4, 7].length) (baseStart_2750352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750352 prefixEnd_2750352 := by exact prefixLift 2750352
  have htrace : WordTrace (prefixWord ++ tailWord_2750352) baseStart_2750352 baseEnd_2750352 := by
    simpa [prefixWord, tailWord_2750352, baseEnd_2750352] using wordTrace_append hprefix tailTrace_2750352
  have hstable : (prefixWord ++ tailWord_2750352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750352).length < 2 ^ (prefixWord ++ tailWord_2750352).sum := by decide
  have hdescent : baseEnd_2750352 < baseStart_2750352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750356 : List Nat := [2, 4, 2, 1, 1, 2, 4, 7]
def baseStart_2750356 : Nat := 118140960795 + 2750356 * 2 ^ 59
def prefixEnd_2750356 : Nat := 4983230072969 + 3 ^ 40 * 2750356 * 2
def baseEnd_2750356 : Nat := 52305725888049868637087

theorem tailTrace_2750356 : CollatzResearch.WordTrace tailWord_2750356 prefixEnd_2750356 52305725888049868637087 := by
  unfold tailWord_2750356
  simp only [CollatzResearch.WordTrace]
  refine ⟨50156862211968705126659461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66875816282624940168879281 50156862211968705126659461)
  ·
    refine ⟨9404411664744132211248649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50156862211968705126659461 9404411664744132211248649)
    ·
      refine ⟨7053308748558099158436487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9404411664744132211248649 7053308748558099158436487)
      ·
        refine ⟨10579963122837148737654731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7053308748558099158436487 10579963122837148737654731)
        ·
          refine ⟨15869944684255723106482097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10579963122837148737654731 15869944684255723106482097)
          ·
            refine ⟨11902458513191792329861573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15869944684255723106482097 11902458513191792329861573)
            ·
              refine ⟨2231710971223461061849045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11902458513191792329861573 2231710971223461061849045)
              ·
                refine ⟨52305725888049868637087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2231710971223461061849045 52305725888049868637087)
                ·
                  rfl

theorem cell23_2750356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 7].length) (baseStart_2750356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750356 prefixEnd_2750356 := by exact prefixLift 2750356
  have htrace : WordTrace (prefixWord ++ tailWord_2750356) baseStart_2750356 baseEnd_2750356 := by
    simpa [prefixWord, tailWord_2750356, baseEnd_2750356] using wordTrace_append hprefix tailTrace_2750356
  have hstable : (prefixWord ++ tailWord_2750356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750356).length < 2 ^ (prefixWord ++ tailWord_2750356).sum := by decide
  have hdescent : baseEnd_2750356 < baseStart_2750356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750409 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 2, 4, 3]
def baseStart_2750409 : Nat := 118140960795 + 2750409 * 2 ^ 59
def prefixEnd_2750409 : Nat := 4983230072969 + 3 ^ 40 * 2750409 * 2
def baseEnd_2750409 : Nat := 1412281813452034745838605

theorem tailTrace_2750409 : CollatzResearch.WordTrace tailWord_2750409 prefixEnd_2750409 1412281813452034745838605 := by
  unfold tailWord_2750409
  simp only [CollatzResearch.WordTrace]
  refine ⟨100315657492745400304998281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66877104995163600203332187 100315657492745400304998281)
  ·
    refine ⟨75236743119559050228748711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100315657492745400304998281 75236743119559050228748711)
    ·
      refine ⟨112855114679338575343123067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75236743119559050228748711 112855114679338575343123067)
      ·
        refine ⟨169282672019007863014684601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112855114679338575343123067 169282672019007863014684601)
        ·
          refine ⟨126962004014255897261013451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169282672019007863014684601 126962004014255897261013451)
          ·
            refine ⟨190443006021383845891520177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126962004014255897261013451 190443006021383845891520177)
            ·
              refine ⟨142832254516037884418640133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190443006021383845891520177 142832254516037884418640133)
              ·
                refine ⟨26781047721757103328495025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142832254516037884418640133 26781047721757103328495025)
                ·
                  refine ⟨20085785791317827496371269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26781047721757103328495025 20085785791317827496371269)
                  ·
                    refine ⟨3766084835872092655569613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20085785791317827496371269 3766084835872092655569613)
                    ·
                      refine ⟨1412281813452034745838605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3766084835872092655569613 1412281813452034745838605)
                      ·
                        rfl

theorem cell23_2750409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 4, 3].length) (baseStart_2750409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750409 prefixEnd_2750409 := by exact prefixLift 2750409
  have htrace : WordTrace (prefixWord ++ tailWord_2750409) baseStart_2750409 baseEnd_2750409 := by
    simpa [prefixWord, tailWord_2750409, baseEnd_2750409] using wordTrace_append hprefix tailTrace_2750409
  have hstable : (prefixWord ++ tailWord_2750409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750409).length < 2 ^ (prefixWord ++ tailWord_2750409).sum := by decide
  have hdescent : baseEnd_2750409 < baseStart_2750409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750459 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 4, 5]
def baseStart_2750459 : Nat := 118140960795 + 2750459 * 2 ^ 59
def prefixEnd_2750459 : Nat := 4983230072969 + 3 ^ 40 * 2750459 * 2
def baseEnd_2750459 : Nat := 470769162494919850071125

theorem tailTrace_2750459 : CollatzResearch.WordTrace tailWord_2750459 prefixEnd_2750459 470769162494919850071125 := by
  unfold tailWord_2750459
  simp only [CollatzResearch.WordTrace]
  refine ⟨100317481142564258844318431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66878320761709505896212287 100317481142564258844318431)
  ·
    refine ⟨150476221713846388266477647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100317481142564258844318431 150476221713846388266477647)
    ·
      refine ⟨225714332570769582399716471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150476221713846388266477647 225714332570769582399716471)
      ·
        refine ⟨338571498856154373599574707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225714332570769582399716471 338571498856154373599574707)
        ·
          refine ⟨507857248284231560399362061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338571498856154373599574707 507857248284231560399362061)
          ·
            refine ⟨190446468106586835149760773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 507857248284231560399362061 190446468106586835149760773)
            ·
              refine ⟨35708712769985031590580145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190446468106586835149760773 35708712769985031590580145)
              ·
                refine ⟨26781534577488773692935109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35708712769985031590580145 26781534577488773692935109)
                ·
                  refine ⟨5021537733279145067425333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26781534577488773692935109 5021537733279145067425333)
                  ·
                    refine ⟨470769162494919850071125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5021537733279145067425333 470769162494919850071125)
                    ·
                      rfl

theorem cell23_2750459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 5].length) (baseStart_2750459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750459 prefixEnd_2750459 := by exact prefixLift 2750459
  have htrace : WordTrace (prefixWord ++ tailWord_2750459) baseStart_2750459 baseEnd_2750459 := by
    simpa [prefixWord, tailWord_2750459, baseEnd_2750459] using wordTrace_append hprefix tailTrace_2750459
  have hstable : (prefixWord ++ tailWord_2750459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750459).length < 2 ^ (prefixWord ++ tailWord_2750459).sum := by decide
  have hdescent : baseEnd_2750459 < baseStart_2750459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750513 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 2, 4, 2]
def baseStart_2750513 : Nat := 118140960795 + 2750513 * 2 ^ 59
def prefixEnd_2750513 : Nat := 4983230072969 + 3 ^ 40 * 2750513 * 2
def baseEnd_2750513 : Nat := 1412335215440102338938127

theorem tailTrace_2750513 : CollatzResearch.WordTrace tailWord_2750513 prefixEnd_2750513 1412335215440102338938127 := by
  unfold tailWord_2750513
  simp only [CollatzResearch.WordTrace]
  refine ⟨100319450684368626066784193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66879633789579084044522795 100319450684368626066784193)
  ·
    refine ⟨75239588013276469550088145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100319450684368626066784193 75239588013276469550088145)
    ·
      refine ⟨56429691009957352162566109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75239588013276469550088145 56429691009957352162566109)
      ·
        refine ⟨21161134128734007060962291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56429691009957352162566109 21161134128734007060962291)
        ·
          refine ⟨31741701193101010591443437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21161134128734007060962291 31741701193101010591443437)
          ·
            refine ⟨11903137947412878971791289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31741701193101010591443437 11903137947412878971791289)
            ·
              refine ⟨8927353460559659228843467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11903137947412878971791289 8927353460559659228843467)
              ·
                refine ⟨13391030190839488843265201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8927353460559659228843467 13391030190839488843265201)
                ·
                  refine ⟨10043272643129616632448901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13391030190839488843265201 10043272643129616632448901)
                  ·
                    refine ⟨1883113620586803118584169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10043272643129616632448901 1883113620586803118584169)
                    ·
                      refine ⟨1412335215440102338938127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1883113620586803118584169 1412335215440102338938127)
                      ·
                        rfl

theorem cell23_2750513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_2750513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750513 prefixEnd_2750513 := by exact prefixLift 2750513
  have htrace : WordTrace (prefixWord ++ tailWord_2750513) baseStart_2750513 baseEnd_2750513 := by
    simpa [prefixWord, tailWord_2750513, baseEnd_2750513] using wordTrace_append hprefix tailTrace_2750513
  have hstable : (prefixWord ++ tailWord_2750513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750513).length < 2 ^ (prefixWord ++ tailWord_2750513).sum := by decide
  have hdescent : baseEnd_2750513 < baseStart_2750513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750539 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 6]
def baseStart_2750539 : Nat := 118140960795 + 2750539 * 2 ^ 59
def prefixEnd_2750539 : Nat := 4983230072969 + 3 ^ 40 * 2750539 * 2
def baseEnd_2750539 : Nat := 1412348565937119237213007

theorem tailTrace_2750539 : CollatzResearch.WordTrace tailWord_2750539 prefixEnd_2750539 1412348565937119237213007 := by
  unfold tailWord_2750539
  simp only [CollatzResearch.WordTrace]
  refine ⟨100320398982274432507230671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66880265988182955004820447 100320398982274432507230671)
  ·
    refine ⟨150480598473411648760846007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100320398982274432507230671 150480598473411648760846007)
    ·
      refine ⟨225720897710117473141269011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150480598473411648760846007 225720897710117473141269011)
      ·
        refine ⟨338581346565176209711903517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225720897710117473141269011 338581346565176209711903517)
        ·
          refine ⟨126968004961941078641963819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 338581346565176209711903517 126968004961941078641963819)
          ·
            refine ⟨190452007442911617962945729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126968004961941078641963819 190452007442911617962945729)
            ·
              refine ⟨142839005582183713472209297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190452007442911617962945729 142839005582183713472209297)
              ·
                refine ⟨107129254186637785104156973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142839005582183713472209297 107129254186637785104156973)
                ·
                  refine ⟨40173470319989169414058865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107129254186637785104156973 40173470319989169414058865)
                  ·
                    refine ⟨30130102739991877060544149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40173470319989169414058865 30130102739991877060544149)
                    ·
                      refine ⟨1412348565937119237213007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30130102739991877060544149 1412348565937119237213007)
                      ·
                        rfl

theorem cell23_2750539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 6].length) (baseStart_2750539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750539 prefixEnd_2750539 := by exact prefixLift 2750539
  have htrace : WordTrace (prefixWord ++ tailWord_2750539) baseStart_2750539 baseEnd_2750539 := by
    simpa [prefixWord, tailWord_2750539, baseEnd_2750539] using wordTrace_append hprefix tailTrace_2750539
  have hstable : (prefixWord ++ tailWord_2750539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750539).length < 2 ^ (prefixWord ++ tailWord_2750539).sum := by decide
  have hdescent : baseEnd_2750539 < baseStart_2750539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750540 : List Nat := [2, 2, 1, 3, 1, 1, 5, 3, 1, 4]
def baseStart_2750540 : Nat := 118140960795 + 2750540 * 2 ^ 59
def prefixEnd_2750540 : Nat := 4983230072969 + 3 ^ 40 * 2750540 * 2
def baseEnd_2750540 : Nat := 470783026472591244433501

theorem tailTrace_2750540 : CollatzResearch.WordTrace tailWord_2750540 prefixEnd_2750540 470783026472591244433501 := by
  unfold tailWord_2750540
  simp only [CollatzResearch.WordTrace]
  refine ⟨50160217727635404839008537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66880290303513873118678049 50160217727635404839008537)
  ·
    refine ⟨37620163295726553629256403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50160217727635404839008537 37620163295726553629256403)
    ·
      refine ⟨56430244943589830443884605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37620163295726553629256403 56430244943589830443884605)
      ·
        refine ⟨21161341853846186416456727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56430244943589830443884605 21161341853846186416456727)
        ·
          refine ⟨31742012780769279624685091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21161341853846186416456727 31742012780769279624685091)
          ·
            refine ⟨47613019171153919437027637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31742012780769279624685091 47613019171153919437027637)
            ·
              refine ⟨4463720547295679947221341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47613019171153919437027637 4463720547295679947221341)
              ·
                refine ⟨1673895205235879980208003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4463720547295679947221341 1673895205235879980208003)
                ·
                  refine ⟨2510842807853819970312005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1673895205235879980208003 2510842807853819970312005)
                  ·
                    refine ⟨470783026472591244433501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2510842807853819970312005 470783026472591244433501)
                    ·
                      rfl

theorem cell23_2750540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 1, 4].length) (baseStart_2750540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750540 prefixEnd_2750540 := by exact prefixLift 2750540
  have htrace : WordTrace (prefixWord ++ tailWord_2750540) baseStart_2750540 baseEnd_2750540 := by
    simpa [prefixWord, tailWord_2750540, baseEnd_2750540] using wordTrace_append hprefix tailTrace_2750540
  have hstable : (prefixWord ++ tailWord_2750540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750540).length < 2 ^ (prefixWord ++ tailWord_2750540).sum := by decide
  have hdescent : baseEnd_2750540 < baseStart_2750540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750557 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2750557 : Nat := 118140960795 + 2750557 * 2 ^ 59
def prefixEnd_2750557 : Nat := 4983230072969 + 3 ^ 40 * 2750557 * 2
def baseEnd_2750557 : Nat := 470785936196300055595975

theorem tailTrace_2750557 : CollatzResearch.WordTrace tailWord_2750557 prefixEnd_2750557 470785936196300055595975 := by
  unfold tailWord_2750557
  simp only [CollatzResearch.WordTrace]
  refine ⟨100321055496209221581385925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66880703664139481054257283 100321055496209221581385925)
  ·
    refine ⟨18810197905539229046509861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100321055496209221581385925 18810197905539229046509861)
    ·
      refine ⟨3526912107288605446220599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18810197905539229046509861 3526912107288605446220599)
      ·
        refine ⟨5290368160932908169330899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3526912107288605446220599 5290368160932908169330899)
        ·
          refine ⟨7935552241399362253996349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5290368160932908169330899 7935552241399362253996349)
          ·
            refine ⟨2975832090524760845248631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7935552241399362253996349 2975832090524760845248631)
            ·
              refine ⟨4463748135787141267872947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2975832090524760845248631 4463748135787141267872947)
              ·
                refine ⟨6695622203680711901809421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4463748135787141267872947 6695622203680711901809421)
                ·
                  refine ⟨2510858326380266963178533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6695622203680711901809421 2510858326380266963178533)
                  ·
                    refine ⟨470785936196300055595975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2510858326380266963178533 470785936196300055595975)
                    ·
                      rfl

theorem cell23_2750557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2750557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2750557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2750557 prefixEnd_2750557 := by exact prefixLift 2750557
  have htrace : WordTrace (prefixWord ++ tailWord_2750557) baseStart_2750557 baseEnd_2750557 := by
    simpa [prefixWord, tailWord_2750557, baseEnd_2750557] using wordTrace_append hprefix tailTrace_2750557
  have hstable : (prefixWord ++ tailWord_2750557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750557).length < 2 ^ (prefixWord ++ tailWord_2750557).sum := by decide
  have hdescent : baseEnd_2750557 < baseStart_2750557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
