import V185TrunkScan23Chunk0037

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_225612 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 2, 8]
def baseStart_225612 : Nat := 118140960795 + 225612 * 2 ^ 59
def prefixEnd_225612 : Nat := 4983230072969 + 3 ^ 40 * 225612 * 2
def baseEnd_225612 : Nat := 38615799140758841904145

theorem tailTrace_225612 : CollatzResearch.WordTrace tailWord_225612 prefixEnd_225612 38615799140758841904145 := by
  unfold tailWord_225612
  simp only [CollatzResearch.WordTrace]
  refine ⟨4114372829326865153531545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5485830439102486871375393 4114372829326865153531545)
  ·
    refine ⟨3085779621995148865148659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4114372829326865153531545 3085779621995148865148659)
    ·
      refine ⟨4628669432992723297722989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3085779621995148865148659 4628669432992723297722989)
      ·
        refine ⟨1735751037372271236646121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4628669432992723297722989 1735751037372271236646121)
        ·
          refine ⟨1301813278029203427484591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1735751037372271236646121 1301813278029203427484591)
          ·
            refine ⟨1952719917043805141226887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301813278029203427484591 1952719917043805141226887)
            ·
              refine ⟨2929079875565707711840331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1952719917043805141226887 2929079875565707711840331)
              ·
                refine ⟨4393619813348561567760497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929079875565707711840331 4393619813348561567760497)
                ·
                  refine ⟨3295214860011421175820373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4393619813348561567760497 3295214860011421175820373)
                  ·
                    refine ⟨38615799140758841904145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3295214860011421175820373 38615799140758841904145)
                    ·
                      rfl

theorem cell23_225612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_225612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225612 prefixEnd_225612 := by exact prefixLift 225612
  have htrace : WordTrace (prefixWord ++ tailWord_225612) baseStart_225612 baseEnd_225612 := by
    simpa [prefixWord, tailWord_225612, baseEnd_225612] using wordTrace_append hprefix tailTrace_225612
  have hstable : (prefixWord ++ tailWord_225612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225612).length < 2 ^ (prefixWord ++ tailWord_225612).sum := by decide
  have hdescent : baseEnd_225612 < baseStart_225612 := by decide
  rcases family_descends (prefixWord ++ tailWord_225612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225619 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 4, 4, 2]
def baseStart_225619 : Nat := 118140960795 + 225619 * 2 ^ 59
def prefixEnd_225619 : Nat := 4983230072969 + 3 ^ 40 * 225619 * 2
def baseEnd_225619 : Nat := 115850991786857998324903

theorem tailTrace_225619 : CollatzResearch.WordTrace tailWord_225619 prefixEnd_225619 115850991786857998324903 := by
  unfold tailWord_225619
  simp only [CollatzResearch.WordTrace]
  refine ⟨8229000969628370502567911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5486000646418913668378607 8229000969628370502567911)
  ·
    refine ⟨12343501454442555753851867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8229000969628370502567911 12343501454442555753851867)
    ·
      refine ⟨18515252181663833630777801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12343501454442555753851867 18515252181663833630777801)
      ·
        refine ⟨13886439136247875223083351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18515252181663833630777801 13886439136247875223083351)
        ·
          refine ⟨20829658704371812834625027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13886439136247875223083351 20829658704371812834625027)
          ·
            refine ⟨31244488056557719251937541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20829658704371812834625027 31244488056557719251937541)
            ·
              refine ⟨5858341510604572359738289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31244488056557719251937541 5858341510604572359738289)
              ·
                refine ⟨4393756132953429269803717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5858341510604572359738289 4393756132953429269803717)
                ·
                  refine ⟨823829274928767988088197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4393756132953429269803717 823829274928767988088197)
                  ·
                    refine ⟨154467989049143997766537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 823829274928767988088197 154467989049143997766537)
                    ·
                      refine ⟨115850991786857998324903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 154467989049143997766537 115850991786857998324903)
                      ·
                        rfl

theorem cell23_225619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 4, 2].length) (baseStart_225619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225619 prefixEnd_225619 := by exact prefixLift 225619
  have htrace : WordTrace (prefixWord ++ tailWord_225619) baseStart_225619 baseEnd_225619 := by
    simpa [prefixWord, tailWord_225619, baseEnd_225619] using wordTrace_append hprefix tailTrace_225619
  have hstable : (prefixWord ++ tailWord_225619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225619).length < 2 ^ (prefixWord ++ tailWord_225619).sum := by decide
  have hdescent : baseEnd_225619 < baseStart_225619 := by decide
  rcases family_descends (prefixWord ++ tailWord_225619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225659 : List Nat := [1, 1, 1, 1, 1, 8, 1, 3, 6]
def baseStart_225659 : Nat := 118140960795 + 225659 * 2 ^ 59
def prefixEnd_225659 : Nat := 4983230072969 + 3 ^ 40 * 225659 * 2
def baseEnd_225659 : Nat := 12874614557004204647191

theorem tailTrace_225659 : CollatzResearch.WordTrace tailWord_225659 prefixEnd_225659 12874614557004204647191 := by
  unfold tailWord_225659
  simp only [CollatzResearch.WordTrace]
  refine ⟨8230459889483457334024031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5486973259655638222682687 8230459889483457334024031)
  ·
    refine ⟨12345689834225186001036047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8230459889483457334024031 12345689834225186001036047)
    ·
      refine ⟨18518534751337779001554071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12345689834225186001036047 18518534751337779001554071)
      ·
        refine ⟨27777802127006668502331107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18518534751337779001554071 27777802127006668502331107)
        ·
          refine ⟨41666703190510002753496661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27777802127006668502331107 41666703190510002753496661)
          ·
            refine ⟨488281678013789094767539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 41666703190510002753496661 488281678013789094767539)
            ·
              refine ⟨732422517020683642151309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488281678013789094767539 732422517020683642151309)
              ·
                refine ⟨274658443882756365806741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 732422517020683642151309 274658443882756365806741)
                ·
                  refine ⟨12874614557004204647191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 274658443882756365806741 12874614557004204647191)
                  ·
                    rfl

theorem cell23_225659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 6].length) (baseStart_225659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225659 prefixEnd_225659 := by exact prefixLift 225659
  have htrace : WordTrace (prefixWord ++ tailWord_225659) baseStart_225659 baseEnd_225659 := by
    simpa [prefixWord, tailWord_225659, baseEnd_225659] using wordTrace_append hprefix tailTrace_225659
  have hstable : (prefixWord ++ tailWord_225659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225659).length < 2 ^ (prefixWord ++ tailWord_225659).sum := by decide
  have hdescent : baseEnd_225659 < baseStart_225659 := by decide
  rcases family_descends (prefixWord ++ tailWord_225659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225719 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 1, 6]
def baseStart_225719 : Nat := 118140960795 + 225719 * 2 ^ 59
def prefixEnd_225719 : Nat := 4983230072969 + 3 ^ 40 * 225719 * 2
def baseEnd_225719 : Nat := 38634113284102535691481

theorem tailTrace_225719 : CollatzResearch.WordTrace tailWord_225719 prefixEnd_225719 38634113284102535691481 := by
  unfold tailWord_225719
  simp only [CollatzResearch.WordTrace]
  refine ⟨8232648269266087581208211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5488432179510725054138807 8232648269266087581208211)
  ·
    refine ⟨12348972403899131371812317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8232648269266087581208211 12348972403899131371812317)
    ·
      refine ⟨4630864651462174264429619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12348972403899131371812317 4630864651462174264429619)
      ·
        refine ⟨6946296977193261396644429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4630864651462174264429619 6946296977193261396644429)
        ·
          refine ⟨2604861366447473023741661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6946296977193261396644429 2604861366447473023741661)
          ·
            refine ⟨976823012417802383903123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2604861366447473023741661 976823012417802383903123)
            ·
              refine ⟨1465234518626703575854685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976823012417802383903123 1465234518626703575854685)
              ·
                refine ⟨549462944485013840945507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1465234518626703575854685 549462944485013840945507)
                ·
                  refine ⟨824194416727520761418261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549462944485013840945507 824194416727520761418261)
                  ·
                    refine ⟨38634113284102535691481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 824194416727520761418261 38634113284102535691481)
                    ·
                      rfl

theorem cell23_225719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_225719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225719 prefixEnd_225719 := by exact prefixLift 225719
  have htrace : WordTrace (prefixWord ++ tailWord_225719) baseStart_225719 baseEnd_225719 := by
    simpa [prefixWord, tailWord_225719, baseEnd_225719] using wordTrace_append hprefix tailTrace_225719
  have hstable : (prefixWord ++ tailWord_225719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225719).length < 2 ^ (prefixWord ++ tailWord_225719).sum := by decide
  have hdescent : baseEnd_225719 < baseStart_225719 := by decide
  rcases family_descends (prefixWord ++ tailWord_225719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225726 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_225726 : Nat := 118140960795 + 225726 * 2 ^ 59
def prefixEnd_225726 : Nat := 4983230072969 + 3 ^ 40 * 225726 * 2
def baseEnd_225726 : Nat := 115905934216889079686911

theorem tailTrace_225726 : CollatzResearch.WordTrace tailWord_225726 prefixEnd_225726 115905934216889079686911 := by
  unfold tailWord_225726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1029112947530090972089129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5488602386827151851142021 1029112947530090972089129)
  ·
    refine ⟨771834710647568229066847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1029112947530090972089129 771834710647568229066847)
    ·
      refine ⟨1157752065971352343600271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 771834710647568229066847 1157752065971352343600271)
      ·
        refine ⟨1736628098957028515400407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1157752065971352343600271 1736628098957028515400407)
        ·
          refine ⟨2604942148435542773100611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1736628098957028515400407 2604942148435542773100611)
          ·
            refine ⟨3907413222653314159650917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2604942148435542773100611 3907413222653314159650917)
            ·
              refine ⟨732639979247496404934547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3907413222653314159650917 732639979247496404934547)
              ·
                refine ⟨1098959968871244607401821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732639979247496404934547 1098959968871244607401821)
                ·
                  refine ⟨412109988326716727775683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1098959968871244607401821 412109988326716727775683)
                  ·
                    refine ⟨618164982490075091663525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 412109988326716727775683 618164982490075091663525)
                    ·
                      refine ⟨115905934216889079686911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 618164982490075091663525 115905934216889079686911)
                      ·
                        rfl

theorem cell23_225726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_225726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225726 prefixEnd_225726 := by exact prefixLift 225726
  have htrace : WordTrace (prefixWord ++ tailWord_225726) baseStart_225726 baseEnd_225726 := by
    simpa [prefixWord, tailWord_225726, baseEnd_225726] using wordTrace_append hprefix tailTrace_225726
  have hstable : (prefixWord ++ tailWord_225726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225726).length < 2 ^ (prefixWord ++ tailWord_225726).sum := by decide
  have hdescent : baseEnd_225726 < baseStart_225726 := by decide
  rcases family_descends (prefixWord ++ tailWord_225726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225740 : List Nat := [2, 2, 1, 4, 3, 2, 2, 1, 1, 5]
def baseStart_225740 : Nat := 118140960795 + 225740 * 2 ^ 59
def prefixEnd_225740 : Nat := 4983230072969 + 3 ^ 40 * 225740 * 2
def baseEnd_225740 : Nat := 38637707648684008303949

theorem tailTrace_225740 : CollatzResearch.WordTrace tailWord_225740 prefixEnd_225740 38637707648684008303949 := by
  unfold tailWord_225740
  simp only [CollatzResearch.WordTrace]
  refine ⟨4116707101095004083861337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5488942801460005445148449 4116707101095004083861337)
  ·
    refine ⟨3087530325821253062896003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4116707101095004083861337 3087530325821253062896003)
    ·
      refine ⟨4631295488731879594344005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3087530325821253062896003 4631295488731879594344005)
      ·
        refine ⟨868367904137227423939501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4631295488731879594344005 868367904137227423939501)
        ·
          refine ⟨325637964051460283977313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 868367904137227423939501 325637964051460283977313)
          ·
            refine ⟨244228473038595212982985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325637964051460283977313 244228473038595212982985)
            ·
              refine ⟨183171354778946409737239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244228473038595212982985 183171354778946409737239)
              ·
                refine ⟨274757032168419614605859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183171354778946409737239 274757032168419614605859)
                ·
                  refine ⟨412135548252629421908789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274757032168419614605859 412135548252629421908789)
                  ·
                    refine ⟨38637707648684008303949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 412135548252629421908789 38637707648684008303949)
                    ·
                      rfl

theorem cell23_225740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 1, 5].length) (baseStart_225740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225740 prefixEnd_225740 := by exact prefixLift 225740
  have htrace : WordTrace (prefixWord ++ tailWord_225740) baseStart_225740 baseEnd_225740 := by
    simpa [prefixWord, tailWord_225740, baseEnd_225740] using wordTrace_append hprefix tailTrace_225740
  have hstable : (prefixWord ++ tailWord_225740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225740).length < 2 ^ (prefixWord ++ tailWord_225740).sum := by decide
  have hdescent : baseEnd_225740 < baseStart_225740 := by decide
  rcases family_descends (prefixWord ++ tailWord_225740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225749 : List Nat := [1, 3, 2, 3, 1, 3, 10]
def baseStart_225749 : Nat := 118140960795 + 225749 * 2 ^ 59
def prefixEnd_225749 : Nat := 4983230072969 + 3 ^ 40 * 225749 * 2
def baseEnd_225749 : Nat := 1431083262616573946905

theorem tailTrace_225749 : CollatzResearch.WordTrace tailWord_225749 prefixEnd_225749 1431083262616573946905 := by
  unfold tailWord_225749
  simp only [CollatzResearch.WordTrace]
  refine ⟨8233742459157402704800301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5489161639438268469866867 8233742459157402704800301)
  ·
    refine ⟨3087653422184026014300113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8233742459157402704800301 3087653422184026014300113)
    ·
      refine ⟨2315740066638019510725085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3087653422184026014300113 2315740066638019510725085)
      ·
        refine ⟨868402524989257316521907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2315740066638019510725085 868402524989257316521907)
        ·
          refine ⟨1302603787483885974782861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868402524989257316521907 1302603787483885974782861)
          ·
            refine ⟨488476420306457240543573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1302603787483885974782861 488476420306457240543573)
            ·
              refine ⟨1431083262616573946905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 488476420306457240543573 1431083262616573946905)
              ·
                rfl

theorem cell23_225749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 10].length) (baseStart_225749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225749 prefixEnd_225749 := by exact prefixLift 225749
  have htrace : WordTrace (prefixWord ++ tailWord_225749) baseStart_225749 baseEnd_225749 := by
    simpa [prefixWord, tailWord_225749, baseEnd_225749] using wordTrace_append hprefix tailTrace_225749
  have hstable : (prefixWord ++ tailWord_225749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225749).length < 2 ^ (prefixWord ++ tailWord_225749).sum := by decide
  have hdescent : baseEnd_225749 < baseStart_225749 := by decide
  rcases family_descends (prefixWord ++ tailWord_225749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225760 : List Nat := [2, 1, 1, 3, 1, 1, 3, 6, 1, 2, 2]
def baseStart_225760 : Nat := 118140960795 + 225760 * 2 ^ 59
def prefixEnd_225760 : Nat := 4983230072969 + 3 ^ 40 * 225760 * 2
def baseEnd_225760 : Nat := 115923392559141946661755

theorem tailTrace_225760 : CollatzResearch.WordTrace tailWord_225760 prefixEnd_225760 115923392559141946661755 := by
  unfold tailWord_225760
  simp only [CollatzResearch.WordTrace]
  refine ⟨4117071831058775791725367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5489429108078367722300489 4117071831058775791725367)
  ·
    refine ⟨6175607746588163687588051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4117071831058775791725367 6175607746588163687588051)
    ·
      refine ⟨9263411619882245531382077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6175607746588163687588051 9263411619882245531382077)
      ·
        refine ⟨3473779357455842074268279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9263411619882245531382077 3473779357455842074268279)
        ·
          refine ⟨5210669036183763111402419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3473779357455842074268279 5210669036183763111402419)
          ·
            refine ⟨7816003554275644667103629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5210669036183763111402419 7816003554275644667103629)
            ·
              refine ⟨2931001332853366750163861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7816003554275644667103629 2931001332853366750163861)
              ·
                refine ⟨137390687477501566413931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2931001332853366750163861 137390687477501566413931)
                ·
                  refine ⟨206086031216252349620897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137390687477501566413931 206086031216252349620897)
                  ·
                    refine ⟨154564523412189262215673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 206086031216252349620897 154564523412189262215673)
                    ·
                      refine ⟨115923392559141946661755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 154564523412189262215673 115923392559141946661755)
                      ·
                        rfl

theorem cell23_225760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_225760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225760 prefixEnd_225760 := by exact prefixLift 225760
  have htrace : WordTrace (prefixWord ++ tailWord_225760) baseStart_225760 baseEnd_225760 := by
    simpa [prefixWord, tailWord_225760, baseEnd_225760] using wordTrace_append hprefix tailTrace_225760
  have hstable : (prefixWord ++ tailWord_225760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225760).length < 2 ^ (prefixWord ++ tailWord_225760).sum := by decide
  have hdescent : baseEnd_225760 < baseStart_225760 := by decide
  rcases family_descends (prefixWord ++ tailWord_225760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225770 : List Nat := [3, 1, 3, 1, 3, 2, 3, 1, 2, 4]
def baseStart_225770 : Nat := 118140960795 + 225770 * 2 ^ 59
def prefixEnd_225770 : Nat := 4983230072969 + 3 ^ 40 * 225770 * 2
def baseEnd_225770 : Nat := 38642842455228969178903

theorem tailTrace_225770 : CollatzResearch.WordTrace tailWord_225770 prefixEnd_225770 38642842455228969178903 := by
  unfold tailWord_225770
  simp only [CollatzResearch.WordTrace]
  refine ⟨2058627098020330822828691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5489672261387548860876509 2058627098020330822828691)
  ·
    refine ⟨3087940647030496234243037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2058627098020330822828691 3087940647030496234243037)
    ·
      refine ⟨1157977742636436087841139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3087940647030496234243037 1157977742636436087841139)
      ·
        refine ⟨1736966613954654131761709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1157977742636436087841139 1736966613954654131761709)
        ·
          refine ⟨651362480232995299410641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1736966613954654131761709 651362480232995299410641)
          ·
            refine ⟨488521860174746474557981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651362480232995299410641 488521860174746474557981)
            ·
              refine ⟨183195697565529927959243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 488521860174746474557981 183195697565529927959243)
              ·
                refine ⟨274793546348294891938865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183195697565529927959243 274793546348294891938865)
                ·
                  refine ⟨206095159761221168954149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274793546348294891938865 206095159761221168954149)
                  ·
                    refine ⟨38642842455228969178903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 206095159761221168954149 38642842455228969178903)
                    ·
                      rfl

theorem cell23_225770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_225770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225770 prefixEnd_225770 := by exact prefixLift 225770
  have htrace : WordTrace (prefixWord ++ tailWord_225770) baseStart_225770 baseEnd_225770 := by
    simpa [prefixWord, tailWord_225770, baseEnd_225770] using wordTrace_append hprefix tailTrace_225770
  have hstable : (prefixWord ++ tailWord_225770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225770).length < 2 ^ (prefixWord ++ tailWord_225770).sum := by decide
  have hdescent : baseEnd_225770 < baseStart_225770 := by decide
  rcases family_descends (prefixWord ++ tailWord_225770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225773 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_225773 : Nat := 118140960795 + 225773 * 2 ^ 59
def prefixEnd_225773 : Nat := 4983230072969 + 3 ^ 40 * 225773 * 2
def baseEnd_225773 : Nat := 115930067807650395799195

theorem tailTrace_225773 : CollatzResearch.WordTrace tailWord_225773 prefixEnd_225773 115930067807650395799195 := by
  unfold tailWord_225773
  simp only [CollatzResearch.WordTrace]
  refine ⟨8234617811070454803673973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5489745207380303202449315 8234617811070454803673973)
  ·
    refine ⟨771995419787855137844435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8234617811070454803673973 771995419787855137844435)
    ·
      refine ⟨1157993129681782706766653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 771995419787855137844435 1157993129681782706766653)
      ·
        refine ⟨434247423630668515037495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1157993129681782706766653 434247423630668515037495)
        ·
          refine ⟨651371135446002772556243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434247423630668515037495 651371135446002772556243)
          ·
            refine ⟨977056703169004158834365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651371135446002772556243 977056703169004158834365)
            ·
              refine ⟨366396263688376559562887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 977056703169004158834365 366396263688376559562887)
              ·
                refine ⟨549594395532564839344331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366396263688376559562887 549594395532564839344331)
                ·
                  refine ⟨824391593298847259016497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549594395532564839344331 824391593298847259016497)
                  ·
                    refine ⟨618293694974135444262373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 824391593298847259016497 618293694974135444262373)
                    ·
                      refine ⟨115930067807650395799195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 618293694974135444262373 115930067807650395799195)
                      ·
                        rfl

theorem cell23_225773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_225773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225773 prefixEnd_225773 := by exact prefixLift 225773
  have htrace : WordTrace (prefixWord ++ tailWord_225773) baseStart_225773 baseEnd_225773 := by
    simpa [prefixWord, tailWord_225773, baseEnd_225773] using wordTrace_append hprefix tailTrace_225773
  have hstable : (prefixWord ++ tailWord_225773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225773).length < 2 ^ (prefixWord ++ tailWord_225773).sum := by decide
  have hdescent : baseEnd_225773 < baseStart_225773 := by decide
  rcases family_descends (prefixWord ++ tailWord_225773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225789 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_225789 : Nat := 118140960795 + 225789 * 2 ^ 59
def prefixEnd_225789 : Nat := 4983230072969 + 3 ^ 40 * 225789 * 2
def baseEnd_225789 : Nat := 115938283498122333199121

theorem tailTrace_225789 : CollatzResearch.WordTrace tailWord_225789 prefixEnd_225789 115938283498122333199121 := by
  unfold tailWord_225789
  simp only [CollatzResearch.WordTrace]
  refine ⟨8235201379012489536256421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5490134252674993024170947 8235201379012489536256421)
  ·
    refine ⟨1544100258564841788048079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8235201379012489536256421 1544100258564841788048079)
    ·
      refine ⟨2316150387847262682072119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1544100258564841788048079 2316150387847262682072119)
      ·
        refine ⟨3474225581770894023108179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2316150387847262682072119 3474225581770894023108179)
        ·
          refine ⟨5211338372656341034662269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3474225581770894023108179 5211338372656341034662269)
          ·
            refine ⟨1954251889746127887998351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5211338372656341034662269 1954251889746127887998351)
            ·
              refine ⟨2931377834619191831997527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954251889746127887998351 2931377834619191831997527)
              ·
                refine ⟨4397066751928787747996291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2931377834619191831997527 4397066751928787747996291)
                ·
                  refine ⟨6595600127893181621994437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397066751928787747996291 6595600127893181621994437)
                  ·
                    refine ⟨1236675023979971554123957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6595600127893181621994437 1236675023979971554123957)
                    ·
                      refine ⟨115938283498122333199121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1236675023979971554123957 115938283498122333199121)
                      ·
                        rfl

theorem cell23_225789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_225789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225789 prefixEnd_225789 := by exact prefixLift 225789
  have htrace : WordTrace (prefixWord ++ tailWord_225789) baseStart_225789 baseEnd_225789 := by
    simpa [prefixWord, tailWord_225789, baseEnd_225789] using wordTrace_append hprefix tailTrace_225789
  have hstable : (prefixWord ++ tailWord_225789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225789).length < 2 ^ (prefixWord ++ tailWord_225789).sum := by decide
  have hdescent : baseEnd_225789 < baseStart_225789 := by decide
  rcases family_descends (prefixWord ++ tailWord_225789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225793 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_225793 : Nat := 118140960795 + 225793 * 2 ^ 59
def prefixEnd_225793 : Nat := 4983230072969 + 3 ^ 40 * 225793 * 2
def baseEnd_225793 : Nat := 115940337420740317549103

theorem tailTrace_225793 : CollatzResearch.WordTrace tailWord_225793 prefixEnd_225793 115940337420740317549103 := by
  unfold tailWord_225793
  simp only [CollatzResearch.WordTrace]
  refine ⟨8235347270997998219402033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5490231513998665479601355 8235347270997998219402033)
  ·
    refine ⟨6176510453248498664551525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8235347270997998219402033 6176510453248498664551525)
    ·
      refine ⟨1158095709984093499603411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6176510453248498664551525 1158095709984093499603411)
      ·
        refine ⟨1737143564976140249405117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1158095709984093499603411 1737143564976140249405117)
        ·
          refine ⟨651428836866052593526919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1737143564976140249405117 651428836866052593526919)
          ·
            refine ⟨977143255299078890290379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651428836866052593526919 977143255299078890290379)
            ·
              refine ⟨1465714882948618335435569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977143255299078890290379 1465714882948618335435569)
              ·
                refine ⟨1099286162211463751576677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1465714882948618335435569 1099286162211463751576677)
                ·
                  refine ⟨206116155414649453420627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1099286162211463751576677 206116155414649453420627)
                  ·
                    refine ⟨309174233121974180130941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 206116155414649453420627 309174233121974180130941)
                    ·
                      refine ⟨115940337420740317549103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 309174233121974180130941 115940337420740317549103)
                      ·
                        rfl

theorem cell23_225793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_225793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225793 prefixEnd_225793 := by exact prefixLift 225793
  have htrace : WordTrace (prefixWord ++ tailWord_225793) baseStart_225793 baseEnd_225793 := by
    simpa [prefixWord, tailWord_225793, baseEnd_225793] using wordTrace_append hprefix tailTrace_225793
  have hstable : (prefixWord ++ tailWord_225793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225793).length < 2 ^ (prefixWord ++ tailWord_225793).sum := by decide
  have hdescent : baseEnd_225793 < baseStart_225793 := by decide
  rcases family_descends (prefixWord ++ tailWord_225793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225809 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 2, 6]
def baseStart_225809 : Nat := 118140960795 + 225809 * 2 ^ 59
def prefixEnd_225809 : Nat := 4983230072969 + 3 ^ 40 * 225809 * 2
def baseEnd_225809 : Nat := 38649517703737418316343

theorem tailTrace_225809 : CollatzResearch.WordTrace tailWord_225809 prefixEnd_225809 38649517703737418316343 := by
  unfold tailWord_225809
  simp only [CollatzResearch.WordTrace]
  refine ⟨8235930838940032951984481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5490620559293355301322987 8235930838940032951984481)
  ·
    refine ⟨6176948129205024713988361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8235930838940032951984481 6176948129205024713988361)
    ·
      refine ⟨4632711096903768535491271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6176948129205024713988361 4632711096903768535491271)
      ·
        refine ⟨6949066645355652803236907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4632711096903768535491271 6949066645355652803236907)
        ·
          refine ⟨10423599968033479204855361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6949066645355652803236907 10423599968033479204855361)
          ·
            refine ⟨7817699976025109403641521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10423599968033479204855361 7817699976025109403641521)
            ·
              refine ⟨5863274982018832052731141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7817699976025109403641521 5863274982018832052731141)
              ·
                refine ⟨1099364059128531009887089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5863274982018832052731141 1099364059128531009887089)
                ·
                  refine ⟨824523044346398257415317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1099364059128531009887089 824523044346398257415317)
                  ·
                    refine ⟨38649517703737418316343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 824523044346398257415317 38649517703737418316343)
                    ·
                      rfl

theorem cell23_225809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_225809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225809 prefixEnd_225809 := by exact prefixLift 225809
  have htrace : WordTrace (prefixWord ++ tailWord_225809) baseStart_225809 baseEnd_225809 := by
    simpa [prefixWord, tailWord_225809, baseEnd_225809] using wordTrace_append hprefix tailTrace_225809
  have hstable : (prefixWord ++ tailWord_225809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225809).length < 2 ^ (prefixWord ++ tailWord_225809).sum := by decide
  have hdescent : baseEnd_225809 < baseStart_225809 := by decide
  rcases family_descends (prefixWord ++ tailWord_225809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225827 : List Nat := [1, 1, 1, 4, 4, 3, 2, 1, 2, 1, 3]
def baseStart_225827 : Nat := 118140960795 + 225827 * 2 ^ 59
def prefixEnd_225827 : Nat := 4983230072969 + 3 ^ 40 * 225827 * 2
def baseEnd_225827 : Nat := 115957795762993184523947

theorem tailTrace_225827 : CollatzResearch.WordTrace tailWord_225827 prefixEnd_225827 115957795762993184523947 := by
  unfold tailWord_225827
  simp only [CollatzResearch.WordTrace]
  refine ⟨8236587352874822026139735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5491058235249881350759823 8236587352874822026139735)
  ·
    refine ⟨12354881029312233039209603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8236587352874822026139735 12354881029312233039209603)
    ·
      refine ⟨18532321543968349558814405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12354881029312233039209603 18532321543968349558814405)
      ·
        refine ⟨3474810289494065542277701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18532321543968349558814405 3474810289494065542277701)
        ·
          refine ⟨651526929280137289177069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3474810289494065542277701 651526929280137289177069)
          ·
            refine ⟨244322598480051483441401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 651526929280137289177069 244322598480051483441401)
            ·
              refine ⟨183241948860038612581051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244322598480051483441401 183241948860038612581051)
              ·
                refine ⟨274862923290057918871577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183241948860038612581051 274862923290057918871577)
                ·
                  refine ⟨206147192467543439153683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274862923290057918871577 206147192467543439153683)
                  ·
                    refine ⟨309220788701315158730525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 206147192467543439153683 309220788701315158730525)
                    ·
                      refine ⟨115957795762993184523947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 309220788701315158730525 115957795762993184523947)
                      ·
                        rfl

theorem cell23_225827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_225827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225827 prefixEnd_225827 := by exact prefixLift 225827
  have htrace : WordTrace (prefixWord ++ tailWord_225827) baseStart_225827 baseEnd_225827 := by
    simpa [prefixWord, tailWord_225827, baseEnd_225827] using wordTrace_append hprefix tailTrace_225827
  have hstable : (prefixWord ++ tailWord_225827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225827).length < 2 ^ (prefixWord ++ tailWord_225827).sum := by decide
  have hdescent : baseEnd_225827 < baseStart_225827 := by decide
  rcases family_descends (prefixWord ++ tailWord_225827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225873 : List Nat := [1, 2, 2, 1, 3, 4, 1, 4, 5]
def baseStart_225873 : Nat := 118140960795 + 225873 * 2 ^ 59
def prefixEnd_225873 : Nat := 4983230072969 + 3 ^ 40 * 225873 * 2
def baseEnd_225873 : Nat := 12886823985900000505415

theorem tailTrace_225873 : CollatzResearch.WordTrace tailWord_225873 prefixEnd_225873 12886823985900000505415 := by
  unfold tailWord_225873
  simp only [CollatzResearch.WordTrace]
  refine ⟨8238265110708171882314273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5492176740472114588209515 8238265110708171882314273)
  ·
    refine ⟨6178698833031128911735705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8238265110708171882314273 6178698833031128911735705)
    ·
      refine ⟨4634024124773346683801779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6178698833031128911735705 4634024124773346683801779)
      ·
        refine ⟨6951036187160020025702669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4634024124773346683801779 6951036187160020025702669)
        ·
          refine ⟨2606638570185007509638501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6951036187160020025702669 2606638570185007509638501)
          ·
            refine ⟨488744731909688908057219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2606638570185007509638501 488744731909688908057219)
            ·
              refine ⟨733117097864533362085829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488744731909688908057219 733117097864533362085829)
              ·
                refine ⟨137459455849600005391093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 733117097864533362085829 137459455849600005391093)
                ·
                  refine ⟨12886823985900000505415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137459455849600005391093 12886823985900000505415)
                  ·
                    rfl

theorem cell23_225873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 5].length) (baseStart_225873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225873 prefixEnd_225873 := by exact prefixLift 225873
  have htrace : WordTrace (prefixWord ++ tailWord_225873) baseStart_225873 baseEnd_225873 := by
    simpa [prefixWord, tailWord_225873, baseEnd_225873] using wordTrace_append hprefix tailTrace_225873
  have hstable : (prefixWord ++ tailWord_225873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225873).length < 2 ^ (prefixWord ++ tailWord_225873).sum := by decide
  have hdescent : baseEnd_225873 < baseStart_225873 := by decide
  rcases family_descends (prefixWord ++ tailWord_225873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225890 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 7]
def baseStart_225890 : Nat := 118140960795 + 225890 * 2 ^ 59
def prefixEnd_225890 : Nat := 4983230072969 + 3 ^ 40 * 225890 * 2
def baseEnd_225890 : Nat := 12887793893802937559573

theorem tailTrace_225890 : CollatzResearch.WordTrace tailWord_225890 prefixEnd_225890 12887793893802937559573 := by
  unfold tailWord_225890
  simp only [CollatzResearch.WordTrace]
  refine ⟨2059721287911645946420781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5492590101097722523788749 2059721287911645946420781)
  ·
    refine ⟨772395482966867229907793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2059721287911645946420781 772395482966867229907793)
    ·
      refine ⟨579296612225150422430845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 772395482966867229907793 579296612225150422430845)
      ·
        refine ⟨217236229584431408411567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 579296612225150422430845 217236229584431408411567)
        ·
          refine ⟨325854344376647112617351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217236229584431408411567 325854344376647112617351)
          ·
            refine ⟨488781516564970668926027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325854344376647112617351 488781516564970668926027)
            ·
              refine ⟨733172274847456003389041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488781516564970668926027 733172274847456003389041)
              ·
                refine ⟨549879206135592002541781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733172274847456003389041 549879206135592002541781)
                ·
                  refine ⟨12887793893802937559573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 549879206135592002541781 12887793893802937559573)
                  ·
                    rfl

theorem cell23_225890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_225890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225890 prefixEnd_225890 := by exact prefixLift 225890
  have htrace : WordTrace (prefixWord ++ tailWord_225890) baseStart_225890 baseEnd_225890 := by
    simpa [prefixWord, tailWord_225890, baseEnd_225890] using wordTrace_append hprefix tailTrace_225890
  have hstable : (prefixWord ++ tailWord_225890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225890).length < 2 ^ (prefixWord ++ tailWord_225890).sum := by decide
  have hdescent : baseEnd_225890 < baseStart_225890 := by decide
  rcases family_descends (prefixWord ++ tailWord_225890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225899 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 1, 10]
def baseStart_225899 : Nat := 118140960795 + 225899 * 2 ^ 59
def prefixEnd_225899 : Nat := 4983230072969 + 3 ^ 40 * 225899 * 2
def baseEnd_225899 : Nat := 38664922123372300941205

theorem tailTrace_225899 : CollatzResearch.WordTrace tailWord_225899 prefixEnd_225899 38664922123372300941205 := by
  unfold tailWord_225899
  simp only [CollatzResearch.WordTrace]
  refine ⟨8239213408613978322760751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5492808939075985548507167 8239213408613978322760751)
  ·
    refine ⟨12358820112920967484141127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8239213408613978322760751 12358820112920967484141127)
    ·
      refine ⟨18538230169381451226211691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12358820112920967484141127 18538230169381451226211691)
      ·
        refine ⟨27807345254072176839317537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18538230169381451226211691 27807345254072176839317537)
        ·
          refine ⟨20855508940554132629488153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27807345254072176839317537 20855508940554132629488153)
          ·
            refine ⟨15641631705415599472116115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20855508940554132629488153 15641631705415599472116115)
            ·
              refine ⟨23462447558123399208174173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15641631705415599472116115 23462447558123399208174173)
              ·
                refine ⟨8798417834296274703065315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23462447558123399208174173 8798417834296274703065315)
                ·
                  refine ⟨13197626751444412054597973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8798417834296274703065315 13197626751444412054597973)
                  ·
                    refine ⟨38664922123372300941205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 13197626751444412054597973 38664922123372300941205)
                    ·
                      rfl

theorem cell23_225899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 10].length) (baseStart_225899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225899 prefixEnd_225899 := by exact prefixLift 225899
  have htrace : WordTrace (prefixWord ++ tailWord_225899) baseStart_225899 baseEnd_225899 := by
    simpa [prefixWord, tailWord_225899, baseEnd_225899] using wordTrace_append hprefix tailTrace_225899
  have hstable : (prefixWord ++ tailWord_225899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225899).length < 2 ^ (prefixWord ++ tailWord_225899).sum := by decide
  have hdescent : baseEnd_225899 < baseStart_225899 := by decide
  rcases family_descends (prefixWord ++ tailWord_225899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225923 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 2, 4, 2]
def baseStart_225923 : Nat := 118140960795 + 225923 * 2 ^ 59
def prefixEnd_225923 : Nat := 4983230072969 + 3 ^ 40 * 225923 * 2
def baseEnd_225923 : Nat := 116007089905824808923505

theorem tailTrace_225923 : CollatzResearch.WordTrace tailWord_225923 prefixEnd_225923 116007089905824808923505 := by
  unfold tailWord_225923
  simp only [CollatzResearch.WordTrace]
  refine ⟨8240088760527030421634423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5493392507018020281089615 8240088760527030421634423)
  ·
    refine ⟨12360133140790545632451635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8240088760527030421634423 12360133140790545632451635)
    ·
      refine ⟨18540199711185818448677453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12360133140790545632451635 18540199711185818448677453)
      ·
        refine ⟨6952574891694681918254045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18540199711185818448677453 6952574891694681918254045)
        ·
          refine ⟨2607215584385505719345267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6952574891694681918254045 2607215584385505719345267)
          ·
            refine ⟨3910823376578258579017901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2607215584385505719345267 3910823376578258579017901)
            ·
              refine ⟨1466558766216846967131713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3910823376578258579017901 1466558766216846967131713)
              ·
                refine ⟨1099919074662635225348785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466558766216846967131713 1099919074662635225348785)
                ·
                  refine ⟨824939305996976419011589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1099919074662635225348785 824939305996976419011589)
                  ·
                    refine ⟨154676119874433078564673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 824939305996976419011589 154676119874433078564673)
                    ·
                      refine ⟨116007089905824808923505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 154676119874433078564673 116007089905824808923505)
                      ·
                        rfl

theorem cell23_225923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 4, 2].length) (baseStart_225923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225923 prefixEnd_225923 := by exact prefixLift 225923
  have htrace : WordTrace (prefixWord ++ tailWord_225923) baseStart_225923 baseEnd_225923 := by
    simpa [prefixWord, tailWord_225923, baseEnd_225923] using wordTrace_append hprefix tailTrace_225923
  have hstable : (prefixWord ++ tailWord_225923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225923).length < 2 ^ (prefixWord ++ tailWord_225923).sum := by decide
  have hdescent : baseEnd_225923 < baseStart_225923 := by decide
  rcases family_descends (prefixWord ++ tailWord_225923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225950 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_225950 : Nat := 118140960795 + 225950 * 2 ^ 59
def prefixEnd_225950 : Nat := 4983230072969 + 3 ^ 40 * 225950 * 2
def baseEnd_225950 : Nat := 38673651294498734428627

theorem tailTrace_225950 : CollatzResearch.WordTrace tailWord_225950 prefixEnd_225950 38673651294498734428627 := by
  unfold tailWord_225950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1030134191428651754108413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5494049020952809355244869 1030134191428651754108413)
  ·
    refine ⟨386300321785744407790655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1030134191428651754108413 386300321785744407790655)
    ·
      refine ⟨579450482678616611685983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386300321785744407790655 579450482678616611685983)
      ·
        refine ⟨869175724017924917528975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579450482678616611685983 869175724017924917528975)
        ·
          refine ⟨1303763586026887376293463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869175724017924917528975 1303763586026887376293463)
          ·
            refine ⟨1955645379040331064440195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303763586026887376293463 1955645379040331064440195)
            ·
              refine ⟨2933468068560496596660293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955645379040331064440195 2933468068560496596660293)
              ·
                refine ⟨550025262855093111873805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2933468068560496596660293 550025262855093111873805)
                ·
                  refine ⟨206259473570659916952677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550025262855093111873805 206259473570659916952677)
                  ·
                    refine ⟨38673651294498734428627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 206259473570659916952677 38673651294498734428627)
                    ·
                      rfl

theorem cell23_225950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_225950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225950 prefixEnd_225950 := by exact prefixLift 225950
  have htrace : WordTrace (prefixWord ++ tailWord_225950) baseStart_225950 baseEnd_225950 := by
    simpa [prefixWord, tailWord_225950, baseEnd_225950] using wordTrace_append hprefix tailTrace_225950
  have hstable : (prefixWord ++ tailWord_225950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225950).length < 2 ^ (prefixWord ++ tailWord_225950).sum := by decide
  have hdescent : baseEnd_225950 < baseStart_225950 := by decide
  rcases family_descends (prefixWord ++ tailWord_225950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225967 : List Nat := [1, 1, 2, 1, 2, 7, 1, 3, 1, 4]
def baseStart_225967 : Nat := 118140960795 + 225967 * 2 ^ 59
def prefixEnd_225967 : Nat := 4983230072969 + 3 ^ 40 * 225967 * 2
def baseEnd_225967 : Nat := 38676561018207545591101

theorem tailTrace_225967 : CollatzResearch.WordTrace tailWord_225967 prefixEnd_225967 38676561018207545591101 := by
  unfold tailWord_225967
  simp only [CollatzResearch.WordTrace]
  refine ⟨8241693572367625936236155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5494462381578417290824103 8241693572367625936236155)
  ·
    refine ⟨12362540358551438904354233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8241693572367625936236155 12362540358551438904354233)
    ·
      refine ⟨9271905268913579178265675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12362540358551438904354233 9271905268913579178265675)
      ·
        refine ⟨13907857903370368767398513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9271905268913579178265675 13907857903370368767398513)
        ·
          refine ⟨10430893427527776575548885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13907857903370368767398513 10430893427527776575548885)
          ·
            refine ⟨244474064707682263489427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 10430893427527776575548885 244474064707682263489427)
            ·
              refine ⟨366711097061523395234141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244474064707682263489427 366711097061523395234141)
              ·
                refine ⟨137516661398071273212803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 366711097061523395234141 137516661398071273212803)
                ·
                  refine ⟨206274992097106909819205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137516661398071273212803 206274992097106909819205)
                  ·
                    refine ⟨38676561018207545591101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 206274992097106909819205 38676561018207545591101)
                    ·
                      rfl

theorem cell23_225967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 1, 4].length) (baseStart_225967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225967 prefixEnd_225967 := by exact prefixLift 225967
  have htrace : WordTrace (prefixWord ++ tailWord_225967) baseStart_225967 baseEnd_225967 := by
    simpa [prefixWord, tailWord_225967, baseEnd_225967] using wordTrace_append hprefix tailTrace_225967
  have hstable : (prefixWord ++ tailWord_225967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225967).length < 2 ^ (prefixWord ++ tailWord_225967).sum := by decide
  have hdescent : baseEnd_225967 < baseStart_225967 := by decide
  rcases family_descends (prefixWord ++ tailWord_225967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225976 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 7, 5]
def baseStart_225976 : Nat := 118140960795 + 225976 * 2 ^ 59
def prefixEnd_225976 : Nat := 4983230072969 + 3 ^ 40 * 225976 * 2
def baseEnd_225976 : Nat := 38678101460171033853587

theorem tailTrace_225976 : CollatzResearch.WordTrace tailWord_225976 prefixEnd_225976 38678101460171033853587 := by
  unfold tailWord_225976
  simp only [CollatzResearch.WordTrace]
  refine ⟨4121010914667510236656891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5494681219556680315542521 4121010914667510236656891)
  ·
    refine ⟨6181516372001265354985337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4121010914667510236656891 6181516372001265354985337)
    ·
      refine ⟨4636137279000949016239003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6181516372001265354985337 4636137279000949016239003)
      ·
        refine ⟨6954205918501423524358505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4636137279000949016239003 6954205918501423524358505)
        ·
          refine ⟨5215654438876067643268879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6954205918501423524358505 5215654438876067643268879)
          ·
            refine ⟨7823481658314101464903319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5215654438876067643268879 7823481658314101464903319)
            ·
              refine ⟨11735222487471152197354979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7823481658314101464903319 11735222487471152197354979)
              ·
                refine ⟨17602833731206728296032469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11735222487471152197354979 17602833731206728296032469)
                ·
                  refine ⟨412566415575157694438261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17602833731206728296032469 412566415575157694438261)
                  ·
                    refine ⟨38678101460171033853587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 412566415575157694438261 38678101460171033853587)
                    ·
                      rfl

theorem cell23_225976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_225976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225976 prefixEnd_225976 := by exact prefixLift 225976
  have htrace : WordTrace (prefixWord ++ tailWord_225976) baseStart_225976 baseEnd_225976 := by
    simpa [prefixWord, tailWord_225976, baseEnd_225976] using wordTrace_append hprefix tailTrace_225976
  have hstable : (prefixWord ++ tailWord_225976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225976).length < 2 ^ (prefixWord ++ tailWord_225976).sum := by decide
  have hdescent : baseEnd_225976 < baseStart_225976 := by decide
  rcases family_descends (prefixWord ++ tailWord_225976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225997 : List Nat := [1, 6, 2, 1, 2, 1, 1, 3, 6]
def baseStart_225997 : Nat := 118140960795 + 225997 * 2 ^ 59
def prefixEnd_225997 : Nat := 4983230072969 + 3 ^ 40 * 225997 * 2
def baseEnd_225997 : Nat := 12893898608250835488685

theorem tailTrace_225997 : CollatzResearch.WordTrace tailWord_225997 prefixEnd_225997 12893898608250835488685 := by
  unfold tailWord_225997
  simp only [CollatzResearch.WordTrace]
  refine ⟨8242787762258941059828245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5495191841505960706552163 8242787762258941059828245)
  ·
    refine ⟨386380676355887862179449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8242787762258941059828245 386380676355887862179449)
    ·
      refine ⟨289785507266915896634587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386380676355887862179449 289785507266915896634587)
      ·
        refine ⟨434678260900373844951881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289785507266915896634587 434678260900373844951881)
        ·
          refine ⟨326008695675280383713911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434678260900373844951881 326008695675280383713911)
          ·
            refine ⟨489013043512920575570867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326008695675280383713911 489013043512920575570867)
            ·
              refine ⟨733519565269380863356301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489013043512920575570867 733519565269380863356301)
              ·
                refine ⟨275069836976017823758613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 733519565269380863356301 275069836976017823758613)
                ·
                  refine ⟨12893898608250835488685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 275069836976017823758613 12893898608250835488685)
                  ·
                    rfl

theorem cell23_225997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_225997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225997 prefixEnd_225997 := by exact prefixLift 225997
  have htrace : WordTrace (prefixWord ++ tailWord_225997) baseStart_225997 baseEnd_225997 := by
    simpa [prefixWord, tailWord_225997, baseEnd_225997] using wordTrace_append hprefix tailTrace_225997
  have hstable : (prefixWord ++ tailWord_225997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225997).length < 2 ^ (prefixWord ++ tailWord_225997).sum := by decide
  have hdescent : baseEnd_225997 < baseStart_225997 := by decide
  rcases family_descends (prefixWord ++ tailWord_225997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226017 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 2, 3, 2]
def baseStart_226017 : Nat := 118140960795 + 226017 * 2 ^ 59
def prefixEnd_226017 : Nat := 4983230072969 + 3 ^ 40 * 226017 * 2
def baseEnd_226017 : Nat := 116055357087347441148073

theorem tailTrace_226017 : CollatzResearch.WordTrace tailWord_226017 prefixEnd_226017 116055357087347441148073 := by
  unfold tailWord_226017
  simp only [CollatzResearch.WordTrace]
  refine ⟨8243517222186484475556305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5495678148124322983704203 8243517222186484475556305)
  ·
    refine ⟨6182637916639863356667229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8243517222186484475556305 6182637916639863356667229)
    ·
      refine ⟨2318489218739948758750211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6182637916639863356667229 2318489218739948758750211)
      ·
        refine ⟨3477733828109923138125317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2318489218739948758750211 3477733828109923138125317)
        ·
          refine ⟨652075092770610588398497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3477733828109923138125317 652075092770610588398497)
          ·
            refine ⟨489056319577957941298873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 652075092770610588398497 489056319577957941298873)
            ·
              refine ⟨366792239683468455974155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489056319577957941298873 366792239683468455974155)
              ·
                refine ⟨550188359525202683961233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366792239683468455974155 550188359525202683961233)
                ·
                  refine ⟨412641269643902012970925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550188359525202683961233 412641269643902012970925)
                  ·
                    refine ⟨154740476116463254864097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 412641269643902012970925 154740476116463254864097)
                    ·
                      refine ⟨116055357087347441148073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 154740476116463254864097 116055357087347441148073)
                      ·
                        rfl

theorem cell23_226017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_226017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226017 prefixEnd_226017 := by exact prefixLift 226017
  have htrace : WordTrace (prefixWord ++ tailWord_226017) baseStart_226017 baseEnd_226017 := by
    simpa [prefixWord, tailWord_226017, baseEnd_226017] using wordTrace_append hprefix tailTrace_226017
  have hstable : (prefixWord ++ tailWord_226017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226017).length < 2 ^ (prefixWord ++ tailWord_226017).sum := by decide
  have hdescent : baseEnd_226017 < baseStart_226017 := by decide
  rcases family_descends (prefixWord ++ tailWord_226017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226040 : List Nat := [2, 1, 2, 1, 1, 2, 6, 2, 2, 4]
def baseStart_226040 : Nat := 118140960795 + 226040 * 2 ^ 59
def prefixEnd_226040 : Nat := 4983230072969 + 3 ^ 40 * 226040 * 2
def baseEnd_226040 : Nat := 38689055714133617053489

theorem tailTrace_226040 : CollatzResearch.WordTrace tailWord_226040 prefixEnd_226040 38689055714133617053489 := by
  unfold tailWord_226040
  simp only [CollatzResearch.WordTrace]
  refine ⟨4122178050551579701821787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5496237400735439602429049 4122178050551579701821787)
  ·
    refine ⟨6183267075827369552732681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4122178050551579701821787 6183267075827369552732681)
    ·
      refine ⟨4637450306870527164549511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6183267075827369552732681 4637450306870527164549511)
      ·
        refine ⟨6956175460305790746824267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4637450306870527164549511 6956175460305790746824267)
        ·
          refine ⟨10434263190458686120236401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6956175460305790746824267 10434263190458686120236401)
          ·
            refine ⟨7825697392844014590177301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10434263190458686120236401 7825697392844014590177301)
            ·
              refine ⟨366829565289563183914561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7825697392844014590177301 366829565289563183914561)
              ·
                refine ⟨275122173967172387935921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366829565289563183914561 275122173967172387935921)
                ·
                  refine ⟨206341630475379290951941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275122173967172387935921 206341630475379290951941)
                  ·
                    refine ⟨38689055714133617053489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 206341630475379290951941 38689055714133617053489)
                    ·
                      rfl

theorem cell23_226040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_226040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226040 prefixEnd_226040 := by exact prefixLift 226040
  have htrace : WordTrace (prefixWord ++ tailWord_226040) baseStart_226040 baseEnd_226040 := by
    simpa [prefixWord, tailWord_226040, baseEnd_226040] using wordTrace_append hprefix tailTrace_226040
  have hstable : (prefixWord ++ tailWord_226040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226040).length < 2 ^ (prefixWord ++ tailWord_226040).sum := by decide
  have hdescent : baseEnd_226040 < baseStart_226040 := by decide
  rcases family_descends (prefixWord ++ tailWord_226040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226080 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 3]
def baseStart_226080 : Nat := 118140960795 + 226080 * 2 ^ 59
def prefixEnd_226080 : Nat := 4983230072969 + 3 ^ 40 * 226080 * 2
def baseEnd_226080 : Nat := 116087706368580694660283

theorem tailTrace_226080 : CollatzResearch.WordTrace tailWord_226080 prefixEnd_226080 116087706368580694660283 := by
  unfold tailWord_226080
  simp only [CollatzResearch.WordTrace]
  refine ⟨4122907510479123117549847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5497210013972164156733129 4122907510479123117549847)
  ·
    refine ⟨6184361265718684676324771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4122907510479123117549847 6184361265718684676324771)
    ·
      refine ⟨9276541898578027014487157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6184361265718684676324771 9276541898578027014487157)
      ·
        refine ⟨869675802991690032608171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9276541898578027014487157 869675802991690032608171)
        ·
          refine ⟨1304513704487535048912257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869675802991690032608171 1304513704487535048912257)
          ·
            refine ⟨978385278365651286684193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1304513704487535048912257 978385278365651286684193)
            ·
              refine ⟨733788958774238465013145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 978385278365651286684193 733788958774238465013145)
              ·
                refine ⟨550341719080678848759859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733788958774238465013145 550341719080678848759859)
                ·
                  refine ⟨825512578621018273139789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 550341719080678848759859 825512578621018273139789)
                  ·
                    refine ⟨309567216982881852427421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 825512578621018273139789 309567216982881852427421)
                    ·
                      refine ⟨116087706368580694660283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 309567216982881852427421 116087706368580694660283)
                      ·
                        rfl

theorem cell23_226080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_226080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226080 prefixEnd_226080 := by exact prefixLift 226080
  have htrace : WordTrace (prefixWord ++ tailWord_226080) baseStart_226080 baseEnd_226080 := by
    simpa [prefixWord, tailWord_226080, baseEnd_226080] using wordTrace_append hprefix tailTrace_226080
  have hstable : (prefixWord ++ tailWord_226080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226080).length < 2 ^ (prefixWord ++ tailWord_226080).sum := by decide
  have hdescent : baseEnd_226080 < baseStart_226080 := by decide
  rcases family_descends (prefixWord ++ tailWord_226080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226124 : List Nat := [2, 2, 1, 3, 3, 2, 2, 2, 1, 3, 2]
def baseStart_226124 : Nat := 118140960795 + 226124 * 2 ^ 59
def prefixEnd_226124 : Nat := 4983230072969 + 3 ^ 40 * 226124 * 2
def baseEnd_226124 : Nat := 116110299517378522510081

theorem tailTrace_226124 : CollatzResearch.WordTrace tailWord_226124 prefixEnd_226124 116110299517378522510081 := by
  unfold tailWord_226124
  simp only [CollatzResearch.WordTrace]
  refine ⟨4123709916399420874850713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5498279888532561166467617 4123709916399420874850713)
  ·
    refine ⟨3092782437299565656138035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4123709916399420874850713 3092782437299565656138035)
    ·
      refine ⟨4639173655949348484207053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3092782437299565656138035 4639173655949348484207053)
      ·
        refine ⟨1739690120981005681577645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4639173655949348484207053 1739690120981005681577645)
        ·
          refine ⟨652383795367877130591617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1739690120981005681577645 652383795367877130591617)
          ·
            refine ⟨489287846525907847943713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 652383795367877130591617 489287846525907847943713)
            ·
              refine ⟨366965884894430885957785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489287846525907847943713 366965884894430885957785)
              ·
                refine ⟨275224413670823164468339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366965884894430885957785 275224413670823164468339)
                ·
                  refine ⟨412836620506234746702509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275224413670823164468339 412836620506234746702509)
                  ·
                    refine ⟨154813732689838030013441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 412836620506234746702509 154813732689838030013441)
                    ·
                      refine ⟨116110299517378522510081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 154813732689838030013441 116110299517378522510081)
                      ·
                        rfl

theorem cell23_226124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_226124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226124 prefixEnd_226124 := by exact prefixLift 226124
  have htrace : WordTrace (prefixWord ++ tailWord_226124) baseStart_226124 baseEnd_226124 := by
    simpa [prefixWord, tailWord_226124, baseEnd_226124] using wordTrace_append hprefix tailTrace_226124
  have hstable : (prefixWord ++ tailWord_226124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226124).length < 2 ^ (prefixWord ++ tailWord_226124).sum := by decide
  have hdescent : baseEnd_226124 < baseStart_226124 := by decide
  rcases family_descends (prefixWord ++ tailWord_226124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226137 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 4, 2, 2]
def baseStart_226137 : Nat := 118140960795 + 226137 * 2 ^ 59
def prefixEnd_226137 : Nat := 4983230072969 + 3 ^ 40 * 226137 * 2
def baseEnd_226137 : Nat := 116116974765886971647521

theorem tailTrace_226137 : CollatzResearch.WordTrace tailWord_226137 prefixEnd_226137 116116974765886971647521 := by
  unfold tailWord_226137
  simp only [CollatzResearch.WordTrace]
  refine ⟨8247893981751744969924665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5498595987834496646616443 8247893981751744969924665)
  ·
    refine ⟨6185920486313808727443499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8247893981751744969924665 6185920486313808727443499)
    ·
      refine ⟨9278880729470713091165249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6185920486313808727443499 9278880729470713091165249)
      ·
        refine ⟨6959160547103034818373937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9278880729470713091165249 6959160547103034818373937)
        ·
          refine ⟨5219370410327276113780453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6959160547103034818373937 5219370410327276113780453)
          ·
            refine ⟨978631951936364271333835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5219370410327276113780453 978631951936364271333835)
            ·
              refine ⟨1467947927904546407000753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978631951936364271333835 1467947927904546407000753)
              ·
                refine ⟨1100960945928409805250565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1467947927904546407000753 1100960945928409805250565)
                ·
                  refine ⟨206430177361576838484481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1100960945928409805250565 206430177361576838484481)
                  ·
                    refine ⟨154822633021182628863361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 206430177361576838484481 154822633021182628863361)
                    ·
                      refine ⟨116116974765886971647521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 154822633021182628863361 116116974765886971647521)
                      ·
                        rfl

theorem cell23_226137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 2, 2].length) (baseStart_226137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226137 prefixEnd_226137 := by exact prefixLift 226137
  have htrace : WordTrace (prefixWord ++ tailWord_226137) baseStart_226137 baseEnd_226137 := by
    simpa [prefixWord, tailWord_226137, baseEnd_226137] using wordTrace_append hprefix tailTrace_226137
  have hstable : (prefixWord ++ tailWord_226137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226137).length < 2 ^ (prefixWord ++ tailWord_226137).sum := by decide
  have hdescent : baseEnd_226137 < baseStart_226137 := by decide
  rcases family_descends (prefixWord ++ tailWord_226137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226140 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_226140 : Nat := 118140960795 + 226140 * 2 ^ 59
def prefixEnd_226140 : Nat := 4983230072969 + 3 ^ 40 * 226140 * 2
def baseEnd_226140 : Nat := 116118515207850459910007

theorem tailTrace_226140 : CollatzResearch.WordTrace tailWord_226140 prefixEnd_226140 116118515207850459910007 := by
  unfold tailWord_226140
  simp only [CollatzResearch.WordTrace]
  refine ⟨4124001700370438241141937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5498668933827250988189249 4124001700370438241141937)
  ·
    refine ⟨3093001275277828680856453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4124001700370438241141937 3093001275277828680856453)
    ·
      refine ⟨579937739114592877660585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3093001275277828680856453 579937739114592877660585)
      ·
        refine ⟨434953304335944658245439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579937739114592877660585 434953304335944658245439)
        ·
          refine ⟨652429956503916987368159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434953304335944658245439 652429956503916987368159)
          ·
            refine ⟨978644934755875481052239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652429956503916987368159 978644934755875481052239)
            ·
              refine ⟨1467967402133813221578359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978644934755875481052239 1467967402133813221578359)
              ·
                refine ⟨2201951103200719832367539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467967402133813221578359 2201951103200719832367539)
                ·
                  refine ⟨3302926654801079748551309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201951103200719832367539 3302926654801079748551309)
                  ·
                    refine ⟨1238597495550404905706741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3302926654801079748551309 1238597495550404905706741)
                    ·
                      refine ⟨116118515207850459910007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1238597495550404905706741 116118515207850459910007)
                      ·
                        rfl

theorem cell23_226140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_226140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226140 prefixEnd_226140 := by exact prefixLift 226140
  have htrace : WordTrace (prefixWord ++ tailWord_226140) baseStart_226140 baseEnd_226140 := by
    simpa [prefixWord, tailWord_226140, baseEnd_226140] using wordTrace_append hprefix tailTrace_226140
  have hstable : (prefixWord ++ tailWord_226140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226140).length < 2 ^ (prefixWord ++ tailWord_226140).sum := by decide
  have hdescent : baseEnd_226140 < baseStart_226140 := by decide
  rcases family_descends (prefixWord ++ tailWord_226140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226160 : List Nat := [2, 1, 1, 1, 4, 1, 2, 6, 5]
def baseStart_226160 : Nat := 118140960795 + 226160 * 2 ^ 59
def prefixEnd_226160 : Nat := 4983230072969 + 3 ^ 40 * 226160 * 2
def baseEnd_226160 : Nat := 12903198313437820184435

theorem tailTrace_226160 : CollatzResearch.WordTrace tailWord_226160 prefixEnd_226160 12903198313437820184435 := by
  unfold tailWord_226160
  simp only [CollatzResearch.WordTrace]
  refine ⟨4124366430334209949005967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5499155240445613265341289 4124366430334209949005967)
  ·
    refine ⟨6186549645501314923508951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4124366430334209949005967 6186549645501314923508951)
    ·
      refine ⟨9279824468251972385263427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6186549645501314923508951 9279824468251972385263427)
      ·
        refine ⟨13919736702377958577895141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9279824468251972385263427 13919736702377958577895141)
        ·
          refine ⟨2609950631695867233355339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13919736702377958577895141 2609950631695867233355339)
          ·
            refine ⟨3914925947543800850033009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609950631695867233355339 3914925947543800850033009)
            ·
              refine ⟨2936194460657850637524757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3914925947543800850033009 2936194460657850637524757)
              ·
                refine ⟨137634115343336748633973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2936194460657850637524757 137634115343336748633973)
                ·
                  refine ⟨12903198313437820184435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137634115343336748633973 12903198313437820184435)
                  ·
                    rfl

theorem cell23_226160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 5].length) (baseStart_226160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226160 prefixEnd_226160 := by exact prefixLift 226160
  have htrace : WordTrace (prefixWord ++ tailWord_226160) baseStart_226160 baseEnd_226160 := by
    simpa [prefixWord, tailWord_226160, baseEnd_226160] using wordTrace_append hprefix tailTrace_226160
  have hstable : (prefixWord ++ tailWord_226160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226160).length < 2 ^ (prefixWord ++ tailWord_226160).sum := by decide
  have hdescent : baseEnd_226160 < baseStart_226160 := by decide
  rcases family_descends (prefixWord ++ tailWord_226160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226173 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 3, 7]
def baseStart_226173 : Nat := 118140960795 + 226173 * 2 ^ 59
def prefixEnd_226173 : Nat := 4983230072969 + 3 ^ 40 * 226173 * 2
def baseEnd_226173 : Nat := 38711820023149610265785

theorem tailTrace_226173 : CollatzResearch.WordTrace tailWord_226173 prefixEnd_226173 38711820023149610265785 := by
  unfold tailWord_226173
  simp only [CollatzResearch.WordTrace]
  refine ⟨8249207009621323118235173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5499471339747548745490115 8249207009621323118235173)
  ·
    refine ⟨1546726314303998084669095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8249207009621323118235173 1546726314303998084669095)
    ·
      refine ⟨2320089471455997127003643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1546726314303998084669095 2320089471455997127003643)
      ·
        refine ⟨3480134207183995690505465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2320089471455997127003643 3480134207183995690505465)
        ·
          refine ⟨2610100655387996767879099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3480134207183995690505465 2610100655387996767879099)
          ·
            refine ⟨3915150983081995151818649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610100655387996767879099 3915150983081995151818649)
            ·
              refine ⟨2936363237311496363863987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3915150983081995151818649 2936363237311496363863987)
              ·
                refine ⟨4404544855967244545795981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2936363237311496363863987 4404544855967244545795981)
                ·
                  refine ⟨1651704320987716704673493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4404544855967244545795981 1651704320987716704673493)
                  ·
                    refine ⟨38711820023149610265785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1651704320987716704673493 38711820023149610265785)
                    ·
                      rfl

theorem cell23_226173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_226173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226173 prefixEnd_226173 := by exact prefixLift 226173
  have htrace : WordTrace (prefixWord ++ tailWord_226173) baseStart_226173 baseEnd_226173 := by
    simpa [prefixWord, tailWord_226173, baseEnd_226173] using wordTrace_append hprefix tailTrace_226173
  have hstable : (prefixWord ++ tailWord_226173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226173).length < 2 ^ (prefixWord ++ tailWord_226173).sum := by decide
  have hdescent : baseEnd_226173 < baseStart_226173 := by decide
  rcases family_descends (prefixWord ++ tailWord_226173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226223 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 6]
def baseStart_226223 : Nat := 118140960795 + 226223 * 2 ^ 59
def prefixEnd_226223 : Nat := 4983230072969 + 3 ^ 40 * 226223 * 2
def baseEnd_226223 : Nat := 116161134102173635172125

theorem tailTrace_226223 : CollatzResearch.WordTrace tailWord_226223 prefixEnd_226223 116161134102173635172125 := by
  unfold tailWord_226223
  simp only [CollatzResearch.WordTrace]
  refine ⟨8251030659440181657555323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5500687106293454438370215 8251030659440181657555323)
  ·
    refine ⟨12376545989160272486332985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8251030659440181657555323 12376545989160272486332985)
    ·
      refine ⟨9282409491870204364749739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12376545989160272486332985 9282409491870204364749739)
      ·
        refine ⟨13923614237805306547124609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9282409491870204364749739 13923614237805306547124609)
        ·
          refine ⟨10442710678353979910343457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13923614237805306547124609 10442710678353979910343457)
          ·
            refine ⟨7832033008765484932757593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10442710678353979910343457 7832033008765484932757593)
            ·
              refine ⟨5874024756574113699568195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7832033008765484932757593 5874024756574113699568195)
              ·
                refine ⟨8811037134861170549352293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5874024756574113699568195 8811037134861170549352293)
                ·
                  refine ⟨1652069462786469478003555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8811037134861170549352293 1652069462786469478003555)
                  ·
                    refine ⟨2478104194179704217005333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1652069462786469478003555 2478104194179704217005333)
                    ·
                      refine ⟨116161134102173635172125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2478104194179704217005333 116161134102173635172125)
                      ·
                        rfl

theorem cell23_226223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_226223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226223 prefixEnd_226223 := by exact prefixLift 226223
  have htrace : WordTrace (prefixWord ++ tailWord_226223) baseStart_226223 baseEnd_226223 := by
    simpa [prefixWord, tailWord_226223, baseEnd_226223] using wordTrace_append hprefix tailTrace_226223
  have hstable : (prefixWord ++ tailWord_226223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226223).length < 2 ^ (prefixWord ++ tailWord_226223).sum := by decide
  have hdescent : baseEnd_226223 < baseStart_226223 := by decide
  rcases family_descends (prefixWord ++ tailWord_226223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226244 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_226244 : Nat := 118140960795 + 226244 * 2 ^ 59
def prefixEnd_226244 : Nat := 4983230072969 + 3 ^ 40 * 226244 * 2
def baseEnd_226244 : Nat := 116171917195918053009529

theorem tailTrace_226244 : CollatzResearch.WordTrace tailWord_226244 prefixEnd_226244 116171917195918053009529 := by
  unfold tailWord_226244
  simp only [CollatzResearch.WordTrace]
  refine ⟨4125898296182051122034893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5501197728242734829379857 4125898296182051122034893)
  ·
    refine ⟨1547211861068269170763085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4125898296182051122034893 1547211861068269170763085)
    ·
      refine ⟨580204447900600939036157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1547211861068269170763085 580204447900600939036157)
      ·
        refine ⟨217576667962725352138559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 580204447900600939036157 217576667962725352138559)
        ·
          refine ⟨326365001944088028207839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217576667962725352138559 326365001944088028207839)
          ·
            refine ⟨489547502916132042311759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326365001944088028207839 489547502916132042311759)
            ·
              refine ⟨734321254374198063467639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489547502916132042311759 734321254374198063467639)
              ·
                refine ⟨1101481881561297095201459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734321254374198063467639 1101481881561297095201459)
                ·
                  refine ⟨1652222822341945642802189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1101481881561297095201459 1652222822341945642802189)
                  ·
                    refine ⟨619583558378229616050821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1652222822341945642802189 619583558378229616050821)
                    ·
                      refine ⟨116171917195918053009529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 619583558378229616050821 116171917195918053009529)
                      ·
                        rfl

theorem cell23_226244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_226244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226244 prefixEnd_226244 := by exact prefixLift 226244
  have htrace : WordTrace (prefixWord ++ tailWord_226244) baseStart_226244 baseEnd_226244 := by
    simpa [prefixWord, tailWord_226244, baseEnd_226244] using wordTrace_append hprefix tailTrace_226244
  have hstable : (prefixWord ++ tailWord_226244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226244).length < 2 ^ (prefixWord ++ tailWord_226244).sum := by decide
  have hdescent : baseEnd_226244 < baseStart_226244 := by decide
  rcases family_descends (prefixWord ++ tailWord_226244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226247 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 3]
def baseStart_226247 : Nat := 118140960795 + 226247 * 2 ^ 59
def prefixEnd_226247 : Nat := 4983230072969 + 3 ^ 40 * 226247 * 2
def baseEnd_226247 : Nat := 116173457637881541272015

theorem tailTrace_226247 : CollatzResearch.WordTrace tailWord_226247 prefixEnd_226247 116173457637881541272015 := by
  unfold tailWord_226247
  simp only [CollatzResearch.WordTrace]
  refine ⟨8251906011353233756428995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5501270674235489170952663 8251906011353233756428995)
  ·
    refine ⟨12377859017029850634643493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8251906011353233756428995 12377859017029850634643493)
    ·
      refine ⟨2320848565693096993995655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12377859017029850634643493 2320848565693096993995655)
      ·
        refine ⟨3481272848539645490993483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2320848565693096993995655 3481272848539645490993483)
        ·
          refine ⟨5221909272809468236490225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3481272848539645490993483 5221909272809468236490225)
          ·
            refine ⟨3916431954607101177367669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5221909272809468236490225 3916431954607101177367669)
            ·
              refine ⟨367165495744415735378219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3916431954607101177367669 367165495744415735378219)
              ·
                refine ⟨550748243616623603067329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367165495744415735378219 550748243616623603067329)
                ·
                  refine ⟨413061182712467702300497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550748243616623603067329 413061182712467702300497)
                  ·
                    refine ⟨309795887034350776725373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 413061182712467702300497 309795887034350776725373)
                    ·
                      refine ⟨116173457637881541272015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 309795887034350776725373 116173457637881541272015)
                      ·
                        rfl

theorem cell23_226247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_226247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226247 prefixEnd_226247 := by exact prefixLift 226247
  have htrace : WordTrace (prefixWord ++ tailWord_226247) baseStart_226247 baseEnd_226247 := by
    simpa [prefixWord, tailWord_226247, baseEnd_226247] using wordTrace_append hprefix tailTrace_226247
  have hstable : (prefixWord ++ tailWord_226247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226247).length < 2 ^ (prefixWord ++ tailWord_226247).sum := by decide
  have hdescent : baseEnd_226247 < baseStart_226247 := by decide
  rcases family_descends (prefixWord ++ tailWord_226247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226254 : List Nat := [4, 1, 1, 1, 2, 3, 1, 5, 1, 4]
def baseStart_226254 : Nat := 118140960795 + 226254 * 2 ^ 59
def prefixEnd_226254 : Nat := 4983230072969 + 3 ^ 40 * 226254 * 2
def baseEnd_226254 : Nat := 38725684000821004628161

theorem tailTrace_226254 : CollatzResearch.WordTrace tailWord_226254 prefixEnd_226254 38725684000821004628161 := by
  unfold tailWord_226254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1031520165290984243991727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5501440881551915967955877 1031520165290984243991727)
  ·
    refine ⟨1547280247936476365987591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1031520165290984243991727 1547280247936476365987591)
    ·
      refine ⟨2320920371904714548981387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1547280247936476365987591 2320920371904714548981387)
      ·
        refine ⟨3481380557857071823472081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2320920371904714548981387 3481380557857071823472081)
        ·
          refine ⟨2611035418392803867604061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3481380557857071823472081 2611035418392803867604061)
          ·
            refine ⟨979138281897301450351523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2611035418392803867604061 979138281897301450351523)
            ·
              refine ⟨1468707422845952175527285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979138281897301450351523 1468707422845952175527285)
              ·
                refine ⟨137691320891808016455683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1468707422845952175527285 137691320891808016455683)
                ·
                  refine ⟨206536981337712024683525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137691320891808016455683 206536981337712024683525)
                  ·
                    refine ⟨38725684000821004628161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 206536981337712024683525 38725684000821004628161)
                    ·
                      rfl

theorem cell23_226254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_226254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226254 prefixEnd_226254 := by exact prefixLift 226254
  have htrace : WordTrace (prefixWord ++ tailWord_226254) baseStart_226254 baseEnd_226254 := by
    simpa [prefixWord, tailWord_226254, baseEnd_226254] using wordTrace_append hprefix tailTrace_226254
  have hstable : (prefixWord ++ tailWord_226254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226254).length < 2 ^ (prefixWord ++ tailWord_226254).sum := by decide
  have hdescent : baseEnd_226254 < baseStart_226254 := by decide
  rcases family_descends (prefixWord ++ tailWord_226254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226280 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 5, 5]
def baseStart_226280 : Nat := 118140960795 + 226280 * 2 ^ 59
def prefixEnd_226280 : Nat := 4983230072969 + 3 ^ 40 * 226280 * 2
def baseEnd_226280 : Nat := 38730134166493304053121

theorem tailTrace_226280 : CollatzResearch.WordTrace tailWord_226280 prefixEnd_226280 38730134166493304053121 := by
  unfold tailWord_226280
  simp only [CollatzResearch.WordTrace]
  refine ⟨4126554810116840196190147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5502073080155786928253529 4126554810116840196190147)
  ·
    refine ⟨6189832215175260294285221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4126554810116840196190147 6189832215175260294285221)
    ·
      refine ⟨1160593540345361305178479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6189832215175260294285221 1160593540345361305178479)
      ·
        refine ⟨1740890310518041957767719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160593540345361305178479 1740890310518041957767719)
        ·
          refine ⟨2611335465777062936651579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740890310518041957767719 2611335465777062936651579)
          ·
            refine ⟨3917003198665594404977369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2611335465777062936651579 3917003198665594404977369)
            ·
              refine ⟨2937752398999195803733027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3917003198665594404977369 2937752398999195803733027)
              ·
                refine ⟨4406628598498793705599541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937752398999195803733027 4406628598498793705599541)
                ·
                  refine ⟨413121431109261909899957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4406628598498793705599541 413121431109261909899957)
                  ·
                    refine ⟨38730134166493304053121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 413121431109261909899957 38730134166493304053121)
                    ·
                      rfl

theorem cell23_226280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_226280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226280 prefixEnd_226280 := by exact prefixLift 226280
  have htrace : WordTrace (prefixWord ++ tailWord_226280) baseStart_226280 baseEnd_226280 := by
    simpa [prefixWord, tailWord_226280, baseEnd_226280] using wordTrace_append hprefix tailTrace_226280
  have hstable : (prefixWord ++ tailWord_226280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226280).length < 2 ^ (prefixWord ++ tailWord_226280).sum := by decide
  have hdescent : baseEnd_226280 < baseStart_226280 := by decide
  rcases family_descends (prefixWord ++ tailWord_226280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226287 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 1, 5, 2]
def baseStart_226287 : Nat := 118140960795 + 226287 * 2 ^ 59
def prefixEnd_226287 : Nat := 4983230072969 + 3 ^ 40 * 226287 * 2
def baseEnd_226287 : Nat := 116193996864061384771831

theorem tailTrace_226287 : CollatzResearch.WordTrace tailWord_226287 prefixEnd_226287 116193996864061384771831 := by
  unfold tailWord_226287
  simp only [CollatzResearch.WordTrace]
  refine ⟨8253364931208320587885115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5502243287472213725256743 8253364931208320587885115)
  ·
    refine ⟨12380047396812480881827673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8253364931208320587885115 12380047396812480881827673)
    ·
      refine ⟨9285035547609360661370755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12380047396812480881827673 9285035547609360661370755)
      ·
        refine ⟨13927553321414040992056133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9285035547609360661370755 13927553321414040992056133)
        ·
          refine ⟨2611416247765132686010525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13927553321414040992056133 2611416247765132686010525)
          ·
            refine ⟨979281092911924757253947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2611416247765132686010525 979281092911924757253947)
            ·
              refine ⟨1468921639367887135880921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979281092911924757253947 1468921639367887135880921)
              ·
                refine ⟨1101691229525915351910691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468921639367887135880921 1101691229525915351910691)
                ·
                  refine ⟨1652536844288873027866037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1101691229525915351910691 1652536844288873027866037)
                  ·
                    refine ⟨154925329152081846362441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1652536844288873027866037 154925329152081846362441)
                    ·
                      refine ⟨116193996864061384771831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 154925329152081846362441 116193996864061384771831)
                      ·
                        rfl

theorem cell23_226287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 5, 2].length) (baseStart_226287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226287 prefixEnd_226287 := by exact prefixLift 226287
  have htrace : WordTrace (prefixWord ++ tailWord_226287) baseStart_226287 baseEnd_226287 := by
    simpa [prefixWord, tailWord_226287, baseEnd_226287] using wordTrace_append hprefix tailTrace_226287
  have hstable : (prefixWord ++ tailWord_226287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226287).length < 2 ^ (prefixWord ++ tailWord_226287).sum := by decide
  have hdescent : baseEnd_226287 < baseStart_226287 := by decide
  rcases family_descends (prefixWord ++ tailWord_226287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226297 : List Nat := [1, 2, 1, 3, 1, 3, 4, 2, 1, 5]
def baseStart_226297 : Nat := 118140960795 + 226297 * 2 ^ 59
def prefixEnd_226297 : Nat := 4983230072969 + 3 ^ 40 * 226297 * 2
def baseEnd_226297 : Nat := 38733043890202115215595

theorem tailTrace_226297 : CollatzResearch.WordTrace tailWord_226297 prefixEnd_226297 38733043890202115215595 := by
  unfold tailWord_226297
  simp only [CollatzResearch.WordTrace]
  refine ⟨8253729661172092295749145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5502486440781394863832763 8253729661172092295749145)
  ·
    refine ⟨6190297245879069221811859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8253729661172092295749145 6190297245879069221811859)
    ·
      refine ⟨9285445868818603832717789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6190297245879069221811859 9285445868818603832717789)
      ·
        refine ⟨3482042200806976437269171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9285445868818603832717789 3482042200806976437269171)
        ·
          refine ⟨5223063301210464655903757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3482042200806976437269171 5223063301210464655903757)
          ·
            refine ⟨1958648737953924245963909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5223063301210464655903757 1958648737953924245963909)
            ·
              refine ⟨367246638366360796118233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1958648737953924245963909 367246638366360796118233)
              ·
                refine ⟨275434978774770597088675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367246638366360796118233 275434978774770597088675)
                ·
                  refine ⟨413152468162155895633013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275434978774770597088675 413152468162155895633013)
                  ·
                    refine ⟨38733043890202115215595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 413152468162155895633013 38733043890202115215595)
                    ·
                      rfl

theorem cell23_226297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 5].length) (baseStart_226297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226297 prefixEnd_226297 := by exact prefixLift 226297
  have htrace : WordTrace (prefixWord ++ tailWord_226297) baseStart_226297 baseEnd_226297 := by
    simpa [prefixWord, tailWord_226297, baseEnd_226297] using wordTrace_append hprefix tailTrace_226297
  have hstable : (prefixWord ++ tailWord_226297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226297).length < 2 ^ (prefixWord ++ tailWord_226297).sum := by decide
  have hdescent : baseEnd_226297 < baseStart_226297 := by decide
  rcases family_descends (prefixWord ++ tailWord_226297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226322 : List Nat := [3, 2, 5, 1, 1, 1, 3, 2, 1, 4]
def baseStart_226322 : Nat := 118140960795 + 226322 * 2 ^ 59
def prefixEnd_226322 : Nat := 4983230072969 + 3 ^ 40 * 226322 * 2
def baseEnd_226322 : Nat := 38737322895656249278057

theorem tailTrace_226322 : CollatzResearch.WordTrace tailWord_226322 prefixEnd_226322 38737322895656249278057 := by
  unfold tailWord_226322
  simp only [CollatzResearch.WordTrace]
  refine ⟨2063660371520380391352305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5503094324054347710272813 2063660371520380391352305)
  ·
    refine ⟨1547745278640285293514229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2063660371520380391352305 1547745278640285293514229)
    ·
      refine ⟨145101119872526746266959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1547745278640285293514229 145101119872526746266959)
      ·
        refine ⟨217651679808790119400439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145101119872526746266959 217651679808790119400439)
        ·
          refine ⟨326477519713185179100659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217651679808790119400439 326477519713185179100659)
          ·
            refine ⟨489716279569777768650989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326477519713185179100659 489716279569777768650989)
            ·
              refine ⟨183643604838666663244121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 489716279569777768650989 183643604838666663244121)
              ·
                refine ⟨137732703628999997433091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183643604838666663244121 137732703628999997433091)
                ·
                  refine ⟨206599055443499996149637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137732703628999997433091 206599055443499996149637)
                  ·
                    refine ⟨38737322895656249278057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 206599055443499996149637 38737322895656249278057)
                    ·
                      rfl

theorem cell23_226322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_226322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226322 prefixEnd_226322 := by exact prefixLift 226322
  have htrace : WordTrace (prefixWord ++ tailWord_226322) baseStart_226322 baseEnd_226322 := by
    simpa [prefixWord, tailWord_226322, baseEnd_226322] using wordTrace_append hprefix tailTrace_226322
  have hstable : (prefixWord ++ tailWord_226322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226322).length < 2 ^ (prefixWord ++ tailWord_226322).sum := by decide
  have hdescent : baseEnd_226322 < baseStart_226322 := by decide
  rcases family_descends (prefixWord ++ tailWord_226322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226328 : List Nat := [2, 1, 2, 3, 2, 3, 3, 2, 1, 1, 3]
def baseStart_226328 : Nat := 118140960795 + 226328 * 2 ^ 59
def prefixEnd_226328 : Nat := 4983230072969 + 3 ^ 40 * 226328 * 2
def baseEnd_226328 : Nat := 116215049570895724359143

theorem tailTrace_226328 : CollatzResearch.WordTrace tailWord_226328 prefixEnd_226328 116215049570895724359143 := by
  unfold tailWord_226328
  simp only [CollatzResearch.WordTrace]
  refine ⟨4127430162029892295063819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5503240216039856393418425 4127430162029892295063819)
  ·
    refine ⟨6191145243044838442595729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4127430162029892295063819 6191145243044838442595729)
    ·
      refine ⟨4643358932283628831946797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6191145243044838442595729 4643358932283628831946797)
      ·
        refine ⟨1741259599606360811980049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4643358932283628831946797 1741259599606360811980049)
        ·
          refine ⟨1305944699704770608985037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1741259599606360811980049 1305944699704770608985037)
          ·
            refine ⟨489729262389288978369389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1305944699704770608985037 489729262389288978369389)
            ·
              refine ⟨183648473395983366888521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 489729262389288978369389 183648473395983366888521)
              ·
                refine ⟨137736355046987525166391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183648473395983366888521 137736355046987525166391)
                ·
                  refine ⟨206604532570481287749587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137736355046987525166391 206604532570481287749587)
                  ·
                    refine ⟨309906798855721931624381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 206604532570481287749587 309906798855721931624381)
                    ·
                      refine ⟨116215049570895724359143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 309906798855721931624381 116215049570895724359143)
                      ·
                        rfl

theorem cell23_226328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_226328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226328 prefixEnd_226328 := by exact prefixLift 226328
  have htrace : WordTrace (prefixWord ++ tailWord_226328) baseStart_226328 baseEnd_226328 := by
    simpa [prefixWord, tailWord_226328, baseEnd_226328] using wordTrace_append hprefix tailTrace_226328
  have hstable : (prefixWord ++ tailWord_226328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226328).length < 2 ^ (prefixWord ++ tailWord_226328).sum := by decide
  have hdescent : baseEnd_226328 < baseStart_226328 := by decide
  rcases family_descends (prefixWord ++ tailWord_226328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226330 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6]
def baseStart_226330 : Nat := 118140960795 + 226330 * 2 ^ 59
def prefixEnd_226330 : Nat := 4983230072969 + 3 ^ 40 * 226330 * 2
def baseEnd_226330 : Nat := 116216076532204716534133

theorem tailTrace_226330 : CollatzResearch.WordTrace tailWord_226330 prefixEnd_226330 116216076532204716534133 := by
  unfold tailWord_226330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2063733317513134732925111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5503288846701692621133629 2063733317513134732925111)
  ·
    refine ⟨3095599976269702099387667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2063733317513134732925111 3095599976269702099387667)
    ·
      refine ⟨4643399964404553149081501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3095599976269702099387667 4643399964404553149081501)
      ·
        refine ⟨1741274986651707430905563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4643399964404553149081501 1741274986651707430905563)
        ·
          refine ⟨2611912479977561146358345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1741274986651707430905563 2611912479977561146358345)
          ·
            refine ⟨1958934359983170859768759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2611912479977561146358345 1958934359983170859768759)
            ·
              refine ⟨2938401539974756289653139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958934359983170859768759 2938401539974756289653139)
              ·
                refine ⟨4407602309962134434479709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938401539974756289653139 4407602309962134434479709)
                ·
                  refine ⟨1652850866235800412929891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4407602309962134434479709 1652850866235800412929891)
                  ·
                    refine ⟨2479276299353700619394837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1652850866235800412929891 2479276299353700619394837)
                    ·
                      refine ⟨116216076532204716534133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2479276299353700619394837 116216076532204716534133)
                      ·
                        rfl

theorem cell23_226330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_226330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226330 prefixEnd_226330 := by exact prefixLift 226330
  have htrace : WordTrace (prefixWord ++ tailWord_226330) baseStart_226330 baseEnd_226330 := by
    simpa [prefixWord, tailWord_226330, baseEnd_226330] using wordTrace_append hprefix tailTrace_226330
  have hstable : (prefixWord ++ tailWord_226330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226330).length < 2 ^ (prefixWord ++ tailWord_226330).sum := by decide
  have hdescent : baseEnd_226330 < baseStart_226330 := by decide
  rcases family_descends (prefixWord ++ tailWord_226330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226337 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_226337 : Nat := 118140960795 + 226337 * 2 ^ 59
def prefixEnd_226337 : Nat := 4983230072969 + 3 ^ 40 * 226337 * 2
def baseEnd_226337 : Nat := 116219670896786189146601

theorem tailTrace_226337 : CollatzResearch.WordTrace tailWord_226337 prefixEnd_226337 116219670896786189146601 := by
  unfold tailWord_226337
  simp only [CollatzResearch.WordTrace]
  refine ⟨8255188581027179127205265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5503459054018119418136843 8255188581027179127205265)
  ·
    refine ⟨6191391435770384345403949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8255188581027179127205265 6191391435770384345403949)
    ·
      refine ⟨2321771788413894129526481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6191391435770384345403949 2321771788413894129526481)
      ·
        refine ⟨1741328841310420597144861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2321771788413894129526481 1741328841310420597144861)
        ·
          refine ⟨652998315491407723929323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1741328841310420597144861 652998315491407723929323)
          ·
            refine ⟨979497473237111585893985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652998315491407723929323 979497473237111585893985)
            ·
              refine ⟨734623104927833689420489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 979497473237111585893985 734623104927833689420489)
              ·
                refine ⟨550967328695875267065367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734623104927833689420489 550967328695875267065367)
                ·
                  refine ⟨826450993043812900598051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 550967328695875267065367 826450993043812900598051)
                  ·
                    refine ⟨1239676489565719350897077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 826450993043812900598051 1239676489565719350897077)
                    ·
                      refine ⟨116219670896786189146601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1239676489565719350897077 116219670896786189146601)
                      ·
                        rfl

theorem cell23_226337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_226337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226337 prefixEnd_226337 := by exact prefixLift 226337
  have htrace : WordTrace (prefixWord ++ tailWord_226337) baseStart_226337 baseEnd_226337 := by
    simpa [prefixWord, tailWord_226337, baseEnd_226337] using wordTrace_append hprefix tailTrace_226337
  have hstable : (prefixWord ++ tailWord_226337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226337).length < 2 ^ (prefixWord ++ tailWord_226337).sum := by decide
  have hdescent : baseEnd_226337 < baseStart_226337 := by decide
  rcases family_descends (prefixWord ++ tailWord_226337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226398 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_226398 : Nat := 118140960795 + 226398 * 2 ^ 59
def prefixEnd_226398 : Nat := 4983230072969 + 3 ^ 40 * 226398 * 2
def baseEnd_226398 : Nat := 116250993216710450483821

theorem tailTrace_226398 : CollatzResearch.WordTrace tailWord_226398 prefixEnd_226398 116250993216710450483821 := by
  unfold tailWord_226398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1032176679225773318146981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5504942289204124363450565 1032176679225773318146981)
  ·
    refine ⟨193533127354832497152559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1032176679225773318146981 193533127354832497152559)
    ·
      refine ⟨290299691032248745728839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193533127354832497152559 290299691032248745728839)
      ·
        refine ⟨435449536548373118593259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290299691032248745728839 435449536548373118593259)
        ·
          refine ⟨653174304822559677889889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435449536548373118593259 653174304822559677889889)
          ·
            refine ⟨489880728616919758417417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 653174304822559677889889 489880728616919758417417)
            ·
              refine ⟨367410546462689818813063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489880728616919758417417 367410546462689818813063)
              ·
                refine ⟨551115819694034728219595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367410546462689818813063 551115819694034728219595)
                ·
                  refine ⟨826673729541052092329393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 551115819694034728219595 826673729541052092329393)
                  ·
                    refine ⟨620005297155789069247045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 826673729541052092329393 620005297155789069247045)
                    ·
                      refine ⟨116250993216710450483821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 620005297155789069247045 116250993216710450483821)
                      ·
                        rfl

theorem cell23_226398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_226398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226398 prefixEnd_226398 := by exact prefixLift 226398
  have htrace : WordTrace (prefixWord ++ tailWord_226398) baseStart_226398 baseEnd_226398 := by
    simpa [prefixWord, tailWord_226398, baseEnd_226398] using wordTrace_append hprefix tailTrace_226398
  have hstable : (prefixWord ++ tailWord_226398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226398).length < 2 ^ (prefixWord ++ tailWord_226398).sum := by decide
  have hdescent : baseEnd_226398 < baseStart_226398 := by decide
  rcases family_descends (prefixWord ++ tailWord_226398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226424 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 1, 4, 2]
def baseStart_226424 : Nat := 118140960795 + 226424 * 2 ^ 59
def prefixEnd_226424 : Nat := 4983230072969 + 3 ^ 40 * 226424 * 2
def baseEnd_226424 : Nat := 116264343713727348758701

theorem tailTrace_226424 : CollatzResearch.WordTrace tailWord_226424 prefixEnd_226424 116264343713727348758701 := by
  unfold tailWord_226424
  simp only [CollatzResearch.WordTrace]
  refine ⟨4129180865855996492811163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5505574487807995323748217 4129180865855996492811163)
  ·
    refine ⟨6193771298783994739216745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4129180865855996492811163 6193771298783994739216745)
    ·
      refine ⟨4645328474087996054412559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6193771298783994739216745 4645328474087996054412559)
      ·
        refine ⟨6967992711131994081618839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4645328474087996054412559 6967992711131994081618839)
        ·
          refine ⟨10451989066697991122428259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6967992711131994081618839 10451989066697991122428259)
          ·
            refine ⟨15677983600046986683642389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10451989066697991122428259 15677983600046986683642389)
            ·
              refine ⟨734905481252202500795737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15677983600046986683642389 734905481252202500795737)
              ·
                refine ⟨551179110939151875596803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734905481252202500795737 551179110939151875596803)
                ·
                  refine ⟨826768666408727813395205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 551179110939151875596803 826768666408727813395205)
                  ·
                    refine ⟨155019124951636465011601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 826768666408727813395205 155019124951636465011601)
                    ·
                      refine ⟨116264343713727348758701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 155019124951636465011601 116264343713727348758701)
                      ·
                        rfl

theorem cell23_226424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 1, 4, 2].length) (baseStart_226424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226424 prefixEnd_226424 := by exact prefixLift 226424
  have htrace : WordTrace (prefixWord ++ tailWord_226424) baseStart_226424 baseEnd_226424 := by
    simpa [prefixWord, tailWord_226424, baseEnd_226424] using wordTrace_append hprefix tailTrace_226424
  have hstable : (prefixWord ++ tailWord_226424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226424).length < 2 ^ (prefixWord ++ tailWord_226424).sum := by decide
  have hdescent : baseEnd_226424 < baseStart_226424 := by decide
  rcases family_descends (prefixWord ++ tailWord_226424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226441 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 4, 2, 2]
def baseStart_226441 : Nat := 118140960795 + 226441 * 2 ^ 59
def prefixEnd_226441 : Nat := 4983230072969 + 3 ^ 40 * 226441 * 2
def baseEnd_226441 : Nat := 116273072884853782246123

theorem tailTrace_226441 : CollatzResearch.WordTrace tailWord_226441 prefixEnd_226441 116273072884853782246123 := by
  unfold tailWord_226441
  simp only [CollatzResearch.WordTrace]
  refine ⟨8258981772650404888991177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5505987848433603259327451 8258981772650404888991177)
  ·
    refine ⟨6194236329487803666743383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8258981772650404888991177 6194236329487803666743383)
    ·
      refine ⟨9291354494231705500115075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6194236329487803666743383 9291354494231705500115075)
      ·
        refine ⟨13937031741347558250172613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9291354494231705500115075 13937031741347558250172613)
        ·
          refine ⟨2613193451502667171907365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13937031741347558250172613 2613193451502667171907365)
          ·
            refine ⟨489973772156750094732631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2613193451502667171907365 489973772156750094732631)
            ·
              refine ⟨734960658235125142098947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489973772156750094732631 734960658235125142098947)
              ·
                refine ⟨1102440987352687713148421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734960658235125142098947 1102440987352687713148421)
                ·
                  refine ⟨206707685128628946215329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1102440987352687713148421 206707685128628946215329)
                  ·
                    refine ⟨155030763846471709661497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 206707685128628946215329 155030763846471709661497)
                    ·
                      refine ⟨116273072884853782246123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 155030763846471709661497 116273072884853782246123)
                      ·
                        rfl

theorem cell23_226441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 2, 2].length) (baseStart_226441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226441 prefixEnd_226441 := by exact prefixLift 226441
  have htrace : WordTrace (prefixWord ++ tailWord_226441) baseStart_226441 baseEnd_226441 := by
    simpa [prefixWord, tailWord_226441, baseEnd_226441] using wordTrace_append hprefix tailTrace_226441
  have hstable : (prefixWord ++ tailWord_226441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226441).length < 2 ^ (prefixWord ++ tailWord_226441).sum := by decide
  have hdescent : baseEnd_226441 < baseStart_226441 := by decide
  rcases family_descends (prefixWord ++ tailWord_226441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226458 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2]
def baseStart_226458 : Nat := 118140960795 + 226458 * 2 ^ 59
def prefixEnd_226458 : Nat := 4983230072969 + 3 ^ 40 * 226458 * 2
def baseEnd_226458 : Nat := 116281802055980215733545

theorem tailTrace_226458 : CollatzResearch.WordTrace tailWord_226458 prefixEnd_226458 116281802055980215733545 := by
  unfold tailWord_226458
  simp only [CollatzResearch.WordTrace]
  refine ⟨2064900453397204198090007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5506401209059211194906685 2064900453397204198090007)
  ·
    refine ⟨3097350680095806297135011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2064900453397204198090007 3097350680095806297135011)
    ·
      refine ⟨4646026020143709445702517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3097350680095806297135011 4646026020143709445702517)
      ·
        refine ⟨435564939388472760534611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4646026020143709445702517 435564939388472760534611)
        ·
          refine ⟨653347409082709140801917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435564939388472760534611 653347409082709140801917)
          ·
            refine ⟨245005278406015927800719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 653347409082709140801917 245005278406015927800719)
            ·
              refine ⟨367507917609023891701079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245005278406015927800719 367507917609023891701079)
              ·
                refine ⟨551261876413535837551619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367507917609023891701079 551261876413535837551619)
                ·
                  refine ⟨826892814620303756327429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 551261876413535837551619 826892814620303756327429)
                  ·
                    refine ⟨155042402741306954311393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 826892814620303756327429 155042402741306954311393)
                    ·
                      refine ⟨116281802055980215733545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 155042402741306954311393 116281802055980215733545)
                      ·
                        rfl

theorem cell23_226458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_226458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226458 prefixEnd_226458 := by exact prefixLift 226458
  have htrace : WordTrace (prefixWord ++ tailWord_226458) baseStart_226458 baseEnd_226458 := by
    simpa [prefixWord, tailWord_226458, baseEnd_226458] using wordTrace_append hprefix tailTrace_226458
  have hstable : (prefixWord ++ tailWord_226458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226458).length < 2 ^ (prefixWord ++ tailWord_226458).sum := by decide
  have hdescent : baseEnd_226458 < baseStart_226458 := by decide
  rcases family_descends (prefixWord ++ tailWord_226458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226481 : List Nat := [1, 2, 2, 5, 1, 1, 3, 3, 5]
def baseStart_226481 : Nat := 118140960795 + 226481 * 2 ^ 59
def prefixEnd_226481 : Nat := 4983230072969 + 3 ^ 40 * 226481 * 2
def baseEnd_226481 : Nat := 12921512456781513971771

theorem tailTrace_226481 : CollatzResearch.WordTrace tailWord_226481 prefixEnd_226481 12921512456781513971771 := by
  unfold tailWord_226481
  simp only [CollatzResearch.WordTrace]
  refine ⟨8260440692505491720447297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5506960461670327813631531 8260440692505491720447297)
  ·
    refine ⟨6195330519379118790335473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8260440692505491720447297 6195330519379118790335473)
    ·
      refine ⟨4646497889534339092751605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6195330519379118790335473 4646497889534339092751605)
      ·
        refine ⟨435609177143844289945463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4646497889534339092751605 435609177143844289945463)
        ·
          refine ⟨653413765715766434918195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435609177143844289945463 653413765715766434918195)
          ·
            refine ⟨980120648573649652377293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653413765715766434918195 980120648573649652377293)
            ·
              refine ⟨367545243215118619641485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 980120648573649652377293 367545243215118619641485)
              ·
                refine ⟨137829466205669482365557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 367545243215118619641485 137829466205669482365557)
                ·
                  refine ⟨12921512456781513971771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137829466205669482365557 12921512456781513971771)
                  ·
                    rfl

theorem cell23_226481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 5].length) (baseStart_226481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226481 prefixEnd_226481 := by exact prefixLift 226481
  have htrace : WordTrace (prefixWord ++ tailWord_226481) baseStart_226481 baseEnd_226481 := by
    simpa [prefixWord, tailWord_226481, baseEnd_226481] using wordTrace_append hprefix tailTrace_226481
  have hstable : (prefixWord ++ tailWord_226481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226481).length < 2 ^ (prefixWord ++ tailWord_226481).sum := by decide
  have hdescent : baseEnd_226481 < baseStart_226481 := by decide
  rcases family_descends (prefixWord ++ tailWord_226481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226487 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 5]
def baseStart_226487 : Nat := 118140960795 + 226487 * 2 ^ 59
def prefixEnd_226487 : Nat := 4983230072969 + 3 ^ 40 * 226487 * 2
def baseEnd_226487 : Nat := 116296692994960602270911

theorem tailTrace_226487 : CollatzResearch.WordTrace tailWord_226487 prefixEnd_226487 116296692994960602270911 := by
  unfold tailWord_226487
  simp only [CollatzResearch.WordTrace]
  refine ⟨8260659530483754745165715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5507106353655836496777143 8260659530483754745165715)
  ·
    refine ⟨12390989295725632117748573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8260659530483754745165715 12390989295725632117748573)
    ·
      refine ⟨4646620985897112044155715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12390989295725632117748573 4646620985897112044155715)
      ·
        refine ⟨6969931478845668066233573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4646620985897112044155715 6969931478845668066233573)
        ·
          refine ⟨1306862152283562762418795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6969931478845668066233573 1306862152283562762418795)
          ·
            refine ⟨1960293228425344143628193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306862152283562762418795 1960293228425344143628193)
            ·
              refine ⟨1470219921319008107721145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1960293228425344143628193 1470219921319008107721145)
              ·
                refine ⟨1102664940989256080790859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1470219921319008107721145 1102664940989256080790859)
                ·
                  refine ⟨1653997411483884121186289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102664940989256080790859 1653997411483884121186289)
                  ·
                    refine ⟨1240498058612913090889717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1653997411483884121186289 1240498058612913090889717)
                    ·
                      refine ⟨116296692994960602270911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1240498058612913090889717 116296692994960602270911)
                      ·
                        rfl

theorem cell23_226487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_226487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226487 prefixEnd_226487 := by exact prefixLift 226487
  have htrace : WordTrace (prefixWord ++ tailWord_226487) baseStart_226487 baseEnd_226487 := by
    simpa [prefixWord, tailWord_226487, baseEnd_226487] using wordTrace_append hprefix tailTrace_226487
  have hstable : (prefixWord ++ tailWord_226487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226487).length < 2 ^ (prefixWord ++ tailWord_226487).sum := by decide
  have hdescent : baseEnd_226487 < baseStart_226487 := by decide
  rcases family_descends (prefixWord ++ tailWord_226487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226494 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_226494 : Nat := 118140960795 + 226494 * 2 ^ 59
def prefixEnd_226494 : Nat := 4983230072969 + 3 ^ 40 * 226494 * 2
def baseEnd_226494 : Nat := 38766762453180691627793

theorem tailTrace_226494 : CollatzResearch.WordTrace tailWord_226494 prefixEnd_226494 38766762453180691627793 := by
  unfold tailWord_226494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1032614355182299367583817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5507276560972263293780357 1032614355182299367583817)
  ·
    refine ⟨774460766386724525687863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1032614355182299367583817 774460766386724525687863)
    ·
      refine ⟨1161691149580086788531795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 774460766386724525687863 1161691149580086788531795)
      ·
        refine ⟨1742536724370130182797693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1161691149580086788531795 1742536724370130182797693)
        ·
          refine ⟨653451271638798818549135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1742536724370130182797693 653451271638798818549135)
          ·
            refine ⟨980176907458198227823703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653451271638798818549135 980176907458198227823703)
            ·
              refine ⟨1470265361187297341735555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980176907458198227823703 1470265361187297341735555)
              ·
                refine ⟨2205398041780946012603333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470265361187297341735555 2205398041780946012603333)
                ·
                  refine ⟨413512132833927377363125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205398041780946012603333 413512132833927377363125)
                  ·
                    refine ⟨38766762453180691627793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 413512132833927377363125 38766762453180691627793)
                    ·
                      rfl

theorem cell23_226494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_226494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226494 prefixEnd_226494 := by exact prefixLift 226494
  have htrace : WordTrace (prefixWord ++ tailWord_226494) baseStart_226494 baseEnd_226494 := by
    simpa [prefixWord, tailWord_226494, baseEnd_226494] using wordTrace_append hprefix tailTrace_226494
  have hstable : (prefixWord ++ tailWord_226494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226494).length < 2 ^ (prefixWord ++ tailWord_226494).sum := by decide
  have hdescent : baseEnd_226494 < baseStart_226494 := by decide
  rcases family_descends (prefixWord ++ tailWord_226494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226514 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_226514 : Nat := 118140960795 + 226514 * 2 ^ 59
def prefixEnd_226514 : Nat := 4983230072969 + 3 ^ 40 * 226514 * 2
def baseEnd_226514 : Nat := 116310556972631996633287

theorem tailTrace_226514 : CollatzResearch.WordTrace tailWord_226514 prefixEnd_226514 116310556972631996633287 := by
  unfold tailWord_226514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2065411075346484589099649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5507762867590625570932397 2065411075346484589099649)
  ·
    refine ⟨1549058306509863441824737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2065411075346484589099649 1549058306509863441824737)
    ·
      refine ⟨1161793729882397581368553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1549058306509863441824737 1161793729882397581368553)
      ·
        refine ⟨871345297411798186026415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1161793729882397581368553 871345297411798186026415)
        ·
          refine ⟨1307017946117697279039623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871345297411798186026415 1307017946117697279039623)
          ·
            refine ⟨1960526919176545918559435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307017946117697279039623 1960526919176545918559435)
            ·
              refine ⟨2940790378764818877839153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960526919176545918559435 2940790378764818877839153)
              ·
                refine ⟨2205592784073614158379365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2940790378764818877839153 2205592784073614158379365)
                ·
                  refine ⟨413548647013802654696131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205592784073614158379365 413548647013802654696131)
                  ·
                    refine ⟨620322970520703982044197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 413548647013802654696131 620322970520703982044197)
                    ·
                      refine ⟨116310556972631996633287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 620322970520703982044197 116310556972631996633287)
                      ·
                        rfl

theorem cell23_226514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_226514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226514 prefixEnd_226514 := by exact prefixLift 226514
  have htrace : WordTrace (prefixWord ++ tailWord_226514) baseStart_226514 baseEnd_226514 := by
    simpa [prefixWord, tailWord_226514, baseEnd_226514] using wordTrace_append hprefix tailTrace_226514
  have hstable : (prefixWord ++ tailWord_226514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226514).length < 2 ^ (prefixWord ++ tailWord_226514).sum := by decide
  have hdescent : baseEnd_226514 < baseStart_226514 := by decide
  rcases family_descends (prefixWord ++ tailWord_226514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226527 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 4]
def baseStart_226527 : Nat := 118140960795 + 226527 * 2 ^ 59
def prefixEnd_226527 : Nat := 4983230072969 + 3 ^ 40 * 226527 * 2
def baseEnd_226527 : Nat := 116317232221140445770727

theorem tailTrace_226527 : CollatzResearch.WordTrace tailWord_226527 prefixEnd_226527 116317232221140445770727 := by
  unfold tailWord_226527
  simp only [CollatzResearch.WordTrace]
  refine ⟨8262118450338841576621835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5508078966892561051081223 8262118450338841576621835)
  ·
    refine ⟨12393177675508262364932753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8262118450338841576621835 12393177675508262364932753)
    ·
      refine ⟨9294883256631196773699565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12393177675508262364932753 9294883256631196773699565)
      ·
        refine ⟨3485581221236698790137337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9294883256631196773699565 3485581221236698790137337)
        ·
          refine ⟨2614185915927524092603003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3485581221236698790137337 2614185915927524092603003)
          ·
            refine ⟨3921278873891286138904505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2614185915927524092603003 3921278873891286138904505)
            ·
              refine ⟨2940959155418464604178379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3921278873891286138904505 2940959155418464604178379)
              ·
                refine ⟨4411438733127696906267569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940959155418464604178379 4411438733127696906267569)
                ·
                  refine ⟨3308579049845772679700677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4411438733127696906267569 3308579049845772679700677)
                  ·
                    refine ⟨620358571846082377443877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3308579049845772679700677 620358571846082377443877)
                    ·
                      refine ⟨116317232221140445770727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 620358571846082377443877 116317232221140445770727)
                      ·
                        rfl

theorem cell23_226527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_226527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226527 prefixEnd_226527 := by exact prefixLift 226527
  have htrace : WordTrace (prefixWord ++ tailWord_226527) baseStart_226527 baseEnd_226527 := by
    simpa [prefixWord, tailWord_226527, baseEnd_226527] using wordTrace_append hprefix tailTrace_226527
  have hstable : (prefixWord ++ tailWord_226527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226527).length < 2 ^ (prefixWord ++ tailWord_226527).sum := by decide
  have hdescent : baseEnd_226527 < baseStart_226527 := by decide
  rcases family_descends (prefixWord ++ tailWord_226527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226554 : List Nat := [3, 1, 1, 1, 1, 4, 4, 2, 6]
def baseStart_226554 : Nat := 118140960795 + 226554 * 2 ^ 59
def prefixEnd_226554 : Nat := 4983230072969 + 3 ^ 40 * 226554 * 2
def baseEnd_226554 : Nat := 12925677355423537792567

theorem tailTrace_226554 : CollatzResearch.WordTrace tailWord_226554 prefixEnd_226554 12925677355423537792567 := by
  unfold tailWord_226554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2065775805310256296963679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5508735480827350125236477 2065775805310256296963679)
  ·
    refine ⟨3098663707965384445445519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2065775805310256296963679 3098663707965384445445519)
    ·
      refine ⟨4647995561948076668168279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3098663707965384445445519 4647995561948076668168279)
      ·
        refine ⟨6971993342922115002252419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4647995561948076668168279 6971993342922115002252419)
        ·
          refine ⟨10457990014383172503378629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6971993342922115002252419 10457990014383172503378629)
          ·
            refine ⟨1960873127696844844383493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10457990014383172503378629 1960873127696844844383493)
            ·
              refine ⟨367663711443158408321905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1960873127696844844383493 367663711443158408321905)
              ·
                refine ⟨275747783582368806241429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367663711443158408321905 275747783582368806241429)
                ·
                  refine ⟨12925677355423537792567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 275747783582368806241429 12925677355423537792567)
                  ·
                    rfl

theorem cell23_226554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 6].length) (baseStart_226554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226554 prefixEnd_226554 := by exact prefixLift 226554
  have htrace : WordTrace (prefixWord ++ tailWord_226554) baseStart_226554 baseEnd_226554 := by
    simpa [prefixWord, tailWord_226554, baseEnd_226554] using wordTrace_append hprefix tailTrace_226554
  have hstable : (prefixWord ++ tailWord_226554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226554).length < 2 ^ (prefixWord ++ tailWord_226554).sum := by decide
  have hdescent : baseEnd_226554 < baseStart_226554 := by decide
  rcases family_descends (prefixWord ++ tailWord_226554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226577 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 7]
def baseStart_226577 : Nat := 118140960795 + 226577 * 2 ^ 59
def prefixEnd_226577 : Nat := 4983230072969 + 3 ^ 40 * 226577 * 2
def baseEnd_226577 : Nat := 116342906253865250145497

theorem tailTrace_226577 : CollatzResearch.WordTrace tailWord_226577 prefixEnd_226577 116342906253865250145497 := by
  unfold tailWord_226577
  simp only [CollatzResearch.WordTrace]
  refine ⟨8263942100157700115941985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5509294733438466743961323 8263942100157700115941985)
  ·
    refine ⟨6197956575118275086956489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8263942100157700115941985 6197956575118275086956489)
    ·
      refine ⟨4648467431338706315217367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6197956575118275086956489 4648467431338706315217367)
      ·
        refine ⟨6972701147008059472826051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4648467431338706315217367 6972701147008059472826051)
        ·
          refine ⟨10459051720512089209239077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6972701147008059472826051 10459051720512089209239077)
          ·
            refine ⟨1961072197596016726732327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10459051720512089209239077 1961072197596016726732327)
            ·
              refine ⟨2941608296394025090098491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1961072197596016726732327 2941608296394025090098491)
              ·
                refine ⟨4412412444591037635147737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941608296394025090098491 4412412444591037635147737)
                ·
                  refine ⟨3309309333443278226360803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4412412444591037635147737 3309309333443278226360803)
                  ·
                    refine ⟨4963964000164917339541205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3309309333443278226360803 4963964000164917339541205)
                    ·
                      refine ⟨116342906253865250145497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4963964000164917339541205 116342906253865250145497)
                      ·
                        rfl

theorem cell23_226577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_226577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226577 prefixEnd_226577 := by exact prefixLift 226577
  have htrace : WordTrace (prefixWord ++ tailWord_226577) baseStart_226577 baseEnd_226577 := by
    simpa [prefixWord, tailWord_226577, baseEnd_226577] using wordTrace_append hprefix tailTrace_226577
  have hstable : (prefixWord ++ tailWord_226577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226577).length < 2 ^ (prefixWord ++ tailWord_226577).sum := by decide
  have hdescent : baseEnd_226577 < baseStart_226577 := by decide
  rcases family_descends (prefixWord ++ tailWord_226577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226584 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 3, 5]
def baseStart_226584 : Nat := 118140960795 + 226584 * 2 ^ 59
def prefixEnd_226584 : Nat := 4983230072969 + 3 ^ 40 * 226584 * 2
def baseEnd_226584 : Nat := 38782166872815574252655

theorem tailTrace_226584 : CollatzResearch.WordTrace tailWord_226584 prefixEnd_226584 38782166872815574252655 := by
  unfold tailWord_226584
  simp only [CollatzResearch.WordTrace]
  refine ⟨4132098705566170155723403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5509464940754893540964537 4132098705566170155723403)
  ·
    refine ⟨6198148058349255233585105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4132098705566170155723403 6198148058349255233585105)
    ·
      refine ⟨4648611043761941425188829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6198148058349255233585105 4648611043761941425188829)
      ·
        refine ⟨1743229141410728034445811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4648611043761941425188829 1743229141410728034445811)
        ·
          refine ⟨2614843712116092051668717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1743229141410728034445811 2614843712116092051668717)
          ·
            refine ⟨980566392043534519375769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2614843712116092051668717 980566392043534519375769)
            ·
              refine ⟨735424794032650889531827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980566392043534519375769 735424794032650889531827)
              ·
                refine ⟨1103137191048976334297741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 735424794032650889531827 1103137191048976334297741)
                ·
                  refine ⟨413676446643366125361653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1103137191048976334297741 413676446643366125361653)
                  ·
                    refine ⟨38782166872815574252655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 413676446643366125361653 38782166872815574252655)
                    ·
                      rfl

theorem cell23_226584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_226584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226584 prefixEnd_226584 := by exact prefixLift 226584
  have htrace : WordTrace (prefixWord ++ tailWord_226584) baseStart_226584 baseEnd_226584 := by
    simpa [prefixWord, tailWord_226584, baseEnd_226584] using wordTrace_append hprefix tailTrace_226584
  have hstable : (prefixWord ++ tailWord_226584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226584).length < 2 ^ (prefixWord ++ tailWord_226584).sum := by decide
  have hdescent : baseEnd_226584 < baseStart_226584 := by decide
  rcases family_descends (prefixWord ++ tailWord_226584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226624 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 5]
def baseStart_226624 : Nat := 118140960795 + 226624 * 2 ^ 59
def prefixEnd_226624 : Nat := 4983230072969 + 3 ^ 40 * 226624 * 2
def baseEnd_226624 : Nat := 116367039844626566257781

theorem tailTrace_226624 : CollatzResearch.WordTrace tailWord_226624 prefixEnd_226624 116367039844626566257781 := by
  unfold tailWord_226624
  simp only [CollatzResearch.WordTrace]
  refine ⟨4132828165493713571451463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5510437553991618095268617 4132828165493713571451463)
  ·
    refine ⟨6199242248240570357177195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4132828165493713571451463 6199242248240570357177195)
    ·
      refine ⟨9298863372360855535765793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6199242248240570357177195 9298863372360855535765793)
      ·
        refine ⟨6974147529270641651824345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9298863372360855535765793 6974147529270641651824345)
        ·
          refine ⟨5230610646952981238868259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6974147529270641651824345 5230610646952981238868259)
          ·
            refine ⟨7845915970429471858302389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5230610646952981238868259 7845915970429471858302389)
            ·
              refine ⟨735554622227762986715849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7845915970429471858302389 735554622227762986715849)
              ·
                refine ⟨551665966670822240036887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735554622227762986715849 551665966670822240036887)
                ·
                  refine ⟨827498950006233360055331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 551665966670822240036887 827498950006233360055331)
                  ·
                    refine ⟨1241248425009350040082997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 827498950006233360055331 1241248425009350040082997)
                    ·
                      refine ⟨116367039844626566257781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1241248425009350040082997 116367039844626566257781)
                      ·
                        rfl

theorem cell23_226624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_226624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226624 prefixEnd_226624 := by exact prefixLift 226624
  have htrace : WordTrace (prefixWord ++ tailWord_226624) baseStart_226624 baseEnd_226624 := by
    simpa [prefixWord, tailWord_226624, baseEnd_226624] using wordTrace_append hprefix tailTrace_226624
  have hstable : (prefixWord ++ tailWord_226624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226624).length < 2 ^ (prefixWord ++ tailWord_226624).sum := by decide
  have hdescent : baseEnd_226624 < baseStart_226624 := by decide
  rcases family_descends (prefixWord ++ tailWord_226624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226627 : List Nat := [1, 1, 1, 3, 1, 3, 1, 12]
def baseStart_226627 : Nat := 118140960795 + 226627 * 2 ^ 59
def prefixEnd_226627 : Nat := 4983230072969 + 3 ^ 40 * 226627 * 2
def baseEnd_226627 : Nat := 4309947418021853871121

theorem tailTrace_226627 : CollatzResearch.WordTrace tailWord_226627 prefixEnd_226627 4309947418021853871121 := by
  unfold tailWord_226627
  simp only [CollatzResearch.WordTrace]
  refine ⟨8265765749976558655262135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5510510499984372436841423 8265765749976558655262135)
  ·
    refine ⟨12398648624964837982893203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8265765749976558655262135 12398648624964837982893203)
    ·
      refine ⟨18597972937447256974339805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12398648624964837982893203 18597972937447256974339805)
      ·
        refine ⟨6974239851542721365377427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18597972937447256974339805 6974239851542721365377427)
        ·
          refine ⟨10461359777314082048066141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6974239851542721365377427 10461359777314082048066141)
          ·
            refine ⟨3923009916492780768024803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10461359777314082048066141 3923009916492780768024803)
            ·
              refine ⟨5884514874739171152037205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3923009916492780768024803 5884514874739171152037205)
              ·
                refine ⟨4309947418021853871121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 5884514874739171152037205 4309947418021853871121)
                ·
                  rfl

theorem cell23_226627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 12].length) (baseStart_226627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226627 prefixEnd_226627 := by exact prefixLift 226627
  have htrace : WordTrace (prefixWord ++ tailWord_226627) baseStart_226627 baseEnd_226627 := by
    simpa [prefixWord, tailWord_226627, baseEnd_226627] using wordTrace_append hprefix tailTrace_226627
  have hstable : (prefixWord ++ tailWord_226627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226627).length < 2 ^ (prefixWord ++ tailWord_226627).sum := by decide
  have hdescent : baseEnd_226627 < baseStart_226627 := by decide
  rcases family_descends (prefixWord ++ tailWord_226627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226631 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 1, 6]
def baseStart_226631 : Nat := 118140960795 + 226631 * 2 ^ 59
def prefixEnd_226631 : Nat := 4983230072969 + 3 ^ 40 * 226631 * 2
def baseEnd_226631 : Nat := 38790211403069346290083

theorem tailTrace_226631 : CollatzResearch.WordTrace tailWord_226631 prefixEnd_226631 38790211403069346290083 := by
  unfold tailWord_226631
  simp only [CollatzResearch.WordTrace]
  refine ⟨8265911641962067338407747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5510607761308044892271831 8265911641962067338407747)
  ·
    refine ⟨12398867462943101007611621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8265911641962067338407747 12398867462943101007611621)
    ·
      refine ⟨2324787649301831438927179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12398867462943101007611621 2324787649301831438927179)
      ·
        refine ⟨3487181473952747158390769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2324787649301831438927179 3487181473952747158390769)
        ·
          refine ⟨2615386105464560368793077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3487181473952747158390769 2615386105464560368793077)
          ·
            refine ⟨245192447387302534574351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2615386105464560368793077 245192447387302534574351)
            ·
              refine ⟨367788671080953801861527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245192447387302534574351 367788671080953801861527)
              ·
                refine ⟨551683006621430702792291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367788671080953801861527 551683006621430702792291)
                ·
                  refine ⟨827524509932146054188437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 551683006621430702792291 827524509932146054188437)
                  ·
                    refine ⟨38790211403069346290083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 827524509932146054188437 38790211403069346290083)
                    ·
                      rfl

theorem cell23_226631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_226631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226631 prefixEnd_226631 := by exact prefixLift 226631
  have htrace : WordTrace (prefixWord ++ tailWord_226631) baseStart_226631 baseEnd_226631 := by
    simpa [prefixWord, tailWord_226631, baseEnd_226631] using wordTrace_append hprefix tailTrace_226631
  have hstable : (prefixWord ++ tailWord_226631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226631).length < 2 ^ (prefixWord ++ tailWord_226631).sum := by decide
  have hdescent : baseEnd_226631 < baseStart_226631 := by decide
  rcases family_descends (prefixWord ++ tailWord_226631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226638 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2]
def baseStart_226638 : Nat := 118140960795 + 226638 * 2 ^ 59
def prefixEnd_226638 : Nat := 4983230072969 + 3 ^ 40 * 226638 * 2
def baseEnd_226638 : Nat := 116374228573789511482717

theorem tailTrace_226638 : CollatzResearch.WordTrace tailWord_226638 prefixEnd_226638 116374228573789511482717 := by
  unfold tailWord_226638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1033270869117088441739071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5510777968624471689275045 1033270869117088441739071)
  ·
    refine ⟨1549906303675632662608607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1033270869117088441739071 1549906303675632662608607)
    ·
      refine ⟨2324859455513448993912911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1549906303675632662608607 2324859455513448993912911)
      ·
        refine ⟨3487289183270173490869367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2324859455513448993912911 3487289183270173490869367)
        ·
          refine ⟨5230933774905260236304051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3487289183270173490869367 5230933774905260236304051)
          ·
            refine ⟨7846400662357890354456077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5230933774905260236304051 7846400662357890354456077)
            ·
              refine ⟨2942400248384208882921029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7846400662357890354456077 2942400248384208882921029)
              ·
                refine ⟨551700046572039165547693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2942400248384208882921029 551700046572039165547693)
                ·
                  refine ⟨206887517464514687080385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 551700046572039165547693 206887517464514687080385)
                  ·
                    refine ⟨155165638098386015310289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 206887517464514687080385 155165638098386015310289)
                    ·
                      refine ⟨116374228573789511482717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 155165638098386015310289 116374228573789511482717)
                      ·
                        rfl

theorem cell23_226638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_226638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226638 prefixEnd_226638 := by exact prefixLift 226638
  have htrace : WordTrace (prefixWord ++ tailWord_226638) baseStart_226638 baseEnd_226638 := by
    simpa [prefixWord, tailWord_226638, baseEnd_226638] using wordTrace_append hprefix tailTrace_226638
  have hstable : (prefixWord ++ tailWord_226638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226638).length < 2 ^ (prefixWord ++ tailWord_226638).sum := by decide
  have hdescent : baseEnd_226638 < baseStart_226638 := by decide
  rcases family_descends (prefixWord ++ tailWord_226638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226644 : List Nat := [2, 4, 1, 1, 2, 1, 3, 9]
def baseStart_226644 : Nat := 118140960795 + 226644 * 2 ^ 59
def prefixEnd_226644 : Nat := 4983230072969 + 3 ^ 40 * 226644 * 2
def baseEnd_226644 : Nat := 4310270720656166222507

theorem tailTrace_226644 : CollatzResearch.WordTrace tailWord_226644 prefixEnd_226644 4310270720656166222507 := by
  unfold tailWord_226644
  simp only [CollatzResearch.WordTrace]
  refine ⟨4133192895457485279315493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5510923860609980372420657 4133192895457485279315493)
  ·
    refine ⟨774973667898278489871655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4133192895457485279315493 774973667898278489871655)
    ·
      refine ⟨1162460501847417734807483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 774973667898278489871655 1162460501847417734807483)
      ·
        refine ⟨1743690752771126602211225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1162460501847417734807483 1743690752771126602211225)
        ·
          refine ⟨1307768064578344951658419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1743690752771126602211225 1307768064578344951658419)
          ·
            refine ⟨1961652096867517427487629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307768064578344951658419 1961652096867517427487629)
            ·
              refine ⟨735619536325319035307861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1961652096867517427487629 735619536325319035307861)
              ·
                refine ⟨4310270720656166222507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 735619536325319035307861 4310270720656166222507)
                ·
                  rfl

theorem cell23_226644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 9].length) (baseStart_226644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226644 prefixEnd_226644 := by exact prefixLift 226644
  have htrace : WordTrace (prefixWord ++ tailWord_226644) baseStart_226644 baseEnd_226644 := by
    simpa [prefixWord, tailWord_226644, baseEnd_226644] using wordTrace_append hprefix tailTrace_226644
  have hstable : (prefixWord ++ tailWord_226644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226644).length < 2 ^ (prefixWord ++ tailWord_226644).sum := by decide
  have hdescent : baseEnd_226644 < baseStart_226644 := by decide
  rcases family_descends (prefixWord ++ tailWord_226644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226658 : List Nat := [3, 3, 2, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_226658 : Nat := 118140960795 + 226658 * 2 ^ 59
def prefixEnd_226658 : Nat := 4983230072969 + 3 ^ 40 * 226658 * 2
def baseEnd_226658 : Nat := 116384498186879433232625

theorem tailTrace_226658 : CollatzResearch.WordTrace tailWord_226658 prefixEnd_226658 116384498186879433232625 := by
  unfold tailWord_226658
  simp only [CollatzResearch.WordTrace]
  refine ⟨2066724103216062737410157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5511264275242833966427085 2066724103216062737410157)
  ·
    refine ⟨775021538706023526528809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2066724103216062737410157 775021538706023526528809)
    ·
      refine ⟨581266154029517644896607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 775021538706023526528809 581266154029517644896607)
      ·
        refine ⟨871899231044276467344911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581266154029517644896607 871899231044276467344911)
        ·
          refine ⟨1307848846566414701017367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871899231044276467344911 1307848846566414701017367)
          ·
            refine ⟨1961773269849622051526051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307848846566414701017367 1961773269849622051526051)
            ·
              refine ⟨2942659904774433077289077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1961773269849622051526051 2942659904774433077289077)
              ·
                refine ⟨275874366072603100995851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2942659904774433077289077 275874366072603100995851)
                ·
                  refine ⟨413811549108904651493777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275874366072603100995851 413811549108904651493777)
                  ·
                    refine ⟨310358661831678488620333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 413811549108904651493777 310358661831678488620333)
                    ·
                      refine ⟨116384498186879433232625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 310358661831678488620333 116384498186879433232625)
                      ·
                        rfl

theorem cell23_226658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_226658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226658 prefixEnd_226658 := by exact prefixLift 226658
  have htrace : WordTrace (prefixWord ++ tailWord_226658) baseStart_226658 baseEnd_226658 := by
    simpa [prefixWord, tailWord_226658, baseEnd_226658] using wordTrace_append hprefix tailTrace_226658
  have hstable : (prefixWord ++ tailWord_226658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226658).length < 2 ^ (prefixWord ++ tailWord_226658).sum := by decide
  have hdescent : baseEnd_226658 < baseStart_226658 := by decide
  rcases family_descends (prefixWord ++ tailWord_226658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226671 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 4, 1, 3]
def baseStart_226671 : Nat := 118140960795 + 226671 * 2 ^ 59
def prefixEnd_226671 : Nat := 4983230072969 + 3 ^ 40 * 226671 * 2
def baseEnd_226671 : Nat := 116391173435387882370065

theorem tailTrace_226671 : CollatzResearch.WordTrace tailWord_226671 prefixEnd_226671 116391173435387882370065 := by
  unfold tailWord_226671
  simp only [CollatzResearch.WordTrace]
  refine ⟨8267370561817154169863867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5511580374544769446575911 8267370561817154169863867)
  ·
    refine ⟨12401055842725731254795801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8267370561817154169863867 12401055842725731254795801)
    ·
      refine ⟨9300791882044298441096851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12401055842725731254795801 9300791882044298441096851)
      ·
        refine ⟨13951187823066447661645277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9300791882044298441096851 13951187823066447661645277)
        ·
          refine ⟨5231695433649917873116979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13951187823066447661645277 5231695433649917873116979)
          ·
            refine ⟨7847543150474876809675469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5231695433649917873116979 7847543150474876809675469)
            ·
              refine ⟨2942828681428078803628301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7847543150474876809675469 2942828681428078803628301)
              ·
                refine ⟨1103560755535529551360613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2942828681428078803628301 1103560755535529551360613)
                ·
                  refine ⟨206917641662911790880115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1103560755535529551360613 206917641662911790880115)
                  ·
                    refine ⟨310376462494367686320173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 206917641662911790880115 310376462494367686320173)
                    ·
                      refine ⟨116391173435387882370065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 310376462494367686320173 116391173435387882370065)
                      ·
                        rfl

theorem cell23_226671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 1, 3].length) (baseStart_226671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226671 prefixEnd_226671 := by exact prefixLift 226671
  have htrace : WordTrace (prefixWord ++ tailWord_226671) baseStart_226671 baseEnd_226671 := by
    simpa [prefixWord, tailWord_226671, baseEnd_226671] using wordTrace_append hprefix tailTrace_226671
  have hstable : (prefixWord ++ tailWord_226671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226671).length < 2 ^ (prefixWord ++ tailWord_226671).sum := by decide
  have hdescent : baseEnd_226671 < baseStart_226671 := by decide
  rcases family_descends (prefixWord ++ tailWord_226671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226672 : List Nat := [2, 1, 1, 1, 4, 2, 5, 2, 1, 2, 2]
def baseStart_226672 : Nat := 118140960795 + 226672 * 2 ^ 59
def prefixEnd_226672 : Nat := 4983230072969 + 3 ^ 40 * 226672 * 2
def baseEnd_226672 : Nat := 116391686916042378457561

theorem tailTrace_226672 : CollatzResearch.WordTrace tailWord_226672 prefixEnd_226672 116391686916042378457561 := by
  unfold tailWord_226672
  simp only [CollatzResearch.WordTrace]
  refine ⟨4133703517406765670325135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5511604689875687560433513 4133703517406765670325135)
  ·
    refine ⟨6200555276110148505487703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4133703517406765670325135 6200555276110148505487703)
    ·
      refine ⟨9300832914165222758231555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6200555276110148505487703 9300832914165222758231555)
      ·
        refine ⟨13951249371247834137347333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9300832914165222758231555 13951249371247834137347333)
        ·
          refine ⟨2615859257108968900752625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13951249371247834137347333 2615859257108968900752625)
          ·
            refine ⟨1961894442831726675564469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2615859257108968900752625 1961894442831726675564469)
            ·
              refine ⟨183927604015474375834169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1961894442831726675564469 183927604015474375834169)
              ·
                refine ⟨137945703011605781875627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183927604015474375834169 137945703011605781875627)
                ·
                  refine ⟨206918554517408672813441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137945703011605781875627 206918554517408672813441)
                  ·
                    refine ⟨155188915888056504610081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 206918554517408672813441 155188915888056504610081)
                    ·
                      refine ⟨116391686916042378457561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 155188915888056504610081 116391686916042378457561)
                      ·
                        rfl

theorem cell23_226672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 1, 2, 2].length) (baseStart_226672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226672 prefixEnd_226672 := by exact prefixLift 226672
  have htrace : WordTrace (prefixWord ++ tailWord_226672) baseStart_226672 baseEnd_226672 := by
    simpa [prefixWord, tailWord_226672, baseEnd_226672] using wordTrace_append hprefix tailTrace_226672
  have hstable : (prefixWord ++ tailWord_226672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226672).length < 2 ^ (prefixWord ++ tailWord_226672).sum := by decide
  have hdescent : baseEnd_226672 < baseStart_226672 := by decide
  rcases family_descends (prefixWord ++ tailWord_226672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226674 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 2, 7]
def baseStart_226674 : Nat := 118140960795 + 226674 * 2 ^ 59
def prefixEnd_226674 : Nat := 4983230072969 + 3 ^ 40 * 226674 * 2
def baseEnd_226674 : Nat := 38797571292450456877517

theorem tailTrace_226674 : CollatzResearch.WordTrace tailWord_226674 prefixEnd_226674 38797571292450456877517 := by
  unfold tailWord_226674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2066869995201571420555769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5511653320537523788148717 2066869995201571420555769)
  ·
    refine ⟨1550152496401178565416827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2066869995201571420555769 1550152496401178565416827)
    ·
      refine ⟨2325228744601767848125241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1550152496401178565416827 2325228744601767848125241)
      ·
        refine ⟨1743921558451325886093931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2325228744601767848125241 1743921558451325886093931)
        ·
          refine ⟨2615882337676988829140897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1743921558451325886093931 2615882337676988829140897)
          ·
            refine ⟨1961911753257741621855673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2615882337676988829140897 1961911753257741621855673)
            ·
              refine ⟨1471433814943306216391755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1961911753257741621855673 1471433814943306216391755)
              ·
                refine ⟨2207150722414959324587633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1471433814943306216391755 2207150722414959324587633)
                ·
                  refine ⟨1655363041811219493440725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2207150722414959324587633 1655363041811219493440725)
                  ·
                    refine ⟨38797571292450456877517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1655363041811219493440725 38797571292450456877517)
                    ·
                      rfl

theorem cell23_226674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_226674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226674 prefixEnd_226674 := by exact prefixLift 226674
  have htrace : WordTrace (prefixWord ++ tailWord_226674) baseStart_226674 baseEnd_226674 := by
    simpa [prefixWord, tailWord_226674, baseEnd_226674] using wordTrace_append hprefix tailTrace_226674
  have hstable : (prefixWord ++ tailWord_226674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226674).length < 2 ^ (prefixWord ++ tailWord_226674).sum := by decide
  have hdescent : baseEnd_226674 < baseStart_226674 := by decide
  rcases family_descends (prefixWord ++ tailWord_226674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226724 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_226724 : Nat := 118140960795 + 226724 * 2 ^ 59
def prefixEnd_226724 : Nat := 4983230072969 + 3 ^ 40 * 226724 * 2
def baseEnd_226724 : Nat := 116418387910076175007321

theorem tailTrace_226724 : CollatzResearch.WordTrace tailWord_226724 prefixEnd_226724 116418387910076175007321 := by
  unfold tailWord_226724
  simp only [CollatzResearch.WordTrace]
  refine ⟨4134651815312572110771613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5512869087083429481028817 4134651815312572110771613)
  ·
    refine ⟨1550494430742214541539355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4134651815312572110771613 1550494430742214541539355)
    ·
      refine ⟨2325741646113321812309033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1550494430742214541539355 2325741646113321812309033)
      ·
        refine ⟨1744306234584991359231775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2325741646113321812309033 1744306234584991359231775)
        ·
          refine ⟨2616459351877487038847663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1744306234584991359231775 2616459351877487038847663)
          ·
            refine ⟨3924689027816230558271495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2616459351877487038847663 3924689027816230558271495)
            ·
              refine ⟨5887033541724345837407243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3924689027816230558271495 5887033541724345837407243)
              ·
                refine ⟨8830550312586518756110865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5887033541724345837407243 8830550312586518756110865)
                ·
                  refine ⟨6622912734439889067083149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8830550312586518756110865 6622912734439889067083149)
                  ·
                    refine ⟨2483592275414958400156181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6622912734439889067083149 2483592275414958400156181)
                    ·
                      refine ⟨116418387910076175007321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2483592275414958400156181 116418387910076175007321)
                      ·
                        rfl

theorem cell23_226724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_226724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226724 prefixEnd_226724 := by exact prefixLift 226724
  have htrace : WordTrace (prefixWord ++ tailWord_226724) baseStart_226724 baseEnd_226724 := by
    simpa [prefixWord, tailWord_226724, baseEnd_226724] using wordTrace_append hprefix tailTrace_226724
  have hstable : (prefixWord ++ tailWord_226724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226724).length < 2 ^ (prefixWord ++ tailWord_226724).sum := by decide
  have hdescent : baseEnd_226724 < baseStart_226724 := by decide
  rcases family_descends (prefixWord ++ tailWord_226724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226741 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_226741 : Nat := 118140960795 + 226741 * 2 ^ 59
def prefixEnd_226741 : Nat := 4983230072969 + 3 ^ 40 * 226741 * 2
def baseEnd_226741 : Nat := 116427117081202608494743

theorem tailTrace_226741 : CollatzResearch.WordTrace tailWord_226741 prefixEnd_226741 116427117081202608494743 := by
  unfold tailWord_226741
  simp only [CollatzResearch.WordTrace]
  refine ⟨8269923671563556124912077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5513282447709037416608051 8269923671563556124912077)
  ·
    refine ⟨3101221376836333546842029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8269923671563556124912077 3101221376836333546842029)
    ·
      refine ⟨1162958016313625080065761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3101221376836333546842029 1162958016313625080065761)
      ·
        refine ⟨872218512235218810049321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1162958016313625080065761 872218512235218810049321)
        ·
          refine ⟨654163884176414107536991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 872218512235218810049321 654163884176414107536991)
          ·
            refine ⟨981245826264621161305487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654163884176414107536991 981245826264621161305487)
            ·
              refine ⟨1471868739396931741958231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981245826264621161305487 1471868739396931741958231)
              ·
                refine ⟨2207803109095397612937347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1471868739396931741958231 2207803109095397612937347)
                ·
                  refine ⟨3311704663643096419406021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207803109095397612937347 3311704663643096419406021)
                  ·
                    refine ⟨620944624433080578638629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3311704663643096419406021 620944624433080578638629)
                    ·
                      refine ⟨116427117081202608494743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 620944624433080578638629 116427117081202608494743)
                      ·
                        rfl

theorem cell23_226741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_226741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226741 prefixEnd_226741 := by exact prefixLift 226741
  have htrace : WordTrace (prefixWord ++ tailWord_226741) baseStart_226741 baseEnd_226741 := by
    simpa [prefixWord, tailWord_226741, baseEnd_226741] using wordTrace_append hprefix tailTrace_226741
  have hstable : (prefixWord ++ tailWord_226741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226741).length < 2 ^ (prefixWord ++ tailWord_226741).sum := by decide
  have hdescent : baseEnd_226741 < baseStart_226741 := by decide
  rcases family_descends (prefixWord ++ tailWord_226741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226745 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 1, 4, 2]
def baseStart_226745 : Nat := 118140960795 + 226745 * 2 ^ 59
def prefixEnd_226745 : Nat := 4983230072969 + 3 ^ 40 * 226745 * 2
def baseEnd_226745 : Nat := 116429171003820592844725

theorem tailTrace_226745 : CollatzResearch.WordTrace tailWord_226745 prefixEnd_226745 116429171003820592844725 := by
  unfold tailWord_226745
  simp only [CollatzResearch.WordTrace]
  refine ⟨8270069563549064808057689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5513379709032709872038459 8270069563549064808057689)
  ·
    refine ⟨6202552172661798606043267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8270069563549064808057689 6202552172661798606043267)
    ·
      refine ⟨9303828258992697909064901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6202552172661798606043267 9303828258992697909064901)
      ·
        refine ⟨1744467798561130857949669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9303828258992697909064901 1744467798561130857949669)
        ·
          refine ⟨327087712230212035865563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1744467798561130857949669 327087712230212035865563)
          ·
            refine ⟨490631568345318053798345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327087712230212035865563 490631568345318053798345)
            ·
              refine ⟨367973676258988540348759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490631568345318053798345 367973676258988540348759)
              ·
                refine ⟨551960514388482810523139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367973676258988540348759 551960514388482810523139)
                ·
                  refine ⟨827940771582724215784709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 551960514388482810523139 827940771582724215784709)
                  ·
                    refine ⟨155238894671760790459633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 827940771582724215784709 155238894671760790459633)
                    ·
                      refine ⟨116429171003820592844725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 155238894671760790459633 116429171003820592844725)
                      ·
                        rfl

theorem cell23_226745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_226745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226745 prefixEnd_226745 := by exact prefixLift 226745
  have htrace : WordTrace (prefixWord ++ tailWord_226745) baseStart_226745 baseEnd_226745 := by
    simpa [prefixWord, tailWord_226745, baseEnd_226745] using wordTrace_append hprefix tailTrace_226745
  have hstable : (prefixWord ++ tailWord_226745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226745).length < 2 ^ (prefixWord ++ tailWord_226745).sum := by decide
  have hdescent : baseEnd_226745 < baseStart_226745 := by decide
  rcases family_descends (prefixWord ++ tailWord_226745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226801 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 1, 3, 4]
def baseStart_226801 : Nat := 118140960795 + 226801 * 2 ^ 59
def prefixEnd_226801 : Nat := 4983230072969 + 3 ^ 40 * 226801 * 2
def baseEnd_226801 : Nat := 116457925920472373744467

theorem tailTrace_226801 : CollatzResearch.WordTrace tailWord_226801 prefixEnd_226801 116457925920472373744467 := by
  unfold tailWord_226801
  simp only [CollatzResearch.WordTrace]
  refine ⟨8272112051346186372096257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5514741367564124248064171 8272112051346186372096257)
  ·
    refine ⟨6204084038509639779072193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8272112051346186372096257 6204084038509639779072193)
    ·
      refine ⟨4653063028882229834304145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6204084038509639779072193 4653063028882229834304145)
      ·
        refine ⟨3489797271661672375728109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4653063028882229834304145 3489797271661672375728109)
        ·
          refine ⟨1308673976873127140898041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3489797271661672375728109 1308673976873127140898041)
          ·
            refine ⟨981505482654845355673531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1308673976873127140898041 981505482654845355673531)
            ·
              refine ⟨1472258223982268033510297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981505482654845355673531 1472258223982268033510297)
              ·
                refine ⟨1104193667986701025132723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1472258223982268033510297 1104193667986701025132723)
                ·
                  refine ⟨1656290501980051537699085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1104193667986701025132723 1656290501980051537699085)
                  ·
                    refine ⟨621108938242519326637157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1656290501980051537699085 621108938242519326637157)
                    ·
                      refine ⟨116457925920472373744467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 621108938242519326637157 116457925920472373744467)
                      ·
                        rfl

theorem cell23_226801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_226801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226801 prefixEnd_226801 := by exact prefixLift 226801
  have htrace : WordTrace (prefixWord ++ tailWord_226801) baseStart_226801 baseEnd_226801 := by
    simpa [prefixWord, tailWord_226801, baseEnd_226801] using wordTrace_append hprefix tailTrace_226801
  have hstable : (prefixWord ++ tailWord_226801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226801).length < 2 ^ (prefixWord ++ tailWord_226801).sum := by decide
  have hdescent : baseEnd_226801 < baseStart_226801 := by decide
  rcases family_descends (prefixWord ++ tailWord_226801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226858 : List Nat := [3, 1, 4, 1, 1, 1, 3, 3, 6]
def baseStart_226858 : Nat := 118140960795 + 226858 * 2 ^ 59
def prefixEnd_226858 : Nat := 4983230072969 + 3 ^ 40 * 226858 * 2
def baseEnd_226858 : Nat := 12943021590864294525745

theorem tailTrace_226858 : CollatzResearch.WordTrace tailWord_226858 prefixEnd_226858 12943021590864294525745 := by
  unfold tailWord_226858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2068547753034921276730307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5516127341426456737947485 2068547753034921276730307)
  ·
    refine ⟨3102821629552381915095461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2068547753034921276730307 3102821629552381915095461)
    ·
      refine ⟨581779055541071609080399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3102821629552381915095461 581779055541071609080399)
      ·
        refine ⟨872668583311607413620599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581779055541071609080399 872668583311607413620599)
        ·
          refine ⟨1309002874967411120430899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872668583311607413620599 1309002874967411120430899)
          ·
            refine ⟨1963504312451116680646349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309002874967411120430899 1963504312451116680646349)
            ·
              refine ⟨736314117169168755242381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1963504312451116680646349 736314117169168755242381)
              ·
                refine ⟨276117793938438283215893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 736314117169168755242381 276117793938438283215893)
                ·
                  refine ⟨12943021590864294525745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 276117793938438283215893 12943021590864294525745)
                  ·
                    rfl

theorem cell23_226858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 6].length) (baseStart_226858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226858 prefixEnd_226858 := by exact prefixLift 226858
  have htrace : WordTrace (prefixWord ++ tailWord_226858) baseStart_226858 baseEnd_226858 := by
    simpa [prefixWord, tailWord_226858, baseEnd_226858] using wordTrace_append hprefix tailTrace_226858
  have hstable : (prefixWord ++ tailWord_226858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226858).length < 2 ^ (prefixWord ++ tailWord_226858).sum := by decide
  have hdescent : baseEnd_226858 < baseStart_226858 := by decide
  rcases family_descends (prefixWord ++ tailWord_226858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226901 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 5, 6]
def baseStart_226901 : Nat := 118140960795 + 226901 * 2 ^ 59
def prefixEnd_226901 : Nat := 4983230072969 + 3 ^ 40 * 226901 * 2
def baseEnd_226901 : Nat := 38836424661973994164669

theorem tailTrace_226901 : CollatzResearch.WordTrace tailWord_226901 prefixEnd_226901 38836424661973994164669 := by
  unfold tailWord_226901
  simp only [CollatzResearch.WordTrace]
  refine ⟨8275759350983903450736557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5517172900655935633824371 8275759350983903450736557)
  ·
    refine ⟨3103409756618963794026209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8275759350983903450736557 3103409756618963794026209)
    ·
      refine ⟨2327557317464222845519657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3103409756618963794026209 2327557317464222845519657)
      ·
        refine ⟨1745667988098167134139743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2327557317464222845519657 1745667988098167134139743)
        ·
          refine ⟨2618501982147250701209615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1745667988098167134139743 2618501982147250701209615)
          ·
            refine ⟨3927752973220876051814423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2618501982147250701209615 3927752973220876051814423)
            ·
              refine ⟨5891629459831314077721635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3927752973220876051814423 5891629459831314077721635)
              ·
                refine ⟨8837444189746971116582453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5891629459831314077721635 8837444189746971116582453)
                ·
                  refine ⟨828510392788778542179605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8837444189746971116582453 828510392788778542179605)
                  ·
                    refine ⟨38836424661973994164669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 828510392788778542179605 38836424661973994164669)
                    ·
                      rfl

theorem cell23_226901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_226901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226901 prefixEnd_226901 := by exact prefixLift 226901
  have htrace : WordTrace (prefixWord ++ tailWord_226901) baseStart_226901 baseEnd_226901 := by
    simpa [prefixWord, tailWord_226901, baseEnd_226901] using wordTrace_append hprefix tailTrace_226901
  have hstable : (prefixWord ++ tailWord_226901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226901).length < 2 ^ (prefixWord ++ tailWord_226901).sum := by decide
  have hdescent : baseEnd_226901 < baseStart_226901 := by decide
  rcases family_descends (prefixWord ++ tailWord_226901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226921 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 1, 1, 6]
def baseStart_226921 : Nat := 118140960795 + 226921 * 2 ^ 59
def prefixEnd_226921 : Nat := 4983230072969 + 3 ^ 40 * 226921 * 2
def baseEnd_226921 : Nat := 116519543599011904243915

theorem tailTrace_226921 : CollatzResearch.WordTrace tailWord_226921 prefixEnd_226921 116519543599011904243915 := by
  unfold tailWord_226921
  simp only [CollatzResearch.WordTrace]
  refine ⟨8276488810911446866464617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5517659207274297910976411 8276488810911446866464617)
  ·
    refine ⟨6207366608183585149848463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8276488810911446866464617 6207366608183585149848463)
    ·
      refine ⟨9311049912275377724772695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6207366608183585149848463 9311049912275377724772695)
      ·
        refine ⟨13966574868413066587159043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9311049912275377724772695 13966574868413066587159043)
        ·
          refine ⟨20949862302619599880738565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13966574868413066587159043 20949862302619599880738565)
          ·
            refine ⟨3928099181741174977638481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20949862302619599880738565 3928099181741174977638481)
            ·
              refine ⟨2946074386305881233228861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3928099181741174977638481 2946074386305881233228861)
              ·
                refine ⟨1104777894864705462460823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2946074386305881233228861 1104777894864705462460823)
                ·
                  refine ⟨1657166842297058193691235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1104777894864705462460823 1657166842297058193691235)
                  ·
                    refine ⟨2485750263445587290536853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1657166842297058193691235 2485750263445587290536853)
                    ·
                      refine ⟨116519543599011904243915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2485750263445587290536853 116519543599011904243915)
                      ·
                        rfl

theorem cell23_226921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_226921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226921 prefixEnd_226921 := by exact prefixLift 226921
  have htrace : WordTrace (prefixWord ++ tailWord_226921) baseStart_226921 baseEnd_226921 := by
    simpa [prefixWord, tailWord_226921, baseEnd_226921] using wordTrace_append hprefix tailTrace_226921
  have hstable : (prefixWord ++ tailWord_226921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226921).length < 2 ^ (prefixWord ++ tailWord_226921).sum := by decide
  have hdescent : baseEnd_226921 < baseStart_226921 := by decide
  rcases family_descends (prefixWord ++ tailWord_226921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226948 : List Nat := [2, 3, 2, 1, 4, 1, 10]
def baseStart_226948 : Nat := 118140960795 + 226948 * 2 ^ 59
def prefixEnd_226948 : Nat := 4983230072969 + 3 ^ 40 * 226948 * 2
def baseEnd_226948 : Nat := 1438684044156583933411

theorem tailTrace_226948 : CollatzResearch.WordTrace tailWord_226948 prefixEnd_226948 1438684044156583933411 := by
  unfold tailWord_226948
  simp only [CollatzResearch.WordTrace]
  refine ⟨4138736790906815238848749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5518315721209086985131665 4138736790906815238848749)
  ·
    refine ⟨1552026296590055714568281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4138736790906815238848749 1552026296590055714568281)
    ·
      refine ⟨1164019722442541785926211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1552026296590055714568281 1164019722442541785926211)
      ·
        refine ⟨1746029583663812678889317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1164019722442541785926211 1746029583663812678889317)
        ·
          refine ⟨327380546936964877291747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1746029583663812678889317 327380546936964877291747)
          ·
            refine ⟨491070820405447315937621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327380546936964877291747 491070820405447315937621)
            ·
              refine ⟨1438684044156583933411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 491070820405447315937621 1438684044156583933411)
              ·
                rfl

theorem cell23_226948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 10].length) (baseStart_226948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226948 prefixEnd_226948 := by exact prefixLift 226948
  have htrace : WordTrace (prefixWord ++ tailWord_226948) baseStart_226948 baseEnd_226948 := by
    simpa [prefixWord, tailWord_226948, baseEnd_226948] using wordTrace_append hprefix tailTrace_226948
  have hstable : (prefixWord ++ tailWord_226948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226948).length < 2 ^ (prefixWord ++ tailWord_226948).sum := by decide
  have hdescent : baseEnd_226948 < baseStart_226948 := by decide
  rcases family_descends (prefixWord ++ tailWord_226948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226952 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 4, 4]
def baseStart_226952 : Nat := 118140960795 + 226952 * 2 ^ 59
def prefixEnd_226952 : Nat := 4983230072969 + 3 ^ 40 * 226952 * 2
def baseEnd_226952 : Nat := 38845153833100427652091

theorem tailTrace_226952 : CollatzResearch.WordTrace tailWord_226952 prefixEnd_226952 38845153833100427652091 := by
  unfold tailWord_226952
  simp only [CollatzResearch.WordTrace]
  refine ⟨4138809736899569580421555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5518412982532759440562073 4138809736899569580421555)
  ·
    refine ⟨6208214605349354370632333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4138809736899569580421555 6208214605349354370632333)
    ·
      refine ⟨2328080477006007888987125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6208214605349354370632333 2328080477006007888987125)
      ·
        refine ⟨218257544719313239592543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2328080477006007888987125 218257544719313239592543)
        ·
          refine ⟨327386317078969859388815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218257544719313239592543 327386317078969859388815)
          ·
            refine ⟨491079475618454789083223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327386317078969859388815 491079475618454789083223)
            ·
              refine ⟨736619213427682183624835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491079475618454789083223 736619213427682183624835)
              ·
                refine ⟨1104928820141523275437253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 736619213427682183624835 1104928820141523275437253)
                ·
                  refine ⟨207174153776535614144485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1104928820141523275437253 207174153776535614144485)
                  ·
                    refine ⟨38845153833100427652091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 207174153776535614144485 38845153833100427652091)
                    ·
                      rfl

theorem cell23_226952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_226952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226952 prefixEnd_226952 := by exact prefixLift 226952
  have htrace : WordTrace (prefixWord ++ tailWord_226952) baseStart_226952 baseEnd_226952 := by
    simpa [prefixWord, tailWord_226952, baseEnd_226952] using wordTrace_append hprefix tailTrace_226952
  have hstable : (prefixWord ++ tailWord_226952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226952).length < 2 ^ (prefixWord ++ tailWord_226952).sum := by decide
  have hdescent : baseEnd_226952 < baseStart_226952 := by decide
  rcases family_descends (prefixWord ++ tailWord_226952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226961 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 2, 7]
def baseStart_226961 : Nat := 118140960795 + 226961 * 2 ^ 59
def prefixEnd_226961 : Nat := 4983230072969 + 3 ^ 40 * 226961 * 2
def baseEnd_226961 : Nat := 38846694275063915914577

theorem tailTrace_226961 : CollatzResearch.WordTrace tailWord_226961 prefixEnd_226961 38846694275063915914577 := by
  unfold tailWord_226961
  simp only [CollatzResearch.WordTrace]
  refine ⟨8277947730766533697920737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5518631820511022465280491 8277947730766533697920737)
  ·
    refine ⟨6208460798074900273440553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8277947730766533697920737 6208460798074900273440553)
    ·
      refine ⟨4656345598556175205080415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6208460798074900273440553 4656345598556175205080415)
      ·
        refine ⟨6984518397834262807620623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4656345598556175205080415 6984518397834262807620623)
        ·
          refine ⟨10476777596751394211430935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6984518397834262807620623 10476777596751394211430935)
          ·
            refine ⟨15715166395127091317146403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10476777596751394211430935 15715166395127091317146403)
            ·
              refine ⟨23572749592690636975719605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15715166395127091317146403 23572749592690636975719605)
              ·
                refine ⟨2209945274314747216473713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23572749592690636975719605 2209945274314747216473713)
                ·
                  refine ⟨1657458955736060412355285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2209945274314747216473713 1657458955736060412355285)
                  ·
                    refine ⟨38846694275063915914577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1657458955736060412355285 38846694275063915914577)
                    ·
                      rfl

theorem cell23_226961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_226961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226961 prefixEnd_226961 := by exact prefixLift 226961
  have htrace : WordTrace (prefixWord ++ tailWord_226961) baseStart_226961 baseEnd_226961 := by
    simpa [prefixWord, tailWord_226961, baseEnd_226961] using wordTrace_append hprefix tailTrace_226961
  have hstable : (prefixWord ++ tailWord_226961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226961).length < 2 ^ (prefixWord ++ tailWord_226961).sum := by decide
  have hdescent : baseEnd_226961 < baseStart_226961 := by decide
  rcases family_descends (prefixWord ++ tailWord_226961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226972 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_226972 : Nat := 118140960795 + 226972 * 2 ^ 59
def prefixEnd_226972 : Nat := 4983230072969 + 3 ^ 40 * 226972 * 2
def baseEnd_226972 : Nat := 116545731112391204706181

theorem tailTrace_226972 : CollatzResearch.WordTrace tailWord_226972 prefixEnd_226972 116545731112391204706181 := by
  unfold tailWord_226972
  simp only [CollatzResearch.WordTrace]
  refine ⟨4139174466863341288285585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5518899289151121717714113 4139174466863341288285585)
  ·
    refine ⟨3104380850147505966214189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4139174466863341288285585 3104380850147505966214189)
    ·
      refine ⟨1164142818805314737330321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3104380850147505966214189 1164142818805314737330321)
      ·
        refine ⟨873107114103986052997741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1164142818805314737330321 873107114103986052997741)
        ·
          refine ⟨327415167788994769874153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 873107114103986052997741 327415167788994769874153)
          ·
            refine ⟨245561375841746077405615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327415167788994769874153 245561375841746077405615)
            ·
              refine ⟨368342063762619116108423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245561375841746077405615 368342063762619116108423)
              ·
                refine ⟨552513095643928674162635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368342063762619116108423 552513095643928674162635)
                ·
                  refine ⟨828769643465893011243953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552513095643928674162635 828769643465893011243953)
                  ·
                    refine ⟨621577232599419758432965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 828769643465893011243953 621577232599419758432965)
                    ·
                      refine ⟨116545731112391204706181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 621577232599419758432965 116545731112391204706181)
                      ·
                        rfl

theorem cell23_226972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_226972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_226972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_226972 prefixEnd_226972 := by exact prefixLift 226972
  have htrace : WordTrace (prefixWord ++ tailWord_226972) baseStart_226972 baseEnd_226972 := by
    simpa [prefixWord, tailWord_226972, baseEnd_226972] using wordTrace_append hprefix tailTrace_226972
  have hstable : (prefixWord ++ tailWord_226972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226972).length < 2 ^ (prefixWord ++ tailWord_226972).sum := by decide
  have hdescent : baseEnd_226972 < baseStart_226972 := by decide
  rcases family_descends (prefixWord ++ tailWord_226972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227002 : List Nat := [3, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2]
def baseStart_227002 : Nat := 118140960795 + 227002 * 2 ^ 59
def prefixEnd_227002 : Nat := 4983230072969 + 3 ^ 40 * 227002 * 2
def baseEnd_227002 : Nat := 116561135532026087331043

theorem tailTrace_227002 : CollatzResearch.WordTrace tailWord_227002 prefixEnd_227002 116561135532026087331043 := by
  unfold tailWord_227002
  simp only [CollatzResearch.WordTrace]
  refine ⟨2069860780904499425040815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5519628749078665133442173 2069860780904499425040815)
  ·
    refine ⟨3104791171356749137561223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2069860780904499425040815 3104791171356749137561223)
    ·
      refine ⟨4657186757035123706341835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3104791171356749137561223 4657186757035123706341835)
      ·
        refine ⟨6985780135552685559512753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4657186757035123706341835 6985780135552685559512753)
        ·
          refine ⟨5239335101664514169634565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6985780135552685559512753 5239335101664514169634565)
          ·
            refine ⟨982375331562096406806481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5239335101664514169634565 982375331562096406806481)
            ·
              refine ⟨736781498671572305104861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982375331562096406806481 736781498671572305104861)
              ·
                refine ⟨276293062001839614414323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 736781498671572305104861 276293062001839614414323)
                ·
                  refine ⟨414439593002759421621485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276293062001839614414323 414439593002759421621485)
                  ·
                    refine ⟨155414847376034783108057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 414439593002759421621485 155414847376034783108057)
                    ·
                      refine ⟨116561135532026087331043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 155414847376034783108057 116561135532026087331043)
                      ·
                        rfl

theorem cell23_227002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2].length) (baseStart_227002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227002 prefixEnd_227002 := by exact prefixLift 227002
  have htrace : WordTrace (prefixWord ++ tailWord_227002) baseStart_227002 baseEnd_227002 := by
    simpa [prefixWord, tailWord_227002, baseEnd_227002] using wordTrace_append hprefix tailTrace_227002
  have hstable : (prefixWord ++ tailWord_227002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227002).length < 2 ^ (prefixWord ++ tailWord_227002).sum := by decide
  have hdescent : baseEnd_227002 < baseStart_227002 := by decide
  rcases family_descends (prefixWord ++ tailWord_227002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227010 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_227010 : Nat := 118140960795 + 227010 * 2 ^ 59
def prefixEnd_227010 : Nat := 4983230072969 + 3 ^ 40 * 227010 * 2
def baseEnd_227010 : Nat := 116565243377262056031007

theorem tailTrace_227010 : CollatzResearch.WordTrace tailWord_227010 prefixEnd_227010 116565243377262056031007 := by
  unfold tailWord_227010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2069933726897253766613621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5519823271726010044302989 2069933726897253766613621)
  ·
    refine ⟨194056286896617540620027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2069933726897253766613621 194056286896617540620027)
    ·
      refine ⟨291084430344926310930041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194056286896617540620027 291084430344926310930041)
      ·
        refine ⟨218313322758694733197531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291084430344926310930041 218313322758694733197531)
        ·
          refine ⟨327469984138042099796297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218313322758694733197531 327469984138042099796297)
          ·
            refine ⟨245602488103531574847223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327469984138042099796297 245602488103531574847223)
            ·
              refine ⟨368403732155297362270835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245602488103531574847223 368403732155297362270835)
              ·
                refine ⟨552605598232946043406253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368403732155297362270835 552605598232946043406253)
                ·
                  refine ⟨207227099337354766277345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552605598232946043406253 207227099337354766277345)
                  ·
                    refine ⟨155420324503016074708009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 207227099337354766277345 155420324503016074708009)
                    ·
                      refine ⟨116565243377262056031007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 155420324503016074708009 116565243377262056031007)
                      ·
                        rfl

theorem cell23_227010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_227010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227010 prefixEnd_227010 := by exact prefixLift 227010
  have htrace : WordTrace (prefixWord ++ tailWord_227010) baseStart_227010 baseEnd_227010 := by
    simpa [prefixWord, tailWord_227010, baseEnd_227010] using wordTrace_append hprefix tailTrace_227010
  have hstable : (prefixWord ++ tailWord_227010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227010).length < 2 ^ (prefixWord ++ tailWord_227010).sum := by decide
  have hdescent : baseEnd_227010 < baseStart_227010 := by decide
  rcases family_descends (prefixWord ++ tailWord_227010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227026 : List Nat := [3, 2, 2, 2, 2, 3, 2, 1, 2, 1, 3]
def baseStart_227026 : Nat := 118140960795 + 227026 * 2 ^ 59
def prefixEnd_227026 : Nat := 4983230072969 + 3 ^ 40 * 227026 * 2
def baseEnd_227026 : Nat := 116573459067733993430933

theorem tailTrace_227026 : CollatzResearch.WordTrace tailWord_227026 prefixEnd_227026 116573459067733993430933 := by
  unfold tailWord_227026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2070079618882762449759233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5520212317020699866024621 2070079618882762449759233)
  ·
    refine ⟨1552559714162071837319425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2070079618882762449759233 1552559714162071837319425)
    ·
      refine ⟨1164419785621553877989569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1552559714162071837319425 1164419785621553877989569)
      ·
        refine ⟨873314839216165408492177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1164419785621553877989569 873314839216165408492177)
        ·
          refine ⟨654986129412124056369133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 873314839216165408492177 654986129412124056369133)
          ·
            refine ⟨245619798529546521138425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 654986129412124056369133 245619798529546521138425)
            ·
              refine ⟨184214848897159890853819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245619798529546521138425 184214848897159890853819)
              ·
                refine ⟨276322273345739836280729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184214848897159890853819 276322273345739836280729)
                ·
                  refine ⟨207241705009304877210547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276322273345739836280729 207241705009304877210547)
                  ·
                    refine ⟨310862557513957315815821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 207241705009304877210547 310862557513957315815821)
                    ·
                      refine ⟨116573459067733993430933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 310862557513957315815821 116573459067733993430933)
                      ·
                        rfl

theorem cell23_227026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_227026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227026 prefixEnd_227026 := by exact prefixLift 227026
  have htrace : WordTrace (prefixWord ++ tailWord_227026) baseStart_227026 baseEnd_227026 := by
    simpa [prefixWord, tailWord_227026, baseEnd_227026] using wordTrace_append hprefix tailTrace_227026
  have hstable : (prefixWord ++ tailWord_227026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227026).length < 2 ^ (prefixWord ++ tailWord_227026).sum := by decide
  have hdescent : baseEnd_227026 < baseStart_227026 := by decide
  rcases family_descends (prefixWord ++ tailWord_227026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227055 : List Nat := [1, 1, 2, 1, 5, 1, 2, 5, 5]
def baseStart_227055 : Nat := 118140960795 + 227055 * 2 ^ 59
def prefixEnd_227055 : Nat := 4983230072969 + 3 ^ 40 * 227055 * 2
def baseEnd_227055 : Nat := 12954261111857153329811

theorem tailTrace_227055 : CollatzResearch.WordTrace tailWord_227055 prefixEnd_227055 12954261111857153329811 := by
  unfold tailWord_227055
  simp only [CollatzResearch.WordTrace]
  refine ⟨8281376192425987751842619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5520917461617325167895079 8281376192425987751842619)
  ·
    refine ⟨12422064288638981627763929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8281376192425987751842619 12422064288638981627763929)
    ·
      refine ⟨9316548216479236220822947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12422064288638981627763929 9316548216479236220822947)
      ·
        refine ⟨13974822324718854331234421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9316548216479236220822947 13974822324718854331234421)
        ·
          refine ⟨1310139592942392593553227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13974822324718854331234421 1310139592942392593553227)
          ·
            refine ⟨1965209389413588890329841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310139592942392593553227 1965209389413588890329841)
            ·
              refine ⟨1473907042060191667747381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1965209389413588890329841 1473907042060191667747381)
              ·
                refine ⟨138178785193142968851317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1473907042060191667747381 138178785193142968851317)
                ·
                  refine ⟨12954261111857153329811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138178785193142968851317 12954261111857153329811)
                  ·
                    rfl

theorem cell23_227055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 5].length) (baseStart_227055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227055 prefixEnd_227055 := by exact prefixLift 227055
  have htrace : WordTrace (prefixWord ++ tailWord_227055) baseStart_227055 baseEnd_227055 := by
    simpa [prefixWord, tailWord_227055, baseEnd_227055] using wordTrace_append hprefix tailTrace_227055
  have hstable : (prefixWord ++ tailWord_227055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227055).length < 2 ^ (prefixWord ++ tailWord_227055).sum := by decide
  have hdescent : baseEnd_227055 < baseStart_227055 := by decide
  rcases family_descends (prefixWord ++ tailWord_227055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227075 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 2, 5, 2]
def baseStart_227075 : Nat := 118140960795 + 227075 * 2 ^ 59
def prefixEnd_227075 : Nat := 4983230072969 + 3 ^ 40 * 227075 * 2
def baseEnd_227075 : Nat := 116598619619804301718207

theorem tailTrace_227075 : CollatzResearch.WordTrace tailWord_227075 prefixEnd_227075 116598619619804301718207 := by
  unfold tailWord_227075
  simp only [CollatzResearch.WordTrace]
  refine ⟨8282105652353531167570679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5521403768235687445047119 8282105652353531167570679)
  ·
    refine ⟨12423158478530296751356019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8282105652353531167570679 12423158478530296751356019)
    ·
      refine ⟨18634737717795445127034029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12423158478530296751356019 18634737717795445127034029)
      ·
        refine ⟨6988026644173291922637761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18634737717795445127034029 6988026644173291922637761)
        ·
          refine ⟨5241019983129968941978321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6988026644173291922637761 5241019983129968941978321)
          ·
            refine ⟨3930764987347476706483741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5241019983129968941978321 3930764987347476706483741)
            ·
              refine ⟨1474036870255303764931403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3930764987347476706483741 1474036870255303764931403)
              ·
                refine ⟨2211055305382955647397105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474036870255303764931403 2211055305382955647397105)
                ·
                  refine ⟨1658291479037216735547829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2211055305382955647397105 1658291479037216735547829)
                  ·
                    refine ⟨155464826159739068957609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1658291479037216735547829 155464826159739068957609)
                    ·
                      refine ⟨116598619619804301718207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 155464826159739068957609 116598619619804301718207)
                      ·
                        rfl

theorem cell23_227075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 5, 2].length) (baseStart_227075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227075 prefixEnd_227075 := by exact prefixLift 227075
  have htrace : WordTrace (prefixWord ++ tailWord_227075) baseStart_227075 baseEnd_227075 := by
    simpa [prefixWord, tailWord_227075, baseEnd_227075] using wordTrace_append hprefix tailTrace_227075
  have hstable : (prefixWord ++ tailWord_227075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227075).length < 2 ^ (prefixWord ++ tailWord_227075).sum := by decide
  have hdescent : baseEnd_227075 < baseStart_227075 := by decide
  rcases family_descends (prefixWord ++ tailWord_227075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227105 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_227105 : Nat := 118140960795 + 227105 * 2 ^ 59
def prefixEnd_227105 : Nat := 4983230072969 + 3 ^ 40 * 227105 * 2
def baseEnd_227105 : Nat := 116614024039439184343069

theorem tailTrace_227105 : CollatzResearch.WordTrace tailWord_227105 prefixEnd_227105 116614024039439184343069 := by
  unfold tailWord_227105
  simp only [CollatzResearch.WordTrace]
  refine ⟨8283199842244846291162769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5522133228163230860775179 8283199842244846291162769)
  ·
    refine ⟨6212399881683634718372077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8283199842244846291162769 6212399881683634718372077)
    ·
      refine ⟨2329649955631363019389529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6212399881683634718372077 2329649955631363019389529)
      ·
        refine ⟨1747237466723522264542147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2329649955631363019389529 1747237466723522264542147)
        ·
          refine ⟨2620856200085283396813221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747237466723522264542147 2620856200085283396813221)
          ·
            refine ⟨491410537515990636902479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2620856200085283396813221 491410537515990636902479)
            ·
              refine ⟨737115806273985955353719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491410537515990636902479 737115806273985955353719)
              ·
                refine ⟨1105673709410978933030579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737115806273985955353719 1105673709410978933030579)
                ·
                  refine ⟨1658510564116468399545869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105673709410978933030579 1658510564116468399545869)
                  ·
                    refine ⟨621941461543675649829701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1658510564116468399545869 621941461543675649829701)
                    ·
                      refine ⟨116614024039439184343069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 621941461543675649829701 116614024039439184343069)
                      ·
                        rfl

theorem cell23_227105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_227105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227105 prefixEnd_227105 := by exact prefixLift 227105
  have htrace : WordTrace (prefixWord ++ tailWord_227105) baseStart_227105 baseEnd_227105 := by
    simpa [prefixWord, tailWord_227105, baseEnd_227105] using wordTrace_append hprefix tailTrace_227105
  have hstable : (prefixWord ++ tailWord_227105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227105).length < 2 ^ (prefixWord ++ tailWord_227105).sum := by decide
  have hdescent : baseEnd_227105 < baseStart_227105 := by decide
  rcases family_descends (prefixWord ++ tailWord_227105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227122 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2]
def baseStart_227122 : Nat := 118140960795 + 227122 * 2 ^ 59
def prefixEnd_227122 : Nat := 4983230072969 + 3 ^ 40 * 227122 * 2
def baseEnd_227122 : Nat := 116622753210565617830491

theorem tailTrace_227122 : CollatzResearch.WordTrace tailWord_227122 prefixEnd_227122 116622753210565617830491 := by
  unfold tailWord_227122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2070954970795814548632905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5522546588788838796354413 2070954970795814548632905)
  ·
    refine ⟨1553216228096860911474679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2070954970795814548632905 1553216228096860911474679)
    ·
      refine ⟨2329824342145291367212019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1553216228096860911474679 2329824342145291367212019)
      ·
        refine ⟨3494736513217937050818029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2329824342145291367212019 3494736513217937050818029)
        ·
          refine ⟨1310526192456726394056761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3494736513217937050818029 1310526192456726394056761)
          ·
            refine ⟨982894644342544795542571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1310526192456726394056761 982894644342544795542571)
            ·
              refine ⟨1474341966513817193313857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982894644342544795542571 1474341966513817193313857)
              ·
                refine ⟨1105756474885362894985393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1474341966513817193313857 1105756474885362894985393)
                ·
                  refine ⟨829317356164022171239045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1105756474885362894985393 829317356164022171239045)
                  ·
                    refine ⟨155497004280754157107321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 829317356164022171239045 155497004280754157107321)
                    ·
                      refine ⟨116622753210565617830491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 155497004280754157107321 116622753210565617830491)
                      ·
                        rfl

theorem cell23_227122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_227122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227122 prefixEnd_227122 := by exact prefixLift 227122
  have htrace : WordTrace (prefixWord ++ tailWord_227122) baseStart_227122 baseEnd_227122 := by
    simpa [prefixWord, tailWord_227122, baseEnd_227122] using wordTrace_append hprefix tailTrace_227122
  have hstable : (prefixWord ++ tailWord_227122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227122).length < 2 ^ (prefixWord ++ tailWord_227122).sum := by decide
  have hdescent : baseEnd_227122 < baseStart_227122 := by decide
  rcases family_descends (prefixWord ++ tailWord_227122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227149 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_227149 : Nat := 118140960795 + 227149 * 2 ^ 59
def prefixEnd_227149 : Nat := 4983230072969 + 3 ^ 40 * 227149 * 2
def baseEnd_227149 : Nat := 38878872396079004064289

theorem tailTrace_227149 : CollatzResearch.WordTrace tailWord_227149 prefixEnd_227149 38878872396079004064289 := by
  unfold tailWord_227149
  simp only [CollatzResearch.WordTrace]
  refine ⟨8284804654085441805764501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5523203102723627870509667 8284804654085441805764501)
  ·
    refine ⟨388350218160255084645211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8284804654085441805764501 388350218160255084645211)
    ·
      refine ⟨582525327240382626967817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388350218160255084645211 582525327240382626967817)
      ·
        refine ⟨436893995430286970225863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582525327240382626967817 436893995430286970225863)
        ·
          refine ⟨655340993145430455338795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436893995430286970225863 655340993145430455338795)
          ·
            refine ⟨983011489718145683008193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655340993145430455338795 983011489718145683008193)
            ·
              refine ⟨737258617288609262256145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 983011489718145683008193 737258617288609262256145)
              ·
                refine ⟨552943962966456946692109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 737258617288609262256145 552943962966456946692109)
                ·
                  refine ⟨207353986112421355009541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552943962966456946692109 207353986112421355009541)
                  ·
                    refine ⟨38878872396079004064289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 207353986112421355009541 38878872396079004064289)
                    ·
                      rfl

theorem cell23_227149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_227149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227149 prefixEnd_227149 := by exact prefixLift 227149
  have htrace : WordTrace (prefixWord ++ tailWord_227149) baseStart_227149 baseEnd_227149 := by
    simpa [prefixWord, tailWord_227149, baseEnd_227149] using wordTrace_append hprefix tailTrace_227149
  have hstable : (prefixWord ++ tailWord_227149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227149).length < 2 ^ (prefixWord ++ tailWord_227149).sum := by decide
  have hdescent : baseEnd_227149 < baseStart_227149 := by decide
  rcases family_descends (prefixWord ++ tailWord_227149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227195 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 4]
def baseStart_227195 : Nat := 118140960795 + 227195 * 2 ^ 59
def prefixEnd_227195 : Nat := 4983230072969 + 3 ^ 40 * 227195 * 2
def baseEnd_227195 : Nat := 116660237298343832217655

theorem tailTrace_227195 : CollatzResearch.WordTrace tailWord_227195 prefixEnd_227195 116660237298343832217655 := by
  unfold tailWord_227195
  simp only [CollatzResearch.WordTrace]
  refine ⟨8286482411918791661939039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5524321607945861107959359 8286482411918791661939039)
  ·
    refine ⟨12429723617878187492908559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8286482411918791661939039 12429723617878187492908559)
    ·
      refine ⟨18644585426817281239362839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12429723617878187492908559 18644585426817281239362839)
      ·
        refine ⟨27966878140225921859044259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18644585426817281239362839 27966878140225921859044259)
        ·
          refine ⟨41950317210338882788566389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27966878140225921859044259 41950317210338882788566389)
          ·
            refine ⟨3932842238469270261428099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41950317210338882788566389 3932842238469270261428099)
            ·
              refine ⟨5899263357703905392142149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3932842238469270261428099 5899263357703905392142149)
              ·
                refine ⟨1106111879569482261026653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5899263357703905392142149 1106111879569482261026653)
                ·
                  refine ⟨414791954838555847884995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106111879569482261026653 414791954838555847884995)
                  ·
                    refine ⟨622187932257833771827493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 414791954838555847884995 622187932257833771827493)
                    ·
                      refine ⟨116660237298343832217655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 622187932257833771827493 116660237298343832217655)
                      ·
                        rfl

theorem cell23_227195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 4].length) (baseStart_227195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227195 prefixEnd_227195 := by exact prefixLift 227195
  have htrace : WordTrace (prefixWord ++ tailWord_227195) baseStart_227195 baseEnd_227195 := by
    simpa [prefixWord, tailWord_227195, baseEnd_227195] using wordTrace_append hprefix tailTrace_227195
  have hstable : (prefixWord ++ tailWord_227195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227195).length < 2 ^ (prefixWord ++ tailWord_227195).sum := by decide
  have hdescent : baseEnd_227195 < baseStart_227195 := by decide
  rcases family_descends (prefixWord ++ tailWord_227195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227205 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 1, 6]
def baseStart_227205 : Nat := 118140960795 + 227205 * 2 ^ 59
def prefixEnd_227205 : Nat := 4983230072969 + 3 ^ 40 * 227205 * 2
def baseEnd_227205 : Nat := 38888457368296264364203

theorem tailTrace_227205 : CollatzResearch.WordTrace tailWord_227205 prefixEnd_227205 38888457368296264364203 := by
  unfold tailWord_227205
  simp only [CollatzResearch.WordTrace]
  refine ⟨8286847141882563369803069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5524564761255042246535379 8286847141882563369803069)
  ·
    refine ⟨3107567678205961263676151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8286847141882563369803069 3107567678205961263676151)
    ·
      refine ⟨4661351517308941895514227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3107567678205961263676151 4661351517308941895514227)
      ·
        refine ⟨6992027275963412843271341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4661351517308941895514227 6992027275963412843271341)
        ·
          refine ⟨2622010228486279816226753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6992027275963412843271341 2622010228486279816226753)
          ·
            refine ⟨1966507671364709862170065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2622010228486279816226753 1966507671364709862170065)
            ·
              refine ⟨1474880753523532396627549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1966507671364709862170065 1474880753523532396627549)
              ·
                refine ⟨553080282571324648735331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1474880753523532396627549 553080282571324648735331)
                ·
                  refine ⟨829620423856986973102997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553080282571324648735331 829620423856986973102997)
                  ·
                    refine ⟨38888457368296264364203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 829620423856986973102997 38888457368296264364203)
                    ·
                      rfl

theorem cell23_227205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_227205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227205 prefixEnd_227205 := by exact prefixLift 227205
  have htrace : WordTrace (prefixWord ++ tailWord_227205) baseStart_227205 baseEnd_227205 := by
    simpa [prefixWord, tailWord_227205, baseEnd_227205] using wordTrace_append hprefix tailTrace_227205
  have hstable : (prefixWord ++ tailWord_227205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227205).length < 2 ^ (prefixWord ++ tailWord_227205).sum := by decide
  have hdescent : baseEnd_227205 < baseStart_227205 := by decide
  rcases family_descends (prefixWord ++ tailWord_227205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227225 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 3, 2, 4]
def baseStart_227225 : Nat := 118140960795 + 227225 * 2 ^ 59
def prefixEnd_227225 : Nat := 4983230072969 + 3 ^ 40 * 227225 * 2
def baseEnd_227225 : Nat := 116675641717978714842517

theorem tailTrace_227225 : CollatzResearch.WordTrace tailWord_227225 prefixEnd_227225 116675641717978714842517 := by
  unfold tailWord_227225
  simp only [CollatzResearch.WordTrace]
  refine ⟨8287576601810106785531129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5525051067873404523687419 8287576601810106785531129)
  ·
    refine ⟨6215682451357580089148347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8287576601810106785531129 6215682451357580089148347)
    ·
      refine ⟨9323523677036370133722521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6215682451357580089148347 9323523677036370133722521)
      ·
        refine ⟨6992642757777277600291891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9323523677036370133722521 6992642757777277600291891)
        ·
          refine ⟨10488964136665916400437837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6992642757777277600291891 10488964136665916400437837)
          ·
            refine ⟨3933361551249718650164189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10488964136665916400437837 3933361551249718650164189)
            ·
              refine ⟨1475010581718644493811571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3933361551249718650164189 1475010581718644493811571)
              ·
                refine ⟨2212515872577966740717357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475010581718644493811571 2212515872577966740717357)
                ·
                  refine ⟨829693452216737527769009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2212515872577966740717357 829693452216737527769009)
                  ·
                    refine ⟨622270089162553145826757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 829693452216737527769009 622270089162553145826757)
                    ·
                      refine ⟨116675641717978714842517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 622270089162553145826757 116675641717978714842517)
                      ·
                        rfl

theorem cell23_227225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_227225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227225 prefixEnd_227225 := by exact prefixLift 227225
  have htrace : WordTrace (prefixWord ++ tailWord_227225) baseStart_227225 baseEnd_227225 := by
    simpa [prefixWord, tailWord_227225, baseEnd_227225] using wordTrace_append hprefix tailTrace_227225
  have hstable : (prefixWord ++ tailWord_227225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227225).length < 2 ^ (prefixWord ++ tailWord_227225).sum := by decide
  have hdescent : baseEnd_227225 < baseStart_227225 := by decide
  rcases family_descends (prefixWord ++ tailWord_227225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227239 : List Nat := [1, 1, 6, 1, 2, 1, 1, 4, 2, 4]
def baseStart_227239 : Nat := 118140960795 + 227239 * 2 ^ 59
def prefixEnd_227239 : Nat := 4983230072969 + 3 ^ 40 * 227239 * 2
def baseEnd_227239 : Nat := 38894276815713886689151

theorem tailTrace_227239 : CollatzResearch.WordTrace tailWord_227239 prefixEnd_227239 38894276815713886689151 := by
  unfold tailWord_227239
  simp only [CollatzResearch.WordTrace]
  refine ⟨8288087223759387176540771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5525391482506258117693847 8288087223759387176540771)
  ·
    refine ⟨12432130835639080764811157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8288087223759387176540771 12432130835639080764811157)
    ·
      refine ⟨582756132920581910850523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12432130835639080764811157 582756132920581910850523)
      ·
        refine ⟨874134199380872866275785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582756132920581910850523 874134199380872866275785)
        ·
          refine ⟨655600649535654649706839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 874134199380872866275785 655600649535654649706839)
          ·
            refine ⟨983400974303481974560259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655600649535654649706839 983400974303481974560259)
            ·
              refine ⟨1475101461455222961840389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 983400974303481974560259 1475101461455222961840389)
              ·
                refine ⟨276581524022854305345073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1475101461455222961840389 276581524022854305345073)
                ·
                  refine ⟨207436143017140729008805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276581524022854305345073 207436143017140729008805)
                  ·
                    refine ⟨38894276815713886689151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 207436143017140729008805 38894276815713886689151)
                    ·
                      rfl

theorem cell23_227239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_227239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227239 prefixEnd_227239 := by exact prefixLift 227239
  have htrace : WordTrace (prefixWord ++ tailWord_227239) baseStart_227239 baseEnd_227239 := by
    simpa [prefixWord, tailWord_227239, baseEnd_227239] using wordTrace_append hprefix tailTrace_227239
  have hstable : (prefixWord ++ tailWord_227239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227239).length < 2 ^ (prefixWord ++ tailWord_227239).sum := by decide
  have hdescent : baseEnd_227239 < baseStart_227239 := by decide
  rcases family_descends (prefixWord ++ tailWord_227239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227240 : List Nat := [2, 1, 6, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_227240 : Nat := 118140960795 + 227240 * 2 ^ 59
def prefixEnd_227240 : Nat := 4983230072969 + 3 ^ 40 * 227240 * 2
def baseEnd_227240 : Nat := 116683343927796156154949

theorem tailTrace_227240 : CollatzResearch.WordTrace tailWord_227240 prefixEnd_227240 116683343927796156154949 := by
  unfold tailWord_227240
  simp only [CollatzResearch.WordTrace]
  refine ⟨4144061848377882173663587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5525415797837176231551449 4144061848377882173663587)
  ·
    refine ⟨6216092772566823260495381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4144061848377882173663587 6216092772566823260495381)
    ·
      refine ⟨291379348714069840335721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6216092772566823260495381 291379348714069840335721)
      ·
        refine ⟨218534511535552380251791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291379348714069840335721 218534511535552380251791)
        ·
          refine ⟨327801767303328570377687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218534511535552380251791 327801767303328570377687)
          ·
            refine ⟨491702650954992855566531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327801767303328570377687 491702650954992855566531)
            ·
              refine ⟨737553976432489283349797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491702650954992855566531 737553976432489283349797)
              ·
                refine ⟨138291370581091740628087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 737553976432489283349797 138291370581091740628087)
                ·
                  refine ⟨207437055871637610942131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138291370581091740628087 207437055871637610942131)
                  ·
                    refine ⟨311155583807456416413197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 207437055871637610942131 311155583807456416413197)
                    ·
                      refine ⟨116683343927796156154949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 311155583807456416413197 116683343927796156154949)
                      ·
                        rfl

theorem cell23_227240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_227240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227240 prefixEnd_227240 := by exact prefixLift 227240
  have htrace : WordTrace (prefixWord ++ tailWord_227240) baseStart_227240 baseEnd_227240 := by
    simpa [prefixWord, tailWord_227240, baseEnd_227240] using wordTrace_append hprefix tailTrace_227240
  have hstable : (prefixWord ++ tailWord_227240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227240).length < 2 ^ (prefixWord ++ tailWord_227240).sum := by decide
  have hdescent : baseEnd_227240 < baseStart_227240 := by decide
  rcases family_descends (prefixWord ++ tailWord_227240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227275 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 5]
def baseStart_227275 : Nat := 118140960795 + 227275 * 2 ^ 59
def prefixEnd_227275 : Nat := 4983230072969 + 3 ^ 40 * 227275 * 2
def baseEnd_227275 : Nat := 116701315750703519217287

theorem tailTrace_227275 : CollatzResearch.WordTrace tailWord_227275 prefixEnd_227275 116701315750703519217287 := by
  unfold tailWord_227275
  simp only [CollatzResearch.WordTrace]
  refine ⟨8289400251628965324851279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5526266834419310216567519 8289400251628965324851279)
  ·
    refine ⟨12434100377443447987276919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8289400251628965324851279 12434100377443447987276919)
    ·
      refine ⟨18651150566165171980915379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12434100377443447987276919 18651150566165171980915379)
      ·
        refine ⟨27976725849247757971373069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18651150566165171980915379 27976725849247757971373069)
        ·
          refine ⟨10491272193467909239264901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27976725849247757971373069 10491272193467909239264901)
          ·
            refine ⟨1967113536275232982362169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10491272193467909239264901 1967113536275232982362169)
            ·
              refine ⟨1475335152206424736771627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1967113536275232982362169 1475335152206424736771627)
              ·
                refine ⟨2213002728309637105157441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475335152206424736771627 2213002728309637105157441)
                ·
                  refine ⟨1659752046232227828868081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2213002728309637105157441 1659752046232227828868081)
                  ·
                    refine ⟨1244814034674170871651061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1659752046232227828868081 1244814034674170871651061)
                    ·
                      refine ⟨116701315750703519217287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1244814034674170871651061 116701315750703519217287)
                      ·
                        rfl

theorem cell23_227275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 5].length) (baseStart_227275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227275 prefixEnd_227275 := by exact prefixLift 227275
  have htrace : WordTrace (prefixWord ++ tailWord_227275) baseStart_227275 baseEnd_227275 := by
    simpa [prefixWord, tailWord_227275, baseEnd_227275] using wordTrace_append hprefix tailTrace_227275
  have hstable : (prefixWord ++ tailWord_227275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227275).length < 2 ^ (prefixWord ++ tailWord_227275).sum := by decide
  have hdescent : baseEnd_227275 < baseStart_227275 := by decide
  rcases family_descends (prefixWord ++ tailWord_227275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227313 : List Nat := [1, 2, 2, 2, 5, 1, 3, 1, 2, 1, 3]
def baseStart_227313 : Nat := 118140960795 + 227313 * 2 ^ 59
def prefixEnd_227313 : Nat := 4983230072969 + 3 ^ 40 * 227313 * 2
def baseEnd_227313 : Nat := 116720828015574370542113

theorem tailTrace_227313 : CollatzResearch.WordTrace tailWord_227313 prefixEnd_227313 116720828015574370542113 := by
  unfold tailWord_227313
  simp only [CollatzResearch.WordTrace]
  refine ⟨8290786225491297814734593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5527190816994198543156395 8290786225491297814734593)
  ·
    refine ⟨6218089669118473361050945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8290786225491297814734593 6218089669118473361050945)
    ·
      refine ⟨4663567251838855020788209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6218089669118473361050945 4663567251838855020788209)
      ·
        refine ⟨3497675438879141265591157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4663567251838855020788209 3497675438879141265591157)
        ·
          refine ⟨327907072394919493649171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3497675438879141265591157 327907072394919493649171)
          ·
            refine ⟨491860608592379240473757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327907072394919493649171 491860608592379240473757)
            ·
              refine ⟨184447728222142215177659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 491860608592379240473757 184447728222142215177659)
              ·
                refine ⟨276671592333213322766489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184447728222142215177659 276671592333213322766489)
                ·
                  refine ⟨207503694249909992074867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276671592333213322766489 207503694249909992074867)
                  ·
                    refine ⟨311255541374864988112301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 207503694249909992074867 311255541374864988112301)
                    ·
                      refine ⟨116720828015574370542113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 311255541374864988112301 116720828015574370542113)
                      ·
                        rfl

theorem cell23_227313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_227313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227313 prefixEnd_227313 := by exact prefixLift 227313
  have htrace : WordTrace (prefixWord ++ tailWord_227313) baseStart_227313 baseEnd_227313 := by
    simpa [prefixWord, tailWord_227313, baseEnd_227313] using wordTrace_append hprefix tailTrace_227313
  have hstable : (prefixWord ++ tailWord_227313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227313).length < 2 ^ (prefixWord ++ tailWord_227313).sum := by decide
  have hdescent : baseEnd_227313 < baseStart_227313 := by decide
  rcases family_descends (prefixWord ++ tailWord_227313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227345 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 6]
def baseStart_227345 : Nat := 118140960795 + 227345 * 2 ^ 59
def prefixEnd_227345 : Nat := 4983230072969 + 3 ^ 40 * 227345 * 2
def baseEnd_227345 : Nat := 116737259396518245341965

theorem tailTrace_227345 : CollatzResearch.WordTrace tailWord_227345 prefixEnd_227345 116737259396518245341965 := by
  unfold tailWord_227345
  simp only [CollatzResearch.WordTrace]
  refine ⟨8291953361375367279899489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5527968907583578186599659 8291953361375367279899489)
  ·
    refine ⟨6218965021031525459924617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8291953361375367279899489 6218965021031525459924617)
    ·
      refine ⟨4664223765773644094943463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6218965021031525459924617 4664223765773644094943463)
      ·
        refine ⟨6996335648660466142415195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4664223765773644094943463 6996335648660466142415195)
        ·
          refine ⟨10494503472990699213622793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6996335648660466142415195 10494503472990699213622793)
          ·
            refine ⟨7870877604743024410217095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10494503472990699213622793 7870877604743024410217095)
            ·
              refine ⟨11806316407114536615325643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7870877604743024410217095 11806316407114536615325643)
              ·
                refine ⟨17709474610671804922988465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11806316407114536615325643 17709474610671804922988465)
                ·
                  refine ⟨13282105958003853692241349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17709474610671804922988465 13282105958003853692241349)
                  ·
                    refine ⟨2490394867125722567295253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13282105958003853692241349 2490394867125722567295253)
                    ·
                      refine ⟨116737259396518245341965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2490394867125722567295253 116737259396518245341965)
                      ·
                        rfl

theorem cell23_227345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_227345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227345 prefixEnd_227345 := by exact prefixLift 227345
  have htrace : WordTrace (prefixWord ++ tailWord_227345) baseStart_227345 baseEnd_227345 := by
    simpa [prefixWord, tailWord_227345, baseEnd_227345] using wordTrace_append hprefix tailTrace_227345
  have hstable : (prefixWord ++ tailWord_227345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227345).length < 2 ^ (prefixWord ++ tailWord_227345).sum := by decide
  have hdescent : baseEnd_227345 < baseStart_227345 := by decide
  rcases family_descends (prefixWord ++ tailWord_227345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227355 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 3, 7]
def baseStart_227355 : Nat := 118140960795 + 227355 * 2 ^ 59
def prefixEnd_227355 : Nat := 4983230072969 + 3 ^ 40 * 227355 * 2
def baseEnd_227355 : Nat := 38914131401021068738973

theorem tailTrace_227355 : CollatzResearch.WordTrace tailWord_227355 prefixEnd_227355 38914131401021068738973 := by
  unfold tailWord_227355
  simp only [CollatzResearch.WordTrace]
  refine ⟨8292318091339138987763519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5528212060892759325175679 8292318091339138987763519)
  ·
    refine ⟨12438477137008708481645279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8292318091339138987763519 12438477137008708481645279)
    ·
      refine ⟨18657715705513062722467919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12438477137008708481645279 18657715705513062722467919)
      ·
        refine ⟨27986573558269594083701879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18657715705513062722467919 27986573558269594083701879)
        ·
          refine ⟨41979860337404391125552819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27986573558269594083701879 41979860337404391125552819)
          ·
            refine ⟨62969790506106586688329229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41979860337404391125552819 62969790506106586688329229)
            ·
              refine ⟨23613671439789970008123461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62969790506106586688329229 23613671439789970008123461)
              ·
                refine ⟨4427563394960619376523149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23613671439789970008123461 4427563394960619376523149)
                ·
                  refine ⟨1660336273110232266196181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4427563394960619376523149 1660336273110232266196181)
                  ·
                    refine ⟨38914131401021068738973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1660336273110232266196181 38914131401021068738973)
                    ·
                      rfl

theorem cell23_227355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 7].length) (baseStart_227355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227355 prefixEnd_227355 := by exact prefixLift 227355
  have htrace : WordTrace (prefixWord ++ tailWord_227355) baseStart_227355 baseEnd_227355 := by
    simpa [prefixWord, tailWord_227355, baseEnd_227355] using wordTrace_append hprefix tailTrace_227355
  have hstable : (prefixWord ++ tailWord_227355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227355).length < 2 ^ (prefixWord ++ tailWord_227355).sum := by decide
  have hdescent : baseEnd_227355 < baseStart_227355 := by decide
  rcases family_descends (prefixWord ++ tailWord_227355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227370 : List Nat := [3, 1, 4, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_227370 : Nat := 118140960795 + 227370 * 2 ^ 59
def prefixEnd_227370 : Nat := 4983230072969 + 3 ^ 40 * 227370 * 2
def baseEnd_227370 : Nat := 116750096412880647529351

theorem tailTrace_227370 : CollatzResearch.WordTrace tailWord_227370 prefixEnd_227370 116750096412880647529351 := by
  unfold tailWord_227370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2073216296571199137389891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5528576790856531033039709 2073216296571199137389891)
  ·
    refine ⟨3109824444856798706084837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2073216296571199137389891 3109824444856798706084837)
    ·
      refine ⟨583092083410649757390907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3109824444856798706084837 583092083410649757390907)
      ·
        refine ⟨874638125115974636086361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583092083410649757390907 874638125115974636086361)
        ·
          refine ⟨655978593836980977064771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 874638125115974636086361 655978593836980977064771)
          ·
            refine ⟨983967890755471465597157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655978593836980977064771 983967890755471465597157)
            ·
              refine ⟨184493979516650899799467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 983967890755471465597157 184493979516650899799467)
              ·
                refine ⟨276740969274976349699201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184493979516650899799467 276740969274976349699201)
                ·
                  refine ⟨207555726956232262274401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276740969274976349699201 207555726956232262274401)
                  ·
                    refine ⟨155666795217174196705801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 207555726956232262274401 155666795217174196705801)
                    ·
                      refine ⟨116750096412880647529351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 155666795217174196705801 116750096412880647529351)
                      ·
                        rfl

theorem cell23_227370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_227370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227370 prefixEnd_227370 := by exact prefixLift 227370
  have htrace : WordTrace (prefixWord ++ tailWord_227370) baseStart_227370 baseEnd_227370 := by
    simpa [prefixWord, tailWord_227370, baseEnd_227370] using wordTrace_append hprefix tailTrace_227370
  have hstable : (prefixWord ++ tailWord_227370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227370).length < 2 ^ (prefixWord ++ tailWord_227370).sum := by decide
  have hdescent : baseEnd_227370 < baseStart_227370 := by decide
  rcases family_descends (prefixWord ++ tailWord_227370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227389 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 2, 5]
def baseStart_227389 : Nat := 118140960795 + 227389 * 2 ^ 59
def prefixEnd_227389 : Nat := 4983230072969 + 3 ^ 40 * 227389 * 2
def baseEnd_227389 : Nat := 38919950848438691063921

theorem tailTrace_227389 : CollatzResearch.WordTrace tailWord_227389 prefixEnd_227389 38919950848438691063921 := by
  unfold tailWord_227389
  simp only [CollatzResearch.WordTrace]
  refine ⟨8293558173215962794501221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5529038782143975196334147 8293558173215962794501221)
  ·
    refine ⟨1555042157477993023968979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8293558173215962794501221 1555042157477993023968979)
    ·
      refine ⟨2332563236216989535953469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1555042157477993023968979 2332563236216989535953469)
      ·
        refine ⟨874711213581371075982551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2332563236216989535953469 874711213581371075982551)
        ·
          refine ⟨1312066820372056613973827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874711213581371075982551 1312066820372056613973827)
          ·
            refine ⟨1968100230558084920960741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312066820372056613973827 1968100230558084920960741)
            ·
              refine ⟨369018793229640922680139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1968100230558084920960741 369018793229640922680139)
              ·
                refine ⟨553528189844461384020209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369018793229640922680139 553528189844461384020209)
                ·
                  refine ⟨415146142383346038015157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553528189844461384020209 415146142383346038015157)
                  ·
                    refine ⟨38919950848438691063921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 415146142383346038015157 38919950848438691063921)
                    ·
                      rfl

theorem cell23_227389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_227389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227389 prefixEnd_227389 := by exact prefixLift 227389
  have htrace : WordTrace (prefixWord ++ tailWord_227389) baseStart_227389 baseEnd_227389 := by
    simpa [prefixWord, tailWord_227389, baseEnd_227389] using wordTrace_append hprefix tailTrace_227389
  have hstable : (prefixWord ++ tailWord_227389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227389).length < 2 ^ (prefixWord ++ tailWord_227389).sum := by decide
  have hdescent : baseEnd_227389 < baseStart_227389 := by decide
  rcases family_descends (prefixWord ++ tailWord_227389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227409 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 2, 4, 2]
def baseStart_227409 : Nat := 118140960795 + 227409 * 2 ^ 59
def prefixEnd_227409 : Nat := 4983230072969 + 3 ^ 40 * 227409 * 2
def baseEnd_227409 : Nat := 116770122158405994941671

theorem tailTrace_227409 : CollatzResearch.WordTrace tailWord_227409 prefixEnd_227409 116770122158405994941671 := by
  unfold tailWord_227409
  simp only [CollatzResearch.WordTrace]
  refine ⟨8294287633143506210229281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5529525088762337473486187 8294287633143506210229281)
  ·
    refine ⟨6220715724857629657671961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8294287633143506210229281 6220715724857629657671961)
    ·
      refine ⟨4665536793643222243253971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6220715724857629657671961 4665536793643222243253971)
      ·
        refine ⟨6998305190464833364880957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4665536793643222243253971 6998305190464833364880957)
        ·
          refine ⟨2624364446424312511830359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6998305190464833364880957 2624364446424312511830359)
          ·
            refine ⟨3936546669636468767745539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2624364446424312511830359 3936546669636468767745539)
            ·
              refine ⟨5904820004454703151618309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3936546669636468767745539 5904820004454703151618309)
              ·
                refine ⟨1107153750835256840928433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5904820004454703151618309 1107153750835256840928433)
                ·
                  refine ⟨830365313126442630696325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1107153750835256840928433 830365313126442630696325)
                  ·
                    refine ⟨155693496211207993255561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 830365313126442630696325 155693496211207993255561)
                    ·
                      refine ⟨116770122158405994941671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 155693496211207993255561 116770122158405994941671)
                      ·
                        rfl

theorem cell23_227409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 4, 2].length) (baseStart_227409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227409 prefixEnd_227409 := by exact prefixLift 227409
  have htrace : WordTrace (prefixWord ++ tailWord_227409) baseStart_227409 baseEnd_227409 := by
    simpa [prefixWord, tailWord_227409, baseEnd_227409] using wordTrace_append hprefix tailTrace_227409
  have hstable : (prefixWord ++ tailWord_227409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227409).length < 2 ^ (prefixWord ++ tailWord_227409).sum := by decide
  have hdescent : baseEnd_227409 < baseStart_227409 := by decide
  rcases family_descends (prefixWord ++ tailWord_227409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227410 : List Nat := [3, 2, 2, 1, 5, 1, 2, 2, 5]
def baseStart_227410 : Nat := 118140960795 + 227410 * 2 ^ 59
def prefixEnd_227410 : Nat := 4983230072969 + 3 ^ 40 * 227410 * 2
def baseEnd_227410 : Nat := 12974515071006721225463

theorem tailTrace_227410 : CollatzResearch.WordTrace tailWord_227410 prefixEnd_227410 12974515071006721225463 := by
  unfold tailWord_227410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2073581026534970845253921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5529549404093255587343789 2073581026534970845253921)
  ·
    refine ⟨1555185769901228133940441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2073581026534970845253921 1555185769901228133940441)
    ·
      refine ⟨1166389327425921100455331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1555185769901228133940441 1166389327425921100455331)
      ·
        refine ⟨1749583991138881650682997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1166389327425921100455331 1749583991138881650682997)
        ·
          refine ⟨164023499169270154751531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1749583991138881650682997 164023499169270154751531)
          ·
            refine ⟨246035248753905232127297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164023499169270154751531 246035248753905232127297)
            ·
              refine ⟨184526436565428924095473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246035248753905232127297 184526436565428924095473)
              ·
                refine ⟨138394827424071693071605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184526436565428924095473 138394827424071693071605)
                ·
                  refine ⟨12974515071006721225463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138394827424071693071605 12974515071006721225463)
                  ·
                    rfl

theorem cell23_227410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_227410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227410 prefixEnd_227410 := by exact prefixLift 227410
  have htrace : WordTrace (prefixWord ++ tailWord_227410) baseStart_227410 baseEnd_227410 := by
    simpa [prefixWord, tailWord_227410, baseEnd_227410] using wordTrace_append hprefix tailTrace_227410
  have hstable : (prefixWord ++ tailWord_227410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227410).length < 2 ^ (prefixWord ++ tailWord_227410).sum := by decide
  have hdescent : baseEnd_227410 < baseStart_227410 := by decide
  rcases family_descends (prefixWord ++ tailWord_227410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227412 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_227412 : Nat := 118140960795 + 227412 * 2 ^ 59
def prefixEnd_227412 : Nat := 4983230072969 + 3 ^ 40 * 227412 * 2
def baseEnd_227412 : Nat := 116771662600369483204157

theorem tailTrace_227412 : CollatzResearch.WordTrace tailWord_227412 prefixEnd_227412 116771662600369483204157 := by
  unfold tailWord_227412
  simp only [CollatzResearch.WordTrace]
  refine ⟨4147198526066318861294245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5529598034755091815058993 4147198526066318861294245)
  ·
    refine ⟨777599723637434786492671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4147198526066318861294245 777599723637434786492671)
    ·
      refine ⟨1166399585456152179739007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 777599723637434786492671 1166399585456152179739007)
      ·
        refine ⟨1749599378184228269608511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1166399585456152179739007 1749599378184228269608511)
        ·
          refine ⟨2624399067276342404412767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1749599378184228269608511 2624399067276342404412767)
          ·
            refine ⟨3936598600914513606619151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2624399067276342404412767 3936598600914513606619151)
            ·
              refine ⟨5904897901371770409928727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3936598600914513606619151 5904897901371770409928727)
              ·
                refine ⟨8857346852057655614893091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5904897901371770409928727 8857346852057655614893091)
                ·
                  refine ⟨13286020278086483422339637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8857346852057655614893091 13286020278086483422339637)
                  ·
                    refine ⟨1245564401070607820844341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13286020278086483422339637 1245564401070607820844341)
                    ·
                      refine ⟨116771662600369483204157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1245564401070607820844341 116771662600369483204157)
                      ·
                        rfl

theorem cell23_227412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_227412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227412 prefixEnd_227412 := by exact prefixLift 227412
  have htrace : WordTrace (prefixWord ++ tailWord_227412) baseStart_227412 baseEnd_227412 := by
    simpa [prefixWord, tailWord_227412, baseEnd_227412] using wordTrace_append hprefix tailTrace_227412
  have hstable : (prefixWord ++ tailWord_227412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227412).length < 2 ^ (prefixWord ++ tailWord_227412).sum := by decide
  have hdescent : baseEnd_227412 < baseStart_227412 := by decide
  rcases family_descends (prefixWord ++ tailWord_227412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227446 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_227446 : Nat := 118140960795 + 227446 * 2 ^ 59
def prefixEnd_227446 : Nat := 4983230072969 + 3 ^ 40 * 227446 * 2
def baseEnd_227446 : Nat := 116789120942622350179001

theorem tailTrace_227446 : CollatzResearch.WordTrace tailWord_227446 prefixEnd_227446 116789120942622350179001 := by
  unfold tailWord_227446
  simp only [CollatzResearch.WordTrace]
  refine ⟨518477320875591345582887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5530424756006307686217461 518477320875591345582887)
  ·
    refine ⟨777715981313387018374331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 518477320875591345582887 777715981313387018374331)
    ·
      refine ⟨1166573971970080527561497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 777715981313387018374331 1166573971970080527561497)
      ·
        refine ⟨874930478977560395671123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1166573971970080527561497 874930478977560395671123)
        ·
          refine ⟨1312395718466340593506685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874930478977560395671123 1312395718466340593506685)
          ·
            refine ⟨492148394424877722565007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1312395718466340593506685 492148394424877722565007)
            ·
              refine ⟨738222591637316583847511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492148394424877722565007 738222591637316583847511)
              ·
                refine ⟨1107333887455974875771267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738222591637316583847511 1107333887455974875771267)
                ·
                  refine ⟨1661000831183962313656901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1107333887455974875771267 1661000831183962313656901)
                  ·
                    refine ⟨311437655846992933810669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1661000831183962313656901 311437655846992933810669)
                    ·
                      refine ⟨116789120942622350179001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 311437655846992933810669 116789120942622350179001)
                      ·
                        rfl

theorem cell23_227446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_227446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227446 prefixEnd_227446 := by exact prefixLift 227446
  have htrace : WordTrace (prefixWord ++ tailWord_227446) baseStart_227446 baseEnd_227446 := by
    simpa [prefixWord, tailWord_227446, baseEnd_227446] using wordTrace_append hprefix tailTrace_227446
  have hstable : (prefixWord ++ tailWord_227446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227446).length < 2 ^ (prefixWord ++ tailWord_227446).sum := by decide
  have hdescent : baseEnd_227446 < baseStart_227446 := by decide
  rcases family_descends (prefixWord ++ tailWord_227446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227453 : List Nat := [1, 4, 1, 1, 3, 3, 2, 3, 1, 4]
def baseStart_227453 : Nat := 118140960795 + 227453 * 2 ^ 59
def prefixEnd_227453 : Nat := 4983230072969 + 3 ^ 40 * 227453 * 2
def baseEnd_227453 : Nat := 38930905102401274263823

theorem tailTrace_227453 : CollatzResearch.WordTrace tailWord_227453 prefixEnd_227453 38930905102401274263823 := by
  unfold tailWord_227453
  simp only [CollatzResearch.WordTrace]
  refine ⟨8295892444984101724831013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5530594963322734483220675 8295892444984101724831013)
  ·
    refine ⟨1555479833434519073405815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8295892444984101724831013 1555479833434519073405815)
    ·
      refine ⟨2333219750151778610108723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1555479833434519073405815 2333219750151778610108723)
      ·
        refine ⟨3499829625227667915163085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2333219750151778610108723 3499829625227667915163085)
        ·
          refine ⟨1312436109460375468186157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3499829625227667915163085 1312436109460375468186157)
          ·
            refine ⟨492163541047640800569809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1312436109460375468186157 492163541047640800569809)
            ·
              refine ⟨369122655785730600427357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492163541047640800569809 369122655785730600427357)
              ·
                refine ⟨138420995919648975160259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369122655785730600427357 138420995919648975160259)
                ·
                  refine ⟨207631493879473462740389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138420995919648975160259 207631493879473462740389)
                  ·
                    refine ⟨38930905102401274263823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 207631493879473462740389 38930905102401274263823)
                    ·
                      rfl

theorem cell23_227453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_227453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227453 prefixEnd_227453 := by exact prefixLift 227453
  have htrace : WordTrace (prefixWord ++ tailWord_227453) baseStart_227453 baseEnd_227453 := by
    simpa [prefixWord, tailWord_227453, baseEnd_227453] using wordTrace_append hprefix tailTrace_227453
  have hstable : (prefixWord ++ tailWord_227453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227453).length < 2 ^ (prefixWord ++ tailWord_227453).sum := by decide
  have hdescent : baseEnd_227453 < baseStart_227453 := by decide
  rcases family_descends (prefixWord ++ tailWord_227453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227466 : List Nat := [3, 1, 2, 3, 1, 4, 1, 2, 6]
def baseStart_227466 : Nat := 118140960795 + 227466 * 2 ^ 59
def prefixEnd_227466 : Nat := 4983230072969 + 3 ^ 40 * 227466 * 2
def baseEnd_227466 : Nat := 12977710061745807992101

theorem tailTrace_227466 : CollatzResearch.WordTrace tailWord_227466 prefixEnd_227466 12977710061745807992101 := by
  unfold tailWord_227466
  simp only [CollatzResearch.WordTrace]
  refine ⟨2074091648484251236263563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5530911062624669963369501 2074091648484251236263563)
  ·
    refine ⟨3111137472726376854395345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2074091648484251236263563 3111137472726376854395345)
    ·
      refine ⟨2333353104544782640796509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3111137472726376854395345 2333353104544782640796509)
      ·
        refine ⟨875007414204293490298691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2333353104544782640796509 875007414204293490298691)
        ·
          refine ⟨1312511121306440235448037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875007414204293490298691 1312511121306440235448037)
          ·
            refine ⟨246095835244957544146507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1312511121306440235448037 246095835244957544146507)
            ·
              refine ⟨369143752867436316219761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246095835244957544146507 369143752867436316219761)
              ·
                refine ⟨276857814650577237164821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369143752867436316219761 276857814650577237164821)
                ·
                  refine ⟨12977710061745807992101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 276857814650577237164821 12977710061745807992101)
                  ·
                    rfl

theorem cell23_227466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 6].length) (baseStart_227466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227466 prefixEnd_227466 := by exact prefixLift 227466
  have htrace : WordTrace (prefixWord ++ tailWord_227466) baseStart_227466 baseEnd_227466 := by
    simpa [prefixWord, tailWord_227466, baseEnd_227466] using wordTrace_append hprefix tailTrace_227466
  have hstable : (prefixWord ++ tailWord_227466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227466).length < 2 ^ (prefixWord ++ tailWord_227466).sum := by decide
  have hdescent : baseEnd_227466 < baseStart_227466 := by decide
  rcases family_descends (prefixWord ++ tailWord_227466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227519 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 3]
def baseStart_227519 : Nat := 118140960795 + 227519 * 2 ^ 59
def prefixEnd_227519 : Nat := 4983230072969 + 3 ^ 40 * 227519 * 2
def baseEnd_227519 : Nat := 116826605030400564566165

theorem tailTrace_227519 : CollatzResearch.WordTrace tailWord_227519 prefixEnd_227519 116826605030400564566165 := by
  unfold tailWord_227519
  simp only [CollatzResearch.WordTrace]
  refine ⟨8298299662744994996733611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5532199775163329997822407 8298299662744994996733611)
  ·
    refine ⟨12447449494117492495100417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8298299662744994996733611 12447449494117492495100417)
    ·
      refine ⟨9335587120588119371325313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12447449494117492495100417 9335587120588119371325313)
      ·
        refine ⟨7001690340441089528493985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9335587120588119371325313 7001690340441089528493985)
        ·
          refine ⟨5251267755330817146370489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7001690340441089528493985 5251267755330817146370489)
          ·
            refine ⟨3938450816498112859777867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5251267755330817146370489 3938450816498112859777867)
            ·
              refine ⟨5907676224747169289666801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3938450816498112859777867 5907676224747169289666801)
              ·
                refine ⟨4430757168560376967250101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5907676224747169289666801 4430757168560376967250101)
                ·
                  refine ⟨415383484552535340679697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4430757168560376967250101 415383484552535340679697)
                  ·
                    refine ⟨311537613414401505509773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 415383484552535340679697 311537613414401505509773)
                    ·
                      refine ⟨116826605030400564566165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 311537613414401505509773 116826605030400564566165)
                      ·
                        rfl

theorem cell23_227519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_227519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227519 prefixEnd_227519 := by exact prefixLift 227519
  have htrace : WordTrace (prefixWord ++ tailWord_227519) baseStart_227519 baseEnd_227519 := by
    simpa [prefixWord, tailWord_227519, baseEnd_227519] using wordTrace_append hprefix tailTrace_227519
  have hstable : (prefixWord ++ tailWord_227519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227519).length < 2 ^ (prefixWord ++ tailWord_227519).sum := by decide
  have hdescent : baseEnd_227519 < baseStart_227519 := by decide
  rcases family_descends (prefixWord ++ tailWord_227519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227554 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_227554 : Nat := 118140960795 + 227554 * 2 ^ 59
def prefixEnd_227554 : Nat := 4983230072969 + 3 ^ 40 * 227554 * 2
def baseEnd_227554 : Nat := 116844576853307927628505

theorem tailTrace_227554 : CollatzResearch.WordTrace tailWord_227554 prefixEnd_227554 116844576853307927628505 := by
  unfold tailWord_227554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2074894054404548993564429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5533050811745463982838477 2074894054404548993564429)
  ·
    refine ⟨778085270401705872586661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2074894054404548993564429 778085270401705872586661)
    ·
      refine ⟨145890988200319851109999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 778085270401705872586661 145890988200319851109999)
      ·
        refine ⟨218836482300479776664999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145890988200319851109999 218836482300479776664999)
        ·
          refine ⟨328254723450719664997499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218836482300479776664999 328254723450719664997499)
          ·
            refine ⟨492382085176079497496249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328254723450719664997499 492382085176079497496249)
            ·
              refine ⟨369286563882059623122187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492382085176079497496249 369286563882059623122187)
              ·
                refine ⟨553929845823089434683281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369286563882059623122187 553929845823089434683281)
                ·
                  refine ⟨415447384367317076012461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553929845823089434683281 415447384367317076012461)
                  ·
                    refine ⟨155792769137743903504673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 415447384367317076012461 155792769137743903504673)
                    ·
                      refine ⟨116844576853307927628505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 155792769137743903504673 116844576853307927628505)
                      ·
                        rfl

theorem cell23_227554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_227554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227554 prefixEnd_227554 := by exact prefixLift 227554
  have htrace : WordTrace (prefixWord ++ tailWord_227554) baseStart_227554 baseEnd_227554 := by
    simpa [prefixWord, tailWord_227554, baseEnd_227554] using wordTrace_append hprefix tailTrace_227554
  have hstable : (prefixWord ++ tailWord_227554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227554).length < 2 ^ (prefixWord ++ tailWord_227554).sum := by decide
  have hdescent : baseEnd_227554 < baseStart_227554 := by decide
  rcases family_descends (prefixWord ++ tailWord_227554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227570 : List Nat := [3, 2, 1, 3, 2, 2, 3, 1, 1, 2, 3]
def baseStart_227570 : Nat := 118140960795 + 227570 * 2 ^ 59
def prefixEnd_227570 : Nat := 4983230072969 + 3 ^ 40 * 227570 * 2
def baseEnd_227570 : Nat := 116852792543779865028431

theorem tailTrace_227570 : CollatzResearch.WordTrace tailWord_227570 prefixEnd_227570 116852792543779865028431 := by
  unfold tailWord_227570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2075039946390057676710041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5533439857040153804560109 2075039946390057676710041)
  ·
    refine ⟨1556279959792543257532531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2075039946390057676710041 1556279959792543257532531)
    ·
      refine ⟨2334419939688814886298797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1556279959792543257532531 2334419939688814886298797)
      ·
        refine ⟨875407477383305582362049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2334419939688814886298797 875407477383305582362049)
        ·
          refine ⟨656555608037479186771537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 875407477383305582362049 656555608037479186771537)
          ·
            refine ⟨492416706028109390078653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 656555608037479186771537 492416706028109390078653)
            ·
              refine ⟨184656264760541021279495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 492416706028109390078653 184656264760541021279495)
              ·
                refine ⟨276984397140811531919243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184656264760541021279495 276984397140811531919243)
                ·
                  refine ⟨415476595711217297878865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276984397140811531919243 415476595711217297878865)
                  ·
                    refine ⟨311607446783412973409149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 415476595711217297878865 311607446783412973409149)
                    ·
                      refine ⟨116852792543779865028431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 311607446783412973409149 116852792543779865028431)
                      ·
                        rfl

theorem cell23_227570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_227570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227570 prefixEnd_227570 := by exact prefixLift 227570
  have htrace : WordTrace (prefixWord ++ tailWord_227570) baseStart_227570 baseEnd_227570 := by
    simpa [prefixWord, tailWord_227570, baseEnd_227570] using wordTrace_append hprefix tailTrace_227570
  have hstable : (prefixWord ++ tailWord_227570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227570).length < 2 ^ (prefixWord ++ tailWord_227570).sum := by decide
  have hdescent : baseEnd_227570 < baseStart_227570 := by decide
  rcases family_descends (prefixWord ++ tailWord_227570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227583 : List Nat := [1, 1, 2, 2, 1, 4, 4, 2, 2, 1, 3]
def baseStart_227583 : Nat := 118140960795 + 227583 * 2 ^ 59
def prefixEnd_227583 : Nat := 4983230072969 + 3 ^ 40 * 227583 * 2
def baseEnd_227583 : Nat := 116859467792288314165871

theorem tailTrace_227583 : CollatzResearch.WordTrace tailWord_227583 prefixEnd_227583 116859467792288314165871 := by
  unfold tailWord_227583
  simp only [CollatzResearch.WordTrace]
  refine ⟨8300633934513133927063403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5533755956342089284708935 8300633934513133927063403)
  ·
    refine ⟨12450950901769700890595105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8300633934513133927063403 12450950901769700890595105)
    ·
      refine ⟨9338213176327275667946329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12450950901769700890595105 9338213176327275667946329)
      ·
        refine ⟨7003659882245456750959747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9338213176327275667946329 7003659882245456750959747)
        ·
          refine ⟨10505489823368185126439621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7003659882245456750959747 10505489823368185126439621)
          ·
            refine ⟨1969779341881534711207429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10505489823368185126439621 1969779341881534711207429)
            ·
              refine ⟨369333626602787758351393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1969779341881534711207429 369333626602787758351393)
              ·
                refine ⟨277000219952090818763545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369333626602787758351393 277000219952090818763545)
                ·
                  refine ⟨207750164964068114072659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277000219952090818763545 207750164964068114072659)
                  ·
                    refine ⟨311625247446102171108989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 207750164964068114072659 311625247446102171108989)
                    ·
                      refine ⟨116859467792288314165871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 311625247446102171108989 116859467792288314165871)
                      ·
                        rfl

theorem cell23_227583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 1, 3].length) (baseStart_227583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227583 prefixEnd_227583 := by exact prefixLift 227583
  have htrace : WordTrace (prefixWord ++ tailWord_227583) baseStart_227583 baseEnd_227583 := by
    simpa [prefixWord, tailWord_227583, baseEnd_227583] using wordTrace_append hprefix tailTrace_227583
  have hstable : (prefixWord ++ tailWord_227583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227583).length < 2 ^ (prefixWord ++ tailWord_227583).sum := by decide
  have hdescent : baseEnd_227583 < baseStart_227583 := by decide
  rcases family_descends (prefixWord ++ tailWord_227583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227586 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_227586 : Nat := 118140960795 + 227586 * 2 ^ 59
def prefixEnd_227586 : Nat := 4983230072969 + 3 ^ 40 * 227586 * 2
def baseEnd_227586 : Nat := 38953669411417267476119

theorem tailTrace_227586 : CollatzResearch.WordTrace tailWord_227586 prefixEnd_227586 38953669411417267476119 := by
  unfold tailWord_227586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2075185838375566359855653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5533828902334843626281741 2075185838375566359855653)
  ·
    refine ⟨389097344695418692472935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2075185838375566359855653 389097344695418692472935)
    ·
      refine ⟨583646017043128038709403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389097344695418692472935 583646017043128038709403)
      ·
        refine ⟨875469025564692058064105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583646017043128038709403 875469025564692058064105)
        ·
          refine ⟨656601769173519043548079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 875469025564692058064105 656601769173519043548079)
          ·
            refine ⟨984902653760278565322119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656601769173519043548079 984902653760278565322119)
            ·
              refine ⟨1477353980640417847983179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984902653760278565322119 1477353980640417847983179)
              ·
                refine ⟨2216030970960626771974769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1477353980640417847983179 2216030970960626771974769)
                ·
                  refine ⟨1662023228220470078981077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2216030970960626771974769 1662023228220470078981077)
                  ·
                    refine ⟨38953669411417267476119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1662023228220470078981077 38953669411417267476119)
                    ·
                      rfl

theorem cell23_227586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_227586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227586 prefixEnd_227586 := by exact prefixLift 227586
  have htrace : WordTrace (prefixWord ++ tailWord_227586) baseStart_227586 baseEnd_227586 := by
    simpa [prefixWord, tailWord_227586, baseEnd_227586] using wordTrace_append hprefix tailTrace_227586
  have hstable : (prefixWord ++ tailWord_227586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227586).length < 2 ^ (prefixWord ++ tailWord_227586).sum := by decide
  have hdescent : baseEnd_227586 < baseStart_227586 := by decide
  rcases family_descends (prefixWord ++ tailWord_227586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227619 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 4]
def baseStart_227619 : Nat := 118140960795 + 227619 * 2 ^ 59
def prefixEnd_227619 : Nat := 4983230072969 + 3 ^ 40 * 227619 * 2
def baseEnd_227619 : Nat := 116877953095850173315705

theorem tailTrace_227619 : CollatzResearch.WordTrace tailWord_227619 prefixEnd_227619 116877953095850173315705 := by
  unfold tailWord_227619
  simp only [CollatzResearch.WordTrace]
  refine ⟨8301946962382712075373911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5534631308255141383582607 8301946962382712075373911)
  ·
    refine ⟨12452920443574068113060867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8301946962382712075373911 12452920443574068113060867)
    ·
      refine ⟨18679380665361102169591301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12452920443574068113060867 18679380665361102169591301)
      ·
        refine ⟨3502383874755206656798369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18679380665361102169591301 3502383874755206656798369)
        ·
          refine ⟨2626787906066404992598777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3502383874755206656798369 2626787906066404992598777)
          ·
            refine ⟨1970090929549803744449083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2626787906066404992598777 1970090929549803744449083)
            ·
              refine ⟨2955136394324705616673625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1970090929549803744449083 2955136394324705616673625)
              ·
                refine ⟨2216352295743529212505219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2955136394324705616673625 2216352295743529212505219)
                ·
                  refine ⟨3324528443615293818757829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2216352295743529212505219 3324528443615293818757829)
                  ·
                    refine ⟨623349083177867591017093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3324528443615293818757829 623349083177867591017093)
                    ·
                      refine ⟨116877953095850173315705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 623349083177867591017093 116877953095850173315705)
                      ·
                        rfl

theorem cell23_227619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_227619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227619 prefixEnd_227619 := by exact prefixLift 227619
  have htrace : WordTrace (prefixWord ++ tailWord_227619) baseStart_227619 baseEnd_227619 := by
    simpa [prefixWord, tailWord_227619, baseEnd_227619] using wordTrace_append hprefix tailTrace_227619
  have hstable : (prefixWord ++ tailWord_227619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227619).length < 2 ^ (prefixWord ++ tailWord_227619).sum := by decide
  have hdescent : baseEnd_227619 < baseStart_227619 := by decide
  rcases family_descends (prefixWord ++ tailWord_227619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227640 : List Nat := [2, 1, 2, 1, 3, 1, 5, 2, 2, 2, 2]
def baseStart_227640 : Nat := 118140960795 + 227640 * 2 ^ 59
def prefixEnd_227640 : Nat := 4983230072969 + 3 ^ 40 * 227640 * 2
def baseEnd_227640 : Nat := 116888736189594591153109

theorem tailTrace_227640 : CollatzResearch.WordTrace tailWord_227640 prefixEnd_227640 116888736189594591153109 := by
  unfold tailWord_227640
  simp only [CollatzResearch.WordTrace]
  refine ⟨4151356447653316330944187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5535141930204421774592249 4151356447653316330944187)
  ·
    refine ⟨6227034671479974496416281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4151356447653316330944187 6227034671479974496416281)
    ·
      refine ⟨4670276003609980872312211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6227034671479974496416281 4670276003609980872312211)
      ·
        refine ⟨7005414005414971308468317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4670276003609980872312211 7005414005414971308468317)
        ·
          refine ⟨2627030252030614240675619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7005414005414971308468317 2627030252030614240675619)
          ·
            refine ⟨3940545378045921361013429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2627030252030614240675619 3940545378045921361013429)
            ·
              refine ⟨369426129191805127595009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3940545378045921361013429 369426129191805127595009)
              ·
                refine ⟨277069596893853845696257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369426129191805127595009 277069596893853845696257)
                ·
                  refine ⟨207802197670390384272193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277069596893853845696257 207802197670390384272193)
                  ·
                    refine ⟨155851648252792788204145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 207802197670390384272193 155851648252792788204145)
                    ·
                      refine ⟨116888736189594591153109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 155851648252792788204145 116888736189594591153109)
                      ·
                        rfl

theorem cell23_227640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 2, 2, 2].length) (baseStart_227640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227640 prefixEnd_227640 := by exact prefixLift 227640
  have htrace : WordTrace (prefixWord ++ tailWord_227640) baseStart_227640 baseEnd_227640 := by
    simpa [prefixWord, tailWord_227640, baseEnd_227640] using wordTrace_append hprefix tailTrace_227640
  have hstable : (prefixWord ++ tailWord_227640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227640).length < 2 ^ (prefixWord ++ tailWord_227640).sum := by decide
  have hdescent : baseEnd_227640 < baseStart_227640 := by decide
  rcases family_descends (prefixWord ++ tailWord_227640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227646 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 7]
def baseStart_227646 : Nat := 118140960795 + 227646 * 2 ^ 59
def prefixEnd_227646 : Nat := 4983230072969 + 3 ^ 40 * 227646 * 2
def baseEnd_227646 : Nat := 12987979674835729742009

theorem tailTrace_227646 : CollatzResearch.WordTrace tailWord_227646 prefixEnd_227646 12987979674835729742009 := by
  unfold tailWord_227646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1037866466660611960825849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5535287822189930457737861 1037866466660611960825849)
  ·
    refine ⟨778399849995458970619387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1037866466660611960825849 778399849995458970619387)
    ·
      refine ⟨1167599774993188455929081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 778399849995458970619387 1167599774993188455929081)
      ·
        refine ⟨875699831244891341946811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1167599774993188455929081 875699831244891341946811)
        ·
          refine ⟨1313549746867337012920217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875699831244891341946811 1313549746867337012920217)
          ·
            refine ⟨985162310150502759690163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1313549746867337012920217 985162310150502759690163)
            ·
              refine ⟨1477743465225754139535245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985162310150502759690163 1477743465225754139535245)
              ·
                refine ⟨554153799459657802325717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1477743465225754139535245 554153799459657802325717)
                ·
                  refine ⟨12987979674835729742009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 554153799459657802325717 12987979674835729742009)
                  ·
                    rfl

theorem cell23_227646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_227646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227646 prefixEnd_227646 := by exact prefixLift 227646
  have htrace : WordTrace (prefixWord ++ tailWord_227646) baseStart_227646 baseEnd_227646 := by
    simpa [prefixWord, tailWord_227646, baseEnd_227646] using wordTrace_append hprefix tailTrace_227646
  have hstable : (prefixWord ++ tailWord_227646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227646).length < 2 ^ (prefixWord ++ tailWord_227646).sum := by decide
  have hdescent : baseEnd_227646 < baseStart_227646 := by decide
  rcases family_descends (prefixWord ++ tailWord_227646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227656 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 2, 3, 3]
def baseStart_227656 : Nat := 118140960795 + 227656 * 2 ^ 59
def prefixEnd_227656 : Nat := 4983230072969 + 3 ^ 40 * 227656 * 2
def baseEnd_227656 : Nat := 116896951880066528553035

theorem tailTrace_227656 : CollatzResearch.WordTrace tailWord_227656 prefixEnd_227656 116896951880066528553035 := by
  unfold tailWord_227656
  simp only [CollatzResearch.WordTrace]
  refine ⟨4151648231624333697235411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5535530975499111596313881 4151648231624333697235411)
  ·
    refine ⟨6227472347436500545853117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4151648231624333697235411 6227472347436500545853117)
    ·
      refine ⟨2335302130288687704694919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6227472347436500545853117 2335302130288687704694919)
      ·
        refine ⟨3502953195433031557042379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2335302130288687704694919 3502953195433031557042379)
        ·
          refine ⟨5254429793149547335563569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3502953195433031557042379 5254429793149547335563569)
          ·
            refine ⟨3940822344862160501672677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5254429793149547335563569 3940822344862160501672677)
            ·
              refine ⟨738904189661655094063627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3940822344862160501672677 738904189661655094063627)
              ·
                refine ⟨1108356284492482641095441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738904189661655094063627 1108356284492482641095441)
                ·
                  refine ⟨831267213369361980821581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1108356284492482641095441 831267213369361980821581)
                  ·
                    refine ⟨311725205013510742808093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 831267213369361980821581 311725205013510742808093)
                    ·
                      refine ⟨116896951880066528553035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 311725205013510742808093 116896951880066528553035)
                      ·
                        rfl

theorem cell23_227656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_227656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227656 prefixEnd_227656 := by exact prefixLift 227656
  have htrace : WordTrace (prefixWord ++ tailWord_227656) baseStart_227656 baseEnd_227656 := by
    simpa [prefixWord, tailWord_227656, baseEnd_227656] using wordTrace_append hprefix tailTrace_227656
  have hstable : (prefixWord ++ tailWord_227656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227656).length < 2 ^ (prefixWord ++ tailWord_227656).sum := by decide
  have hdescent : baseEnd_227656 < baseStart_227656 := by decide
  rcases family_descends (prefixWord ++ tailWord_227656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227659 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 6, 5]
def baseStart_227659 : Nat := 118140960795 + 227659 * 2 ^ 59
def prefixEnd_227659 : Nat := 4983230072969 + 3 ^ 40 * 227659 * 2
def baseEnd_227659 : Nat := 38966164107343338938507

theorem tailTrace_227659 : CollatzResearch.WordTrace tailWord_227659 prefixEnd_227659 38966164107343338938507 := by
  unfold tailWord_227659
  simp only [CollatzResearch.WordTrace]
  refine ⟨8303405882237798906830031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5535603921491865937886687 8303405882237798906830031)
  ·
    refine ⟨12455108823356698360245047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8303405882237798906830031 12455108823356698360245047)
    ·
      refine ⟨18682663235035047540367571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12455108823356698360245047 18682663235035047540367571)
      ·
        refine ⟨28023994852552571310551357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18682663235035047540367571 28023994852552571310551357)
        ·
          refine ⟨10508998069707214241456759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28023994852552571310551357 10508998069707214241456759)
          ·
            refine ⟨15763497104560821362185139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10508998069707214241456759 15763497104560821362185139)
            ·
              refine ⟨23645245656841232043277709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15763497104560821362185139 23645245656841232043277709)
              ·
                refine ⟨8866967121315462016229141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23645245656841232043277709 8866967121315462016229141)
                ·
                  refine ⟨415639083811662282010741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8866967121315462016229141 415639083811662282010741)
                  ·
                    refine ⟨38966164107343338938507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 415639083811662282010741 38966164107343338938507)
                    ·
                      rfl

theorem cell23_227659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 5].length) (baseStart_227659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227659 prefixEnd_227659 := by exact prefixLift 227659
  have htrace : WordTrace (prefixWord ++ tailWord_227659) baseStart_227659 baseEnd_227659 := by
    simpa [prefixWord, tailWord_227659, baseEnd_227659] using wordTrace_append hprefix tailTrace_227659
  have hstable : (prefixWord ++ tailWord_227659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227659).length < 2 ^ (prefixWord ++ tailWord_227659).sum := by decide
  have hdescent : baseEnd_227659 < baseStart_227659 := by decide
  rcases family_descends (prefixWord ++ tailWord_227659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227680 : List Nat := [2, 1, 1, 3, 5, 2, 1, 3, 5]
def baseStart_227680 : Nat := 118140960795 + 227680 * 2 ^ 59
def prefixEnd_227680 : Nat := 4983230072969 + 3 ^ 40 * 227680 * 2
def baseEnd_227680 : Nat := 12989919490641603850325

theorem tailTrace_227680 : CollatzResearch.WordTrace tailWord_227680 prefixEnd_227680 12989919490641603850325 := by
  unfold tailWord_227680
  simp only [CollatzResearch.WordTrace]
  refine ⟨4152085907580859746672247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5536114543441146328896329 4152085907580859746672247)
  ·
    refine ⟨6228128861371289620008371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4152085907580859746672247 6228128861371289620008371)
    ·
      refine ⟨9342193292056934430012557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6228128861371289620008371 9342193292056934430012557)
      ·
        refine ⟨3503322484521350411254709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9342193292056934430012557 3503322484521350411254709)
        ·
          refine ⟨328436482923876601055129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3503322484521350411254709 328436482923876601055129)
          ·
            refine ⟨246327362192907450791347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328436482923876601055129 246327362192907450791347)
            ·
              refine ⟨369491043289361176187021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246327362192907450791347 369491043289361176187021)
              ·
                refine ⟨138559141233510441070133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369491043289361176187021 138559141233510441070133)
                ·
                  refine ⟨12989919490641603850325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138559141233510441070133 12989919490641603850325)
                  ·
                    rfl

theorem cell23_227680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 5].length) (baseStart_227680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227680 prefixEnd_227680 := by exact prefixLift 227680
  have htrace : WordTrace (prefixWord ++ tailWord_227680) baseStart_227680 baseEnd_227680 := by
    simpa [prefixWord, tailWord_227680, baseEnd_227680] using wordTrace_append hprefix tailTrace_227680
  have hstable : (prefixWord ++ tailWord_227680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227680).length < 2 ^ (prefixWord ++ tailWord_227680).sum := by decide
  have hdescent : baseEnd_227680 < baseStart_227680 := by decide
  rcases family_descends (prefixWord ++ tailWord_227680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227696 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 4]
def baseStart_227696 : Nat := 118140960795 + 227696 * 2 ^ 59
def prefixEnd_227696 : Nat := 4983230072969 + 3 ^ 40 * 227696 * 2
def baseEnd_227696 : Nat := 116917491106246372052851

theorem tailTrace_227696 : CollatzResearch.WordTrace tailWord_227696 prefixEnd_227696 116917491106246372052851 := by
  unfold tailWord_227696
  simp only [CollatzResearch.WordTrace]
  refine ⟨4152377691551877112963471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5536503588735836150617961 4152377691551877112963471)
  ·
    refine ⟨6228566537327815669445207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4152377691551877112963471 6228566537327815669445207)
    ·
      refine ⟨9342849805991723504167811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6228566537327815669445207 9342849805991723504167811)
      ·
        refine ⟨14014274708987585256251717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9342849805991723504167811 14014274708987585256251717)
        ·
          refine ⟨2627676507935172235547197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14014274708987585256251717 2627676507935172235547197)
          ·
            refine ⟨985378690475689588330199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2627676507935172235547197 985378690475689588330199)
            ·
              refine ⟨1478068035713534382495299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985378690475689588330199 1478068035713534382495299)
              ·
                refine ⟨2217102053570301573742949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478068035713534382495299 2217102053570301573742949)
                ·
                  refine ⟨415706635044431545076803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2217102053570301573742949 415706635044431545076803)
                  ·
                    refine ⟨623559952566647317615205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 415706635044431545076803 623559952566647317615205)
                    ·
                      refine ⟨116917491106246372052851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 623559952566647317615205 116917491106246372052851)
                      ·
                        rfl

theorem cell23_227696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 4].length) (baseStart_227696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227696 prefixEnd_227696 := by exact prefixLift 227696
  have htrace : WordTrace (prefixWord ++ tailWord_227696) baseStart_227696 baseEnd_227696 := by
    simpa [prefixWord, tailWord_227696, baseEnd_227696] using wordTrace_append hprefix tailTrace_227696
  have hstable : (prefixWord ++ tailWord_227696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227696).length < 2 ^ (prefixWord ++ tailWord_227696).sum := by decide
  have hdescent : baseEnd_227696 < baseStart_227696 := by decide
  rcases family_descends (prefixWord ++ tailWord_227696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227699 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 5]
def baseStart_227699 : Nat := 118140960795 + 227699 * 2 ^ 59
def prefixEnd_227699 : Nat := 4983230072969 + 3 ^ 40 * 227699 * 2
def baseEnd_227699 : Nat := 116919031548209860315337

theorem tailTrace_227699 : CollatzResearch.WordTrace tailWord_227699 prefixEnd_227699 116919031548209860315337 := by
  unfold tailWord_227699
  simp only [CollatzResearch.WordTrace]
  refine ⟨8304864802092885738286151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5536576534728590492190767 8304864802092885738286151)
  ·
    refine ⟨12457297203139328607429227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8304864802092885738286151 12457297203139328607429227)
    ·
      refine ⟨18685945804708992911143841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12457297203139328607429227 18685945804708992911143841)
      ·
        refine ⟨14014459353531744683357881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18685945804708992911143841 14014459353531744683357881)
        ·
          refine ⟨10510844515148808512518411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14014459353531744683357881 10510844515148808512518411)
          ·
            refine ⟨15766266772723212768777617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10510844515148808512518411 15766266772723212768777617)
            ·
              refine ⟨11824700079542409576583213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15766266772723212768777617 11824700079542409576583213)
              ·
                refine ⟨4434262529828403591218705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11824700079542409576583213 4434262529828403591218705)
                ·
                  refine ⟨3325696897371302693414029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4434262529828403591218705 3325696897371302693414029)
                  ·
                    refine ⟨1247136336514238510030261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3325696897371302693414029 1247136336514238510030261)
                    ·
                      refine ⟨116919031548209860315337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1247136336514238510030261 116919031548209860315337)
                      ·
                        rfl

theorem cell23_227699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_227699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227699 prefixEnd_227699 := by exact prefixLift 227699
  have htrace : WordTrace (prefixWord ++ tailWord_227699) baseStart_227699 baseEnd_227699 := by
    simpa [prefixWord, tailWord_227699, baseEnd_227699] using wordTrace_append hprefix tailTrace_227699
  have hstable : (prefixWord ++ tailWord_227699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227699).length < 2 ^ (prefixWord ++ tailWord_227699).sum := by decide
  have hdescent : baseEnd_227699 < baseStart_227699 := by decide
  rcases family_descends (prefixWord ++ tailWord_227699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227729 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 9]
def baseStart_227729 : Nat := 118140960795 + 227729 * 2 ^ 59
def prefixEnd_227729 : Nat := 4983230072969 + 3 ^ 40 * 227729 * 2
def baseEnd_227729 : Nat := 116934435967844742940199

theorem tailTrace_227729 : CollatzResearch.WordTrace tailWord_227729 prefixEnd_227729 116934435967844742940199 := by
  unfold tailWord_227729
  simp only [CollatzResearch.WordTrace]
  refine ⟨8305958991984200861878241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5537305994656133907918827 8305958991984200861878241)
  ·
    refine ⟨6229469243988150646408681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8305958991984200861878241 6229469243988150646408681)
    ·
      refine ⟨4672101932991112984806511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6229469243988150646408681 4672101932991112984806511)
      ·
        refine ⟨7008152899486669477209767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4672101932991112984806511 7008152899486669477209767)
        ·
          refine ⟨10512229349230004215814651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7008152899486669477209767 10512229349230004215814651)
          ·
            refine ⟨15768344023845006323721977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10512229349230004215814651 15768344023845006323721977)
            ·
              refine ⟨11826258017883754742791483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15768344023845006323721977 11826258017883754742791483)
              ·
                refine ⟨17739387026825632114187225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11826258017883754742791483 17739387026825632114187225)
                ·
                  refine ⟨13304540270119224085640419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17739387026825632114187225 13304540270119224085640419)
                  ·
                    refine ⟨19956810405178836128460629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13304540270119224085640419 19956810405178836128460629)
                    ·
                      refine ⟨116934435967844742940199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 19956810405178836128460629 116934435967844742940199)
                      ·
                        rfl

theorem cell23_227729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_227729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227729 prefixEnd_227729 := by exact prefixLift 227729
  have htrace : WordTrace (prefixWord ++ tailWord_227729) baseStart_227729 baseEnd_227729 := by
    simpa [prefixWord, tailWord_227729, baseEnd_227729] using wordTrace_append hprefix tailTrace_227729
  have hstable : (prefixWord ++ tailWord_227729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227729).length < 2 ^ (prefixWord ++ tailWord_227729).sum := by decide
  have hdescent : baseEnd_227729 < baseStart_227729 := by decide
  rcases family_descends (prefixWord ++ tailWord_227729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227739 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 6]
def baseStart_227739 : Nat := 118140960795 + 227739 * 2 ^ 59
def prefixEnd_227739 : Nat := 4983230072969 + 3 ^ 40 * 227739 * 2
def baseEnd_227739 : Nat := 116939570774389703815153

theorem tailTrace_227739 : CollatzResearch.WordTrace tailWord_227739 prefixEnd_227739 116939570774389703815153 := by
  unfold tailWord_227739
  simp only [CollatzResearch.WordTrace]
  refine ⟨8306323721947972569742271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5537549147965315046494847 8306323721947972569742271)
  ·
    refine ⟨12459485582921958854613407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8306323721947972569742271 12459485582921958854613407)
    ·
      refine ⟨18689228374382938281920111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12459485582921958854613407 18689228374382938281920111)
      ·
        refine ⟨28033842561574407422880167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18689228374382938281920111 28033842561574407422880167)
        ·
          refine ⟨42050763842361611134320251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28033842561574407422880167 42050763842361611134320251)
          ·
            refine ⟨63076145763542416701480377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42050763842361611134320251 63076145763542416701480377)
            ·
              refine ⟨47307109322656812526110283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63076145763542416701480377 47307109322656812526110283)
              ·
                refine ⟨70960663983985218789165425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47307109322656812526110283 70960663983985218789165425)
                ·
                  refine ⟨53220497987988914091874069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70960663983985218789165425 53220497987988914091874069)
                  ·
                    refine ⟨2494710843186980348056597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53220497987988914091874069 2494710843186980348056597)
                    ·
                      refine ⟨116939570774389703815153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2494710843186980348056597 116939570774389703815153)
                      ·
                        rfl

theorem cell23_227739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 6].length) (baseStart_227739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227739 prefixEnd_227739 := by exact prefixLift 227739
  have htrace : WordTrace (prefixWord ++ tailWord_227739) baseStart_227739 baseEnd_227739 := by
    simpa [prefixWord, tailWord_227739, baseEnd_227739] using wordTrace_append hprefix tailTrace_227739
  have hstable : (prefixWord ++ tailWord_227739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227739).length < 2 ^ (prefixWord ++ tailWord_227739).sum := by decide
  have hdescent : baseEnd_227739 < baseStart_227739 := by decide
  rcases family_descends (prefixWord ++ tailWord_227739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227764 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_227764 : Nat := 118140960795 + 227764 * 2 ^ 59
def prefixEnd_227764 : Nat := 4983230072969 + 3 ^ 40 * 227764 * 2
def baseEnd_227764 : Nat := 116952407790752106002539

theorem tailTrace_227764 : CollatzResearch.WordTrace tailWord_227764 prefixEnd_227764 116952407790752106002539 := by
  unfold tailWord_227764
  simp only [CollatzResearch.WordTrace]
  refine ⟨4153617773428700919701173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5538157031238267892934897 4153617773428700919701173)
  ·
    refine ⟨389401666258940711221985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4153617773428700919701173 389401666258940711221985)
    ·
      refine ⟨292051249694205533416489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389401666258940711221985 292051249694205533416489)
      ·
        refine ⟨219038437270654150062367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292051249694205533416489 219038437270654150062367)
        ·
          refine ⟨328557655905981225093551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219038437270654150062367 328557655905981225093551)
          ·
            refine ⟨492836483858971837640327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328557655905981225093551 492836483858971837640327)
            ·
              refine ⟨739254725788457756460491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492836483858971837640327 739254725788457756460491)
              ·
                refine ⟨1108882088682686634690737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 739254725788457756460491 1108882088682686634690737)
                ·
                  refine ⟨831661566512014976018053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1108882088682686634690737 831661566512014976018053)
                  ·
                    refine ⟨155936543721002808003385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 831661566512014976018053 155936543721002808003385)
                    ·
                      refine ⟨116952407790752106002539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 155936543721002808003385 116952407790752106002539)
                      ·
                        rfl

theorem cell23_227764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_227764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227764 prefixEnd_227764 := by exact prefixLift 227764
  have htrace : WordTrace (prefixWord ++ tailWord_227764) baseStart_227764 baseEnd_227764 := by
    simpa [prefixWord, tailWord_227764, baseEnd_227764] using wordTrace_append hprefix tailTrace_227764
  have hstable : (prefixWord ++ tailWord_227764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227764).length < 2 ^ (prefixWord ++ tailWord_227764).sum := by decide
  have hdescent : baseEnd_227764 < baseStart_227764 := by decide
  rcases family_descends (prefixWord ++ tailWord_227764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227797 : List Nat := [1, 3, 2, 3, 1, 2, 1, 5, 1, 1, 3]
def baseStart_227797 : Nat := 118140960795 + 227797 * 2 ^ 59
def prefixEnd_227797 : Nat := 4983230072969 + 3 ^ 40 * 227797 * 2
def baseEnd_227797 : Nat := 116969352652350476889887

theorem tailTrace_227797 : CollatzResearch.WordTrace tailWord_227797 prefixEnd_227797 116969352652350476889887 := by
  unfold tailWord_227797
  simp only [CollatzResearch.WordTrace]
  refine ⟨8308439155737848475353645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5538959437158565650235763 8308439155737848475353645)
  ·
    refine ⟨3115664683401693178257617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8308439155737848475353645 3115664683401693178257617)
    ·
      refine ⟨2336748512551269883693213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3115664683401693178257617 2336748512551269883693213)
      ·
        refine ⟨876280692206726206384955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2336748512551269883693213 876280692206726206384955)
        ·
          refine ⟨1314421038310089309577433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876280692206726206384955 1314421038310089309577433)
          ·
            refine ⟨985815778732566982183075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314421038310089309577433 985815778732566982183075)
            ·
              refine ⟨1478723668098850473274613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985815778732566982183075 1478723668098850473274613)
              ·
                refine ⟨138630343884267231869495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1478723668098850473274613 138630343884267231869495)
                ·
                  refine ⟨207945515826400847804243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138630343884267231869495 207945515826400847804243)
                  ·
                    refine ⟨311918273739601271706365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 207945515826400847804243 311918273739601271706365)
                    ·
                      refine ⟨116969352652350476889887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 311918273739601271706365 116969352652350476889887)
                      ·
                        rfl

theorem cell23_227797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_227797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227797 prefixEnd_227797 := by exact prefixLift 227797
  have htrace : WordTrace (prefixWord ++ tailWord_227797) baseStart_227797 baseEnd_227797 := by
    simpa [prefixWord, tailWord_227797, baseEnd_227797] using wordTrace_append hprefix tailTrace_227797
  have hstable : (prefixWord ++ tailWord_227797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227797).length < 2 ^ (prefixWord ++ tailWord_227797).sum := by decide
  have hdescent : baseEnd_227797 < baseStart_227797 := by decide
  rcases family_descends (prefixWord ++ tailWord_227797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227833 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 1, 2, 4]
def baseStart_227833 : Nat := 118140960795 + 227833 * 2 ^ 59
def prefixEnd_227833 : Nat := 4983230072969 + 3 ^ 40 * 227833 * 2
def baseEnd_227833 : Nat := 116987837955912336039721

theorem tailTrace_227833 : CollatzResearch.WordTrace tailWord_227833 prefixEnd_227833 116987837955912336039721 := by
  unfold tailWord_227833
  simp only [CollatzResearch.WordTrace]
  refine ⟨8309752183607426623664153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5539834789071617749109435 8309752183607426623664153)
  ·
    refine ⟨6232314137705569967748115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8309752183607426623664153 6232314137705569967748115)
    ·
      refine ⟨9348471206558354951622173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6232314137705569967748115 9348471206558354951622173)
      ·
        refine ⟨3505676702459383106858315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9348471206558354951622173 3505676702459383106858315)
        ·
          refine ⟨5258515053689074660287473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3505676702459383106858315 5258515053689074660287473)
          ·
            refine ⟨3943886290266805995215605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5258515053689074660287473 3943886290266805995215605)
            ·
              refine ⟨369739339712513062051463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3943886290266805995215605 369739339712513062051463)
              ·
                refine ⟨554609009568769593077195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369739339712513062051463 554609009568769593077195)
                ·
                  refine ⟨831913514353154389615793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554609009568769593077195 831913514353154389615793)
                  ·
                    refine ⟨623935135764865792211845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 831913514353154389615793 623935135764865792211845)
                    ·
                      refine ⟨116987837955912336039721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 623935135764865792211845 116987837955912336039721)
                      ·
                        rfl

theorem cell23_227833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_227833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227833 prefixEnd_227833 := by exact prefixLift 227833
  have htrace : WordTrace (prefixWord ++ tailWord_227833) baseStart_227833 baseEnd_227833 := by
    simpa [prefixWord, tailWord_227833, baseEnd_227833] using wordTrace_append hprefix tailTrace_227833
  have hstable : (prefixWord ++ tailWord_227833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227833).length < 2 ^ (prefixWord ++ tailWord_227833).sum := by decide
  have hdescent : baseEnd_227833 < baseStart_227833 := by decide
  rcases family_descends (prefixWord ++ tailWord_227833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227860 : List Nat := [2, 4, 3, 1, 1, 3, 9]
def baseStart_227860 : Nat := 118140960795 + 227860 * 2 ^ 59
def prefixEnd_227860 : Nat := 4983230072969 + 3 ^ 40 * 227860 * 2
def baseEnd_227860 : Nat := 1444465455970169511137

theorem tailTrace_227860 : CollatzResearch.WordTrace tailWord_227860 prefixEnd_227860 1444465455970169511137 := by
  unfold tailWord_227860
  simp only [CollatzResearch.WordTrace]
  refine ⟨4155368477254805117448517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5540491303006406823264689 4155368477254805117448517)
  ·
    refine ⟨779131589485275959521597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4155368477254805117448517 779131589485275959521597)
    ·
      refine ⟨292174346056978484820599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 779131589485275959521597 292174346056978484820599)
      ·
        refine ⟨438261519085467727230899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292174346056978484820599 438261519085467727230899)
        ·
          refine ⟨657392278628201590846349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438261519085467727230899 657392278628201590846349)
          ·
            refine ⟨246522104485575596567381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 657392278628201590846349 246522104485575596567381)
            ·
              refine ⟨1444465455970169511137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 246522104485575596567381 1444465455970169511137)
              ·
                rfl

theorem cell23_227860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 9].length) (baseStart_227860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227860 prefixEnd_227860 := by exact prefixLift 227860
  have htrace : WordTrace (prefixWord ++ tailWord_227860) baseStart_227860 baseEnd_227860 := by
    simpa [prefixWord, tailWord_227860, baseEnd_227860] using wordTrace_append hprefix tailTrace_227860
  have hstable : (prefixWord ++ tailWord_227860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227860).length < 2 ^ (prefixWord ++ tailWord_227860).sum := by decide
  have hdescent : baseEnd_227860 < baseStart_227860 := by decide
  rcases family_descends (prefixWord ++ tailWord_227860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227908 : List Nat := [2, 3, 5, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_227908 : Nat := 118140960795 + 227908 * 2 ^ 59
def prefixEnd_227908 : Nat := 4983230072969 + 3 ^ 40 * 227908 * 2
def baseEnd_227908 : Nat := 117026349004999542601877

theorem tailTrace_227908 : CollatzResearch.WordTrace tailWord_227908 prefixEnd_227908 117026349004999542601877 := by
  unfold tailWord_227908
  simp only [CollatzResearch.WordTrace]
  refine ⟨4156243829167857216322189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5541658438890476288429585 4156243829167857216322189)
  ·
    refine ⟨1558591435937946456120821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4156243829167857216322189 1558591435937946456120821)
    ·
      refine ⟨146117947119182480261327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1558591435937946456120821 146117947119182480261327)
      ·
        refine ⟨219176920678773720391991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146117947119182480261327 219176920678773720391991)
        ·
          refine ⟨328765381018160580587987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219176920678773720391991 328765381018160580587987)
          ·
            refine ⟨493148071527240870881981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328765381018160580587987 493148071527240870881981)
            ·
              refine ⟨184930526822715326580743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 493148071527240870881981 184930526822715326580743)
              ·
                refine ⟨277395790234072989871115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184930526822715326580743 277395790234072989871115)
                ·
                  refine ⟨416093685351109484806673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277395790234072989871115 416093685351109484806673)
                  ·
                    refine ⟨312070264013332113605005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 416093685351109484806673 312070264013332113605005)
                    ·
                      refine ⟨117026349004999542601877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 312070264013332113605005 117026349004999542601877)
                      ·
                        rfl

theorem cell23_227908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_227908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227908 prefixEnd_227908 := by exact prefixLift 227908
  have htrace : WordTrace (prefixWord ++ tailWord_227908) baseStart_227908 baseEnd_227908 := by
    simpa [prefixWord, tailWord_227908, baseEnd_227908] using wordTrace_append hprefix tailTrace_227908
  have hstable : (prefixWord ++ tailWord_227908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227908).length < 2 ^ (prefixWord ++ tailWord_227908).sum := by decide
  have hdescent : baseEnd_227908 < baseStart_227908 := by decide
  rcases family_descends (prefixWord ++ tailWord_227908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227914 : List Nat := [3, 1, 2, 1, 1, 5, 3, 1, 1, 3, 2]
def baseStart_227914 : Nat := 118140960795 + 227914 * 2 ^ 59
def prefixEnd_227914 : Nat := 4983230072969 + 3 ^ 40 * 227914 * 2
def baseEnd_227914 : Nat := 117029429888926519126849

theorem tailTrace_227914 : CollatzResearch.WordTrace tailWord_227914 prefixEnd_227914 117029429888926519126849 := by
  unfold tailWord_227914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2078176624078494364340699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5541804330875984971575197 2078176624078494364340699)
  ·
    refine ⟨3117264936117741546511049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2078176624078494364340699 3117264936117741546511049)
    ·
      refine ⟨2337948702088306159883287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3117264936117741546511049 2337948702088306159883287)
      ·
        refine ⟨3506923053132459239824931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2337948702088306159883287 3506923053132459239824931)
        ·
          refine ⟨5260384579698688859737397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3506923053132459239824931 5260384579698688859737397)
          ·
            refine ⟨493161054346752080600381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5260384579698688859737397 493161054346752080600381)
            ·
              refine ⟨184935395380032030225143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 493161054346752080600381 184935395380032030225143)
              ·
                refine ⟨277403093070048045337715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184935395380032030225143 277403093070048045337715)
                ·
                  refine ⟨416104639605072068006573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277403093070048045337715 416104639605072068006573)
                  ·
                    refine ⟨156039239851902025502465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 416104639605072068006573 156039239851902025502465)
                    ·
                      refine ⟨117029429888926519126849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 156039239851902025502465 117029429888926519126849)
                      ·
                        rfl

theorem cell23_227914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_227914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227914 prefixEnd_227914 := by exact prefixLift 227914
  have htrace : WordTrace (prefixWord ++ tailWord_227914) baseStart_227914 baseEnd_227914 := by
    simpa [prefixWord, tailWord_227914, baseEnd_227914] using wordTrace_append hprefix tailTrace_227914
  have hstable : (prefixWord ++ tailWord_227914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227914).length < 2 ^ (prefixWord ++ tailWord_227914).sum := by decide
  have hdescent : baseEnd_227914 < baseStart_227914 := by decide
  rcases family_descends (prefixWord ++ tailWord_227914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227944 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 1, 4, 2]
def baseStart_227944 : Nat := 118140960795 + 227944 * 2 ^ 59
def prefixEnd_227944 : Nat := 4983230072969 + 3 ^ 40 * 227944 * 2
def baseEnd_227944 : Nat := 117044834308561401751711

theorem tailTrace_227944 : CollatzResearch.WordTrace tailWord_227944 prefixEnd_227944 117044834308561401751711 := by
  unfold tailWord_227944
  simp only [CollatzResearch.WordTrace]
  refine ⟨4156900343102646290477443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5542533790803528387303257 4156900343102646290477443)
  ·
    refine ⟨6235350514653969435716165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4156900343102646290477443 6235350514653969435716165)
    ·
      refine ⟨1169128221497619269196781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6235350514653969435716165 1169128221497619269196781)
      ·
        refine ⟨438423083061607225948793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1169128221497619269196781 438423083061607225948793)
        ·
          refine ⟨328817312296205419461595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438423083061607225948793 328817312296205419461595)
          ·
            refine ⟨493225968444308129192393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328817312296205419461595 493225968444308129192393)
            ·
              refine ⟨369919476333231096894295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493225968444308129192393 369919476333231096894295)
              ·
                refine ⟨554879214499846645341443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369919476333231096894295 554879214499846645341443)
                ·
                  refine ⟨832318821749769968012165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554879214499846645341443 832318821749769968012165)
                  ·
                    refine ⟨156059779078081869002281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 832318821749769968012165 156059779078081869002281)
                    ·
                      refine ⟨117044834308561401751711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 156059779078081869002281 117044834308561401751711)
                      ·
                        rfl

theorem cell23_227944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_227944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227944 prefixEnd_227944 := by exact prefixLift 227944
  have htrace : WordTrace (prefixWord ++ tailWord_227944) baseStart_227944 baseEnd_227944 := by
    simpa [prefixWord, tailWord_227944, baseEnd_227944] using wordTrace_append hprefix tailTrace_227944
  have hstable : (prefixWord ++ tailWord_227944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227944).length < 2 ^ (prefixWord ++ tailWord_227944).sum := by decide
  have hdescent : baseEnd_227944 < baseStart_227944 := by decide
  rcases family_descends (prefixWord ++ tailWord_227944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227950 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 7]
def baseStart_227950 : Nat := 118140960795 + 227950 * 2 ^ 59
def prefixEnd_227950 : Nat := 4983230072969 + 3 ^ 40 * 227950 * 2
def baseEnd_227950 : Nat := 13005323910276486475187

theorem tailTrace_227950 : CollatzResearch.WordTrace tailWord_227950 prefixEnd_227950 13005323910276486475187 := by
  unfold tailWord_227950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1039252440522944450709163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5542679682789037070448869 1039252440522944450709163)
  ·
    refine ⟨1558878660784416676063745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1039252440522944450709163 1558878660784416676063745)
    ·
      refine ⟨1169158995588312507047809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1558878660784416676063745 1169158995588312507047809)
      ·
        refine ⟨876869246691234380285857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1169158995588312507047809 876869246691234380285857)
        ·
          refine ⟨657651935018425785214393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 876869246691234380285857 657651935018425785214393)
          ·
            refine ⟨493238951263819338910795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657651935018425785214393 493238951263819338910795)
            ·
              refine ⟨739858426895729008366193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493238951263819338910795 739858426895729008366193)
              ·
                refine ⟨554893820171796756274645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 739858426895729008366193 554893820171796756274645)
                ·
                  refine ⟨13005323910276486475187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 554893820171796756274645 13005323910276486475187)
                  ·
                    rfl

theorem cell23_227950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_227950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227950 prefixEnd_227950 := by exact prefixLift 227950
  have htrace : WordTrace (prefixWord ++ tailWord_227950) baseStart_227950 baseEnd_227950 := by
    simpa [prefixWord, tailWord_227950, baseEnd_227950] using wordTrace_append hprefix tailTrace_227950
  have hstable : (prefixWord ++ tailWord_227950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227950).length < 2 ^ (prefixWord ++ tailWord_227950).sum := by decide
  have hdescent : baseEnd_227950 < baseStart_227950 := by decide
  rcases family_descends (prefixWord ++ tailWord_227950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227963 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 2, 5]
def baseStart_227963 : Nat := 118140960795 + 227963 * 2 ^ 59
def prefixEnd_227963 : Nat := 4983230072969 + 3 ^ 40 * 227963 * 2
def baseEnd_227963 : Nat := 39018196813665609138041

theorem tailTrace_227963 : CollatzResearch.WordTrace tailWord_227963 prefixEnd_227963 39018196813665609138041 := by
  unfold tailWord_227963
  simp only [CollatzResearch.WordTrace]
  refine ⟨8314493673136458825896543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5542995782090972550597695 8314493673136458825896543)
  ·
    refine ⟨12471740509704688238844815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8314493673136458825896543 12471740509704688238844815)
    ·
      refine ⟨18707610764557032358267223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12471740509704688238844815 18707610764557032358267223)
      ·
        refine ⟨28061416146835548537400835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18707610764557032358267223 28061416146835548537400835)
        ·
          refine ⟨42092124220253322806101253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28061416146835548537400835 42092124220253322806101253)
          ·
            refine ⟨7892273291297498026143985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42092124220253322806101253 7892273291297498026143985)
            ·
              refine ⟨5919204968473123519607989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7892273291297498026143985 5919204968473123519607989)
              ·
                refine ⟨554925465794355329963249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5919204968473123519607989 554925465794355329963249)
                ·
                  refine ⟨416194099345766497472437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554925465794355329963249 416194099345766497472437)
                  ·
                    refine ⟨39018196813665609138041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 416194099345766497472437 39018196813665609138041)
                    ·
                      rfl

theorem cell23_227963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 5].length) (baseStart_227963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227963 prefixEnd_227963 := by exact prefixLift 227963
  have htrace : WordTrace (prefixWord ++ tailWord_227963) baseStart_227963 baseEnd_227963 := by
    simpa [prefixWord, tailWord_227963, baseEnd_227963] using wordTrace_append hprefix tailTrace_227963
  have hstable : (prefixWord ++ tailWord_227963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227963).length < 2 ^ (prefixWord ++ tailWord_227963).sum := by decide
  have hdescent : baseEnd_227963 < baseStart_227963 := by decide
  rcases family_descends (prefixWord ++ tailWord_227963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227978 : List Nat := [3, 1, 2, 3, 4, 1, 1, 2, 2, 2, 2]
def baseStart_227978 : Nat := 118140960795 + 227978 * 2 ^ 59
def prefixEnd_227978 : Nat := 4983230072969 + 3 ^ 40 * 227978 * 2
def baseEnd_227978 : Nat := 117062292650814268726555

theorem tailTrace_227978 : CollatzResearch.WordTrace tailWord_227978 prefixEnd_227978 117062292650814268726555 := by
  unfold tailWord_227978
  simp only [CollatzResearch.WordTrace]
  refine ⟨2078760192020529096923147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5543360512054744258461725 2078760192020529096923147)
  ·
    refine ⟨3118140288030793645384721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2078760192020529096923147 3118140288030793645384721)
    ·
      refine ⟨2338605216023095234038541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3118140288030793645384721 2338605216023095234038541)
      ·
        refine ⟨876976956008660712764453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2338605216023095234038541 876976956008660712764453)
        ·
          refine ⟨164433179251623883643335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 876976956008660712764453 164433179251623883643335)
          ·
            refine ⟨246649768877435825465003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164433179251623883643335 246649768877435825465003)
            ·
              refine ⟨369974653316153738197505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246649768877435825465003 369974653316153738197505)
              ·
                refine ⟨277480989987115303648129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369974653316153738197505 277480989987115303648129)
                ·
                  refine ⟨208110742490336477736097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277480989987115303648129 208110742490336477736097)
                  ·
                    refine ⟨156083056867752358302073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 208110742490336477736097 156083056867752358302073)
                    ·
                      refine ⟨117062292650814268726555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 156083056867752358302073 117062292650814268726555)
                      ·
                        rfl

theorem cell23_227978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_227978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_227978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_227978 prefixEnd_227978 := by exact prefixLift 227978
  have htrace : WordTrace (prefixWord ++ tailWord_227978) baseStart_227978 baseEnd_227978 := by
    simpa [prefixWord, tailWord_227978, baseEnd_227978] using wordTrace_append hprefix tailTrace_227978
  have hstable : (prefixWord ++ tailWord_227978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227978).length < 2 ^ (prefixWord ++ tailWord_227978).sum := by decide
  have hdescent : baseEnd_227978 < baseStart_227978 := by decide
  rcases family_descends (prefixWord ++ tailWord_227978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228044 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 3, 4]
def baseStart_228044 : Nat := 118140960795 + 228044 * 2 ^ 59
def prefixEnd_228044 : Nat := 4983230072969 + 3 ^ 40 * 228044 * 2
def baseEnd_228044 : Nat := 39032060791337003500417

theorem tailTrace_228044 : CollatzResearch.WordTrace tailWord_228044 prefixEnd_228044 39032060791337003500417 := by
  unfold tailWord_228044
  simp only [CollatzResearch.WordTrace]
  refine ⟨4158723992921504829797593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5544965323895339773063457 4158723992921504829797593)
  ·
    refine ⟨3119042994691128622348195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4158723992921504829797593 3119042994691128622348195)
    ·
      refine ⟨4678564492036692933522293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3119042994691128622348195 4678564492036692933522293)
      ·
        refine ⟨438615421128439962517715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4678564492036692933522293 438615421128439962517715)
        ·
          refine ⟨657923131692659943776573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438615421128439962517715 657923131692659943776573)
          ·
            refine ⟨246721174384747478916215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 657923131692659943776573 246721174384747478916215)
            ·
              refine ⟨370081761577121218374323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246721174384747478916215 370081761577121218374323)
              ·
                refine ⟨555122642365681827561485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370081761577121218374323 555122642365681827561485)
                ·
                  refine ⟨208170990887130685335557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 555122642365681827561485 208170990887130685335557)
                  ·
                    refine ⟨39032060791337003500417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 208170990887130685335557 39032060791337003500417)
                    ·
                      rfl

theorem cell23_228044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_228044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228044 prefixEnd_228044 := by exact prefixLift 228044
  have htrace : WordTrace (prefixWord ++ tailWord_228044) baseStart_228044 baseEnd_228044 := by
    simpa [prefixWord, tailWord_228044, baseEnd_228044] using wordTrace_append hprefix tailTrace_228044
  have hstable : (prefixWord ++ tailWord_228044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228044).length < 2 ^ (prefixWord ++ tailWord_228044).sum := by decide
  have hdescent : baseEnd_228044 < baseStart_228044 := by decide
  rcases family_descends (prefixWord ++ tailWord_228044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228100 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 3, 6]
def baseStart_228100 : Nat := 118140960795 + 228100 * 2 ^ 59
def prefixEnd_228100 : Nat := 4983230072969 + 3 ^ 40 * 228100 * 2
def baseEnd_228100 : Nat := 39041645763554263800331

theorem tailTrace_228100 : CollatzResearch.WordTrace tailWord_228100 prefixEnd_228100 39041645763554263800331 := by
  unfold tailWord_228100
  simp only [CollatzResearch.WordTrace]
  refine ⟨4159745236820065611816877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5546326982426754149089169 4159745236820065611816877)
  ·
    refine ⟨1559904463807524604431329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4159745236820065611816877 1559904463807524604431329)
    ·
      refine ⟨1169928347855643453323497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1559904463807524604431329 1169928347855643453323497)
      ·
        refine ⟨877446260891732589992623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1169928347855643453323497 877446260891732589992623)
        ·
          refine ⟨1316169391337598884988935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877446260891732589992623 1316169391337598884988935)
          ·
            refine ⟨1974254087006398327483403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316169391337598884988935 1974254087006398327483403)
            ·
              refine ⟨2961381130509597491225105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1974254087006398327483403 2961381130509597491225105)
              ·
                refine ⟨2221035847882198118418829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2961381130509597491225105 2221035847882198118418829)
                ·
                  refine ⟨832888442955824294407061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2221035847882198118418829 832888442955824294407061)
                  ·
                    refine ⟨39041645763554263800331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 832888442955824294407061 39041645763554263800331)
                    ·
                      rfl

theorem cell23_228100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_228100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228100 prefixEnd_228100 := by exact prefixLift 228100
  have htrace : WordTrace (prefixWord ++ tailWord_228100) baseStart_228100 baseEnd_228100 := by
    simpa [prefixWord, tailWord_228100, baseEnd_228100] using wordTrace_append hprefix tailTrace_228100
  have hstable : (prefixWord ++ tailWord_228100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228100).length < 2 ^ (prefixWord ++ tailWord_228100).sum := by decide
  have hdescent : baseEnd_228100 < baseStart_228100 := by decide
  rcases family_descends (prefixWord ++ tailWord_228100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228110 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_228110 : Nat := 118140960795 + 228110 * 2 ^ 59
def prefixEnd_228110 : Nat := 4983230072969 + 3 ^ 40 * 228110 * 2
def baseEnd_228110 : Nat := 117130072097207752275947

theorem tailTrace_228110 : CollatzResearch.WordTrace tailWord_228110 prefixEnd_228110 117130072097207752275947 := by
  unfold tailWord_228110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1039981900450487866437223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5546570135735935287665189 1039981900450487866437223)
  ·
    refine ⟨1559972850675731799655835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1039981900450487866437223 1559972850675731799655835)
    ·
      refine ⟨2339959276013597699483753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1559972850675731799655835 2339959276013597699483753)
      ·
        refine ⟨1754969457010198274612815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2339959276013597699483753 1754969457010198274612815)
        ·
          refine ⟨2632454185515297411919223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754969457010198274612815 2632454185515297411919223)
          ·
            refine ⟨3948681278272946117878835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632454185515297411919223 3948681278272946117878835)
            ·
              refine ⟨5923021917409419176818253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3948681278272946117878835 5923021917409419176818253)
              ·
                refine ⟨2221133219028532191306845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5923021917409419176818253 2221133219028532191306845)
                ·
                  refine ⟨832924957135699571740067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2221133219028532191306845 832924957135699571740067)
                  ·
                    refine ⟨1249387435703549357610101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 832924957135699571740067 1249387435703549357610101)
                    ·
                      refine ⟨117130072097207752275947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1249387435703549357610101 117130072097207752275947)
                      ·
                        rfl

theorem cell23_228110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_228110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228110 prefixEnd_228110 := by exact prefixLift 228110
  have htrace : WordTrace (prefixWord ++ tailWord_228110) baseStart_228110 baseEnd_228110 := by
    simpa [prefixWord, tailWord_228110, baseEnd_228110] using wordTrace_append hprefix tailTrace_228110
  have hstable : (prefixWord ++ tailWord_228110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228110).length < 2 ^ (prefixWord ++ tailWord_228110).sum := by decide
  have hdescent : baseEnd_228110 < baseStart_228110 := by decide
  rcases family_descends (prefixWord ++ tailWord_228110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228117 : List Nat := [1, 3, 2, 1, 2, 2, 1, 5, 2, 4]
def baseStart_228117 : Nat := 118140960795 + 228117 * 2 ^ 59
def prefixEnd_228117 : Nat := 4983230072969 + 3 ^ 40 * 228117 * 2
def baseEnd_228117 : Nat := 39044555487263074962805

theorem tailTrace_228117 : CollatzResearch.WordTrace tailWord_228117 prefixEnd_228117 39044555487263074962805 := by
  unfold tailWord_228117
  simp only [CollatzResearch.WordTrace]
  refine ⟨8320110514578543127002605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5546740343052362084668403 8320110514578543127002605)
  ·
    refine ⟨3120041442966953672625977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8320110514578543127002605 3120041442966953672625977)
    ·
      refine ⟨2340031082225215254469483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3120041442966953672625977 2340031082225215254469483)
      ·
        refine ⟨3510046623337822881704225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2340031082225215254469483 3510046623337822881704225)
        ·
          refine ⟨2632534967503367161278169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3510046623337822881704225 2632534967503367161278169)
          ·
            refine ⟨1974401225627525370958627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2632534967503367161278169 1974401225627525370958627)
            ·
              refine ⟨2961601838441288056437941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1974401225627525370958627 2961601838441288056437941)
              ·
                refine ⟨277650172353870755291057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2961601838441288056437941 277650172353870755291057)
                ·
                  refine ⟨208237629265403066468293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277650172353870755291057 208237629265403066468293)
                  ·
                    refine ⟨39044555487263074962805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 208237629265403066468293 39044555487263074962805)
                    ·
                      rfl

theorem cell23_228117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_228117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228117 prefixEnd_228117 := by exact prefixLift 228117
  have htrace : WordTrace (prefixWord ++ tailWord_228117) baseStart_228117 baseEnd_228117 := by
    simpa [prefixWord, tailWord_228117, baseEnd_228117] using wordTrace_append hprefix tailTrace_228117
  have hstable : (prefixWord ++ tailWord_228117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228117).length < 2 ^ (prefixWord ++ tailWord_228117).sum := by decide
  have hdescent : baseEnd_228117 < baseStart_228117 := by decide
  rcases family_descends (prefixWord ++ tailWord_228117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228124 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 5, 2, 2]
def baseStart_228124 : Nat := 118140960795 + 228124 * 2 ^ 59
def prefixEnd_228124 : Nat := 4983230072969 + 3 ^ 40 * 228124 * 2
def baseEnd_228124 : Nat := 117137260826370697500883

theorem tailTrace_228124 : CollatzResearch.WordTrace tailWord_228124 prefixEnd_228124 117137260826370697500883 := by
  unfold tailWord_228124
  simp only [CollatzResearch.WordTrace]
  refine ⟨4160182912776591661253713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5546910550368788881671617 4160182912776591661253713)
  ·
    refine ⟨3120137184582443745940285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4160182912776591661253713 3120137184582443745940285)
    ·
      refine ⟨1170051444218416404727607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3120137184582443745940285 1170051444218416404727607)
      ·
        refine ⟨1755077166327624607091411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1170051444218416404727607 1755077166327624607091411)
        ·
          refine ⟨2632615749491436910637117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1755077166327624607091411 2632615749491436910637117)
          ·
            refine ⟨987230906059288841488919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2632615749491436910637117 987230906059288841488919)
            ·
              refine ⟨1480846359088933262233379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987230906059288841488919 1480846359088933262233379)
              ·
                refine ⟨2221269538633399893350069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1480846359088933262233379 2221269538633399893350069)
                ·
                  refine ⟨208244019246881240001569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2221269538633399893350069 208244019246881240001569)
                  ·
                    refine ⟨156183014435160930001177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 208244019246881240001569 156183014435160930001177)
                    ·
                      refine ⟨117137260826370697500883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 156183014435160930001177 117137260826370697500883)
                      ·
                        rfl

theorem cell23_228124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_228124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228124 prefixEnd_228124 := by exact prefixLift 228124
  have htrace : WordTrace (prefixWord ++ tailWord_228124) baseStart_228124 baseEnd_228124 := by
    simpa [prefixWord, tailWord_228124, baseEnd_228124] using wordTrace_append hprefix tailTrace_228124
  have hstable : (prefixWord ++ tailWord_228124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228124).length < 2 ^ (prefixWord ++ tailWord_228124).sum := by decide
  have hdescent : baseEnd_228124 < baseStart_228124 := by decide
  rcases family_descends (prefixWord ++ tailWord_228124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228127 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 3]
def baseStart_228127 : Nat := 118140960795 + 228127 * 2 ^ 59
def prefixEnd_228127 : Nat := 4983230072969 + 3 ^ 40 * 228127 * 2
def baseEnd_228127 : Nat := 117138801268334185763369

theorem tailTrace_228127 : CollatzResearch.WordTrace tailWord_228127 prefixEnd_228127 117138801268334185763369 := by
  unfold tailWord_228127
  simp only [CollatzResearch.WordTrace]
  refine ⟨8320475244542314834866635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5546983496361543223244423 8320475244542314834866635)
  ·
    refine ⟨12480712866813472252299953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8320475244542314834866635 12480712866813472252299953)
    ·
      refine ⟨9360534650110104189224965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12480712866813472252299953 9360534650110104189224965)
      ·
        refine ⟨1755100246895644535479681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9360534650110104189224965 1755100246895644535479681)
        ·
          refine ⟨1316325185171733401609761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1755100246895644535479681 1316325185171733401609761)
          ·
            refine ⟨987243888878800051207321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1316325185171733401609761 987243888878800051207321)
            ·
              refine ⟨740432916659100038405491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 987243888878800051207321 740432916659100038405491)
              ·
                refine ⟨1110649374988650057608237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740432916659100038405491 1110649374988650057608237)
                ·
                  refine ⟨416493515620743771603089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1110649374988650057608237 416493515620743771603089)
                  ·
                    refine ⟨312370136715557828702317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 416493515620743771603089 312370136715557828702317)
                    ·
                      refine ⟨117138801268334185763369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 312370136715557828702317 117138801268334185763369)
                      ·
                        rfl

theorem cell23_228127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_228127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228127 prefixEnd_228127 := by exact prefixLift 228127
  have htrace : WordTrace (prefixWord ++ tailWord_228127) baseStart_228127 baseEnd_228127 := by
    simpa [prefixWord, tailWord_228127, baseEnd_228127] using wordTrace_append hprefix tailTrace_228127
  have hstable : (prefixWord ++ tailWord_228127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228127).length < 2 ^ (prefixWord ++ tailWord_228127).sum := by decide
  have hdescent : baseEnd_228127 < baseStart_228127 := by decide
  rcases family_descends (prefixWord ++ tailWord_228127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228138 : List Nat := [3, 1, 4, 3, 1, 2, 2, 1, 1, 5]
def baseStart_228138 : Nat := 118140960795 + 228138 * 2 ^ 59
def prefixEnd_228138 : Nat := 4983230072969 + 3 ^ 40 * 228138 * 2
def baseEnd_228138 : Nat := 39048149851844547575273

theorem tailTrace_228138 : CollatzResearch.WordTrace tailWord_228138 prefixEnd_228138 39048149851844547575273 := by
  unfold tailWord_228138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2080219111875615928379267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5547250965001642475678045 2080219111875615928379267)
  ·
    refine ⟨3120328667813423892568901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2080219111875615928379267 3120328667813423892568901)
    ·
      refine ⟨585061625215016979856669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3120328667813423892568901 585061625215016979856669)
      ·
        refine ⟨219398109455631367446251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 585061625215016979856669 219398109455631367446251)
        ·
          refine ⟨329097164183447051169377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219398109455631367446251 329097164183447051169377)
          ·
            refine ⟨246822873137585288377033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329097164183447051169377 246822873137585288377033)
            ·
              refine ⟨185117154853188966282775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246822873137585288377033 185117154853188966282775)
              ·
                refine ⟨277675732279783449424163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185117154853188966282775 277675732279783449424163)
                ·
                  refine ⟨416513598419675174136245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277675732279783449424163 416513598419675174136245)
                  ·
                    refine ⟨39048149851844547575273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 416513598419675174136245 39048149851844547575273)
                    ·
                      rfl

theorem cell23_228138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_228138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228138 prefixEnd_228138 := by exact prefixLift 228138
  have htrace : WordTrace (prefixWord ++ tailWord_228138) baseStart_228138 baseEnd_228138 := by
    simpa [prefixWord, tailWord_228138, baseEnd_228138] using wordTrace_append hprefix tailTrace_228138
  have hstable : (prefixWord ++ tailWord_228138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228138).length < 2 ^ (prefixWord ++ tailWord_228138).sum := by decide
  have hdescent : baseEnd_228138 < baseStart_228138 := by decide
  rcases family_descends (prefixWord ++ tailWord_228138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228158 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 3, 2, 2]
def baseStart_228158 : Nat := 118140960795 + 228158 * 2 ^ 59
def prefixEnd_228158 : Nat := 4983230072969 + 3 ^ 40 * 228158 * 2
def baseEnd_228158 : Nat := 117154719168623564475727

theorem tailTrace_228158 : CollatzResearch.WordTrace tailWord_228158 prefixEnd_228158 117154719168623564475727 := by
  unfold tailWord_228158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1040200738428750891155641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5547737271620004752830085 1040200738428750891155641)
  ·
    refine ⟨780150553821563168366731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1040200738428750891155641 780150553821563168366731)
    ·
      refine ⟨1170225830732344752550097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 780150553821563168366731 1170225830732344752550097)
      ·
        refine ⟨877669373049258564412573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1170225830732344752550097 877669373049258564412573)
        ·
          refine ⟨329126014893471961654715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 877669373049258564412573 329126014893471961654715)
          ·
            refine ⟨493689022340207942482073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329126014893471961654715 493689022340207942482073)
            ·
              refine ⟨370266766755155956861555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493689022340207942482073 370266766755155956861555)
              ·
                refine ⟨555400150132733935292333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370266766755155956861555 555400150132733935292333)
                ·
                  refine ⟨208275056299775225734625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 555400150132733935292333 208275056299775225734625)
                  ·
                    refine ⟨156206292224831419300969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 208275056299775225734625 156206292224831419300969)
                    ·
                      refine ⟨117154719168623564475727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 156206292224831419300969 117154719168623564475727)
                      ·
                        rfl

theorem cell23_228158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_228158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228158 prefixEnd_228158 := by exact prefixLift 228158
  have htrace : WordTrace (prefixWord ++ tailWord_228158) baseStart_228158 baseEnd_228158 := by
    simpa [prefixWord, tailWord_228158, baseEnd_228158] using wordTrace_append hprefix tailTrace_228158
  have hstable : (prefixWord ++ tailWord_228158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228158).length < 2 ^ (prefixWord ++ tailWord_228158).sum := by decide
  have hdescent : baseEnd_228158 < baseStart_228158 := by decide
  rcases family_descends (prefixWord ++ tailWord_228158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228174 : List Nat := [4, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3]
def baseStart_228174 : Nat := 118140960795 + 228174 * 2 ^ 59
def prefixEnd_228174 : Nat := 4983230072969 + 3 ^ 40 * 228174 * 2
def baseEnd_228174 : Nat := 117162934859095501875653

theorem tailTrace_228174 : CollatzResearch.WordTrace tailWord_228174 prefixEnd_228174 117162934859095501875653 := by
  unfold tailWord_228174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1040273684421505232728447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5548126316914694574551717 1040273684421505232728447)
  ·
    refine ⟨1560410526632257849092671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1040273684421505232728447 1560410526632257849092671)
    ·
      refine ⟨2340615789948386773639007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1560410526632257849092671 2340615789948386773639007)
      ·
        refine ⟨3510923684922580160458511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2340615789948386773639007 3510923684922580160458511)
        ·
          refine ⟨5266385527383870240687767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3510923684922580160458511 5266385527383870240687767)
          ·
            refine ⟨7899578291075805361031651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5266385527383870240687767 7899578291075805361031651)
            ·
              refine ⟨11849367436613708041547477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7899578291075805361031651 11849367436613708041547477)
              ·
                refine ⟨277719549295633782223769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11849367436613708041547477 277719549295633782223769)
                ·
                  refine ⟨208289661971725336667827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277719549295633782223769 208289661971725336667827)
                  ·
                    refine ⟨312434492957588005001741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 208289661971725336667827 312434492957588005001741)
                    ·
                      refine ⟨117162934859095501875653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 312434492957588005001741 117162934859095501875653)
                      ·
                        rfl

theorem cell23_228174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_228174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228174 prefixEnd_228174 := by exact prefixLift 228174
  have htrace : WordTrace (prefixWord ++ tailWord_228174) baseStart_228174 baseEnd_228174 := by
    simpa [prefixWord, tailWord_228174, baseEnd_228174] using wordTrace_append hprefix tailTrace_228174
  have hstable : (prefixWord ++ tailWord_228174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228174).length < 2 ^ (prefixWord ++ tailWord_228174).sum := by decide
  have hdescent : baseEnd_228174 < baseStart_228174 := by decide
  rcases family_descends (prefixWord ++ tailWord_228174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228277 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_228277 : Nat := 118140960795 + 228277 * 2 ^ 59
def prefixEnd_228277 : Nat := 4983230072969 + 3 ^ 40 * 228277 * 2
def baseEnd_228277 : Nat := 117215823366508598887679

theorem tailTrace_228277 : CollatzResearch.WordTrace tailWord_228277 prefixEnd_228277 117215823366508598887679 := by
  unfold tailWord_228277
  simp only [CollatzResearch.WordTrace]
  refine ⟨8325946193998890452827085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5550630795999260301884723 8325946193998890452827085)
  ·
    refine ⟨3122229822749583919810157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8325946193998890452827085 3122229822749583919810157)
    ·
      refine ⟨1170836183531093969928809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3122229822749583919810157 1170836183531093969928809)
      ·
        refine ⟨878127137648320477446607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1170836183531093969928809 878127137648320477446607)
        ·
          refine ⟨1317190706472480716169911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878127137648320477446607 1317190706472480716169911)
          ·
            refine ⟨1975786059708721074254867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317190706472480716169911 1975786059708721074254867)
            ·
              refine ⟨2963679089563081611382301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1975786059708721074254867 2963679089563081611382301)
              ·
                refine ⟨1111379658586155604268363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2963679089563081611382301 1111379658586155604268363)
                ·
                  refine ⟨1667069487879233406402545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111379658586155604268363 1667069487879233406402545)
                  ·
                    refine ⟨1250302115909425054801909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1667069487879233406402545 1250302115909425054801909)
                    ·
                      refine ⟨117215823366508598887679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1250302115909425054801909 117215823366508598887679)
                      ·
                        rfl

theorem cell23_228277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_228277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228277 prefixEnd_228277 := by exact prefixLift 228277
  have htrace : WordTrace (prefixWord ++ tailWord_228277) baseStart_228277 baseEnd_228277 := by
    simpa [prefixWord, tailWord_228277, baseEnd_228277] using wordTrace_append hprefix tailTrace_228277
  have hstable : (prefixWord ++ tailWord_228277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228277).length < 2 ^ (prefixWord ++ tailWord_228277).sum := by decide
  have hdescent : baseEnd_228277 < baseStart_228277 := by decide
  rcases family_descends (prefixWord ++ tailWord_228277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228388 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 3, 1, 3]
def baseStart_228388 : Nat := 118140960795 + 228388 * 2 ^ 59
def prefixEnd_228388 : Nat := 4983230072969 + 3 ^ 40 * 228388 * 2
def baseEnd_228388 : Nat := 117272819719157664599669

theorem tailTrace_228388 : CollatzResearch.WordTrace tailWord_228388 prefixEnd_228388 117272819719157664599669 := by
  unfold tailWord_228388
  simp only [CollatzResearch.WordTrace]
  refine ⟨4164997348298378205058909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5553329797731170940078545 4164997348298378205058909)
  ·
    refine ⟨1561874005611891826897091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4164997348298378205058909 1561874005611891826897091)
    ·
      refine ⟨2342811008417837740345637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1561874005611891826897091 2342811008417837740345637)
      ·
        refine ⟨439277064078344576314807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2342811008417837740345637 439277064078344576314807)
        ·
          refine ⟨658915596117516864472211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439277064078344576314807 658915596117516864472211)
          ·
            refine ⟨988373394176275296708317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658915596117516864472211 988373394176275296708317)
            ·
              refine ⟨370640022816103236265619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 988373394176275296708317 370640022816103236265619)
              ·
                refine ⟨555960034224154854398429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370640022816103236265619 555960034224154854398429)
                ·
                  refine ⟨208485012834058070399411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 555960034224154854398429 208485012834058070399411)
                  ·
                    refine ⟨312727519251087105599117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 208485012834058070399411 312727519251087105599117)
                    ·
                      refine ⟨117272819719157664599669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 312727519251087105599117 117272819719157664599669)
                      ·
                        rfl

theorem cell23_228388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_228388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228388 prefixEnd_228388 := by exact prefixLift 228388
  have htrace : WordTrace (prefixWord ++ tailWord_228388) baseStart_228388 baseEnd_228388 := by
    simpa [prefixWord, tailWord_228388, baseEnd_228388] using wordTrace_append hprefix tailTrace_228388
  have hstable : (prefixWord ++ tailWord_228388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228388).length < 2 ^ (prefixWord ++ tailWord_228388).sum := by decide
  have hdescent : baseEnd_228388 < baseStart_228388 := by decide
  rcases family_descends (prefixWord ++ tailWord_228388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228424 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_228424 : Nat := 118140960795 + 228424 * 2 ^ 59
def prefixEnd_228424 : Nat := 4983230072969 + 3 ^ 40 * 228424 * 2
def baseEnd_228424 : Nat := 117291305022719523749503

theorem tailTrace_228424 : CollatzResearch.WordTrace tailWord_228424 prefixEnd_228424 117291305022719523749503 := by
  unfold tailWord_228424
  simp only [CollatzResearch.WordTrace]
  refine ⟨4165653862233167279214163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5554205149644223038952217 4165653862233167279214163)
  ·
    refine ⟨6248480793349750918821245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4165653862233167279214163 6248480793349750918821245)
    ·
      refine ⟨2343180297506156594557967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6248480793349750918821245 2343180297506156594557967)
      ·
        refine ⟨3514770446259234891836951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2343180297506156594557967 3514770446259234891836951)
        ·
          refine ⟨5272155669388852337755427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3514770446259234891836951 5272155669388852337755427)
          ·
            refine ⟨7908233504083278506633141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5272155669388852337755427 7908233504083278506633141)
            ·
              refine ⟨741396891007807359996857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7908233504083278506633141 741396891007807359996857)
              ·
                refine ⟨556047668255855519997643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741396891007807359996857 556047668255855519997643)
                ·
                  refine ⟨834071502383783279996465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556047668255855519997643 834071502383783279996465)
                  ·
                    refine ⟨625553626787837459997349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 834071502383783279996465 625553626787837459997349)
                    ·
                      refine ⟨117291305022719523749503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 625553626787837459997349 117291305022719523749503)
                      ·
                        rfl

theorem cell23_228424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_228424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228424 prefixEnd_228424 := by exact prefixLift 228424
  have htrace : WordTrace (prefixWord ++ tailWord_228424) baseStart_228424 baseEnd_228424 := by
    simpa [prefixWord, tailWord_228424, baseEnd_228424] using wordTrace_append hprefix tailTrace_228424
  have hstable : (prefixWord ++ tailWord_228424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228424).length < 2 ^ (prefixWord ++ tailWord_228424).sum := by decide
  have hdescent : baseEnd_228424 < baseStart_228424 := by decide
  rcases family_descends (prefixWord ++ tailWord_228424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228447 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 1, 9]
def baseStart_228447 : Nat := 118140960795 + 228447 * 2 ^ 59
def prefixEnd_228447 : Nat := 4983230072969 + 3 ^ 40 * 228447 * 2
def baseEnd_228447 : Nat := 39101038359257644587299

theorem tailTrace_228447 : CollatzResearch.WordTrace tailWord_228447 prefixEnd_228447 39101038359257644587299 := by
  unfold tailWord_228447
  simp only [CollatzResearch.WordTrace]
  refine ⟨8332146603383009486515595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5554764402255339657677063 8332146603383009486515595)
  ·
    refine ⟨12498219905074514229773393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8332146603383009486515595 12498219905074514229773393)
    ·
      refine ⟨9373664928805885672330045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12498219905074514229773393 9373664928805885672330045)
      ·
        refine ⟨3515124348302207127123767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9373664928805885672330045 3515124348302207127123767)
        ·
          refine ⟨5272686522453310690685651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3515124348302207127123767 5272686522453310690685651)
          ·
            refine ⟨7909029783679966036028477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5272686522453310690685651 7909029783679966036028477)
            ·
              refine ⟨2965886168879987263510679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7909029783679966036028477 2965886168879987263510679)
              ·
                refine ⟨4448829253319980895266019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2965886168879987263510679 4448829253319980895266019)
                ·
                  refine ⟨6673243879979971342899029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448829253319980895266019 6673243879979971342899029)
                  ·
                    refine ⟨39101038359257644587299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 6673243879979971342899029 39101038359257644587299)
                    ·
                      rfl

theorem cell23_228447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 9].length) (baseStart_228447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228447 prefixEnd_228447 := by exact prefixLift 228447
  have htrace : WordTrace (prefixWord ++ tailWord_228447) baseStart_228447 baseEnd_228447 := by
    simpa [prefixWord, tailWord_228447, baseEnd_228447] using wordTrace_append hprefix tailTrace_228447
  have hstable : (prefixWord ++ tailWord_228447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228447).length < 2 ^ (prefixWord ++ tailWord_228447).sum := by decide
  have hdescent : baseEnd_228447 < baseStart_228447 := by decide
  rcases family_descends (prefixWord ++ tailWord_228447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228461 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_228461 : Nat := 118140960795 + 228461 * 2 ^ 59
def prefixEnd_228461 : Nat := 4983230072969 + 3 ^ 40 * 228461 * 2
def baseEnd_228461 : Nat := 117310303806935878986833

theorem tailTrace_228461 : CollatzResearch.WordTrace tailWord_228461 prefixEnd_228461 117310303806935878986833 := by
  unfold tailWord_228461
  simp only [CollatzResearch.WordTrace]
  refine ⟨8332657225332289877525237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5555104816888193251683491 8332657225332289877525237)
  ·
    refine ⟨781186614874902176017991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8332657225332289877525237 781186614874902176017991)
    ·
      refine ⟨1171779922312353264026987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 781186614874902176017991 1171779922312353264026987)
      ·
        refine ⟨1757669883468529896040481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1171779922312353264026987 1757669883468529896040481)
        ·
          refine ⟨1318252412601397422030361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1757669883468529896040481 1318252412601397422030361)
          ·
            refine ⟨988689309451048066522771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1318252412601397422030361 988689309451048066522771)
            ·
              refine ⟨1483033964176572099784157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 988689309451048066522771 1483033964176572099784157)
              ·
                refine ⟨556137736566214537419059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1483033964176572099784157 556137736566214537419059)
                ·
                  refine ⟨834206604849321806128589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556137736566214537419059 834206604849321806128589)
                  ·
                    refine ⟨312827476818495677298221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 834206604849321806128589 312827476818495677298221)
                    ·
                      refine ⟨117310303806935878986833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 312827476818495677298221 117310303806935878986833)
                      ·
                        rfl

theorem cell23_228461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_228461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228461 prefixEnd_228461 := by exact prefixLift 228461
  have htrace : WordTrace (prefixWord ++ tailWord_228461) baseStart_228461 baseEnd_228461 := by
    simpa [prefixWord, tailWord_228461, baseEnd_228461] using wordTrace_append hprefix tailTrace_228461
  have hstable : (prefixWord ++ tailWord_228461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228461).length < 2 ^ (prefixWord ++ tailWord_228461).sum := by decide
  have hdescent : baseEnd_228461 < baseStart_228461 := by decide
  rcases family_descends (prefixWord ++ tailWord_228461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228471 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 3, 3, 2]
def baseStart_228471 : Nat := 118140960795 + 228471 * 2 ^ 59
def prefixEnd_228471 : Nat := 4983230072969 + 3 ^ 40 * 228471 * 2
def baseEnd_228471 : Nat := 117315438613480839861787

theorem tailTrace_228471 : CollatzResearch.WordTrace tailWord_228471 prefixEnd_228471 117315438613480839861787 := by
  unfold tailWord_228471
  simp only [CollatzResearch.WordTrace]
  refine ⟨8333021955296061585389267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5555347970197374390259511 8333021955296061585389267)
  ·
    refine ⟨12499532932944092378083901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8333021955296061585389267 12499532932944092378083901)
    ·
      refine ⟨4687324849854034641781463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12499532932944092378083901 4687324849854034641781463)
      ·
        refine ⟨7030987274781051962672195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4687324849854034641781463 7030987274781051962672195)
        ·
          refine ⟨10546480912171577944008293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7030987274781051962672195 10546480912171577944008293)
          ·
            refine ⟨1977465171032170864501555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10546480912171577944008293 1977465171032170864501555)
            ·
              refine ⟨2966197756548256296752333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1977465171032170864501555 2966197756548256296752333)
              ·
                refine ⟨1112324158705596111282125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2966197756548256296752333 1112324158705596111282125)
                ·
                  refine ⟨417121559514598541730797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112324158705596111282125 417121559514598541730797)
                  ·
                    refine ⟨156420584817974453149049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 417121559514598541730797 156420584817974453149049)
                    ·
                      refine ⟨117315438613480839861787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 156420584817974453149049 117315438613480839861787)
                      ·
                        rfl

theorem cell23_228471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 3, 2].length) (baseStart_228471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228471 prefixEnd_228471 := by exact prefixLift 228471
  have htrace : WordTrace (prefixWord ++ tailWord_228471) baseStart_228471 baseEnd_228471 := by
    simpa [prefixWord, tailWord_228471, baseEnd_228471] using wordTrace_append hprefix tailTrace_228471
  have hstable : (prefixWord ++ tailWord_228471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228471).length < 2 ^ (prefixWord ++ tailWord_228471).sum := by decide
  have hdescent : baseEnd_228471 < baseStart_228471 := by decide
  rcases family_descends (prefixWord ++ tailWord_228471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228522 : List Nat := [3, 1, 5, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_228522 : Nat := 118140960795 + 228522 * 2 ^ 59
def prefixEnd_228522 : Nat := 4983230072969 + 3 ^ 40 * 228522 * 2
def baseEnd_228522 : Nat := 117341626126860140324053

theorem tailTrace_228522 : CollatzResearch.WordTrace tailWord_228522 prefixEnd_228522 117341626126860140324053 := by
  unfold tailWord_228522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2083720519527824323873955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5556588052074198196997213 2083720519527824323873955)
  ·
    refine ⟨3125580779291736485810933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2083720519527824323873955 3125580779291736485810933)
    ·
      refine ⟨293023198058600295544775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3125580779291736485810933 293023198058600295544775)
      ·
        refine ⟨439534797087900443317163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293023198058600295544775 439534797087900443317163)
        ·
          refine ⟨659302195631850664975745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439534797087900443317163 659302195631850664975745)
          ·
            refine ⟨494476646723887998731809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 659302195631850664975745 494476646723887998731809)
            ·
              refine ⟨370857485042915999048857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494476646723887998731809 370857485042915999048857)
              ·
                refine ⟨278143113782186999286643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370857485042915999048857 278143113782186999286643)
                ·
                  refine ⟨417214670673280498929965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278143113782186999286643 417214670673280498929965)
                  ·
                    refine ⟨156455501502480187098737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 417214670673280498929965 156455501502480187098737)
                    ·
                      refine ⟨117341626126860140324053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 156455501502480187098737 117341626126860140324053)
                      ·
                        rfl

theorem cell23_228522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_228522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228522 prefixEnd_228522 := by exact prefixLift 228522
  have htrace : WordTrace (prefixWord ++ tailWord_228522) baseStart_228522 baseEnd_228522 := by
    simpa [prefixWord, tailWord_228522, baseEnd_228522] using wordTrace_append hprefix tailTrace_228522
  have hstable : (prefixWord ++ tailWord_228522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228522).length < 2 ^ (prefixWord ++ tailWord_228522).sum := by decide
  have hdescent : baseEnd_228522 < baseStart_228522 := by decide
  rcases family_descends (prefixWord ++ tailWord_228522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228558 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 7]
def baseStart_228558 : Nat := 118140960795 + 228558 * 2 ^ 59
def prefixEnd_228558 : Nat := 4983230072969 + 3 ^ 40 * 228558 * 2
def baseEnd_228558 : Nat := 13040012381157999941543

theorem tailTrace_228558 : CollatzResearch.WordTrace tailWord_228558 prefixEnd_228558 13040012381157999941543 := by
  unfold tailWord_228558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042024388247609430475791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5557463403987250295870885 1042024388247609430475791)
  ·
    refine ⟨1563036582371414145713687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1042024388247609430475791 1563036582371414145713687)
    ·
      refine ⟨2344554873557121218570531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1563036582371414145713687 2344554873557121218570531)
      ·
        refine ⟨3516832310335681827855797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2344554873557121218570531 3516832310335681827855797)
        ·
          refine ⟨329703029093970171361481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3516832310335681827855797 329703029093970171361481)
          ·
            refine ⟨247277271820477628521111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329703029093970171361481 247277271820477628521111)
            ·
              refine ⟨370915907730716442781667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247277271820477628521111 370915907730716442781667)
              ·
                refine ⟨556373861596074664172501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370915907730716442781667 556373861596074664172501)
                ·
                  refine ⟨13040012381157999941543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 556373861596074664172501 13040012381157999941543)
                  ·
                    rfl

theorem cell23_228558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_228558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228558 prefixEnd_228558 := by exact prefixLift 228558
  have htrace : WordTrace (prefixWord ++ tailWord_228558) baseStart_228558 baseEnd_228558 := by
    simpa [prefixWord, tailWord_228558, baseEnd_228558] using wordTrace_append hprefix tailTrace_228558
  have hstable : (prefixWord ++ tailWord_228558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228558).length < 2 ^ (prefixWord ++ tailWord_228558).sum := by decide
  have hdescent : baseEnd_228558 < baseStart_228558 := by decide
  rcases family_descends (prefixWord ++ tailWord_228558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228561 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 2, 5, 2]
def baseStart_228561 : Nat := 118140960795 + 228561 * 2 ^ 59
def prefixEnd_228561 : Nat := 4983230072969 + 3 ^ 40 * 228561 * 2
def baseEnd_228561 : Nat := 117361651872385487736373

theorem tailTrace_228561 : CollatzResearch.WordTrace tailWord_228561 prefixEnd_228561 117361651872385487736373 := by
  unfold tailWord_228561
  simp only [CollatzResearch.WordTrace]
  refine ⟨8336304524970006956165537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5557536349980004637443691 8336304524970006956165537)
  ·
    refine ⟨6252228393727505217124153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8336304524970006956165537 6252228393727505217124153)
    ·
      refine ⟨4689171295295628912843115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6252228393727505217124153 4689171295295628912843115)
      ·
        refine ⟨7033756942943443369264673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4689171295295628912843115 7033756942943443369264673)
        ·
          refine ⟨5275317707207582526948505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7033756942943443369264673 5275317707207582526948505)
          ·
            refine ⟨3956488280405686895211379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5275317707207582526948505 3956488280405686895211379)
            ·
              refine ⟨5934732420608530342817069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3956488280405686895211379 5934732420608530342817069)
              ·
                refine ⟨2225524657728198878556401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5934732420608530342817069 2225524657728198878556401)
                ·
                  refine ⟨1669143493296149158917301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2225524657728198878556401 1669143493296149158917301)
                  ·
                    refine ⟨156482202496513983648497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1669143493296149158917301 156482202496513983648497)
                    ·
                      refine ⟨117361651872385487736373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 156482202496513983648497 117361651872385487736373)
                      ·
                        rfl

theorem cell23_228561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 5, 2].length) (baseStart_228561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228561 prefixEnd_228561 := by exact prefixLift 228561
  have htrace : WordTrace (prefixWord ++ tailWord_228561) baseStart_228561 baseEnd_228561 := by
    simpa [prefixWord, tailWord_228561, baseEnd_228561] using wordTrace_append hprefix tailTrace_228561
  have hstable : (prefixWord ++ tailWord_228561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228561).length < 2 ^ (prefixWord ++ tailWord_228561).sum := by decide
  have hdescent : baseEnd_228561 < baseStart_228561 := by decide
  rcases family_descends (prefixWord ++ tailWord_228561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228631 : List Nat := [1, 1, 3, 4, 1, 1, 1, 5, 6]
def baseStart_228631 : Nat := 118140960795 + 228631 * 2 ^ 59
def prefixEnd_228631 : Nat := 4983230072969 + 3 ^ 40 * 228631 * 2
def baseEnd_228631 : Nat := 13044177279800023762339

theorem tailTrace_228631 : CollatzResearch.WordTrace tailWord_228631 prefixEnd_228631 13044177279800023762339 := by
  unfold tailWord_228631
  simp only [CollatzResearch.WordTrace]
  refine ⟨8338857634716408911213747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5559238423144272607475831 8338857634716408911213747)
  ·
    refine ⟨12508286452074613366820621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8338857634716408911213747 12508286452074613366820621)
    ·
      refine ⟨4690607419527980012557733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12508286452074613366820621 4690607419527980012557733)
      ·
        refine ⟨879488891161496252354575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4690607419527980012557733 879488891161496252354575)
        ·
          refine ⟨1319233336742244378531863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879488891161496252354575 1319233336742244378531863)
          ·
            refine ⟨1978850005113366567797795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319233336742244378531863 1978850005113366567797795)
            ·
              refine ⟨2968275007670049851696693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1978850005113366567797795 2968275007670049851696693)
              ·
                refine ⟨278275781969067173596565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2968275007670049851696693 278275781969067173596565)
                ·
                  refine ⟨13044177279800023762339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 278275781969067173596565 13044177279800023762339)
                  ·
                    rfl

theorem cell23_228631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 6].length) (baseStart_228631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228631 prefixEnd_228631 := by exact prefixLift 228631
  have htrace : WordTrace (prefixWord ++ tailWord_228631) baseStart_228631 baseEnd_228631 := by
    simpa [prefixWord, tailWord_228631, baseEnd_228631] using wordTrace_append hprefix tailTrace_228631
  have hstable : (prefixWord ++ tailWord_228631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228631).length < 2 ^ (prefixWord ++ tailWord_228631).sum := by decide
  have hdescent : baseEnd_228631 < baseStart_228631 := by decide
  rcases family_descends (prefixWord ++ tailWord_228631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228642 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 2, 1, 4]
def baseStart_228642 : Nat := 118140960795 + 228642 * 2 ^ 59
def prefixEnd_228642 : Nat := 4983230072969 + 3 ^ 40 * 228642 * 2
def baseEnd_228642 : Nat := 117403243805399670823501

theorem tailTrace_228642 : CollatzResearch.WordTrace tailWord_228642 prefixEnd_228642 117403243805399670823501 := by
  unfold tailWord_228642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2084814709419139447466045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5559505891784371859909453 2084814709419139447466045)
  ·
    refine ⟨781805516032177292799767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2084814709419139447466045 781805516032177292799767)
    ·
      refine ⟨1172708274048265939199651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 781805516032177292799767 1172708274048265939199651)
      ·
        refine ⟨1759062411072398908799477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1172708274048265939199651 1759062411072398908799477)
        ·
          refine ⟨164912101038037397699951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1759062411072398908799477 164912101038037397699951)
          ·
            refine ⟨247368151557056096549927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164912101038037397699951 247368151557056096549927)
            ·
              refine ⟨371052227335584144824891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247368151557056096549927 371052227335584144824891)
              ·
                refine ⟨556578341003376217237337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371052227335584144824891 556578341003376217237337)
                ·
                  refine ⟨417433755752532162928003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556578341003376217237337 417433755752532162928003)
                  ·
                    refine ⟨626150633628798244392005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 417433755752532162928003 626150633628798244392005)
                    ·
                      refine ⟨117403243805399670823501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 626150633628798244392005 117403243805399670823501)
                      ·
                        rfl

theorem cell23_228642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_228642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228642 prefixEnd_228642 := by exact prefixLift 228642
  have htrace : WordTrace (prefixWord ++ tailWord_228642) baseStart_228642 baseEnd_228642 := by
    simpa [prefixWord, tailWord_228642, baseEnd_228642] using wordTrace_append hprefix tailTrace_228642
  have hstable : (prefixWord ++ tailWord_228642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228642).length < 2 ^ (prefixWord ++ tailWord_228642).sum := by decide
  have hdescent : baseEnd_228642 < baseStart_228642 := by decide
  rcases family_descends (prefixWord ++ tailWord_228642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228645 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 2, 2, 3]
def baseStart_228645 : Nat := 118140960795 + 228645 * 2 ^ 59
def prefixEnd_228645 : Nat := 4983230072969 + 3 ^ 40 * 228645 * 2
def baseEnd_228645 : Nat := 117404784247363159085987

theorem tailTrace_228645 : CollatzResearch.WordTrace tailWord_228645 prefixEnd_228645 117404784247363159085987 := by
  unfold tailWord_228645
  simp only [CollatzResearch.WordTrace]
  refine ⟨8339368256665689302223389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5559578837777126201482259 8339368256665689302223389)
  ·
    refine ⟨3127263096249633488333771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8339368256665689302223389 3127263096249633488333771)
    ·
      refine ⟨4690894644374450232500657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3127263096249633488333771 4690894644374450232500657)
      ·
        refine ⟨3518170983280837674375493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4690894644374450232500657 3518170983280837674375493)
        ·
          refine ⟨659657059365157063945405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3518170983280837674375493 659657059365157063945405)
          ·
            refine ⟨247371397261933898979527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 659657059365157063945405 247371397261933898979527)
            ·
              refine ⟨371057095892900848469291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247371397261933898979527 371057095892900848469291)
              ·
                refine ⟨556585643839351272703937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371057095892900848469291 556585643839351272703937)
                ·
                  refine ⟨417439232879513454527953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556585643839351272703937 417439232879513454527953)
                  ·
                    refine ⟨313079424659635090895965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 417439232879513454527953 313079424659635090895965)
                    ·
                      refine ⟨117404784247363159085987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 313079424659635090895965 117404784247363159085987)
                      ·
                        rfl

theorem cell23_228645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_228645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228645 prefixEnd_228645 := by exact prefixLift 228645
  have htrace : WordTrace (prefixWord ++ tailWord_228645) baseStart_228645 baseEnd_228645 := by
    simpa [prefixWord, tailWord_228645, baseEnd_228645] using wordTrace_append hprefix tailTrace_228645
  have hstable : (prefixWord ++ tailWord_228645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228645).length < 2 ^ (prefixWord ++ tailWord_228645).sum := by decide
  have hdescent : baseEnd_228645 < baseStart_228645 := by decide
  rcases family_descends (prefixWord ++ tailWord_228645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228665 : List Nat := [1, 2, 1, 6, 2, 2, 1, 2, 6]
def baseStart_228665 : Nat := 118140960795 + 228665 * 2 ^ 59
def prefixEnd_228665 : Nat := 4983230072969 + 3 ^ 40 * 228665 * 2
def baseEnd_228665 : Nat := 13046117095605897870655

theorem tailTrace_228665 : CollatzResearch.WordTrace tailWord_228665 prefixEnd_228665 13046117095605897870655 := by
  unfold tailWord_228665
  simp only [CollatzResearch.WordTrace]
  refine ⟨8340097716593232717951449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5560065144395488478634299 8340097716593232717951449)
  ·
    refine ⟨6255073287444924538463587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8340097716593232717951449 6255073287444924538463587)
    ·
      refine ⟨9382609931167386807695381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6255073287444924538463587 9382609931167386807695381)
      ·
        refine ⟨439809840523471256610721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9382609931167386807695381 439809840523471256610721)
        ·
          refine ⟨329857380392603442458041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439809840523471256610721 329857380392603442458041)
          ·
            refine ⟨247393035294452581843531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329857380392603442458041 247393035294452581843531)
            ·
              refine ⟨371089552941678872765297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247393035294452581843531 371089552941678872765297)
              ·
                refine ⟨278317164706259154573973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371089552941678872765297 278317164706259154573973)
                ·
                  refine ⟨13046117095605897870655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 278317164706259154573973 13046117095605897870655)
                  ·
                    rfl

theorem cell23_228665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 6].length) (baseStart_228665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228665 prefixEnd_228665 := by exact prefixLift 228665
  have htrace : WordTrace (prefixWord ++ tailWord_228665) baseStart_228665 baseEnd_228665 := by
    simpa [prefixWord, tailWord_228665, baseEnd_228665] using wordTrace_append hprefix tailTrace_228665
  have hstable : (prefixWord ++ tailWord_228665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228665).length < 2 ^ (prefixWord ++ tailWord_228665).sum := by decide
  have hdescent : baseEnd_228665 < baseStart_228665 := by decide
  rcases family_descends (prefixWord ++ tailWord_228665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228681 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 5, 1, 4]
def baseStart_228681 : Nat := 118140960795 + 228681 * 2 ^ 59
def prefixEnd_228681 : Nat := 4983230072969 + 3 ^ 40 * 228681 * 2
def baseEnd_228681 : Nat := 117423269550925018235821

theorem tailTrace_228681 : CollatzResearch.WordTrace tailWord_228681 prefixEnd_228681 117423269550925018235821 := by
  unfold tailWord_228681
  simp only [CollatzResearch.WordTrace]
  refine ⟨8340681284535267450533897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5560454189690178300355931 8340681284535267450533897)
  ·
    refine ⟨6255510963401450587900423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8340681284535267450533897 6255510963401450587900423)
    ·
      refine ⟨9383266445102175881850635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6255510963401450587900423 9383266445102175881850635)
      ·
        refine ⟨14074899667653263822775953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9383266445102175881850635 14074899667653263822775953)
        ·
          refine ⟨10556174750739947867081965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14074899667653263822775953 10556174750739947867081965)
          ·
            refine ⟨3958565531527480450155737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10556174750739947867081965 3958565531527480450155737)
            ·
              refine ⟨2968924148645610337616803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3958565531527480450155737 2968924148645610337616803)
              ·
                refine ⟨4453386222968415506425205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2968924148645610337616803 4453386222968415506425205)
                ·
                  refine ⟨417504958403288953727363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4453386222968415506425205 417504958403288953727363)
                  ·
                    refine ⟨626257437604933430591045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 417504958403288953727363 626257437604933430591045)
                    ·
                      refine ⟨117423269550925018235821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 626257437604933430591045 117423269550925018235821)
                      ·
                        rfl

theorem cell23_228681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 1, 4].length) (baseStart_228681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228681 prefixEnd_228681 := by exact prefixLift 228681
  have htrace : WordTrace (prefixWord ++ tailWord_228681) baseStart_228681 baseEnd_228681 := by
    simpa [prefixWord, tailWord_228681, baseEnd_228681] using wordTrace_append hprefix tailTrace_228681
  have hstable : (prefixWord ++ tailWord_228681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228681).length < 2 ^ (prefixWord ++ tailWord_228681).sum := by decide
  have hdescent : baseEnd_228681 < baseStart_228681 := by decide
  rcases family_descends (prefixWord ++ tailWord_228681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228698 : List Nat := [3, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4]
def baseStart_228698 : Nat := 118140960795 + 228698 * 2 ^ 59
def prefixEnd_228698 : Nat := 4983230072969 + 3 ^ 40 * 228698 * 2
def baseEnd_228698 : Nat := 117431998722051451723243

theorem tailTrace_228698 : CollatzResearch.WordTrace tailWord_228698 prefixEnd_228698 117431998722051451723243 := by
  unfold tailWord_228698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2085325331368419838475687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5560867550315786235935165 2085325331368419838475687)
  ·
    refine ⟨3127987997052629757713531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2085325331368419838475687 3127987997052629757713531)
    ·
      refine ⟨4691981995578944636570297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3127987997052629757713531 4691981995578944636570297)
      ·
        refine ⟨3518986496684208477427723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4691981995578944636570297 3518986496684208477427723)
        ·
          refine ⟨5278479745026312716141585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3518986496684208477427723 5278479745026312716141585)
          ·
            refine ⟨3958859808769734537106189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5278479745026312716141585 3958859808769734537106189)
            ·
              refine ⟨1484572428288650451414821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3958859808769734537106189 1484572428288650451414821)
              ·
                refine ⟨278357330304121959640279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1484572428288650451414821 278357330304121959640279)
                ·
                  refine ⟨417535995456182939460419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278357330304121959640279 417535995456182939460419)
                  ·
                    refine ⟨626303993184274409190629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 417535995456182939460419 626303993184274409190629)
                    ·
                      refine ⟨117431998722051451723243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 626303993184274409190629 117431998722051451723243)
                      ·
                        rfl

theorem cell23_228698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_228698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228698 prefixEnd_228698 := by exact prefixLift 228698
  have htrace : WordTrace (prefixWord ++ tailWord_228698) baseStart_228698 baseEnd_228698 := by
    simpa [prefixWord, tailWord_228698, baseEnd_228698] using wordTrace_append hprefix tailTrace_228698
  have hstable : (prefixWord ++ tailWord_228698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228698).length < 2 ^ (prefixWord ++ tailWord_228698).sum := by decide
  have hdescent : baseEnd_228698 < baseStart_228698 := by decide
  rcases family_descends (prefixWord ++ tailWord_228698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228708 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 4, 4]
def baseStart_228708 : Nat := 118140960795 + 228708 * 2 ^ 59
def prefixEnd_228708 : Nat := 4983230072969 + 3 ^ 40 * 228708 * 2
def baseEnd_228708 : Nat := 39145711176198804199399

theorem tailTrace_228708 : CollatzResearch.WordTrace tailWord_228708 prefixEnd_228708 39145711176198804199399 := by
  unfold tailWord_228708
  simp only [CollatzResearch.WordTrace]
  refine ⟨4170833027718725530883389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5561110703624967374511185 4170833027718725530883389)
  ·
    refine ⟨1564062385394522074081271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4170833027718725530883389 1564062385394522074081271)
    ·
      refine ⟨2346093578091783111121907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1564062385394522074081271 2346093578091783111121907)
      ·
        refine ⟨3519140367137674666682861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2346093578091783111121907 3519140367137674666682861)
        ·
          refine ⟨1319677637676628000006073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3519140367137674666682861 1319677637676628000006073)
          ·
            refine ⟨989758228257471000004555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1319677637676628000006073 989758228257471000004555)
            ·
              refine ⟨1484637342386206500006833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989758228257471000004555 1484637342386206500006833)
              ·
                refine ⟨1113478006789654875005125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1484637342386206500006833 1113478006789654875005125)
                ·
                  refine ⟨208777126273060289063461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1113478006789654875005125 208777126273060289063461)
                  ·
                    refine ⟨39145711176198804199399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 208777126273060289063461 39145711176198804199399)
                    ·
                      rfl

theorem cell23_228708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_228708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228708 prefixEnd_228708 := by exact prefixLift 228708
  have htrace : WordTrace (prefixWord ++ tailWord_228708) baseStart_228708 baseEnd_228708 := by
    simpa [prefixWord, tailWord_228708, baseEnd_228708] using wordTrace_append hprefix tailTrace_228708
  have hstable : (prefixWord ++ tailWord_228708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228708).length < 2 ^ (prefixWord ++ tailWord_228708).sum := by decide
  have hdescent : baseEnd_228708 < baseStart_228708 := by decide
  rcases family_descends (prefixWord ++ tailWord_228708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228748 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 1, 3, 3]
def baseStart_228748 : Nat := 118140960795 + 228748 * 2 ^ 59
def prefixEnd_228748 : Nat := 4983230072969 + 3 ^ 40 * 228748 * 2
def baseEnd_228748 : Nat := 117457672754776256098013

theorem tailTrace_228748 : CollatzResearch.WordTrace tailWord_228748 prefixEnd_228748 117457672754776256098013 := by
  unfold tailWord_228748
  simp only [CollatzResearch.WordTrace]
  refine ⟨4171562487646268946611449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5562083316861691928815265 4171562487646268946611449)
  ·
    refine ⟨3128671865734701709958587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4171562487646268946611449 3128671865734701709958587)
    ·
      refine ⟨4693007798602052564937881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3128671865734701709958587 4693007798602052564937881)
      ·
        refine ⟨3519755848951539423703411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4693007798602052564937881 3519755848951539423703411)
        ·
          refine ⟨5279633773427309135555117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519755848951539423703411 5279633773427309135555117)
          ·
            refine ⟨1979862665035240925833169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5279633773427309135555117 1979862665035240925833169)
            ·
              refine ⟨1484896998776430694374877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1979862665035240925833169 1484896998776430694374877)
              ·
                refine ⟨556836374541161510390579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1484896998776430694374877 556836374541161510390579)
                ·
                  refine ⟨835254561811742265585869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556836374541161510390579 835254561811742265585869)
                  ·
                    refine ⟨313220460679403349594701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 835254561811742265585869 313220460679403349594701)
                    ·
                      refine ⟨117457672754776256098013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 313220460679403349594701 117457672754776256098013)
                      ·
                        rfl

theorem cell23_228748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_228748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228748 prefixEnd_228748 := by exact prefixLift 228748
  have htrace : WordTrace (prefixWord ++ tailWord_228748) baseStart_228748 baseEnd_228748 := by
    simpa [prefixWord, tailWord_228748, baseEnd_228748] using wordTrace_append hprefix tailTrace_228748
  have hstable : (prefixWord ++ tailWord_228748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228748).length < 2 ^ (prefixWord ++ tailWord_228748).sum := by decide
  have hdescent : baseEnd_228748 < baseStart_228748 := by decide
  rcases family_descends (prefixWord ++ tailWord_228748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228765 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_228765 : Nat := 118140960795 + 228765 * 2 ^ 59
def prefixEnd_228765 : Nat := 4983230072969 + 3 ^ 40 * 228765 * 2
def baseEnd_228765 : Nat := 117466401925902689585435

theorem tailTrace_228765 : CollatzResearch.WordTrace tailWord_228765 prefixEnd_228765 117466401925902689585435 := by
  unfold tailWord_228765
  simp only [CollatzResearch.WordTrace]
  refine ⟨8343745016230949796591749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5562496677487299864394499 8343745016230949796591749)
  ·
    refine ⟨1564452190543303086860953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8343745016230949796591749 1564452190543303086860953)
    ·
      refine ⟨1173339142907477315145715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1564452190543303086860953 1173339142907477315145715)
      ·
        refine ⟨1760008714361215972718573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1173339142907477315145715 1760008714361215972718573)
        ·
          refine ⟨660003267885455989769465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1760008714361215972718573 660003267885455989769465)
          ·
            refine ⟨495002450914091992327099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 660003267885455989769465 495002450914091992327099)
            ·
              refine ⟨742503676371137988490649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495002450914091992327099 742503676371137988490649)
              ·
                refine ⟨556877757278353491367987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 742503676371137988490649 556877757278353491367987)
                ·
                  refine ⟨835316635917530237051981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556877757278353491367987 835316635917530237051981)
                  ·
                    refine ⟨313243738469073838894493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 835316635917530237051981 313243738469073838894493)
                    ·
                      refine ⟨117466401925902689585435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 313243738469073838894493 117466401925902689585435)
                      ·
                        rfl

theorem cell23_228765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_228765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228765 prefixEnd_228765 := by exact prefixLift 228765
  have htrace : WordTrace (prefixWord ++ tailWord_228765) baseStart_228765 baseEnd_228765 := by
    simpa [prefixWord, tailWord_228765, baseEnd_228765] using wordTrace_append hprefix tailTrace_228765
  have hstable : (prefixWord ++ tailWord_228765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228765).length < 2 ^ (prefixWord ++ tailWord_228765).sum := by decide
  have hdescent : baseEnd_228765 < baseStart_228765 := by decide
  rcases family_descends (prefixWord ++ tailWord_228765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228808 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 2, 4, 3]
def baseStart_228808 : Nat := 118140960795 + 228808 * 2 ^ 59
def prefixEnd_228808 : Nat := 4983230072969 + 3 ^ 40 * 228808 * 2
def baseEnd_228808 : Nat := 117488481594046021347737

theorem tailTrace_228808 : CollatzResearch.WordTrace tailWord_228808 prefixEnd_228808 117488481594046021347737 := by
  unfold tailWord_228808
  simp only [CollatzResearch.WordTrace]
  refine ⟨4172656677537584070203539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5563542236716778760271385 4172656677537584070203539)
  ·
    refine ⟨6258985016306376105305309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4172656677537584070203539 6258985016306376105305309)
    ·
      refine ⟨2347119381114891039489491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6258985016306376105305309 2347119381114891039489491)
      ·
        refine ⟨3520679071672336559234237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2347119381114891039489491 3520679071672336559234237)
        ·
          refine ⟨1320254651877126209712839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3520679071672336559234237 1320254651877126209712839)
          ·
            refine ⟨1980381977815689314569259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320254651877126209712839 1980381977815689314569259)
            ·
              refine ⟨2970572966723533971853889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980381977815689314569259 2970572966723533971853889)
              ·
                refine ⟨2227929725042650478890417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2970572966723533971853889 2227929725042650478890417)
                ·
                  refine ⟨1670947293781987859167813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2227929725042650478890417 1670947293781987859167813)
                  ·
                    refine ⟨313302617584122723593965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1670947293781987859167813 313302617584122723593965)
                    ·
                      refine ⟨117488481594046021347737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 313302617584122723593965 117488481594046021347737)
                      ·
                        rfl

theorem cell23_228808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_228808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228808 prefixEnd_228808 := by exact prefixLift 228808
  have htrace : WordTrace (prefixWord ++ tailWord_228808) baseStart_228808 baseEnd_228808 := by
    simpa [prefixWord, tailWord_228808, baseEnd_228808] using wordTrace_append hprefix tailTrace_228808
  have hstable : (prefixWord ++ tailWord_228808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228808).length < 2 ^ (prefixWord ++ tailWord_228808).sum := by decide
  have hdescent : baseEnd_228808 < baseStart_228808 := by decide
  rcases family_descends (prefixWord ++ tailWord_228808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228811 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 9]
def baseStart_228811 : Nat := 118140960795 + 228811 * 2 ^ 59
def prefixEnd_228811 : Nat := 4983230072969 + 3 ^ 40 * 228811 * 2
def baseEnd_228811 : Nat := 13054446892889945512247

theorem tailTrace_228811 : CollatzResearch.WordTrace tailWord_228811 prefixEnd_228811 13054446892889945512247 := by
  unfold tailWord_228811
  simp only [CollatzResearch.WordTrace]
  refine ⟨8345422774064299652766287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5563615182709533101844191 8345422774064299652766287)
  ·
    refine ⟨12518134161096449479149431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8345422774064299652766287 12518134161096449479149431)
    ·
      refine ⟨18777201241644674218724147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12518134161096449479149431 18777201241644674218724147)
      ·
        refine ⟨28165801862467011328086221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18777201241644674218724147 28165801862467011328086221)
        ·
          refine ⟨10562175698425129248032333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28165801862467011328086221 10562175698425129248032333)
          ·
            refine ⟨3960815886909423468012125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10562175698425129248032333 3960815886909423468012125)
            ·
              refine ⟨1485305957591033800504547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3960815886909423468012125 1485305957591033800504547)
              ·
                refine ⟨2227958936386550700756821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485305957591033800504547 2227958936386550700756821)
                ·
                  refine ⟨13054446892889945512247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2227958936386550700756821 13054446892889945512247)
                  ·
                    rfl

theorem cell23_228811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 9].length) (baseStart_228811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228811 prefixEnd_228811 := by exact prefixLift 228811
  have htrace : WordTrace (prefixWord ++ tailWord_228811) baseStart_228811 baseEnd_228811 := by
    simpa [prefixWord, tailWord_228811, baseEnd_228811] using wordTrace_append hprefix tailTrace_228811
  have hstable : (prefixWord ++ tailWord_228811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228811).length < 2 ^ (prefixWord ++ tailWord_228811).sum := by decide
  have hdescent : baseEnd_228811 < baseStart_228811 := by decide
  rcases family_descends (prefixWord ++ tailWord_228811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228839 : List Nat := [1, 1, 5, 2, 1, 2, 3, 2, 2, 2, 2]
def baseStart_228839 : Nat := 118140960795 + 228839 * 2 ^ 59
def prefixEnd_228839 : Nat := 4983230072969 + 3 ^ 40 * 228839 * 2
def baseEnd_228839 : Nat := 117504399494335400060095

theorem tailTrace_228839 : CollatzResearch.WordTrace tailWord_228839 prefixEnd_228839 117504399494335400060095 := by
  unfold tailWord_228839
  simp only [CollatzResearch.WordTrace]
  refine ⟨8346444017962860434785571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5564296011975240289857047 8346444017962860434785571)
  ·
    refine ⟨12519666026944290652178357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8346444017962860434785571 12519666026944290652178357)
    ·
      refine ⟨1173718690026027248641721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12519666026944290652178357 1173718690026027248641721)
      ·
        refine ⟨880289017519520436481291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1173718690026027248641721 880289017519520436481291)
        ·
          refine ⟨1320433526279280654721937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880289017519520436481291 1320433526279280654721937)
          ·
            refine ⟨990325144709460491041453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1320433526279280654721937 990325144709460491041453)
            ·
              refine ⟨371371929266047684140545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 990325144709460491041453 371371929266047684140545)
              ·
                refine ⟨278528946949535763105409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371371929266047684140545 278528946949535763105409)
                ·
                  refine ⟨208896710212151822329057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278528946949535763105409 208896710212151822329057)
                  ·
                    refine ⟨156672532659113866746793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 208896710212151822329057 156672532659113866746793)
                    ·
                      refine ⟨117504399494335400060095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 156672532659113866746793 117504399494335400060095)
                      ·
                        rfl

theorem cell23_228839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_228839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228839 prefixEnd_228839 := by exact prefixLift 228839
  have htrace : WordTrace (prefixWord ++ tailWord_228839) baseStart_228839 baseEnd_228839 := by
    simpa [prefixWord, tailWord_228839, baseEnd_228839] using wordTrace_append hprefix tailTrace_228839
  have hstable : (prefixWord ++ tailWord_228839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228839).length < 2 ^ (prefixWord ++ tailWord_228839).sum := by decide
  have hdescent : baseEnd_228839 < baseStart_228839 := by decide
  rcases family_descends (prefixWord ++ tailWord_228839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228895 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 4, 4, 2]
def baseStart_228895 : Nat := 118140960795 + 228895 * 2 ^ 59
def prefixEnd_228895 : Nat := 4983230072969 + 3 ^ 40 * 228895 * 2
def baseEnd_228895 : Nat := 117533154410987180959837

theorem tailTrace_228895 : CollatzResearch.WordTrace tailWord_228895 prefixEnd_228895 117533154410987180959837 := by
  unfold tailWord_228895
  simp only [CollatzResearch.WordTrace]
  refine ⟨8348486505759981998824139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5565657670506654665882759 8348486505759981998824139)
  ·
    refine ⟨12522729758639972998236209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8348486505759981998824139 12522729758639972998236209)
    ·
      refine ⟨9392047318979979748677157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12522729758639972998236209 9392047318979979748677157)
      ·
        refine ⟨1761008872308746202876967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9392047318979979748677157 1761008872308746202876967)
        ·
          refine ⟨2641513308463119304315451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1761008872308746202876967 2641513308463119304315451)
          ·
            refine ⟨3962269962694678956473177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2641513308463119304315451 3962269962694678956473177)
            ·
              refine ⟨2971702472021009217354883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3962269962694678956473177 2971702472021009217354883)
              ·
                refine ⟨4457553708031513826032325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2971702472021009217354883 4457553708031513826032325)
                ·
                  refine ⟨835791320255908842381061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4457553708031513826032325 835791320255908842381061)
                  ·
                    refine ⟨156710872547982907946449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 835791320255908842381061 156710872547982907946449)
                    ·
                      refine ⟨117533154410987180959837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 156710872547982907946449 117533154410987180959837)
                      ·
                        rfl

theorem cell23_228895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_228895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228895 prefixEnd_228895 := by exact prefixLift 228895
  have htrace : WordTrace (prefixWord ++ tailWord_228895) baseStart_228895 baseEnd_228895 := by
    simpa [prefixWord, tailWord_228895, baseEnd_228895] using wordTrace_append hprefix tailTrace_228895
  have hstable : (prefixWord ++ tailWord_228895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228895).length < 2 ^ (prefixWord ++ tailWord_228895).sum := by decide
  have hdescent : baseEnd_228895 < baseStart_228895 := by decide
  rcases family_descends (prefixWord ++ tailWord_228895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228956 : List Nat := [2, 2, 4, 1, 2, 1, 4, 2, 1, 4]
def baseStart_228956 : Nat := 118140960795 + 228956 * 2 ^ 59
def prefixEnd_228956 : Nat := 4983230072969 + 3 ^ 40 * 228956 * 2
def baseEnd_228956 : Nat := 39188158910303814099019

theorem tailTrace_228956 : CollatzResearch.WordTrace tailWord_228956 prefixEnd_228956 39188158910303814099019 := by
  unfold tailWord_228956
  simp only [CollatzResearch.WordTrace]
  refine ⟨4175355679269494708397361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5567140905692659611196481 4175355679269494708397361)
  ·
    refine ⟨3131516759452121031298021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4175355679269494708397361 3131516759452121031298021)
    ·
      refine ⟨587159392397272693368379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3131516759452121031298021 587159392397272693368379)
      ·
        refine ⟨880739088595909040052569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587159392397272693368379 880739088595909040052569)
        ·
          refine ⟨660554316446931780039427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880739088595909040052569 660554316446931780039427)
          ·
            refine ⟨990831474670397670059141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660554316446931780039427 990831474670397670059141)
            ·
              refine ⟨185780901500699563136089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 990831474670397670059141 185780901500699563136089)
              ·
                refine ⟨139335676125524672352067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185780901500699563136089 139335676125524672352067)
                ·
                  refine ⟨209003514188287008528101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139335676125524672352067 209003514188287008528101)
                  ·
                    refine ⟨39188158910303814099019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 209003514188287008528101 39188158910303814099019)
                    ·
                      rfl

theorem cell23_228956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_228956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228956 prefixEnd_228956 := by exact prefixLift 228956
  have htrace : WordTrace (prefixWord ++ tailWord_228956) baseStart_228956 baseEnd_228956 := by
    simpa [prefixWord, tailWord_228956, baseEnd_228956] using wordTrace_append hprefix tailTrace_228956
  have hstable : (prefixWord ++ tailWord_228956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228956).length < 2 ^ (prefixWord ++ tailWord_228956).sum := by decide
  have hdescent : baseEnd_228956 < baseStart_228956 := by decide
  rcases family_descends (prefixWord ++ tailWord_228956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228965 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 3, 5]
def baseStart_228965 : Nat := 118140960795 + 228965 * 2 ^ 59
def prefixEnd_228965 : Nat := 4983230072969 + 3 ^ 40 * 228965 * 2
def baseEnd_228965 : Nat := 39189699352267302361505

theorem tailTrace_228965 : CollatzResearch.WordTrace tailWord_228965 prefixEnd_228965 39189699352267302361505 := by
  unfold tailWord_228965
  simp only [CollatzResearch.WordTrace]
  refine ⟨8351039615506383953872349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5567359743670922635914899 8351039615506383953872349)
  ·
    refine ⟨3131639855814893982702131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8351039615506383953872349 3131639855814893982702131)
    ·
      refine ⟨4697459783722340974053197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3131639855814893982702131 4697459783722340974053197)
      ·
        refine ⟨1761547418895877865269949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4697459783722340974053197 1761547418895877865269949)
        ·
          refine ⟨660580282085954199476231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1761547418895877865269949 660580282085954199476231)
          ·
            refine ⟨990870423128931299214347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660580282085954199476231 990870423128931299214347)
            ·
              refine ⟨1486305634693396948821521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990870423128931299214347 1486305634693396948821521)
              ·
                refine ⟨1114729226020047711616141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1486305634693396948821521 1114729226020047711616141)
                ·
                  refine ⟨418023459757517891856053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114729226020047711616141 418023459757517891856053)
                  ·
                    refine ⟨39189699352267302361505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 418023459757517891856053 39189699352267302361505)
                    ·
                      rfl

theorem cell23_228965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_228965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228965 prefixEnd_228965 := by exact prefixLift 228965
  have htrace : WordTrace (prefixWord ++ tailWord_228965) baseStart_228965 baseEnd_228965 := by
    simpa [prefixWord, tailWord_228965, baseEnd_228965] using wordTrace_append hprefix tailTrace_228965
  have hstable : (prefixWord ++ tailWord_228965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228965).length < 2 ^ (prefixWord ++ tailWord_228965).sum := by decide
  have hdescent : baseEnd_228965 < baseStart_228965 := by decide
  rcases family_descends (prefixWord ++ tailWord_228965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228982 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_228982 : Nat := 118140960795 + 228982 * 2 ^ 59
def prefixEnd_228982 : Nat := 4983230072969 + 3 ^ 40 * 228982 * 2
def baseEnd_228982 : Nat := 39192609075976113523979

theorem tailTrace_228982 : CollatzResearch.WordTrace tailWord_228982 prefixEnd_228982 39192609075976113523979 := by
  unfold tailWord_228982
  simp only [CollatzResearch.WordTrace]
  refine ⟨521978728527799741077575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5567773104296530571494133 521978728527799741077575)
  ·
    refine ⟨782968092791699611616363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 521978728527799741077575 782968092791699611616363)
    ·
      refine ⟨1174452139187549417424545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 782968092791699611616363 1174452139187549417424545)
      ·
        refine ⟨880839104390662063068409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1174452139187549417424545 880839104390662063068409)
        ·
          refine ⟨660629328292996547301307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880839104390662063068409 660629328292996547301307)
          ·
            refine ⟨990943992439494820951961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660629328292996547301307 990943992439494820951961)
            ·
              refine ⟨743207994329621115713971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 990943992439494820951961 743207994329621115713971)
              ·
                refine ⟨1114811991494431673570957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743207994329621115713971 1114811991494431673570957)
                ·
                  refine ⟨418054496810411877589109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114811991494431673570957 418054496810411877589109)
                  ·
                    refine ⟨39192609075976113523979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 418054496810411877589109 39192609075976113523979)
                    ·
                      rfl

theorem cell23_228982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_228982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228982 prefixEnd_228982 := by exact prefixLift 228982
  have htrace : WordTrace (prefixWord ++ tailWord_228982) baseStart_228982 baseEnd_228982 := by
    simpa [prefixWord, tailWord_228982, baseEnd_228982] using wordTrace_append hprefix tailTrace_228982
  have hstable : (prefixWord ++ tailWord_228982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228982).length < 2 ^ (prefixWord ++ tailWord_228982).sum := by decide
  have hdescent : baseEnd_228982 < baseStart_228982 := by decide
  rcases family_descends (prefixWord ++ tailWord_228982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228985 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 3, 1, 4]
def baseStart_228985 : Nat := 118140960795 + 228985 * 2 ^ 59
def prefixEnd_228985 : Nat := 4983230072969 + 3 ^ 40 * 228985 * 2
def baseEnd_228985 : Nat := 117579367669891828834423

theorem tailTrace_228985 : CollatzResearch.WordTrace tailWord_228985 prefixEnd_228985 117579367669891828834423 := by
  unfold tailWord_228985
  simp only [CollatzResearch.WordTrace]
  refine ⟨8351769075433927369600409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5567846050289284913066939 8351769075433927369600409)
  ·
    refine ⟨6263826806575445527200307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8351769075433927369600409 6263826806575445527200307)
    ·
      refine ⟨9395740209863168290800461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6263826806575445527200307 9395740209863168290800461)
      ·
        refine ⟨3523402578698688109050173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9395740209863168290800461 3523402578698688109050173)
        ·
          refine ⟨1321275967012008040893815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3523402578698688109050173 1321275967012008040893815)
          ·
            refine ⟨1981913950518012061340723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1321275967012008040893815 1981913950518012061340723)
            ·
              refine ⟨2972870925777018092011085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981913950518012061340723 2972870925777018092011085)
              ·
                refine ⟨1114826597166381784504157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2972870925777018092011085 1114826597166381784504157)
                ·
                  refine ⟨418059973937393169189059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114826597166381784504157 418059973937393169189059)
                  ·
                    refine ⟨627089960906089753783589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 418059973937393169189059 627089960906089753783589)
                    ·
                      refine ⟨117579367669891828834423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 627089960906089753783589 117579367669891828834423)
                      ·
                        rfl

theorem cell23_228985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_228985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228985 prefixEnd_228985 := by exact prefixLift 228985
  have htrace : WordTrace (prefixWord ++ tailWord_228985) baseStart_228985 baseEnd_228985 := by
    simpa [prefixWord, tailWord_228985, baseEnd_228985] using wordTrace_append hprefix tailTrace_228985
  have hstable : (prefixWord ++ tailWord_228985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228985).length < 2 ^ (prefixWord ++ tailWord_228985).sum := by decide
  have hdescent : baseEnd_228985 < baseStart_228985 := by decide
  rcases family_descends (prefixWord ++ tailWord_228985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228989 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 2, 3, 2]
def baseStart_228989 : Nat := 118140960795 + 228989 * 2 ^ 59
def prefixEnd_228989 : Nat := 4983230072969 + 3 ^ 40 * 228989 * 2
def baseEnd_228989 : Nat := 117581421592509813184405

theorem tailTrace_228989 : CollatzResearch.WordTrace tailWord_228989 prefixEnd_228989 117581421592509813184405 := by
  unfold tailWord_228989
  simp only [CollatzResearch.WordTrace]
  refine ⟨8351914967419436052746021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5567943311612957368497347 8351914967419436052746021)
  ·
    refine ⟨1565984056391144259889879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8351914967419436052746021 1565984056391144259889879)
    ·
      refine ⟨2348976084586716389834819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1565984056391144259889879 2348976084586716389834819)
      ·
        refine ⟨3523464126880074584752229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2348976084586716389834819 3523464126880074584752229)
        ·
          refine ⟨660649523790013984641043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3523464126880074584752229 660649523790013984641043)
          ·
            refine ⟨990974285685020976961565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660649523790013984641043 990974285685020976961565)
            ·
              refine ⟨371615357131882866360587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 990974285685020976961565 371615357131882866360587)
              ·
                refine ⟨557423035697824299540881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371615357131882866360587 557423035697824299540881)
                ·
                  refine ⟨418067276773368224655661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557423035697824299540881 418067276773368224655661)
                  ·
                    refine ⟨156775228790013084245873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 418067276773368224655661 156775228790013084245873)
                    ·
                      refine ⟨117581421592509813184405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 156775228790013084245873 117581421592509813184405)
                      ·
                        rfl

theorem cell23_228989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_228989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228989 prefixEnd_228989 := by exact prefixLift 228989
  have htrace : WordTrace (prefixWord ++ tailWord_228989) baseStart_228989 baseEnd_228989 := by
    simpa [prefixWord, tailWord_228989, baseEnd_228989] using wordTrace_append hprefix tailTrace_228989
  have hstable : (prefixWord ++ tailWord_228989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228989).length < 2 ^ (prefixWord ++ tailWord_228989).sum := by decide
  have hdescent : baseEnd_228989 < baseStart_228989 := by decide
  rcases family_descends (prefixWord ++ tailWord_228989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228995 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 4, 4]
def baseStart_228995 : Nat := 118140960795 + 228995 * 2 ^ 59
def prefixEnd_228995 : Nat := 4983230072969 + 3 ^ 40 * 228995 * 2
def baseEnd_228995 : Nat := 39194834158812263236459

theorem tailTrace_228995 : CollatzResearch.WordTrace tailWord_228995 prefixEnd_228995 39194834158812263236459 := by
  unfold tailWord_228995
  simp only [CollatzResearch.WordTrace]
  refine ⟨8352133805397699077464439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5568089203598466051642959 8352133805397699077464439)
  ·
    refine ⟨12528200708096548616196659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8352133805397699077464439 12528200708096548616196659)
    ·
      refine ⟨18792301062144822924294989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12528200708096548616196659 18792301062144822924294989)
      ·
        refine ⟨7047112898304308596610621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18792301062144822924294989 7047112898304308596610621)
        ·
          refine ⟨2642667336864115723728983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7047112898304308596610621 2642667336864115723728983)
          ·
            refine ⟨3964001005296173585593475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2642667336864115723728983 3964001005296173585593475)
            ·
              refine ⟨5946001507944260378390213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964001005296173585593475 5946001507944260378390213)
              ·
                refine ⟨1114875282739548820948165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5946001507944260378390213 1114875282739548820948165)
                ·
                  refine ⟨209039115513665403927781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1114875282739548820948165 209039115513665403927781)
                  ·
                    refine ⟨39194834158812263236459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 209039115513665403927781 39194834158812263236459)
                    ·
                      rfl

theorem cell23_228995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 4].length) (baseStart_228995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228995 prefixEnd_228995 := by exact prefixLift 228995
  have htrace : WordTrace (prefixWord ++ tailWord_228995) baseStart_228995 baseEnd_228995 := by
    simpa [prefixWord, tailWord_228995, baseEnd_228995] using wordTrace_append hprefix tailTrace_228995
  have hstable : (prefixWord ++ tailWord_228995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228995).length < 2 ^ (prefixWord ++ tailWord_228995).sum := by decide
  have hdescent : baseEnd_228995 < baseStart_228995 := by decide
  rcases family_descends (prefixWord ++ tailWord_228995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228999 : List Nat := [1, 1, 4, 2, 1, 5, 2, 1, 1, 5]
def baseStart_228999 : Nat := 118140960795 + 228999 * 2 ^ 59
def prefixEnd_228999 : Nat := 4983230072969 + 3 ^ 40 * 228999 * 2
def baseEnd_228999 : Nat := 39195518799684924686453

theorem tailTrace_228999 : CollatzResearch.WordTrace tailWord_228999 prefixEnd_228999 39195518799684924686453 := by
  unfold tailWord_228999
  simp only [CollatzResearch.WordTrace]
  refine ⟨8352279697383207760610051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5568186464922138507073367 8352279697383207760610051)
  ·
    refine ⟨12528419546074811640915077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8352279697383207760610051 12528419546074811640915077)
    ·
      refine ⟨2349078664889027182671577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12528419546074811640915077 2349078664889027182671577)
      ·
        refine ⟨1761808998666770387003683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2349078664889027182671577 1761808998666770387003683)
        ·
          refine ⟨2642713498000155580505525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1761808998666770387003683 2642713498000155580505525)
          ·
            refine ⟨247754390437514585672393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2642713498000155580505525 247754390437514585672393)
            ·
              refine ⟨185815792828135939254295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247754390437514585672393 185815792828135939254295)
              ·
                refine ⟨278723689242203908881443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185815792828135939254295 278723689242203908881443)
                ·
                  refine ⟨418085533863305863322165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278723689242203908881443 418085533863305863322165)
                  ·
                    refine ⟨39195518799684924686453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 418085533863305863322165 39195518799684924686453)
                    ·
                      rfl

theorem cell23_228999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_228999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_228999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_228999 prefixEnd_228999 := by exact prefixLift 228999
  have htrace : WordTrace (prefixWord ++ tailWord_228999) baseStart_228999 baseEnd_228999 := by
    simpa [prefixWord, tailWord_228999, baseEnd_228999] using wordTrace_append hprefix tailTrace_228999
  have hstable : (prefixWord ++ tailWord_228999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228999).length < 2 ^ (prefixWord ++ tailWord_228999).sum := by decide
  have hdescent : baseEnd_228999 < baseStart_228999 := by decide
  rcases family_descends (prefixWord ++ tailWord_228999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229022 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_229022 : Nat := 118140960795 + 229022 * 2 ^ 59
def prefixEnd_229022 : Nat := 4983230072969 + 3 ^ 40 * 229022 * 2
def baseEnd_229022 : Nat := 117598366454108184071753

theorem tailTrace_229022 : CollatzResearch.WordTrace tailWord_229022 prefixEnd_229022 117598366454108184071753 := by
  unfold tailWord_229022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1044139822037485336087165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5568745717533255125798213 1044139822037485336087165)
  ·
    refine ⟨391552433264057001032687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1044139822037485336087165 391552433264057001032687)
    ·
      refine ⟨587328649896085501549031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391552433264057001032687 587328649896085501549031)
      ·
        refine ⟨880992974844128252323547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587328649896085501549031 880992974844128252323547)
        ·
          refine ⟨1321489462266192378485321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880992974844128252323547 1321489462266192378485321)
          ·
            refine ⟨991117096699644283863991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1321489462266192378485321 991117096699644283863991)
            ·
              refine ⟨1486675645049466425795987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 991117096699644283863991 1486675645049466425795987)
              ·
                refine ⟨2230013467574199638693981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1486675645049466425795987 2230013467574199638693981)
                ·
                  refine ⟨836255050340324864510243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2230013467574199638693981 836255050340324864510243)
                  ·
                    refine ⟨1254382575510487296765365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 836255050340324864510243 1254382575510487296765365)
                    ·
                      refine ⟨117598366454108184071753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1254382575510487296765365 117598366454108184071753)
                      ·
                        rfl

theorem cell23_229022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_229022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229022 prefixEnd_229022 := by exact prefixLift 229022
  have htrace : WordTrace (prefixWord ++ tailWord_229022) baseStart_229022 baseEnd_229022 := by
    simpa [prefixWord, tailWord_229022, baseEnd_229022] using wordTrace_append hprefix tailTrace_229022
  have hstable : (prefixWord ++ tailWord_229022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229022).length < 2 ^ (prefixWord ++ tailWord_229022).sum := by decide
  have hdescent : baseEnd_229022 < baseStart_229022 := by decide
  rcases family_descends (prefixWord ++ tailWord_229022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229096 : List Nat := [2, 1, 4, 1, 3, 1, 3, 2, 1, 3, 2]
def baseStart_229096 : Nat := 118140960795 + 229096 * 2 ^ 59
def prefixEnd_229096 : Nat := 4983230072969 + 3 ^ 40 * 229096 * 2
def baseEnd_229096 : Nat := 117636364022540894546413

theorem tailTrace_229096 : CollatzResearch.WordTrace tailWord_229096 prefixEnd_229096 117636364022540894546413 := by
  unfold tailWord_229096
  simp only [CollatzResearch.WordTrace]
  refine ⟨4177908789015896663445571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5570545052021195551260761 4177908789015896663445571)
  ·
    refine ⟨6266863183523844995168357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4177908789015896663445571 6266863183523844995168357)
    ·
      refine ⟨1175036846910720936594067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6266863183523844995168357 1175036846910720936594067)
      ·
        refine ⟨1762555270366081404891101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1175036846910720936594067 1762555270366081404891101)
        ·
          refine ⟨660958226387280526834163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1762555270366081404891101 660958226387280526834163)
          ·
            refine ⟨991437339580920790251245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660958226387280526834163 991437339580920790251245)
            ·
              refine ⟨371789002342845296344217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 991437339580920790251245 371789002342845296344217)
              ·
                refine ⟨278841751757133972258163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371789002342845296344217 278841751757133972258163)
                ·
                  refine ⟨418262627635700958387245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278841751757133972258163 418262627635700958387245)
                  ·
                    refine ⟨156848485363387859395217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 418262627635700958387245 156848485363387859395217)
                    ·
                      refine ⟨117636364022540894546413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 156848485363387859395217 117636364022540894546413)
                      ·
                        rfl

theorem cell23_229096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_229096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229096 prefixEnd_229096 := by exact prefixLift 229096
  have htrace : WordTrace (prefixWord ++ tailWord_229096) baseStart_229096 baseEnd_229096 := by
    simpa [prefixWord, tailWord_229096, baseEnd_229096] using wordTrace_append hprefix tailTrace_229096
  have hstable : (prefixWord ++ tailWord_229096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229096).length < 2 ^ (prefixWord ++ tailWord_229096).sum := by decide
  have hdescent : baseEnd_229096 < baseStart_229096 := by decide
  rcases family_descends (prefixWord ++ tailWord_229096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229155 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 7]
def baseStart_229155 : Nat := 118140960795 + 229155 * 2 ^ 59
def prefixEnd_229155 : Nat := 4983230072969 + 3 ^ 40 * 229155 * 2
def baseEnd_229155 : Nat := 117666659381156163708641

theorem tailTrace_229155 : CollatzResearch.WordTrace tailWord_229155 prefixEnd_229155 117666659381156163708641 := by
  unfold tailWord_229155
  simp only [CollatzResearch.WordTrace]
  refine ⟨8357969484818046403288919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5571979656545364268859279 8357969484818046403288919)
  ·
    refine ⟨12536954227227069604933379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8357969484818046403288919 12536954227227069604933379)
    ·
      refine ⟨18805431340840604407400069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12536954227227069604933379 18805431340840604407400069)
      ·
        refine ⟨3526018376407613326387513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18805431340840604407400069 3526018376407613326387513)
        ·
          refine ⟨2644513782305709994790635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3526018376407613326387513 2644513782305709994790635)
          ·
            refine ⟨3966770673458564992185953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644513782305709994790635 3966770673458564992185953)
            ·
              refine ⟨2975078005093923744139465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3966770673458564992185953 2975078005093923744139465)
              ·
                refine ⟨2231308503820442808104599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2975078005093923744139465 2231308503820442808104599)
                ·
                  refine ⟨3346962755730664212156899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2231308503820442808104599 3346962755730664212156899)
                  ·
                    refine ⟨5020444133595996318235349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3346962755730664212156899 5020444133595996318235349)
                    ·
                      refine ⟨117666659381156163708641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5020444133595996318235349 117666659381156163708641)
                      ·
                        rfl

theorem cell23_229155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_229155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229155 prefixEnd_229155 := by exact prefixLift 229155
  have htrace : WordTrace (prefixWord ++ tailWord_229155) baseStart_229155 baseEnd_229155 := by
    simpa [prefixWord, tailWord_229155, baseEnd_229155] using wordTrace_append hprefix tailTrace_229155
  have hstable : (prefixWord ++ tailWord_229155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229155).length < 2 ^ (prefixWord ++ tailWord_229155).sum := by decide
  have hdescent : baseEnd_229155 < baseStart_229155 := by decide
  rcases family_descends (prefixWord ++ tailWord_229155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229177 : List Nat := [1, 2, 1, 7, 2, 1, 1, 2, 2, 2, 2]
def baseStart_229177 : Nat := 118140960795 + 229177 * 2 ^ 59
def prefixEnd_229177 : Nat := 4983230072969 + 3 ^ 40 * 229177 * 2
def baseEnd_229177 : Nat := 117677955955555077633541

theorem tailTrace_229177 : CollatzResearch.WordTrace tailWord_229177 prefixEnd_229177 117677955955555077633541 := by
  unfold tailWord_229177
  simp only [CollatzResearch.WordTrace]
  refine ⟨8358771890738344160589785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5572514593825562773726523 8358771890738344160589785)
  ·
    refine ⟨6269078918053758120442339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8358771890738344160589785 6269078918053758120442339)
    ·
      refine ⟨9403618377080637180663509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6269078918053758120442339 9403618377080637180663509)
      ·
        refine ⟨220397305712827433921801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 9403618377080637180663509 220397305712827433921801)
        ·
          refine ⟨165297979284620575441351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220397305712827433921801 165297979284620575441351)
          ·
            refine ⟨247946968926930863162027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165297979284620575441351 247946968926930863162027)
            ·
              refine ⟨371920453390396294743041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247946968926930863162027 371920453390396294743041)
              ·
                refine ⟨278940340042797221057281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371920453390396294743041 278940340042797221057281)
                ·
                  refine ⟨209205255032097915792961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278940340042797221057281 209205255032097915792961)
                  ·
                    refine ⟨156903941274073436844721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 209205255032097915792961 156903941274073436844721)
                    ·
                      refine ⟨117677955955555077633541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 156903941274073436844721 117677955955555077633541)
                      ·
                        rfl

theorem cell23_229177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_229177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229177 prefixEnd_229177 := by exact prefixLift 229177
  have htrace : WordTrace (prefixWord ++ tailWord_229177) baseStart_229177 baseEnd_229177 := by
    simpa [prefixWord, tailWord_229177, baseEnd_229177] using wordTrace_append hprefix tailTrace_229177
  have hstable : (prefixWord ++ tailWord_229177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229177).length < 2 ^ (prefixWord ++ tailWord_229177).sum := by decide
  have hdescent : baseEnd_229177 < baseStart_229177 := by decide
  rcases family_descends (prefixWord ++ tailWord_229177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229259 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 6, 3, 2]
def baseStart_229259 : Nat := 118140960795 + 229259 * 2 ^ 59
def prefixEnd_229259 : Nat := 4983230072969 + 3 ^ 40 * 229259 * 2
def baseEnd_229259 : Nat := 117720061369223756808163

theorem tailTrace_229259 : CollatzResearch.WordTrace tailWord_229259 prefixEnd_229259 117720061369223756808163 := by
  unfold tailWord_229259
  simp only [CollatzResearch.WordTrace]
  refine ⟨8361762676441272165074831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5574508450960848110049887 8361762676441272165074831)
  ·
    refine ⟨12542644014661908247612247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8361762676441272165074831 12542644014661908247612247)
    ·
      refine ⟨18813966021992862371418371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12542644014661908247612247 18813966021992862371418371)
      ·
        refine ⟨28220949032989293557127557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18813966021992862371418371 28220949032989293557127557)
        ·
          refine ⟨5291427943685492541961417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28220949032989293557127557 5291427943685492541961417)
          ·
            refine ⟨3968570957764119406471063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5291427943685492541961417 3968570957764119406471063)
            ·
              refine ⟨5952856436646179109706595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3968570957764119406471063 5952856436646179109706595)
              ·
                refine ⟨8929284654969268664559893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5952856436646179109706595 8929284654969268664559893)
                ·
                  refine ⟨418560218201684468651245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8929284654969268664559893 418560218201684468651245)
                  ·
                    refine ⟨156960081825631675744217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 418560218201684468651245 156960081825631675744217)
                    ·
                      refine ⟨117720061369223756808163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 156960081825631675744217 117720061369223756808163)
                      ·
                        rfl

theorem cell23_229259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 3, 2].length) (baseStart_229259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229259 prefixEnd_229259 := by exact prefixLift 229259
  have htrace : WordTrace (prefixWord ++ tailWord_229259) baseStart_229259 baseEnd_229259 := by
    simpa [prefixWord, tailWord_229259, baseEnd_229259] using wordTrace_append hprefix tailTrace_229259
  have hstable : (prefixWord ++ tailWord_229259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229259).length < 2 ^ (prefixWord ++ tailWord_229259).sum := by decide
  have hdescent : baseEnd_229259 < baseStart_229259 := by decide
  rcases family_descends (prefixWord ++ tailWord_229259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229326 : List Nat := [4, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3]
def baseStart_229326 : Nat := 118140960795 + 229326 * 2 ^ 59
def prefixEnd_229326 : Nat := 4983230072969 + 3 ^ 40 * 229326 * 2
def baseEnd_229326 : Nat := 117754464573074994670355

theorem tailTrace_229326 : CollatzResearch.WordTrace tailWord_229326 prefixEnd_229326 117754464573074994670355 := by
  unfold tailWord_229326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1045525795899817825970479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5576137578132361738509221 1045525795899817825970479)
  ·
    refine ⟨1568288693849726738955719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1045525795899817825970479 1568288693849726738955719)
    ·
      refine ⟨2352433040774590108433579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1568288693849726738955719 2352433040774590108433579)
      ·
        refine ⟨3528649561161885162650369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2352433040774590108433579 3528649561161885162650369)
        ·
          refine ⟨2646487170871413871987777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3528649561161885162650369 2646487170871413871987777)
          ·
            refine ⟨1984865378153560403990833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2646487170871413871987777 1984865378153560403990833)
            ·
              refine ⟨1488649033615170302993125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1984865378153560403990833 1488649033615170302993125)
              ·
                refine ⟨279121693802844431811211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1488649033615170302993125 279121693802844431811211)
                ·
                  refine ⟨418682540704266647716817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279121693802844431811211 418682540704266647716817)
                  ·
                    refine ⟨314011905528199985787613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 418682540704266647716817 314011905528199985787613)
                    ·
                      refine ⟨117754464573074994670355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 314011905528199985787613 117754464573074994670355)
                      ·
                        rfl

theorem cell23_229326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_229326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229326 prefixEnd_229326 := by exact prefixLift 229326
  have htrace : WordTrace (prefixWord ++ tailWord_229326) baseStart_229326 baseEnd_229326 := by
    simpa [prefixWord, tailWord_229326, baseEnd_229326] using wordTrace_append hprefix tailTrace_229326
  have hstable : (prefixWord ++ tailWord_229326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229326).length < 2 ^ (prefixWord ++ tailWord_229326).sum := by decide
  have hdescent : baseEnd_229326 < baseStart_229326 := by decide
  rcases family_descends (prefixWord ++ tailWord_229326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229343 : List Nat := [1, 1, 2, 3, 4, 1, 4, 1, 1, 2, 3]
def baseStart_229343 : Nat := 118140960795 + 229343 * 2 ^ 59
def prefixEnd_229343 : Nat := 4983230072969 + 3 ^ 40 * 229343 * 2
def baseEnd_229343 : Nat := 117763193744201428157777

theorem tailTrace_229343 : CollatzResearch.WordTrace tailWord_229343 prefixEnd_229343 117763193744201428157777 := by
  unfold tailWord_229343
  simp only [CollatzResearch.WordTrace]
  refine ⟨8364826408136954511132683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5576550938757969674088455 8364826408136954511132683)
  ·
    refine ⟨12547239612205431766699025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8364826408136954511132683 12547239612205431766699025)
    ·
      refine ⟨9410429709154073825024269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12547239612205431766699025 9410429709154073825024269)
      ·
        refine ⟨3528911140932777684384101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9410429709154073825024269 3528911140932777684384101)
        ·
          refine ⟨661670838924895815822019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3528911140932777684384101 661670838924895815822019)
          ·
            refine ⟨992506258387343723733029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661670838924895815822019 992506258387343723733029)
            ·
              refine ⟨186094923447626948199943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 992506258387343723733029 186094923447626948199943)
              ·
                refine ⟨279142385171440422299915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186094923447626948199943 279142385171440422299915)
                ·
                  refine ⟨418713577757160633449873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279142385171440422299915 418713577757160633449873)
                  ·
                    refine ⟨314035183317870475087405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 418713577757160633449873 314035183317870475087405)
                    ·
                      refine ⟨117763193744201428157777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 314035183317870475087405 117763193744201428157777)
                      ·
                        rfl

theorem cell23_229343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_229343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229343 prefixEnd_229343 := by exact prefixLift 229343
  have htrace : WordTrace (prefixWord ++ tailWord_229343) baseStart_229343 baseEnd_229343 := by
    simpa [prefixWord, tailWord_229343, baseEnd_229343] using wordTrace_append hprefix tailTrace_229343
  have hstable : (prefixWord ++ tailWord_229343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229343).length < 2 ^ (prefixWord ++ tailWord_229343).sum := by decide
  have hdescent : baseEnd_229343 < baseStart_229343 := by decide
  rcases family_descends (prefixWord ++ tailWord_229343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229346 : List Nat := [3, 3, 3, 1, 2, 1, 10]
def baseStart_229346 : Nat := 118140960795 + 229346 * 2 ^ 59
def prefixEnd_229346 : Nat := 4983230072969 + 3 ^ 40 * 229346 * 2
def baseEnd_229346 : Nat := 1453885607236603906423

theorem tailTrace_229346 : CollatzResearch.WordTrace tailWord_229346 prefixEnd_229346 1453885607236603906423 := by
  unfold tailWord_229346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2091233956781521505872973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5576623884750724015661261 2091233956781521505872973)
  ·
    refine ⟨784212733793070564702365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2091233956781521505872973 784212733793070564702365)
    ·
      refine ⟨294079775172401461763387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 784212733793070564702365 294079775172401461763387)
      ·
        refine ⟨441119662758602192645081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294079775172401461763387 441119662758602192645081)
        ·
          refine ⟨330839747068951644483811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441119662758602192645081 330839747068951644483811)
          ·
            refine ⟨496259620603427466725717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330839747068951644483811 496259620603427466725717)
            ·
              refine ⟨1453885607236603906423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 496259620603427466725717 1453885607236603906423)
              ·
                rfl

theorem cell23_229346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 10].length) (baseStart_229346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229346 prefixEnd_229346 := by exact prefixLift 229346
  have htrace : WordTrace (prefixWord ++ tailWord_229346) baseStart_229346 baseEnd_229346 := by
    simpa [prefixWord, tailWord_229346, baseEnd_229346] using wordTrace_append hprefix tailTrace_229346
  have hstable : (prefixWord ++ tailWord_229346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229346).length < 2 ^ (prefixWord ++ tailWord_229346).sum := by decide
  have hdescent : baseEnd_229346 < baseStart_229346 := by decide
  rcases family_descends (prefixWord ++ tailWord_229346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229357 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 3, 2, 2]
def baseStart_229357 : Nat := 118140960795 + 229357 * 2 ^ 59
def prefixEnd_229357 : Nat := 4983230072969 + 3 ^ 40 * 229357 * 2
def baseEnd_229357 : Nat := 117770382473364373382713

theorem tailTrace_229357 : CollatzResearch.WordTrace tailWord_229357 prefixEnd_229357 117770382473364373382713 := by
  unfold tailWord_229357
  simp only [CollatzResearch.WordTrace]
  refine ⟨8365337030086234902142325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5576891353390823268094883 8365337030086234902142325)
  ·
    refine ⟨784250346570584522075843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8365337030086234902142325 784250346570584522075843)
    ·
      refine ⟨1176375519855876783113765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 784250346570584522075843 1176375519855876783113765)
      ·
        refine ⟨220570409972976896833831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1176375519855876783113765 220570409972976896833831)
        ·
          refine ⟨330855614959465345250747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220570409972976896833831 330855614959465345250747)
          ·
            refine ⟨496283422439198017876121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330855614959465345250747 496283422439198017876121)
            ·
              refine ⟨372212566829398513407091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496283422439198017876121 372212566829398513407091)
              ·
                refine ⟨558318850244097770110637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372212566829398513407091 558318850244097770110637)
                ·
                  refine ⟨209369568841536663791489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 558318850244097770110637 209369568841536663791489)
                  ·
                    refine ⟨157027176631152497843617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 209369568841536663791489 157027176631152497843617)
                    ·
                      refine ⟨117770382473364373382713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 157027176631152497843617 117770382473364373382713)
                      ·
                        rfl

theorem cell23_229357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_229357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229357 prefixEnd_229357 := by exact prefixLift 229357
  have htrace : WordTrace (prefixWord ++ tailWord_229357) baseStart_229357 baseEnd_229357 := by
    simpa [prefixWord, tailWord_229357, baseEnd_229357] using wordTrace_append hprefix tailTrace_229357
  have hstable : (prefixWord ++ tailWord_229357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229357).length < 2 ^ (prefixWord ++ tailWord_229357).sum := by decide
  have hdescent : baseEnd_229357 < baseStart_229357 := by decide
  rcases family_descends (prefixWord ++ tailWord_229357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229380 : List Nat := [2, 3, 2, 4, 2, 1, 2, 7]
def baseStart_229380 : Nat := 118140960795 + 229380 * 2 ^ 59
def prefixEnd_229380 : Nat := 4983230072969 + 3 ^ 40 * 229380 * 2
def baseEnd_229380 : Nat := 4362303426978436422041

theorem tailTrace_229380 : CollatzResearch.WordTrace tailWord_229380 prefixEnd_229380 4362303426978436422041 := by
  unfold tailWord_229380
  simp only [CollatzResearch.WordTrace]
  refine ⟨4183087954501454915114797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5577450606001939886819729 4183087954501454915114797)
  ·
    refine ⟨1568657982938045593168049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4183087954501454915114797 1568657982938045593168049)
    ·
      refine ⟨1176493487203534194876037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1568657982938045593168049 1176493487203534194876037)
      ·
        refine ⟨220592528850662661539257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1176493487203534194876037 220592528850662661539257)
        ·
          refine ⟨165444396637996996154443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220592528850662661539257 165444396637996996154443)
          ·
            refine ⟨248166594956995494231665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165444396637996996154443 248166594956995494231665)
            ·
              refine ⟨186124946217746620673749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248166594956995494231665 186124946217746620673749)
              ·
                refine ⟨4362303426978436422041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 186124946217746620673749 4362303426978436422041)
                ·
                  rfl

theorem cell23_229380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 7].length) (baseStart_229380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229380 prefixEnd_229380 := by exact prefixLift 229380
  have htrace : WordTrace (prefixWord ++ tailWord_229380) baseStart_229380 baseEnd_229380 := by
    simpa [prefixWord, tailWord_229380, baseEnd_229380] using wordTrace_append hprefix tailTrace_229380
  have hstable : (prefixWord ++ tailWord_229380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229380).length < 2 ^ (prefixWord ++ tailWord_229380).sum := by decide
  have hdescent : baseEnd_229380 < baseStart_229380 := by decide
  rcases family_descends (prefixWord ++ tailWord_229380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229383 : List Nat := [1, 1, 4, 3, 1, 2, 1, 4, 1, 3, 2]
def baseStart_229383 : Nat := 118140960795 + 229383 * 2 ^ 59
def prefixEnd_229383 : Nat := 4983230072969 + 3 ^ 40 * 229383 * 2
def baseEnd_229383 : Nat := 117783732970381271657593

theorem tailTrace_229383 : CollatzResearch.WordTrace tailWord_229383 prefixEnd_229383 117783732970381271657593 := by
  unfold tailWord_229383
  simp only [CollatzResearch.WordTrace]
  refine ⟨8366285327992041342588803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5577523551994694228392535 8366285327992041342588803)
  ·
    refine ⟨12549427991988062013883205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8366285327992041342588803 12549427991988062013883205)
    ·
      refine ⟨2353017748497761627603101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12549427991988062013883205 2353017748497761627603101)
      ·
        refine ⟨882381655686660610351163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2353017748497761627603101 882381655686660610351163)
        ·
          refine ⟨1323572483529990915526745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882381655686660610351163 1323572483529990915526745)
          ·
            refine ⟨992679362647493186645059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1323572483529990915526745 992679362647493186645059)
            ·
              refine ⟨1489019043971239779967589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992679362647493186645059 1489019043971239779967589)
              ·
                refine ⟨279191070744607458743923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1489019043971239779967589 279191070744607458743923)
                ·
                  refine ⟨418786606116911188115885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279191070744607458743923 418786606116911188115885)
                  ·
                    refine ⟨157044977293841695543457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 418786606116911188115885 157044977293841695543457)
                    ·
                      refine ⟨117783732970381271657593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 157044977293841695543457 117783732970381271657593)
                      ·
                        rfl

theorem cell23_229383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_229383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229383 prefixEnd_229383 := by exact prefixLift 229383
  have htrace : WordTrace (prefixWord ++ tailWord_229383) baseStart_229383 baseEnd_229383 := by
    simpa [prefixWord, tailWord_229383, baseEnd_229383] using wordTrace_append hprefix tailTrace_229383
  have hstable : (prefixWord ++ tailWord_229383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229383).length < 2 ^ (prefixWord ++ tailWord_229383).sum := by decide
  have hdescent : baseEnd_229383 < baseStart_229383 := by decide
  rcases family_descends (prefixWord ++ tailWord_229383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229413 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 4, 2, 2]
def baseStart_229413 : Nat := 118140960795 + 229413 * 2 ^ 59
def prefixEnd_229413 : Nat := 4983230072969 + 3 ^ 40 * 229413 * 2
def baseEnd_229413 : Nat := 117799137390016154282455

theorem tailTrace_229413 : CollatzResearch.WordTrace tailWord_229413 prefixEnd_229413 117799137390016154282455 := by
  unfold tailWord_229413
  simp only [CollatzResearch.WordTrace]
  refine ⟨8367379517883356466180893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5578253011922237644120595 8367379517883356466180893)
  ·
    refine ⟨3137767319206258674817835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8367379517883356466180893 3137767319206258674817835)
    ·
      refine ⟨4706650978809388012226753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3137767319206258674817835 4706650978809388012226753)
      ·
        refine ⟨3529988234107041009170065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4706650978809388012226753 3529988234107041009170065)
        ·
          refine ⟨2647491175580280756877549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3529988234107041009170065 2647491175580280756877549)
          ·
            refine ⟨992809190842605283829081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2647491175580280756877549 992809190842605283829081)
            ·
              refine ⟨744606893131953962871811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992809190842605283829081 744606893131953962871811)
              ·
                refine ⟨1116910339697930944307717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744606893131953962871811 1116910339697930944307717)
                ·
                  refine ⟨209420688693362052057697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1116910339697930944307717 209420688693362052057697)
                  ·
                    refine ⟨157065516520021539043273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 209420688693362052057697 157065516520021539043273)
                    ·
                      refine ⟨117799137390016154282455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 157065516520021539043273 117799137390016154282455)
                      ·
                        rfl

theorem cell23_229413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_229413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229413 prefixEnd_229413 := by exact prefixLift 229413
  have htrace : WordTrace (prefixWord ++ tailWord_229413) baseStart_229413 baseEnd_229413 := by
    simpa [prefixWord, tailWord_229413, baseEnd_229413] using wordTrace_append hprefix tailTrace_229413
  have hstable : (prefixWord ++ tailWord_229413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229413).length < 2 ^ (prefixWord ++ tailWord_229413).sum := by decide
  have hdescent : baseEnd_229413 < baseStart_229413 := by decide
  rcases family_descends (prefixWord ++ tailWord_229413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229453 : List Nat := [1, 6, 1, 1, 1, 1, 2, 5, 5]
def baseStart_229453 : Nat := 118140960795 + 229453 * 2 ^ 59
def prefixEnd_229453 : Nat := 4983230072969 + 3 ^ 40 * 229453 * 2
def baseEnd_229453 : Nat := 13091075179577333086919

theorem tailTrace_229453 : CollatzResearch.WordTrace tailWord_229453 prefixEnd_229453 13091075179577333086919 := by
  unfold tailWord_229453
  simp only [CollatzResearch.WordTrace]
  refine ⟨8368838437738443297637013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5579225625158962198424675 8368838437738443297637013)
  ·
    refine ⟨392289301768989529576735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8368838437738443297637013 392289301768989529576735)
    ·
      refine ⟨588433952653484294365103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392289301768989529576735 588433952653484294365103)
      ·
        refine ⟨882650928980226441547655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588433952653484294365103 882650928980226441547655)
        ·
          refine ⟨1323976393470339662321483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882650928980226441547655 1323976393470339662321483)
          ·
            refine ⟨1985964590205509493482225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323976393470339662321483 1985964590205509493482225)
            ·
              refine ⟨1489473442654132120111669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1985964590205509493482225 1489473442654132120111669)
              ·
                refine ⟨139638135248824886260469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1489473442654132120111669 139638135248824886260469)
                ·
                  refine ⟨13091075179577333086919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139638135248824886260469 13091075179577333086919)
                  ·
                    rfl

theorem cell23_229453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_229453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229453 prefixEnd_229453 := by exact prefixLift 229453
  have htrace : WordTrace (prefixWord ++ tailWord_229453) baseStart_229453 baseEnd_229453 := by
    simpa [prefixWord, tailWord_229453, baseEnd_229453] using wordTrace_append hprefix tailTrace_229453
  have hstable : (prefixWord ++ tailWord_229453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229453).length < 2 ^ (prefixWord ++ tailWord_229453).sum := by decide
  have hdescent : baseEnd_229453 < baseStart_229453 := by decide
  rcases family_descends (prefixWord ++ tailWord_229453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229486 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_229486 : Nat := 118140960795 + 229486 * 2 ^ 59
def prefixEnd_229486 : Nat := 4983230072969 + 3 ^ 40 * 229486 * 2
def baseEnd_229486 : Nat := 117836621477794368669619

theorem tailTrace_229486 : CollatzResearch.WordTrace tailWord_229486 prefixEnd_229486 117836621477794368669619 := by
  unfold tailWord_229486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1046255255827361241698539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5580028031079259955725541 1046255255827361241698539)
  ·
    refine ⟨1569382883741041862547809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1046255255827361241698539 1569382883741041862547809)
    ·
      refine ⟨1177037162805781396910857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1569382883741041862547809 1177037162805781396910857)
      ·
        refine ⟨882777872104336047683143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1177037162805781396910857 882777872104336047683143)
        ·
          refine ⟨1324166808156504071524715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882777872104336047683143 1324166808156504071524715)
          ·
            refine ⟨1986250212234756107287073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324166808156504071524715 1986250212234756107287073)
            ·
              refine ⟨1489687659176067080465305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1986250212234756107287073 1489687659176067080465305)
              ·
                refine ⟨1117265744382050310348979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1489687659176067080465305 1117265744382050310348979)
                ·
                  refine ⟨1675898616573075465523469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117265744382050310348979 1675898616573075465523469)
                  ·
                    refine ⟨628461981214903299571301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1675898616573075465523469 628461981214903299571301)
                    ·
                      refine ⟨117836621477794368669619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 628461981214903299571301 117836621477794368669619)
                      ·
                        rfl

theorem cell23_229486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_229486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229486 prefixEnd_229486 := by exact prefixLift 229486
  have htrace : WordTrace (prefixWord ++ tailWord_229486) baseStart_229486 baseEnd_229486 := by
    simpa [prefixWord, tailWord_229486, baseEnd_229486] using wordTrace_append hprefix tailTrace_229486
  have hstable : (prefixWord ++ tailWord_229486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229486).length < 2 ^ (prefixWord ++ tailWord_229486).sum := by decide
  have hdescent : baseEnd_229486 < baseStart_229486 := by decide
  rcases family_descends (prefixWord ++ tailWord_229486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229530 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 3, 4]
def baseStart_229530 : Nat := 118140960795 + 229530 * 2 ^ 59
def prefixEnd_229530 : Nat := 4983230072969 + 3 ^ 40 * 229530 * 2
def baseEnd_229530 : Nat := 39286404875530732173139

theorem tailTrace_229530 : CollatzResearch.WordTrace tailWord_229530 prefixEnd_229530 39286404875530732173139 := by
  unfold tailWord_229530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2092911714614871362047511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5581097905639656965460029 2092911714614871362047511)
  ·
    refine ⟨3139367571922307043071267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2092911714614871362047511 3139367571922307043071267)
    ·
      refine ⟨4709051357883460564606901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3139367571922307043071267 4709051357883460564606901)
      ·
        refine ⟨441473564801574427931897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4709051357883460564606901 441473564801574427931897)
        ·
          refine ⟨331105173601180820948923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441473564801574427931897 331105173601180820948923)
          ·
            refine ⟨496657760401771231423385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331105173601180820948923 496657760401771231423385)
            ·
              refine ⟨372493320301328423567539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496657760401771231423385 372493320301328423567539)
              ·
                refine ⟨558739980451992635351309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372493320301328423567539 558739980451992635351309)
                ·
                  refine ⟨209527492669497238256741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 558739980451992635351309 209527492669497238256741)
                  ·
                    refine ⟨39286404875530732173139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 209527492669497238256741 39286404875530732173139)
                    ·
                      rfl

theorem cell23_229530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_229530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229530 prefixEnd_229530 := by exact prefixLift 229530
  have htrace : WordTrace (prefixWord ++ tailWord_229530) baseStart_229530 baseEnd_229530 := by
    simpa [prefixWord, tailWord_229530, baseEnd_229530] using wordTrace_append hprefix tailTrace_229530
  have hstable : (prefixWord ++ tailWord_229530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229530).length < 2 ^ (prefixWord ++ tailWord_229530).sum := by decide
  have hdescent : baseEnd_229530 < baseStart_229530 := by decide
  rcases family_descends (prefixWord ++ tailWord_229530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229563 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 2, 3, 2]
def baseStart_229563 : Nat := 118140960795 + 229563 * 2 ^ 59
def prefixEnd_229563 : Nat := 4983230072969 + 3 ^ 40 * 229563 * 2
def baseEnd_229563 : Nat := 117876159488190567406765

theorem tailTrace_229563 : CollatzResearch.WordTrace tailWord_229563 prefixEnd_229563 117876159488190567406765 := by
  unfold tailWord_229563
  simp only [CollatzResearch.WordTrace]
  refine ⟨8372850467339932084141343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5581900311559954722760895 8372850467339932084141343)
  ·
    refine ⟨12559275701009898126212015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8372850467339932084141343 12559275701009898126212015)
    ·
      refine ⟨18838913551514847189318023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12559275701009898126212015 18838913551514847189318023)
      ·
        refine ⟨28258370327272270783977035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18838913551514847189318023 28258370327272270783977035)
        ·
          refine ⟨42387555490908406175965553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28258370327272270783977035 42387555490908406175965553)
          ·
            refine ⟨31790666618181304631974165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42387555490908406175965553 31790666618181304631974165)
            ·
              refine ⟨1490187497727248654623789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31790666618181304631974165 1490187497727248654623789)
              ·
                refine ⟨558820311647718245483921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1490187497727248654623789 558820311647718245483921)
                ·
                  refine ⟨419115233735788684112941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558820311647718245483921 419115233735788684112941)
                  ·
                    refine ⟨157168212650920756542353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 419115233735788684112941 157168212650920756542353)
                    ·
                      refine ⟨117876159488190567406765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 157168212650920756542353 117876159488190567406765)
                      ·
                        rfl

theorem cell23_229563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 3, 2].length) (baseStart_229563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229563 prefixEnd_229563 := by exact prefixLift 229563
  have htrace : WordTrace (prefixWord ++ tailWord_229563) baseStart_229563 baseEnd_229563 := by
    simpa [prefixWord, tailWord_229563, baseEnd_229563] using wordTrace_append hprefix tailTrace_229563
  have hstable : (prefixWord ++ tailWord_229563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229563).length < 2 ^ (prefixWord ++ tailWord_229563).sum := by decide
  have hdescent : baseEnd_229563 < baseStart_229563 := by decide
  rcases family_descends (prefixWord ++ tailWord_229563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229564 : List Nat := [2, 2, 2, 3, 4, 1, 1, 3, 1, 4]
def baseStart_229564 : Nat := 118140960795 + 229564 * 2 ^ 59
def prefixEnd_229564 : Nat := 4983230072969 + 3 ^ 40 * 229564 * 2
def baseEnd_229564 : Nat := 39292224322948354498087

theorem tailTrace_229564 : CollatzResearch.WordTrace tailWord_229564 prefixEnd_229564 39292224322948354498087 := by
  unfold tailWord_229564
  simp only [CollatzResearch.WordTrace]
  refine ⟨4186443470168154627463873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5581924626890872836618497 4186443470168154627463873)
  ·
    refine ⟨3139832602626115970597905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4186443470168154627463873 3139832602626115970597905)
    ·
      refine ⟨2354874451969586977948429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3139832602626115970597905 2354874451969586977948429)
      ·
        refine ⟨883077919488595116730661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2354874451969586977948429 883077919488595116730661)
        ·
          refine ⟨165577109904111584386999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 883077919488595116730661 165577109904111584386999)
          ·
            refine ⟨248365664856167376580499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165577109904111584386999 248365664856167376580499)
            ·
              refine ⟨372548497284251064870749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248365664856167376580499 372548497284251064870749)
              ·
                refine ⟨139705686481594149326531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372548497284251064870749 139705686481594149326531)
                ·
                  refine ⟨209558529722391223989797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139705686481594149326531 209558529722391223989797)
                  ·
                    refine ⟨39292224322948354498087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 209558529722391223989797 39292224322948354498087)
                    ·
                      rfl

theorem cell23_229564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_229564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229564 prefixEnd_229564 := by exact prefixLift 229564
  have htrace : WordTrace (prefixWord ++ tailWord_229564) baseStart_229564 baseEnd_229564 := by
    simpa [prefixWord, tailWord_229564, baseEnd_229564] using wordTrace_append hprefix tailTrace_229564
  have hstable : (prefixWord ++ tailWord_229564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229564).length < 2 ^ (prefixWord ++ tailWord_229564).sum := by decide
  have hdescent : baseEnd_229564 < baseStart_229564 := by decide
  rcases family_descends (prefixWord ++ tailWord_229564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229576 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_229576 : Nat := 118140960795 + 229576 * 2 ^ 59
def prefixEnd_229576 : Nat := 4983230072969 + 3 ^ 40 * 229576 * 2
def baseEnd_229576 : Nat := 117882834736699016544205

theorem tailTrace_229576 : CollatzResearch.WordTrace tailWord_229576 prefixEnd_229576 117882834736699016544205 := by
  unfold tailWord_229576
  simp only [CollatzResearch.WordTrace]
  refine ⟨4186662308146417652182291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5582216410861890202909721 4186662308146417652182291)
  ·
    refine ⟨6279993462219626478273437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4186662308146417652182291 6279993462219626478273437)
    ·
      refine ⟨2354997548332359929352539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6279993462219626478273437 2354997548332359929352539)
      ·
        refine ⟨3532496322498539894028809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2354997548332359929352539 3532496322498539894028809)
        ·
          refine ⟨2649372241873904920521607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3532496322498539894028809 2649372241873904920521607)
          ·
            refine ⟨3974058362810857380782411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2649372241873904920521607 3974058362810857380782411)
            ·
              refine ⟨5961087544216286071173617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974058362810857380782411 5961087544216286071173617)
              ·
                refine ⟨4470815658162214553380213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5961087544216286071173617 4470815658162214553380213)
                ·
                  refine ⟨419138967952707614379395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4470815658162214553380213 419138967952707614379395)
                  ·
                    refine ⟨628708451929061421569093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 419138967952707614379395 628708451929061421569093)
                    ·
                      refine ⟨117882834736699016544205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 628708451929061421569093 117882834736699016544205)
                      ·
                        rfl

theorem cell23_229576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_229576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229576 prefixEnd_229576 := by exact prefixLift 229576
  have htrace : WordTrace (prefixWord ++ tailWord_229576) baseStart_229576 baseEnd_229576 := by
    simpa [prefixWord, tailWord_229576, baseEnd_229576] using wordTrace_append hprefix tailTrace_229576
  have hstable : (prefixWord ++ tailWord_229576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229576).length < 2 ^ (prefixWord ++ tailWord_229576).sum := by decide
  have hdescent : baseEnd_229576 < baseStart_229576 := by decide
  rcases family_descends (prefixWord ++ tailWord_229576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229610 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 5, 2, 2]
def baseStart_229610 : Nat := 118140960795 + 229610 * 2 ^ 59
def prefixEnd_229610 : Nat := 4983230072969 + 3 ^ 40 * 229610 * 2
def baseEnd_229610 : Nat := 117900293078951883519049

theorem tailTrace_229610 : CollatzResearch.WordTrace tailWord_229610 prefixEnd_229610 117900293078951883519049 := by
  unfold tailWord_229610
  simp only [CollatzResearch.WordTrace]
  refine ⟨2093641174542414777775571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5583043132113106074068189 2093641174542414777775571)
  ·
    refine ⟨3140461761813622166663357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2093641174542414777775571 3140461761813622166663357)
    ·
      refine ⟨1177673160680108312498759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3140461761813622166663357 1177673160680108312498759)
      ·
        refine ⟨1766509741020162468748139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177673160680108312498759 1766509741020162468748139)
        ·
          refine ⟨2649764611530243703122209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766509741020162468748139 2649764611530243703122209)
          ·
            refine ⟨1987323458647682777341657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2649764611530243703122209 1987323458647682777341657)
            ·
              refine ⟨1490492593985762083006243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1987323458647682777341657 1490492593985762083006243)
              ·
                refine ⟨2235738890978643124509365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1490492593985762083006243 2235738890978643124509365)
                ·
                  refine ⟨209600521029247792922753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2235738890978643124509365 209600521029247792922753)
                  ·
                    refine ⟨157200390771935844692065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 209600521029247792922753 157200390771935844692065)
                    ·
                      refine ⟨117900293078951883519049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 157200390771935844692065 117900293078951883519049)
                      ·
                        rfl

theorem cell23_229610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_229610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229610 prefixEnd_229610 := by exact prefixLift 229610
  have htrace : WordTrace (prefixWord ++ tailWord_229610) baseStart_229610 baseEnd_229610 := by
    simpa [prefixWord, tailWord_229610, baseEnd_229610] using wordTrace_append hprefix tailTrace_229610
  have hstable : (prefixWord ++ tailWord_229610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229610).length < 2 ^ (prefixWord ++ tailWord_229610).sum := by decide
  have hdescent : baseEnd_229610 < baseStart_229610 := by decide
  rcases family_descends (prefixWord ++ tailWord_229610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229646 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 1, 9]
def baseStart_229646 : Nat := 118140960795 + 229646 * 2 ^ 59
def prefixEnd_229646 : Nat := 4983230072969 + 3 ^ 40 * 229646 * 2
def baseEnd_229646 : Nat := 39306259460837914222961

theorem tailTrace_229646 : CollatzResearch.WordTrace tailWord_229646 prefixEnd_229646 39306259460837914222961 := by
  unfold tailWord_229646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1046984715754904657426599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5583918484026158172941861 1046984715754904657426599)
  ·
    refine ⟨1570477073632356986139899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1046984715754904657426599 1570477073632356986139899)
    ·
      refine ⟨2355715610448535479209849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1570477073632356986139899 2355715610448535479209849)
      ·
        refine ⟨1766786707836401609407387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2355715610448535479209849 1766786707836401609407387)
        ·
          refine ⟨2650180061754602414111081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766786707836401609407387 2650180061754602414111081)
          ·
            refine ⟨1987635046315951810583311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2650180061754602414111081 1987635046315951810583311)
            ·
              refine ⟨2981452569473927715874967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987635046315951810583311 2981452569473927715874967)
              ·
                refine ⟨4472178854210891573812451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2981452569473927715874967 4472178854210891573812451)
                ·
                  refine ⟨6708268281316337360718677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472178854210891573812451 6708268281316337360718677)
                  ·
                    refine ⟨39306259460837914222961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 6708268281316337360718677 39306259460837914222961)
                    ·
                      rfl

theorem cell23_229646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_229646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229646 prefixEnd_229646 := by exact prefixLift 229646
  have htrace : WordTrace (prefixWord ++ tailWord_229646) baseStart_229646 baseEnd_229646 := by
    simpa [prefixWord, tailWord_229646, baseEnd_229646] using wordTrace_append hprefix tailTrace_229646
  have hstable : (prefixWord ++ tailWord_229646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229646).length < 2 ^ (prefixWord ++ tailWord_229646).sum := by decide
  have hdescent : baseEnd_229646 < baseStart_229646 := by decide
  rcases family_descends (prefixWord ++ tailWord_229646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229678 : List Nat := [4, 1, 3, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_229678 : Nat := 118140960795 + 229678 * 2 ^ 59
def prefixEnd_229678 : Nat := 4983230072969 + 3 ^ 40 * 229678 * 2
def baseEnd_229678 : Nat := 117935209763457617468737

theorem tailTrace_229678 : CollatzResearch.WordTrace tailWord_229678 prefixEnd_229678 117935209763457617468737 := by
  unfold tailWord_229678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047130607740413340572211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5584696574615537816385125 1047130607740413340572211)
  ·
    refine ⟨1570695911610620010858317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1047130607740413340572211 1570695911610620010858317)
    ·
      refine ⟨589010966853982504071869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1570695911610620010858317 589010966853982504071869)
      ·
        refine ⟨220879112570243439026951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 589010966853982504071869 220879112570243439026951)
        ·
          refine ⟨331318668855365158540427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220879112570243439026951 331318668855365158540427)
          ·
            refine ⟨496978003283047737810641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331318668855365158540427 496978003283047737810641)
            ·
              refine ⟨372733502462285803357981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496978003283047737810641 372733502462285803357981)
              ·
                refine ⟨139775063423357176259243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372733502462285803357981 139775063423357176259243)
                ·
                  refine ⟨209662595135035764388865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139775063423357176259243 209662595135035764388865)
                  ·
                    refine ⟨157246946351276823291649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 209662595135035764388865 157246946351276823291649)
                    ·
                      refine ⟨117935209763457617468737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 157246946351276823291649 117935209763457617468737)
                      ·
                        rfl

theorem cell23_229678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_229678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229678 prefixEnd_229678 := by exact prefixLift 229678
  have htrace : WordTrace (prefixWord ++ tailWord_229678) baseStart_229678 baseEnd_229678 := by
    simpa [prefixWord, tailWord_229678, baseEnd_229678] using wordTrace_append hprefix tailTrace_229678
  have hstable : (prefixWord ++ tailWord_229678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229678).length < 2 ^ (prefixWord ++ tailWord_229678).sum := by decide
  have hdescent : baseEnd_229678 < baseStart_229678 := by decide
  rcases family_descends (prefixWord ++ tailWord_229678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229694 : List Nat := [4, 2, 1, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_229694 : Nat := 118140960795 + 229694 * 2 ^ 59
def prefixEnd_229694 : Nat := 4983230072969 + 3 ^ 40 * 229694 * 2
def baseEnd_229694 : Nat := 117943425453929554868663

theorem tailTrace_229694 : CollatzResearch.WordTrace tailWord_229694 prefixEnd_229694 117943425453929554868663 := by
  unfold tailWord_229694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047203553733167682145017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5585085619910227638106757 1047203553733167682145017)
  ·
    refine ⟨785402665299875761608763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1047203553733167682145017 785402665299875761608763)
    ·
      refine ⟨1178103997949813642413145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 785402665299875761608763 1178103997949813642413145)
      ·
        refine ⟨883577998462360231809859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1178103997949813642413145 883577998462360231809859)
        ·
          refine ⟨1325366997693540347714789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883577998462360231809859 1325366997693540347714789)
          ·
            refine ⟨248506312067538815196523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1325366997693540347714789 248506312067538815196523)
            ·
              refine ⟨372759468101308222794785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248506312067538815196523 372759468101308222794785)
              ·
                refine ⟨279569601075981167096089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372759468101308222794785 279569601075981167096089)
                ·
                  refine ⟨209677200806985875322067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279569601075981167096089 209677200806985875322067)
                  ·
                    refine ⟨314515801210478812983101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 209677200806985875322067 314515801210478812983101)
                    ·
                      refine ⟨117943425453929554868663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 314515801210478812983101 117943425453929554868663)
                      ·
                        rfl

theorem cell23_229694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_229694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229694 prefixEnd_229694 := by exact prefixLift 229694
  have htrace : WordTrace (prefixWord ++ tailWord_229694) baseStart_229694 baseEnd_229694 := by
    simpa [prefixWord, tailWord_229694, baseEnd_229694] using wordTrace_append hprefix tailTrace_229694
  have hstable : (prefixWord ++ tailWord_229694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229694).length < 2 ^ (prefixWord ++ tailWord_229694).sum := by decide
  have hdescent : baseEnd_229694 < baseStart_229694 := by decide
  rcases family_descends (prefixWord ++ tailWord_229694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229713 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 2, 2, 4]
def baseStart_229713 : Nat := 118140960795 + 229713 * 2 ^ 59
def prefixEnd_229713 : Nat := 4983230072969 + 3 ^ 40 * 229713 * 2
def baseEnd_229713 : Nat := 117953181586364980531075

theorem tailTrace_229713 : CollatzResearch.WordTrace tailWord_229713 prefixEnd_229713 117953181586364980531075 := by
  unfold tailWord_229713
  simp only [CollatzResearch.WordTrace]
  refine ⟨8378321416796507702101793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5585547611197671801401195 8378321416796507702101793)
  ·
    refine ⟨6283741062597380776576345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8378321416796507702101793 6283741062597380776576345)
    ·
      refine ⟨4712805796948035582432259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6283741062597380776576345 4712805796948035582432259)
      ·
        refine ⟨7069208695422053373648389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4712805796948035582432259 7069208695422053373648389)
        ·
          refine ⟨1325476630391635007559073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7069208695422053373648389 1325476630391635007559073)
          ·
            refine ⟨994107472793726255669305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1325476630391635007559073 994107472793726255669305)
            ·
              refine ⟨745580604595294691751979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 994107472793726255669305 745580604595294691751979)
              ·
                refine ⟨1118370906892942037627969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745580604595294691751979 1118370906892942037627969)
                ·
                  refine ⟨838778180169706528220977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1118370906892942037627969 838778180169706528220977)
                  ·
                    refine ⟨629083635127279896165733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 838778180169706528220977 629083635127279896165733)
                    ·
                      refine ⟨117953181586364980531075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 629083635127279896165733 117953181586364980531075)
                      ·
                        rfl

theorem cell23_229713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_229713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229713 prefixEnd_229713 := by exact prefixLift 229713
  have htrace : WordTrace (prefixWord ++ tailWord_229713) baseStart_229713 baseEnd_229713 := by
    simpa [prefixWord, tailWord_229713, baseEnd_229713] using wordTrace_append hprefix tailTrace_229713
  have hstable : (prefixWord ++ tailWord_229713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229713).length < 2 ^ (prefixWord ++ tailWord_229713).sum := by decide
  have hdescent : baseEnd_229713 < baseStart_229713 := by decide
  rcases family_descends (prefixWord ++ tailWord_229713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229757 : List Nat := [1, 4, 1, 1, 2, 4, 3, 2, 5]
def baseStart_229757 : Nat := 118140960795 + 229757 * 2 ^ 59
def prefixEnd_229757 : Nat := 4983230072969 + 3 ^ 40 * 229757 * 2
def baseEnd_229757 : Nat := 13108419415018089820097

theorem tailTrace_229757 : CollatzResearch.WordTrace tailWord_229757 prefixEnd_229757 13108419415018089820097 := by
  unfold tailWord_229757
  simp only [CollatzResearch.WordTrace]
  refine ⟨8379926228637103216703525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5586617485758068811135683 8379926228637103216703525)
  ·
    refine ⟨1571236167869456853131911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8379926228637103216703525 1571236167869456853131911)
    ·
      refine ⟨2356854251804185279697867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1571236167869456853131911 2356854251804185279697867)
      ·
        refine ⟨3535281377706277919546801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2356854251804185279697867 3535281377706277919546801)
        ·
          refine ⟨2651461033279708439660101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3535281377706277919546801 2651461033279708439660101)
          ·
            refine ⟨497148943739945332436269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2651461033279708439660101 497148943739945332436269)
            ·
              refine ⟨186430853902479499663601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 497148943739945332436269 186430853902479499663601)
              ·
                refine ⟨139823140426859624747701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186430853902479499663601 139823140426859624747701)
                ·
                  refine ⟨13108419415018089820097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139823140426859624747701 13108419415018089820097)
                  ·
                    rfl

theorem cell23_229757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_229757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229757 prefixEnd_229757 := by exact prefixLift 229757
  have htrace : WordTrace (prefixWord ++ tailWord_229757) baseStart_229757 baseEnd_229757 := by
    simpa [prefixWord, tailWord_229757, baseEnd_229757] using wordTrace_append hprefix tailTrace_229757
  have hstable : (prefixWord ++ tailWord_229757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229757).length < 2 ^ (prefixWord ++ tailWord_229757).sum := by decide
  have hdescent : baseEnd_229757 < baseStart_229757 := by decide
  rcases family_descends (prefixWord ++ tailWord_229757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229810 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3]
def baseStart_229810 : Nat := 118140960795 + 229810 * 2 ^ 59
def prefixEnd_229810 : Nat := 4983230072969 + 3 ^ 40 * 229810 * 2
def baseEnd_229810 : Nat := 118002989209851101018129

theorem tailTrace_229810 : CollatzResearch.WordTrace tailWord_229810 prefixEnd_229810 118002989209851101018129 := by
  unfold tailWord_229810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2095464824361273317095721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5587906198296728845588589 2095464824361273317095721)
  ·
    refine ⟨1571598618270954987821791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2095464824361273317095721 1571598618270954987821791)
    ·
      refine ⟨2357397927406432481732687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1571598618270954987821791 2357397927406432481732687)
      ·
        refine ⟨3536096891109648722599031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357397927406432481732687 3536096891109648722599031)
        ·
          refine ⟨5304145336664473083898547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3536096891109648722599031 5304145336664473083898547)
          ·
            refine ⟨7956218004996709625847821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5304145336664473083898547 7956218004996709625847821)
            ·
              refine ⟨2983581751873766109692933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7956218004996709625847821 2983581751873766109692933)
              ·
                refine ⟨559421578476331145567425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2983581751873766109692933 559421578476331145567425)
                ·
                  refine ⟨419566183857248359175569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559421578476331145567425 419566183857248359175569)
                  ·
                    refine ⟨314674637892936269381677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 419566183857248359175569 314674637892936269381677)
                    ·
                      refine ⟨118002989209851101018129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 314674637892936269381677 118002989209851101018129)
                      ·
                        rfl

theorem cell23_229810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_229810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229810 prefixEnd_229810 := by exact prefixLift 229810
  have htrace : WordTrace (prefixWord ++ tailWord_229810) baseStart_229810 baseEnd_229810 := by
    simpa [prefixWord, tailWord_229810, baseEnd_229810] using wordTrace_append hprefix tailTrace_229810
  have hstable : (prefixWord ++ tailWord_229810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229810).length < 2 ^ (prefixWord ++ tailWord_229810).sum := by decide
  have hdescent : baseEnd_229810 < baseStart_229810 := by decide
  rcases family_descends (prefixWord ++ tailWord_229810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229823 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 3]
def baseStart_229823 : Nat := 118140960795 + 229823 * 2 ^ 59
def prefixEnd_229823 : Nat := 4983230072969 + 3 ^ 40 * 229823 * 2
def baseEnd_229823 : Nat := 118009664458359550155569

theorem tailTrace_229823 : CollatzResearch.WordTrace tailWord_229823 prefixEnd_229823 118009664458359550155569 := by
  unfold tailWord_229823
  simp only [CollatzResearch.WordTrace]
  refine ⟨8382333446397996488606123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5588222297598664325737415 8382333446397996488606123)
  ·
    refine ⟨12573500169596994732909185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8382333446397996488606123 12573500169596994732909185)
    ·
      refine ⟨9430125127197746049681889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12573500169596994732909185 9430125127197746049681889)
      ·
        refine ⟨7072593845398309537261417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9430125127197746049681889 7072593845398309537261417)
        ·
          refine ⟨5304445384048732152946063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7072593845398309537261417 5304445384048732152946063)
          ·
            refine ⟨7956668076073098229419095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5304445384048732152946063 7956668076073098229419095)
            ·
              refine ⟨11935002114109647344128643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7956668076073098229419095 11935002114109647344128643)
              ·
                refine ⟨17902503171164471016192965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11935002114109647344128643 17902503171164471016192965)
                ·
                  refine ⟨3356719344593338315536181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17902503171164471016192965 3356719344593338315536181)
                  ·
                    refine ⟨314692438555625467081517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3356719344593338315536181 314692438555625467081517)
                    ·
                      refine ⟨118009664458359550155569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 314692438555625467081517 118009664458359550155569)
                      ·
                        rfl

theorem cell23_229823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_229823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229823 prefixEnd_229823 := by exact prefixLift 229823
  have htrace : WordTrace (prefixWord ++ tailWord_229823) baseStart_229823 baseEnd_229823 := by
    simpa [prefixWord, tailWord_229823, baseEnd_229823] using wordTrace_append hprefix tailTrace_229823
  have hstable : (prefixWord ++ tailWord_229823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229823).length < 2 ^ (prefixWord ++ tailWord_229823).sum := by decide
  have hdescent : baseEnd_229823 < baseStart_229823 := by decide
  rcases family_descends (prefixWord ++ tailWord_229823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229844 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_229844 : Nat := 118140960795 + 229844 * 2 ^ 59
def prefixEnd_229844 : Nat := 4983230072969 + 3 ^ 40 * 229844 * 2
def baseEnd_229844 : Nat := 118020447552103967992973

theorem tailTrace_229844 : CollatzResearch.WordTrace tailWord_229844 prefixEnd_229844 118020447552103967992973 := by
  unfold tailWord_229844
  simp only [CollatzResearch.WordTrace]
  refine ⟨4191549689660958537560293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5588732919547944716747057 4191549689660958537560293)
  ·
    refine ⟨785915566811429725792555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4191549689660958537560293 785915566811429725792555)
    ·
      refine ⟨1178873350217144588688833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 785915566811429725792555 1178873350217144588688833)
      ·
        refine ⟨884155012662858441516625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1178873350217144588688833 884155012662858441516625)
        ·
          refine ⟨663116259497143831137469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 884155012662858441516625 663116259497143831137469)
          ·
            refine ⟨248668597311428936676551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 663116259497143831137469 248668597311428936676551)
            ·
              refine ⟨373002895967143405014827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248668597311428936676551 373002895967143405014827)
              ·
                refine ⟨559504343950715107522241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373002895967143405014827 559504343950715107522241)
                ·
                  refine ⟨419628257963036330641681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559504343950715107522241 419628257963036330641681)
                  ·
                    refine ⟨314721193472277247981261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 419628257963036330641681 314721193472277247981261)
                    ·
                      refine ⟨118020447552103967992973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 314721193472277247981261 118020447552103967992973)
                      ·
                        rfl

theorem cell23_229844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_229844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229844 prefixEnd_229844 := by exact prefixLift 229844
  have htrace : WordTrace (prefixWord ++ tailWord_229844) baseStart_229844 baseEnd_229844 := by
    simpa [prefixWord, tailWord_229844, baseEnd_229844] using wordTrace_append hprefix tailTrace_229844
  have hstable : (prefixWord ++ tailWord_229844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229844).length < 2 ^ (prefixWord ++ tailWord_229844).sum := by decide
  have hdescent : baseEnd_229844 < baseStart_229844 := by decide
  rcases family_descends (prefixWord ++ tailWord_229844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229897 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 5, 2, 2]
def baseStart_229897 : Nat := 118140960795 + 229897 * 2 ^ 59
def prefixEnd_229897 : Nat := 4983230072969 + 3 ^ 40 * 229897 * 2
def baseEnd_229897 : Nat := 118047662026792260630229

theorem tailTrace_229897 : CollatzResearch.WordTrace tailWord_229897 prefixEnd_229897 118047662026792260630229 := by
  unfold tailWord_229897
  simp only [CollatzResearch.WordTrace]
  refine ⟨8385032448129907126799945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5590021632086604751199963 8385032448129907126799945)
  ·
    refine ⟨6288774336097430345099959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8385032448129907126799945 6288774336097430345099959)
    ·
      refine ⟨9433161504146145517649939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6288774336097430345099959 9433161504146145517649939)
      ·
        refine ⟨14149742256219218276474909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9433161504146145517649939 14149742256219218276474909)
        ·
          refine ⟨5306153346082206853678091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14149742256219218276474909 5306153346082206853678091)
          ·
            refine ⟨7959230019123310280517137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306153346082206853678091 7959230019123310280517137)
            ·
              refine ⟨5969422514342482710387853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7959230019123310280517137 5969422514342482710387853)
              ·
                refine ⟨2238533442878431016395445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5969422514342482710387853 2238533442878431016395445)
                ·
                  refine ⟨209862510269852907787073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2238533442878431016395445 209862510269852907787073)
                  ·
                    refine ⟨157396882702389680840305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 209862510269852907787073 157396882702389680840305)
                    ·
                      refine ⟨118047662026792260630229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 157396882702389680840305 118047662026792260630229)
                      ·
                        rfl

theorem cell23_229897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 2, 2].length) (baseStart_229897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229897 prefixEnd_229897 := by exact prefixLift 229897
  have htrace : WordTrace (prefixWord ++ tailWord_229897) baseStart_229897 baseEnd_229897 := by
    simpa [prefixWord, tailWord_229897, baseEnd_229897] using wordTrace_append hprefix tailTrace_229897
  have hstable : (prefixWord ++ tailWord_229897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229897).length < 2 ^ (prefixWord ++ tailWord_229897).sum := by decide
  have hdescent : baseEnd_229897 < baseStart_229897 := by decide
  rcases family_descends (prefixWord ++ tailWord_229897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229901 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_229901 : Nat := 118140960795 + 229901 * 2 ^ 59
def prefixEnd_229901 : Nat := 4983230072969 + 3 ^ 40 * 229901 * 2
def baseEnd_229901 : Nat := 118049715949410244980211

theorem tailTrace_229901 : CollatzResearch.WordTrace tailWord_229901 prefixEnd_229901 118049715949410244980211 := by
  unfold tailWord_229901
  simp only [CollatzResearch.WordTrace]
  refine ⟨8385178340115415809945557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5590118893410277206630371 8385178340115415809945557)
  ·
    refine ⟨196527617346455058045599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 8385178340115415809945557 196527617346455058045599)
    ·
      refine ⟨294791426019682587068399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196527617346455058045599 294791426019682587068399)
      ·
        refine ⟨442187139029523880602599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294791426019682587068399 442187139029523880602599)
        ·
          refine ⟨663280708544285820903899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442187139029523880602599 663280708544285820903899)
          ·
            refine ⟨994921062816428731355849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663280708544285820903899 994921062816428731355849)
            ·
              refine ⟨746190797112321548516887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 994921062816428731355849 746190797112321548516887)
              ·
                refine ⟨1119286195668482322775331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746190797112321548516887 1119286195668482322775331)
                ·
                  refine ⟨1678929293502723484162997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1119286195668482322775331 1678929293502723484162997)
                  ·
                    refine ⟨157399621265880326640281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1678929293502723484162997 157399621265880326640281)
                    ·
                      refine ⟨118049715949410244980211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 157399621265880326640281 118049715949410244980211)
                      ·
                        rfl

theorem cell23_229901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_229901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229901 prefixEnd_229901 := by exact prefixLift 229901
  have htrace : WordTrace (prefixWord ++ tailWord_229901) baseStart_229901 baseEnd_229901 := by
    simpa [prefixWord, tailWord_229901, baseEnd_229901] using wordTrace_append hprefix tailTrace_229901
  have hstable : (prefixWord ++ tailWord_229901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229901).length < 2 ^ (prefixWord ++ tailWord_229901).sum := by decide
  have hdescent : baseEnd_229901 < baseStart_229901 := by decide
  rcases family_descends (prefixWord ++ tailWord_229901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229908 : List Nat := [2, 4, 3, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_229908 : Nat := 118140960795 + 229908 * 2 ^ 59
def prefixEnd_229908 : Nat := 4983230072969 + 3 ^ 40 * 229908 * 2
def baseEnd_229908 : Nat := 118053310313991717592679

theorem tailTrace_229908 : CollatzResearch.WordTrace tailWord_229908 prefixEnd_229908 118053310313991717592679 := by
  unfold tailWord_229908
  simp only [CollatzResearch.WordTrace]
  refine ⟨4192716825545028002725189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5590289100726704003633585 4192716825545028002725189)
  ·
    refine ⟨786134404789692750510973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4192716825545028002725189 786134404789692750510973)
    ·
      refine ⟨294800401796134781441615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 786134404789692750510973 294800401796134781441615)
      ·
        refine ⟨442200602694202172162423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294800401796134781441615 442200602694202172162423)
        ·
          refine ⟨663300904041303258243635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442200602694202172162423 663300904041303258243635)
          ·
            refine ⟨994951356061954887365453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663300904041303258243635 994951356061954887365453)
            ·
              refine ⟨373106758523233082762045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 994951356061954887365453 373106758523233082762045)
              ·
                refine ⟨139915034446212406035767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373106758523233082762045 139915034446212406035767)
                ·
                  refine ⟨209872551669318609053651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139915034446212406035767 209872551669318609053651)
                  ·
                    refine ⟨314808827503977913580477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 209872551669318609053651 314808827503977913580477)
                    ·
                      refine ⟨118053310313991717592679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 314808827503977913580477 118053310313991717592679)
                      ·
                        rfl

theorem cell23_229908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_229908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229908 prefixEnd_229908 := by exact prefixLift 229908
  have htrace : WordTrace (prefixWord ++ tailWord_229908) baseStart_229908 baseEnd_229908 := by
    simpa [prefixWord, tailWord_229908, baseEnd_229908] using wordTrace_append hprefix tailTrace_229908
  have hstable : (prefixWord ++ tailWord_229908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229908).length < 2 ^ (prefixWord ++ tailWord_229908).sum := by decide
  have hdescent : baseEnd_229908 < baseStart_229908 := by decide
  rcases family_descends (prefixWord ++ tailWord_229908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229917 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_229917 : Nat := 118140960795 + 229917 * 2 ^ 59
def prefixEnd_229917 : Nat := 4983230072969 + 3 ^ 40 * 229917 * 2
def baseEnd_229917 : Nat := 118057931639882182380137

theorem tailTrace_229917 : CollatzResearch.WordTrace tailWord_229917 prefixEnd_229917 118057931639882182380137 := by
  unfold tailWord_229917
  simp only [CollatzResearch.WordTrace]
  refine ⟨8385761908057450542528005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5590507938704967028352003 8385761908057450542528005)
  ·
    refine ⟨1572330357760771976724001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8385761908057450542528005 1572330357760771976724001)
    ·
      refine ⟨1179247768320578982543001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1572330357760771976724001 1179247768320578982543001)
      ·
        refine ⟨884435826240434236907251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1179247768320578982543001 884435826240434236907251)
        ·
          refine ⟨1326653739360651355360877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884435826240434236907251 1326653739360651355360877)
          ·
            refine ⟨497495152260244258260329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1326653739360651355360877 497495152260244258260329)
            ·
              refine ⟨373121364195183193695247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497495152260244258260329 373121364195183193695247)
              ·
                refine ⟨559682046292774790542871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373121364195183193695247 559682046292774790542871)
                ·
                  refine ⟨839523069439162185814307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 559682046292774790542871 839523069439162185814307)
                  ·
                    refine ⟨1259284604158743278721461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 839523069439162185814307 1259284604158743278721461)
                    ·
                      refine ⟨118057931639882182380137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1259284604158743278721461 118057931639882182380137)
                      ·
                        rfl

theorem cell23_229917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_229917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229917 prefixEnd_229917 := by exact prefixLift 229917
  have htrace : WordTrace (prefixWord ++ tailWord_229917) baseStart_229917 baseEnd_229917 := by
    simpa [prefixWord, tailWord_229917, baseEnd_229917] using wordTrace_append hprefix tailTrace_229917
  have hstable : (prefixWord ++ tailWord_229917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229917).length < 2 ^ (prefixWord ++ tailWord_229917).sum := by decide
  have hdescent : baseEnd_229917 < baseStart_229917 := by decide
  rcases family_descends (prefixWord ++ tailWord_229917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229987 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 3, 4, 2]
def baseStart_229987 : Nat := 118140960795 + 229987 * 2 ^ 59
def prefixEnd_229987 : Nat := 4983230072969 + 3 ^ 40 * 229987 * 2
def baseEnd_229987 : Nat := 118093875285696908504815

theorem tailTrace_229987 : CollatzResearch.WordTrace tailWord_229987 prefixEnd_229987 118093875285696908504815 := by
  unfold tailWord_229987
  simp only [CollatzResearch.WordTrace]
  refine ⟨8388315017803852497576215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5592210011869234998384143 8388315017803852497576215)
  ·
    refine ⟨12582472526705778746364323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8388315017803852497576215 12582472526705778746364323)
    ·
      refine ⟨18873708790058668119546485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12582472526705778746364323 18873708790058668119546485)
      ·
        refine ⟨1769410199068000136207483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18873708790058668119546485 1769410199068000136207483)
        ·
          refine ⟨2654115298602000204311225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1769410199068000136207483 2654115298602000204311225)
          ·
            refine ⟨1990586473951500153233419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2654115298602000204311225 1990586473951500153233419)
            ·
              refine ⟨2985879710927250229850129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990586473951500153233419 2985879710927250229850129)
              ·
                refine ⟨2239409783195437672387597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2985879710927250229850129 2239409783195437672387597)
                ·
                  refine ⟨839778668698289127145349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2239409783195437672387597 839778668698289127145349)
                  ·
                    refine ⟨157458500380929211339753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 839778668698289127145349 157458500380929211339753)
                    ·
                      refine ⟨118093875285696908504815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 157458500380929211339753 118093875285696908504815)
                      ·
                        rfl

theorem cell23_229987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_229987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229987 prefixEnd_229987 := by exact prefixLift 229987
  have htrace : WordTrace (prefixWord ++ tailWord_229987) baseStart_229987 baseEnd_229987 := by
    simpa [prefixWord, tailWord_229987, baseEnd_229987] using wordTrace_append hprefix tailTrace_229987
  have hstable : (prefixWord ++ tailWord_229987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229987).length < 2 ^ (prefixWord ++ tailWord_229987).sum := by decide
  have hdescent : baseEnd_229987 < baseStart_229987 := by decide
  rcases family_descends (prefixWord ++ tailWord_229987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229997 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_229997 : Nat := 118140960795 + 229997 * 2 ^ 59
def prefixEnd_229997 : Nat := 4983230072969 + 3 ^ 40 * 229997 * 2
def baseEnd_229997 : Nat := 39366336697413956459923

theorem tailTrace_229997 : CollatzResearch.WordTrace tailWord_229997 prefixEnd_229997 39366336697413956459923 := by
  unfold tailWord_229997
  simp only [CollatzResearch.WordTrace]
  refine ⟨8388679747767624205440245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5592453165178416136960163 8388679747767624205440245)
  ·
    refine ⟨786438726353214769260023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8388679747767624205440245 786438726353214769260023)
    ·
      refine ⟨1179658089529822153890035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 786438726353214769260023 1179658089529822153890035)
      ·
        refine ⟨1769487134294733230835053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1179658089529822153890035 1769487134294733230835053)
        ·
          refine ⟨663557675360524961563145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1769487134294733230835053 663557675360524961563145)
          ·
            refine ⟨497668256520393721172359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 663557675360524961563145 497668256520393721172359)
            ·
              refine ⟨746502384780590581758539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497668256520393721172359 746502384780590581758539)
              ·
                refine ⟨1119753577170885872637809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746502384780590581758539 1119753577170885872637809)
                ·
                  refine ⟨839815182878164404478357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1119753577170885872637809 839815182878164404478357)
                  ·
                    refine ⟨39366336697413956459923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 839815182878164404478357 39366336697413956459923)
                    ·
                      rfl

theorem cell23_229997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_229997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_229997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_229997 prefixEnd_229997 := by exact prefixLift 229997
  have htrace : WordTrace (prefixWord ++ tailWord_229997) baseStart_229997 baseEnd_229997 := by
    simpa [prefixWord, tailWord_229997, baseEnd_229997] using wordTrace_append hprefix tailTrace_229997
  have hstable : (prefixWord ++ tailWord_229997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229997).length < 2 ^ (prefixWord ++ tailWord_229997).sum := by decide
  have hdescent : baseEnd_229997 < baseStart_229997 := by decide
  rcases family_descends (prefixWord ++ tailWord_229997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230044 : List Nat := [2, 2, 3, 2, 2, 1, 2, 4, 5]
def baseStart_230044 : Nat := 118140960795 + 230044 * 2 ^ 59
def prefixEnd_230044 : Nat := 4983230072969 + 3 ^ 40 * 230044 * 2
def baseEnd_230044 : Nat := 13124793742555909499117

theorem tailTrace_230044 : CollatzResearch.WordTrace tailWord_230044 prefixEnd_230044 13124793742555909499117 := by
  unfold tailWord_230044
  simp only [CollatzResearch.WordTrace]
  refine ⟨4195196989298675616200593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5593595985731567488267457 4195196989298675616200593)
  ·
    refine ⟨3146397741974006712150445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4195196989298675616200593 3146397741974006712150445)
    ·
      refine ⟨1179899153240252517056417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3146397741974006712150445 1179899153240252517056417)
      ·
        refine ⟨884924364930189387792313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1179899153240252517056417 884924364930189387792313)
        ·
          refine ⟨663693273697642040844235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 884924364930189387792313 663693273697642040844235)
          ·
            refine ⟨995539910546463061266353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663693273697642040844235 995539910546463061266353)
            ·
              refine ⟨746654932909847295949765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995539910546463061266353 746654932909847295949765)
              ·
                refine ⟨139997799920596367990581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 746654932909847295949765 139997799920596367990581)
                ·
                  refine ⟨13124793742555909499117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139997799920596367990581 13124793742555909499117)
                  ·
                    rfl

theorem cell23_230044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 5].length) (baseStart_230044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230044 prefixEnd_230044 := by exact prefixLift 230044
  have htrace : WordTrace (prefixWord ++ tailWord_230044) baseStart_230044 baseEnd_230044 := by
    simpa [prefixWord, tailWord_230044, baseEnd_230044] using wordTrace_append hprefix tailTrace_230044
  have hstable : (prefixWord ++ tailWord_230044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230044).length < 2 ^ (prefixWord ++ tailWord_230044).sum := by decide
  have hdescent : baseEnd_230044 < baseStart_230044 := by decide
  rcases family_descends (prefixWord ++ tailWord_230044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230055 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_230055 : Nat := 118140960795 + 230055 * 2 ^ 59
def prefixEnd_230055 : Nat := 4983230072969 + 3 ^ 40 * 230055 * 2
def baseEnd_230055 : Nat := 118128791970202642454503

theorem tailTrace_230055 : CollatzResearch.WordTrace tailWord_230055 prefixEnd_230055 118128791970202642454503 := by
  unfold tailWord_230055
  simp only [CollatzResearch.WordTrace]
  refine ⟨8390795181557500111051619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5593863454371666740701079 8390795181557500111051619)
  ·
    refine ⟨12586192772336250166577429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8390795181557500111051619 12586192772336250166577429)
    ·
      refine ⟨589977786203261726558317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12586192772336250166577429 589977786203261726558317)
      ·
        refine ⟨221241669826223147459369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 589977786203261726558317 221241669826223147459369)
        ·
          refine ⟨165931252369667360594527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221241669826223147459369 165931252369667360594527)
          ·
            refine ⟨248896878554501040891791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165931252369667360594527 248896878554501040891791)
            ·
              refine ⟨373345317831751561337687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248896878554501040891791 373345317831751561337687)
              ·
                refine ⟨560017976747627342006531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373345317831751561337687 560017976747627342006531)
                ·
                  refine ⟨840026965121441013009797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560017976747627342006531 840026965121441013009797)
                  ·
                    refine ⟨157505055960270189939337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 840026965121441013009797 157505055960270189939337)
                    ·
                      refine ⟨118128791970202642454503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 157505055960270189939337 118128791970202642454503)
                      ·
                        rfl

theorem cell23_230055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_230055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230055 prefixEnd_230055 := by exact prefixLift 230055
  have htrace : WordTrace (prefixWord ++ tailWord_230055) baseStart_230055 baseEnd_230055 := by
    simpa [prefixWord, tailWord_230055, baseEnd_230055] using wordTrace_append hprefix tailTrace_230055
  have hstable : (prefixWord ++ tailWord_230055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230055).length < 2 ^ (prefixWord ++ tailWord_230055).sum := by decide
  have hdescent : baseEnd_230055 < baseStart_230055 := by decide
  rcases family_descends (prefixWord ++ tailWord_230055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230077 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_230077 : Nat := 118140960795 + 230077 * 2 ^ 59
def prefixEnd_230077 : Nat := 4983230072969 + 3 ^ 40 * 230077 * 2
def baseEnd_230077 : Nat := 118140088544601556379401

theorem tailTrace_230077 : CollatzResearch.WordTrace tailWord_230077 prefixEnd_230077 118140088544601556379401 := by
  unfold tailWord_230077
  simp only [CollatzResearch.WordTrace]
  refine ⟨8391597587477797868352485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5594398391651865245568323 8391597587477797868352485)
  ·
    refine ⟨1573424547652087100316091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8391597587477797868352485 1573424547652087100316091)
    ·
      refine ⟨2360136821478130650474137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1573424547652087100316091 2360136821478130650474137)
      ·
        refine ⟨1770102616108597987855603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2360136821478130650474137 1770102616108597987855603)
        ·
          refine ⟨2655153924162896981783405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770102616108597987855603 2655153924162896981783405)
          ·
            refine ⟨995682721561086368168777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2655153924162896981783405 995682721561086368168777)
            ·
              refine ⟨746762041170814776126583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995682721561086368168777 746762041170814776126583)
              ·
                refine ⟨1120143061756222164189875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746762041170814776126583 1120143061756222164189875)
                ·
                  refine ⟨1680214592634333246284813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120143061756222164189875 1680214592634333246284813)
                  ·
                    refine ⟨630080472237874967356805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1680214592634333246284813 630080472237874967356805)
                    ·
                      refine ⟨118140088544601556379401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 630080472237874967356805 118140088544601556379401)
                      ·
                        rfl

theorem cell23_230077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_230077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230077 prefixEnd_230077 := by exact prefixLift 230077
  have htrace : WordTrace (prefixWord ++ tailWord_230077) baseStart_230077 baseEnd_230077 := by
    simpa [prefixWord, tailWord_230077, baseEnd_230077] using wordTrace_append hprefix tailTrace_230077
  have hstable : (prefixWord ++ tailWord_230077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230077).length < 2 ^ (prefixWord ++ tailWord_230077).sum := by decide
  have hdescent : baseEnd_230077 < baseStart_230077 := by decide
  rcases family_descends (prefixWord ++ tailWord_230077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230094 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_230094 : Nat := 118140960795 + 230094 * 2 ^ 59
def prefixEnd_230094 : Nat := 4983230072969 + 3 ^ 40 * 230094 * 2
def baseEnd_230094 : Nat := 118148817715727989866823

theorem tailTrace_230094 : CollatzResearch.WordTrace tailWord_230094 prefixEnd_230094 118148817715727989866823 := by
  unfold tailWord_230094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1049027203552026221465167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5594811752277473181147557 1049027203552026221465167)
  ·
    refine ⟨1573540805328039332197751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1049027203552026221465167 1573540805328039332197751)
    ·
      refine ⟨2360311207992058998296627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1573540805328039332197751 2360311207992058998296627)
      ·
        refine ⟨3540466811988088497444941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360311207992058998296627 3540466811988088497444941)
        ·
          refine ⟨1327675054495533186541853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3540466811988088497444941 1327675054495533186541853)
          ·
            refine ⟨497878145435824944953195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1327675054495533186541853 497878145435824944953195)
            ·
              refine ⟨746817218153737417429793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497878145435824944953195 746817218153737417429793)
              ·
                refine ⟨560112913615303063072345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746817218153737417429793 560112913615303063072345)
                ·
                  refine ⟨420084685211477297304259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560112913615303063072345 420084685211477297304259)
                  ·
                    refine ⟨630127027817215945956389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 420084685211477297304259 630127027817215945956389)
                    ·
                      refine ⟨118148817715727989866823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 630127027817215945956389 118148817715727989866823)
                      ·
                        rfl

theorem cell23_230094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_230094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230094 prefixEnd_230094 := by exact prefixLift 230094
  have htrace : WordTrace (prefixWord ++ tailWord_230094) baseStart_230094 baseEnd_230094 := by
    simpa [prefixWord, tailWord_230094, baseEnd_230094] using wordTrace_append hprefix tailTrace_230094
  have hstable : (prefixWord ++ tailWord_230094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230094).length < 2 ^ (prefixWord ++ tailWord_230094).sum := by decide
  have hdescent : baseEnd_230094 < baseStart_230094 := by decide
  rcases family_descends (prefixWord ++ tailWord_230094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230104 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 3, 4]
def baseStart_230104 : Nat := 118140960795 + 230104 * 2 ^ 59
def prefixEnd_230104 : Nat := 4983230072969 + 3 ^ 40 * 230104 * 2
def baseEnd_230104 : Nat := 39384650840757650247259

theorem tailTrace_230104 : CollatzResearch.WordTrace tailWord_230104 prefixEnd_230104 39384650840757650247259 := by
  unfold tailWord_230104
  simp only [CollatzResearch.WordTrace]
  refine ⟨4196291179189990739792683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5595054905586654319723577 4196291179189990739792683)
  ·
    refine ⟨6294436768784986109689025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4196291179189990739792683 6294436768784986109689025)
    ·
      refine ⟨4720827576588739582266769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6294436768784986109689025 4720827576588739582266769)
      ·
        refine ⟨3540620682441554686700077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4720827576588739582266769 3540620682441554686700077)
        ·
          refine ⟨1327732755915583007512529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3540620682441554686700077 1327732755915583007512529)
          ·
            refine ⟨995799566936687255634397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1327732755915583007512529 995799566936687255634397)
            ·
              refine ⟨373424837601257720862899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 995799566936687255634397 373424837601257720862899)
              ·
                refine ⟨560137256401886581294349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373424837601257720862899 560137256401886581294349)
                ·
                  refine ⟨210051471150707467985381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560137256401886581294349 210051471150707467985381)
                  ·
                    refine ⟨39384650840757650247259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 210051471150707467985381 39384650840757650247259)
                    ·
                      rfl

theorem cell23_230104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_230104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230104 prefixEnd_230104 := by exact prefixLift 230104
  have htrace : WordTrace (prefixWord ++ tailWord_230104) baseStart_230104 baseEnd_230104 := by
    simpa [prefixWord, tailWord_230104, baseEnd_230104] using wordTrace_append hprefix tailTrace_230104
  have hstable : (prefixWord ++ tailWord_230104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230104).length < 2 ^ (prefixWord ++ tailWord_230104).sum := by decide
  have hdescent : baseEnd_230104 < baseStart_230104 := by decide
  rcases family_descends (prefixWord ++ tailWord_230104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230184 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_230184 : Nat := 118140960795 + 230184 * 2 ^ 59
def prefixEnd_230184 : Nat := 4983230072969 + 3 ^ 40 * 230184 * 2
def baseEnd_230184 : Nat := 118195030974632637741409

theorem tailTrace_230184 : CollatzResearch.WordTrace tailWord_230184 prefixEnd_230184 118195030974632637741409 := by
  unfold tailWord_230184
  simp only [CollatzResearch.WordTrace]
  refine ⟨4197750099045077571248803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5597000132060103428331737 4197750099045077571248803)
  ·
    refine ⟨6296625148567616356873205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4197750099045077571248803 6296625148567616356873205)
    ·
      refine ⟨590308607678214033456863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6296625148567616356873205 590308607678214033456863)
      ·
        refine ⟨885462911517321050185295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590308607678214033456863 885462911517321050185295)
        ·
          refine ⟨1328194367275981575277943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885462911517321050185295 1328194367275981575277943)
          ·
            refine ⟨1992291550913972362916915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328194367275981575277943 1992291550913972362916915)
            ·
              refine ⟨2988437326370958544375373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1992291550913972362916915 2988437326370958544375373)
              ·
                refine ⟨1120663997389109454140765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2988437326370958544375373 1120663997389109454140765)
                ·
                  refine ⟨420248999020916045302787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120663997389109454140765 420248999020916045302787)
                  ·
                    refine ⟨630373498531374067954181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 420248999020916045302787 630373498531374067954181)
                    ·
                      refine ⟨118195030974632637741409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 630373498531374067954181 118195030974632637741409)
                      ·
                        rfl

theorem cell23_230184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_230184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230184 prefixEnd_230184 := by exact prefixLift 230184
  have htrace : WordTrace (prefixWord ++ tailWord_230184) baseStart_230184 baseEnd_230184 := by
    simpa [prefixWord, tailWord_230184, baseEnd_230184] using wordTrace_append hprefix tailTrace_230184
  have hstable : (prefixWord ++ tailWord_230184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230184).length < 2 ^ (prefixWord ++ tailWord_230184).sum := by decide
  have hdescent : baseEnd_230184 < baseStart_230184 := by decide
  rcases family_descends (prefixWord ++ tailWord_230184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230194 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 4, 4]
def baseStart_230194 : Nat := 118140960795 + 230194 * 2 ^ 59
def prefixEnd_230194 : Nat := 4983230072969 + 3 ^ 40 * 230194 * 2
def baseEnd_230194 : Nat := 39400055260392532872121

theorem tailTrace_230194 : CollatzResearch.WordTrace tailWord_230194 prefixEnd_230194 39400055260392532872121 := by
  unfold tailWord_230194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2098966232013481712590409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5597243285369284566907757 2098966232013481712590409)
  ·
    refine ⟨1574224674010111284442807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2098966232013481712590409 1574224674010111284442807)
    ·
      refine ⟨2361337011015166926664211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1574224674010111284442807 2361337011015166926664211)
      ·
        refine ⟨3542005516522750389996317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2361337011015166926664211 3542005516522750389996317)
        ·
          refine ⟨1328252068696031396248619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3542005516522750389996317 1328252068696031396248619)
          ·
            refine ⟨1992378103044047094372929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328252068696031396248619 1992378103044047094372929)
            ·
              refine ⟨1494283577283035320779697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1992378103044047094372929 1494283577283035320779697)
              ·
                refine ⟨1120712682962276490584773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1494283577283035320779697 1120712682962276490584773)
                ·
                  refine ⟨210133628055426841984645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1120712682962276490584773 210133628055426841984645)
                  ·
                    refine ⟨39400055260392532872121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 210133628055426841984645 39400055260392532872121)
                    ·
                      rfl

theorem cell23_230194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_230194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230194 prefixEnd_230194 := by exact prefixLift 230194
  have htrace : WordTrace (prefixWord ++ tailWord_230194) baseStart_230194 baseEnd_230194 := by
    simpa [prefixWord, tailWord_230194, baseEnd_230194] using wordTrace_append hprefix tailTrace_230194
  have hstable : (prefixWord ++ tailWord_230194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230194).length < 2 ^ (prefixWord ++ tailWord_230194).sum := by decide
  have hdescent : baseEnd_230194 < baseStart_230194 := by decide
  rcases family_descends (prefixWord ++ tailWord_230194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230198 : List Nat := [5, 1, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_230198 : Nat := 118140960795 + 230198 * 2 ^ 59
def prefixEnd_230198 : Nat := 4983230072969 + 3 ^ 40 * 230198 * 2
def baseEnd_230198 : Nat := 39400739901265194322115

theorem tailTrace_230198 : CollatzResearch.WordTrace tailWord_230198 prefixEnd_230198 39400739901265194322115 := by
  unfold tailWord_230198
  simp only [CollatzResearch.WordTrace]
  refine ⟨524750676252464720844203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5597340546692957022338165 524750676252464720844203)
  ·
    refine ⟨787126014378697081266305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 524750676252464720844203 787126014378697081266305)
    ·
      refine ⟨590344510784022810949729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 787126014378697081266305 590344510784022810949729)
      ·
        refine ⟨442758383088017108212297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590344510784022810949729 442758383088017108212297)
        ·
          refine ⟨332068787316012831159223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442758383088017108212297 332068787316012831159223)
          ·
            refine ⟨498103180974019246738835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332068787316012831159223 498103180974019246738835)
            ·
              refine ⟨747154771461028870108253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498103180974019246738835 747154771461028870108253)
              ·
                refine ⟨280183039297885826290595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 747154771461028870108253 280183039297885826290595)
                ·
                  refine ⟨420274558946828739435893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280183039297885826290595 420274558946828739435893)
                  ·
                    refine ⟨39400739901265194322115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 420274558946828739435893 39400739901265194322115)
                    ·
                      rfl

theorem cell23_230198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_230198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230198 prefixEnd_230198 := by exact prefixLift 230198
  have htrace : WordTrace (prefixWord ++ tailWord_230198) baseStart_230198 baseEnd_230198 := by
    simpa [prefixWord, tailWord_230198, baseEnd_230198] using wordTrace_append hprefix tailTrace_230198
  have hstable : (prefixWord ++ tailWord_230198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230198).length < 2 ^ (prefixWord ++ tailWord_230198).sum := by decide
  have hdescent : baseEnd_230198 < baseStart_230198 := by decide
  rcases family_descends (prefixWord ++ tailWord_230198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230207 : List Nat := [1, 1, 2, 2, 5, 2, 10]
def baseStart_230207 : Nat := 118140960795 + 230207 * 2 ^ 59
def prefixEnd_230207 : Nat := 4983230072969 + 3 ^ 40 * 230207 * 2
def baseEnd_230207 : Nat := 1459343716415877132763

theorem tailTrace_230207 : CollatzResearch.WordTrace tailWord_230207 prefixEnd_230207 1459343716415877132763 := by
  unfold tailWord_230207
  simp only [CollatzResearch.WordTrace]
  refine ⟨8396339077006830070584875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5597559384671220047056583 8396339077006830070584875)
  ·
    refine ⟨12594508615510245105877313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8396339077006830070584875 12594508615510245105877313)
    ·
      refine ⟨9445881461632683829407985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12594508615510245105877313 9445881461632683829407985)
      ·
        refine ⟨7084411096224512872055989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9445881461632683829407985 7084411096224512872055989)
        ·
          refine ⟨664163540271048081755249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7084411096224512872055989 664163540271048081755249)
          ·
            refine ⟨498122655203286061316437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664163540271048081755249 498122655203286061316437)
            ·
              refine ⟨1459343716415877132763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 498122655203286061316437 1459343716415877132763)
              ·
                rfl

theorem cell23_230207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 10].length) (baseStart_230207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230207 prefixEnd_230207 := by exact prefixLift 230207
  have htrace : WordTrace (prefixWord ++ tailWord_230207) baseStart_230207 baseEnd_230207 := by
    simpa [prefixWord, tailWord_230207, baseEnd_230207] using wordTrace_append hprefix tailTrace_230207
  have hstable : (prefixWord ++ tailWord_230207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230207).length < 2 ^ (prefixWord ++ tailWord_230207).sum := by decide
  have hdescent : baseEnd_230207 < baseStart_230207 := by decide
  rcases family_descends (prefixWord ++ tailWord_230207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230228 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_230228 : Nat := 118140960795 + 230228 * 2 ^ 59
def prefixEnd_230228 : Nat := 4983230072969 + 3 ^ 40 * 230228 * 2
def baseEnd_230228 : Nat := 39405874707810155197069

theorem tailTrace_230228 : CollatzResearch.WordTrace tailWord_230228 prefixEnd_230228 39405874707810155197069 := by
  unfold tailWord_230228
  simp only [CollatzResearch.WordTrace]
  refine ⟨4198552504965375328549669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5598070006620500438066225 4198552504965375328549669)
  ·
    refine ⟨787228594681007874103063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4198552504965375328549669 787228594681007874103063)
    ·
      refine ⟨1180842892021511811154595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 787228594681007874103063 1180842892021511811154595)
      ·
        refine ⟨1771264338032267716731893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180842892021511811154595 1771264338032267716731893)
        ·
          refine ⟨166056031690525098443615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1771264338032267716731893 166056031690525098443615)
          ·
            refine ⟨249084047535787647665423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166056031690525098443615 249084047535787647665423)
            ·
              refine ⟨373626071303681471498135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249084047535787647665423 373626071303681471498135)
              ·
                refine ⟨560439106955522207247203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373626071303681471498135 560439106955522207247203)
                ·
                  refine ⟨840658660433283310870805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560439106955522207247203 840658660433283310870805)
                  ·
                    refine ⟨39405874707810155197069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 840658660433283310870805 39405874707810155197069)
                    ·
                      rfl

theorem cell23_230228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_230228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230228 prefixEnd_230228 := by exact prefixLift 230228
  have htrace : WordTrace (prefixWord ++ tailWord_230228) baseStart_230228 baseEnd_230228 := by
    simpa [prefixWord, tailWord_230228, baseEnd_230228] using wordTrace_append hprefix tailTrace_230228
  have hstable : (prefixWord ++ tailWord_230228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230228).length < 2 ^ (prefixWord ++ tailWord_230228).sum := by decide
  have hdescent : baseEnd_230228 < baseStart_230228 := by decide
  rcases family_descends (prefixWord ++ tailWord_230228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230231 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 1, 2, 4]
def baseStart_230231 : Nat := 118140960795 + 230231 * 2 ^ 59
def prefixEnd_230231 : Nat := 4983230072969 + 3 ^ 40 * 230231 * 2
def baseEnd_230231 : Nat := 118219164565393953853693

theorem tailTrace_230231 : CollatzResearch.WordTrace tailWord_230231 prefixEnd_230231 118219164565393953853693 := by
  unfold tailWord_230231
  simp only [CollatzResearch.WordTrace]
  refine ⟨8397214428919882169458547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5598142952613254779639031 8397214428919882169458547)
  ·
    refine ⟨12595821643379823254187821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8397214428919882169458547 12595821643379823254187821)
    ·
      refine ⟨4723433116267433720320433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12595821643379823254187821 4723433116267433720320433)
      ·
        refine ⟨3542574837200575290240325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4723433116267433720320433 3542574837200575290240325)
        ·
          refine ⟨664232781975107866920061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3542574837200575290240325 664232781975107866920061)
          ·
            refine ⟨249087293240665450095023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 664232781975107866920061 249087293240665450095023)
            ·
              refine ⟨373630939860998175142535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249087293240665450095023 373630939860998175142535)
              ·
                refine ⟨560446409791497262713803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373630939860998175142535 560446409791497262713803)
                ·
                  refine ⟨840669614687245894070705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560446409791497262713803 840669614687245894070705)
                  ·
                    refine ⟨630502211015434420553029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 840669614687245894070705 630502211015434420553029)
                    ·
                      refine ⟨118219164565393953853693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 630502211015434420553029 118219164565393953853693)
                      ·
                        rfl

theorem cell23_230231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_230231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230231 prefixEnd_230231 := by exact prefixLift 230231
  have htrace : WordTrace (prefixWord ++ tailWord_230231) baseStart_230231 baseEnd_230231 := by
    simpa [prefixWord, tailWord_230231, baseEnd_230231] using wordTrace_append hprefix tailTrace_230231
  have hstable : (prefixWord ++ tailWord_230231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230231).length < 2 ^ (prefixWord ++ tailWord_230231).sum := by decide
  have hdescent : baseEnd_230231 < baseStart_230231 := by decide
  rcases family_descends (prefixWord ++ tailWord_230231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230267 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 4, 6]
def baseStart_230267 : Nat := 118140960795 + 230267 * 2 ^ 59
def prefixEnd_230267 : Nat := 4983230072969 + 3 ^ 40 * 230267 * 2
def baseEnd_230267 : Nat := 39412549956318604334509

theorem tailTrace_230267 : CollatzResearch.WordTrace tailWord_230267 prefixEnd_230267 39412549956318604334509 := by
  unfold tailWord_230267
  simp only [CollatzResearch.WordTrace]
  refine ⟨8398527456789460317769055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5599018304526306878512703 8398527456789460317769055)
  ·
    refine ⟨12597791185184190476653583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8398527456789460317769055 12597791185184190476653583)
    ·
      refine ⟨18896686777776285714980375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12597791185184190476653583 18896686777776285714980375)
      ·
        refine ⟨28345030166664428572470563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18896686777776285714980375 28345030166664428572470563)
        ·
          refine ⟨42517545249996642858705845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28345030166664428572470563 42517545249996642858705845)
          ·
            refine ⟨3986019867187185268003673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42517545249996642858705845 3986019867187185268003673)
            ·
              refine ⟨2989514900390388951002755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3986019867187185268003673 2989514900390388951002755)
              ·
                refine ⟨4484272350585583426504133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2989514900390388951002755 4484272350585583426504133)
                ·
                  refine ⟨840801065734796892469525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4484272350585583426504133 840801065734796892469525)
                  ·
                    refine ⟨39412549956318604334509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 840801065734796892469525 39412549956318604334509)
                    ·
                      rfl

theorem cell23_230267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 6].length) (baseStart_230267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230267 prefixEnd_230267 := by exact prefixLift 230267
  have htrace : WordTrace (prefixWord ++ tailWord_230267) baseStart_230267 baseEnd_230267 := by
    simpa [prefixWord, tailWord_230267, baseEnd_230267] using wordTrace_append hprefix tailTrace_230267
  have hstable : (prefixWord ++ tailWord_230267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230267).length < 2 ^ (prefixWord ++ tailWord_230267).sum := by decide
  have hdescent : baseEnd_230267 < baseStart_230267 := by decide
  rcases family_descends (prefixWord ++ tailWord_230267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230291 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 6, 2, 2]
def baseStart_230291 : Nat := 118140960795 + 230291 * 2 ^ 59
def prefixEnd_230291 : Nat := 4983230072969 + 3 ^ 40 * 230291 * 2
def baseEnd_230291 : Nat := 118249973404663719103417

theorem tailTrace_230291 : CollatzResearch.WordTrace tailWord_230291 prefixEnd_230291 118249973404663719103417 := by
  unfold tailWord_230291
  simp only [CollatzResearch.WordTrace]
  refine ⟨8399402808702512416642727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5599601872468341611095151 8399402808702512416642727)
  ·
    refine ⟨12599104213053768624964091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8399402808702512416642727 12599104213053768624964091)
    ·
      refine ⟨18898656319580652937446137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12599104213053768624964091 18898656319580652937446137)
      ·
        refine ⟨14173992239685489703084603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18898656319580652937446137 14173992239685489703084603)
        ·
          refine ⟨21260988359528234554626905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14173992239685489703084603 21260988359528234554626905)
          ·
            refine ⟨15945741269646175915970179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21260988359528234554626905 15945741269646175915970179)
            ·
              refine ⟨23918611904469263873955269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15945741269646175915970179 23918611904469263873955269)
              ·
                refine ⟨4484739732087986976366613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23918611904469263873955269 4484739732087986976366613)
                ·
                  refine ⟨210222174941624389517185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4484739732087986976366613 210222174941624389517185)
                  ·
                    refine ⟨157666631206218292137889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 210222174941624389517185 157666631206218292137889)
                    ·
                      refine ⟨118249973404663719103417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 157666631206218292137889 118249973404663719103417)
                      ·
                        rfl

theorem cell23_230291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 2, 2].length) (baseStart_230291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230291 prefixEnd_230291 := by exact prefixLift 230291
  have htrace : WordTrace (prefixWord ++ tailWord_230291) baseStart_230291 baseEnd_230291 := by
    simpa [prefixWord, tailWord_230291, baseEnd_230291] using wordTrace_append hprefix tailTrace_230291
  have hstable : (prefixWord ++ tailWord_230291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230291).length < 2 ^ (prefixWord ++ tailWord_230291).sum := by decide
  have hdescent : baseEnd_230291 < baseStart_230291 := by decide
  rcases family_descends (prefixWord ++ tailWord_230291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230297 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 9]
def baseStart_230297 : Nat := 118140960795 + 230297 * 2 ^ 59
def prefixEnd_230297 : Nat := 4983230072969 + 3 ^ 40 * 230297 * 2
def baseEnd_230297 : Nat := 13139228254287855069821

theorem tailTrace_230297 : CollatzResearch.WordTrace tailWord_230297 prefixEnd_230297 13139228254287855069821 := by
  unfold tailWord_230297
  simp only [CollatzResearch.WordTrace]
  refine ⟨8399621646680775441361145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5599747764453850294240763 8399621646680775441361145)
  ·
    refine ⟨6299716235010581581020859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8399621646680775441361145 6299716235010581581020859)
    ·
      refine ⟨9449574352515872371531289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6299716235010581581020859 9449574352515872371531289)
      ·
        refine ⟨7087180764386904278648467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9449574352515872371531289 7087180764386904278648467)
        ·
          refine ⟨10630771146580356417972701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7087180764386904278648467 10630771146580356417972701)
          ·
            refine ⟨3986539179967633656739763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10630771146580356417972701 3986539179967633656739763)
            ·
              refine ⟨5979808769951450485109645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3986539179967633656739763 5979808769951450485109645)
              ·
                refine ⟨2242428288731793931916117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5979808769951450485109645 2242428288731793931916117)
                ·
                  refine ⟨13139228254287855069821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2242428288731793931916117 13139228254287855069821)
                  ·
                    rfl

theorem cell23_230297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 9].length) (baseStart_230297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230297 prefixEnd_230297 := by exact prefixLift 230297
  have htrace : WordTrace (prefixWord ++ tailWord_230297) baseStart_230297 baseEnd_230297 := by
    simpa [prefixWord, tailWord_230297, baseEnd_230297] using wordTrace_append hprefix tailTrace_230297
  have hstable : (prefixWord ++ tailWord_230297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230297).length < 2 ^ (prefixWord ++ tailWord_230297).sum := by decide
  have hdescent : baseEnd_230297 < baseStart_230297 := by decide
  rcases family_descends (prefixWord ++ tailWord_230297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230325 : List Nat := [1, 3, 3, 2, 1, 1, 4, 2, 2, 2, 2]
def baseStart_230325 : Nat := 118140960795 + 230325 * 2 ^ 59
def prefixEnd_230325 : Nat := 4983230072969 + 3 ^ 40 * 230325 * 2
def baseEnd_230325 : Nat := 118267431746916586078261

theorem tailTrace_230325 : CollatzResearch.WordTrace tailWord_230325 prefixEnd_230325 118267431746916586078261 := by
  unfold tailWord_230325
  simp only [CollatzResearch.WordTrace]
  refine ⟨8400642890579336223380429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5600428593719557482253619 8400642890579336223380429)
  ·
    refine ⟨3150241083967251083767661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8400642890579336223380429 3150241083967251083767661)
    ·
      refine ⟨1181340406487719156412873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3150241083967251083767661 1181340406487719156412873)
      ·
        refine ⟨886005304865789367309655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1181340406487719156412873 886005304865789367309655)
        ·
          refine ⟨1329007957298684050964483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886005304865789367309655 1329007957298684050964483)
          ·
            refine ⟨1993511935948026076446725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329007957298684050964483 1993511935948026076446725)
            ·
              refine ⟨373783487990254889333761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1993511935948026076446725 373783487990254889333761)
              ·
                refine ⟨280337615992691167000321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373783487990254889333761 280337615992691167000321)
                ·
                  refine ⟨210253211994518375250241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280337615992691167000321 210253211994518375250241)
                  ·
                    refine ⟨157689908995888781437681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 210253211994518375250241 157689908995888781437681)
                    ·
                      refine ⟨118267431746916586078261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 157689908995888781437681 118267431746916586078261)
                      ·
                        rfl

theorem cell23_230325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_230325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230325 prefixEnd_230325 := by exact prefixLift 230325
  have htrace : WordTrace (prefixWord ++ tailWord_230325) baseStart_230325 baseEnd_230325 := by
    simpa [prefixWord, tailWord_230325, baseEnd_230325] using wordTrace_append hprefix tailTrace_230325
  have hstable : (prefixWord ++ tailWord_230325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230325).length < 2 ^ (prefixWord ++ tailWord_230325).sum := by decide
  have hdescent : baseEnd_230325 < baseStart_230325 := by decide
  rcases family_descends (prefixWord ++ tailWord_230325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230361 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 2, 5]
def baseStart_230361 : Nat := 118140960795 + 230361 * 2 ^ 59
def prefixEnd_230361 : Nat := 4983230072969 + 3 ^ 40 * 230361 * 2
def baseEnd_230361 : Nat := 39428639016826148409365

theorem tailTrace_230361 : CollatzResearch.WordTrace tailWord_230361 prefixEnd_230361 39428639016826148409365 := by
  unfold tailWord_230361
  simp only [CollatzResearch.WordTrace]
  refine ⟨8401955918448914371690937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5601303945632609581127291 8401955918448914371690937)
  ·
    refine ⟨6301466938836685778768203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8401955918448914371690937 6301466938836685778768203)
    ·
      refine ⟨9452200408255028668152305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6301466938836685778768203 9452200408255028668152305)
      ·
        refine ⟨7089150306191271501114229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9452200408255028668152305 7089150306191271501114229)
        ·
          refine ⟨664607841205431703229459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7089150306191271501114229 664607841205431703229459)
          ·
            refine ⟨996911761808147554844189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664607841205431703229459 996911761808147554844189)
            ·
              refine ⟨373841910678055333066571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 996911761808147554844189 373841910678055333066571)
              ·
                refine ⟨560762866017082999599857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373841910678055333066571 560762866017082999599857)
                ·
                  refine ⟨420572149512812249699893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560762866017082999599857 420572149512812249699893)
                  ·
                    refine ⟨39428639016826148409365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 420572149512812249699893 39428639016826148409365)
                    ·
                      rfl

theorem cell23_230361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 5].length) (baseStart_230361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230361 prefixEnd_230361 := by exact prefixLift 230361
  have htrace : WordTrace (prefixWord ++ tailWord_230361) baseStart_230361 baseEnd_230361 := by
    simpa [prefixWord, tailWord_230361, baseEnd_230361] using wordTrace_append hprefix tailTrace_230361
  have hstable : (prefixWord ++ tailWord_230361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230361).length < 2 ^ (prefixWord ++ tailWord_230361).sum := by decide
  have hdescent : baseEnd_230361 < baseStart_230361 := by decide
  rcases family_descends (prefixWord ++ tailWord_230361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230401 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_230401 : Nat := 118140960795 + 230401 * 2 ^ 59
def prefixEnd_230401 : Nat := 4983230072969 + 3 ^ 40 * 230401 * 2
def baseEnd_230401 : Nat := 118306456276658288727911

theorem tailTrace_230401 : CollatzResearch.WordTrace tailWord_230401 prefixEnd_230401 118306456276658288727911 := by
  unfold tailWord_230401
  simp only [CollatzResearch.WordTrace]
  refine ⟨8403414838304001203147057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5602276558869334135431371 8403414838304001203147057)
  ·
    refine ⟨6302561128728000902360293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8403414838304001203147057 6302561128728000902360293)
    ·
      refine ⟨1181730211636500169192555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6302561128728000902360293 1181730211636500169192555)
      ·
        refine ⟨1772595317454750253788833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1181730211636500169192555 1772595317454750253788833)
        ·
          refine ⟨1329446488091062690341625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1772595317454750253788833 1329446488091062690341625)
          ·
            refine ⟨997084866068297017756219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1329446488091062690341625 997084866068297017756219)
            ·
              refine ⟨1495627299102445526634329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997084866068297017756219 1495627299102445526634329)
              ·
                refine ⟨1121720474326834144975747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1495627299102445526634329 1121720474326834144975747)
                ·
                  refine ⟨1682580711490251217463621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1121720474326834144975747 1682580711490251217463621)
                  ·
                    refine ⟨315483883404422103274429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1682580711490251217463621 315483883404422103274429)
                    ·
                      refine ⟨118306456276658288727911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 315483883404422103274429 118306456276658288727911)
                      ·
                        rfl

theorem cell23_230401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_230401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230401 prefixEnd_230401 := by exact prefixLift 230401
  have htrace : WordTrace (prefixWord ++ tailWord_230401) baseStart_230401 baseEnd_230401 := by
    simpa [prefixWord, tailWord_230401, baseEnd_230401] using wordTrace_append hprefix tailTrace_230401
  have hstable : (prefixWord ++ tailWord_230401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230401).length < 2 ^ (prefixWord ++ tailWord_230401).sum := by decide
  have hdescent : baseEnd_230401 < baseStart_230401 := by decide
  rcases family_descends (prefixWord ++ tailWord_230401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230442 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 3, 4]
def baseStart_230442 : Nat := 118140960795 + 230442 * 2 ^ 59
def prefixEnd_230442 : Nat := 4983230072969 + 3 ^ 40 * 230442 * 2
def baseEnd_230442 : Nat := 39442502994497542771741

theorem tailTrace_230442 : CollatzResearch.WordTrace tailWord_230442 prefixEnd_230442 39442502994497542771741 := by
  unfold tailWord_230442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2101227557788866301347395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5603273487436976803593053 2101227557788866301347395)
  ·
    refine ⟨3151841336683299452021093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2101227557788866301347395 3151841336683299452021093)
    ·
      refine ⟨590970250628118647253955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3151841336683299452021093 590970250628118647253955)
      ·
        refine ⟨886455375942177970880933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590970250628118647253955 886455375942177970880933)
        ·
          refine ⟨166210382989158369540175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 886455375942177970880933 166210382989158369540175)
          ·
            refine ⟨249315574483737554310263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166210382989158369540175 249315574483737554310263)
            ·
              refine ⟨373973361725606331465395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249315574483737554310263 373973361725606331465395)
              ·
                refine ⟨560960042588409497198093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373973361725606331465395 560960042588409497198093)
                ·
                  refine ⟨210360015970653561449285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560960042588409497198093 210360015970653561449285)
                  ·
                    refine ⟨39442502994497542771741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 210360015970653561449285 39442502994497542771741)
                    ·
                      rfl

theorem cell23_230442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_230442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230442 prefixEnd_230442 := by exact prefixLift 230442
  have htrace : WordTrace (prefixWord ++ tailWord_230442) baseStart_230442 baseEnd_230442 := by
    simpa [prefixWord, tailWord_230442, baseEnd_230442] using wordTrace_append hprefix tailTrace_230442
  have hstable : (prefixWord ++ tailWord_230442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230442).length < 2 ^ (prefixWord ++ tailWord_230442).sum := by decide
  have hdescent : baseEnd_230442 < baseStart_230442 := by decide
  rcases family_descends (prefixWord ++ tailWord_230442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230481 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 6, 4]
def baseStart_230481 : Nat := 118140960795 + 230481 * 2 ^ 59
def prefixEnd_230481 : Nat := 4983230072969 + 3 ^ 40 * 230481 * 2
def baseEnd_230481 : Nat := 39449178243005991909181

theorem tailTrace_230481 : CollatzResearch.WordTrace tailWord_230481 prefixEnd_230481 39449178243005991909181 := by
  unfold tailWord_230481
  simp only [CollatzResearch.WordTrace]
  refine ⟨8406332678014174866059297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5604221785342783244039531 8406332678014174866059297)
  ·
    refine ⟨6304749508510631149544473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8406332678014174866059297 6304749508510631149544473)
    ·
      refine ⟨4728562131382973362158355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6304749508510631149544473 4728562131382973362158355)
      ·
        refine ⟨7092843197074460043237533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4728562131382973362158355 7092843197074460043237533)
        ·
          refine ⟨2659816198902922516214075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7092843197074460043237533 2659816198902922516214075)
          ·
            refine ⟨3989724298354383774321113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2659816198902922516214075 3989724298354383774321113)
            ·
              refine ⟨2992293223765787830740835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3989724298354383774321113 2992293223765787830740835)
              ·
                refine ⟨4488439835648681746111253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2992293223765787830740835 4488439835648681746111253)
                ·
                  refine ⟨210395617296031956848965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4488439835648681746111253 210395617296031956848965)
                  ·
                    refine ⟨39449178243005991909181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 210395617296031956848965 39449178243005991909181)
                    ·
                      rfl

theorem cell23_230481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_230481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230481 prefixEnd_230481 := by exact prefixLift 230481
  have htrace : WordTrace (prefixWord ++ tailWord_230481) baseStart_230481 baseEnd_230481 := by
    simpa [prefixWord, tailWord_230481, baseEnd_230481] using wordTrace_append hprefix tailTrace_230481
  have hstable : (prefixWord ++ tailWord_230481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230481).length < 2 ^ (prefixWord ++ tailWord_230481).sum := by decide
  have hdescent : baseEnd_230481 < baseStart_230481 := by decide
  rcases family_descends (prefixWord ++ tailWord_230481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230501 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 3, 2, 4]
def baseStart_230501 : Nat := 118140960795 + 230501 * 2 ^ 59
def prefixEnd_230501 : Nat := 4983230072969 + 3 ^ 40 * 230501 * 2
def baseEnd_230501 : Nat := 118357804342107897477451

theorem tailTrace_230501 : CollatzResearch.WordTrace tailWord_230501 prefixEnd_230501 118357804342107897477451 := by
  unfold tailWord_230501
  simp only [CollatzResearch.WordTrace]
  refine ⟨8407062137941718281787357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5604708091961145521191571 8407062137941718281787357)
  ·
    refine ⟨3152648301728144355670259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8407062137941718281787357 3152648301728144355670259)
    ·
      refine ⟨4728972452592216533505389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3152648301728144355670259 4728972452592216533505389)
      ·
        refine ⟨1773364669722081200064521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4728972452592216533505389 1773364669722081200064521)
        ·
          refine ⟨1330023502291560900048391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1773364669722081200064521 1330023502291560900048391)
          ·
            refine ⟨1995035253437341350072587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330023502291560900048391 1995035253437341350072587)
            ·
              refine ⟨2992552880156012025108881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1995035253437341350072587 2992552880156012025108881)
              ·
                refine ⟨2244414660117009018831661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2992552880156012025108881 2244414660117009018831661)
                ·
                  refine ⟨841655497543878382061873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2244414660117009018831661 841655497543878382061873)
                  ·
                    refine ⟨631241623157908786546405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 841655497543878382061873 631241623157908786546405)
                    ·
                      refine ⟨118357804342107897477451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 631241623157908786546405 118357804342107897477451)
                      ·
                        rfl

theorem cell23_230501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_230501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230501 prefixEnd_230501 := by exact prefixLift 230501
  have htrace : WordTrace (prefixWord ++ tailWord_230501) baseStart_230501 baseEnd_230501 := by
    simpa [prefixWord, tailWord_230501, baseEnd_230501] using wordTrace_append hprefix tailTrace_230501
  have hstable : (prefixWord ++ tailWord_230501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230501).length < 2 ^ (prefixWord ++ tailWord_230501).sum := by decide
  have hdescent : baseEnd_230501 < baseStart_230501 := by decide
  rcases family_descends (prefixWord ++ tailWord_230501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230538 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 1, 3, 3]
def baseStart_230538 : Nat := 118140960795 + 230538 * 2 ^ 59
def prefixEnd_230538 : Nat := 4983230072969 + 3 ^ 40 * 230538 * 2
def baseEnd_230538 : Nat := 118376803126324252714781

theorem tailTrace_230538 : CollatzResearch.WordTrace tailWord_230538 prefixEnd_230538 118376803126324252714781 := by
  unfold tailWord_230538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2102102909701918400221067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5605607759205115733922845 2102102909701918400221067)
  ·
    refine ⟨3153154364552877600331601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2102102909701918400221067 3153154364552877600331601)
    ·
      refine ⟨2364865773414658200248701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3153154364552877600331601 2364865773414658200248701)
      ·
        refine ⟨886824665030496825093263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2364865773414658200248701 886824665030496825093263)
        ·
          refine ⟨1330236997545745237639895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886824665030496825093263 1330236997545745237639895)
          ·
            refine ⟨1995355496318617856459843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330236997545745237639895 1995355496318617856459843)
            ·
              refine ⟨2993033244477926784689765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1995355496318617856459843 2993033244477926784689765)
              ·
                refine ⟨561193733339611272129331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2993033244477926784689765 561193733339611272129331)
                ·
                  refine ⟨841790600009416908193997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561193733339611272129331 841790600009416908193997)
                  ·
                    refine ⟨315671475003531340572749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 841790600009416908193997 315671475003531340572749)
                    ·
                      refine ⟨118376803126324252714781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 315671475003531340572749 118376803126324252714781)
                      ·
                        rfl

theorem cell23_230538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_230538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230538 prefixEnd_230538 := by exact prefixLift 230538
  have htrace : WordTrace (prefixWord ++ tailWord_230538) baseStart_230538 baseEnd_230538 := by
    simpa [prefixWord, tailWord_230538, baseEnd_230538] using wordTrace_append hprefix tailTrace_230538
  have hstable : (prefixWord ++ tailWord_230538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230538).length < 2 ^ (prefixWord ++ tailWord_230538).sum := by decide
  have hdescent : baseEnd_230538 < baseStart_230538 := by decide
  rcases family_descends (prefixWord ++ tailWord_230538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230542 : List Nat := [4, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3]
def baseStart_230542 : Nat := 118140960795 + 230542 * 2 ^ 59
def prefixEnd_230542 : Nat := 4983230072969 + 3 ^ 40 * 230542 * 2
def baseEnd_230542 : Nat := 118378857048942237064763

theorem tailTrace_230542 : CollatzResearch.WordTrace tailWord_230542 prefixEnd_230542 118378857048942237064763 := by
  unfold tailWord_230542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1051069691349147785503735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5605705020528788189353253 1051069691349147785503735)
  ·
    refine ⟨1576604537023721678255603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1051069691349147785503735 1576604537023721678255603)
    ·
      refine ⟨2364906805535582517383405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1576604537023721678255603 2364906805535582517383405)
      ·
        refine ⟨886840052075843444018777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2364906805535582517383405 886840052075843444018777)
        ·
          refine ⟨665130039056882583014083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 886840052075843444018777 665130039056882583014083)
          ·
            refine ⟨997695058585323874521125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665130039056882583014083 997695058585323874521125)
            ·
              refine ⟨187067823484748226472711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 997695058585323874521125 187067823484748226472711)
              ·
                refine ⟨280601735227122339709067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187067823484748226472711 280601735227122339709067)
                ·
                  refine ⟨420902602840683509563601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280601735227122339709067 420902602840683509563601)
                  ·
                    refine ⟨315676952130512632172701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 420902602840683509563601 315676952130512632172701)
                    ·
                      refine ⟨118378857048942237064763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 315676952130512632172701 118378857048942237064763)
                      ·
                        rfl

theorem cell23_230542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_230542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230542 prefixEnd_230542 := by exact prefixLift 230542
  have htrace : WordTrace (prefixWord ++ tailWord_230542) baseStart_230542 baseEnd_230542 := by
    simpa [prefixWord, tailWord_230542, baseEnd_230542] using wordTrace_append hprefix tailTrace_230542
  have hstable : (prefixWord ++ tailWord_230542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230542).length < 2 ^ (prefixWord ++ tailWord_230542).sum := by decide
  have hdescent : baseEnd_230542 < baseStart_230542 := by decide
  rcases family_descends (prefixWord ++ tailWord_230542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230591 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 4]
def baseStart_230591 : Nat := 118140960795 + 230591 * 2 ^ 59
def prefixEnd_230591 : Nat := 4983230072969 + 3 ^ 40 * 230591 * 2
def baseEnd_230591 : Nat := 118404017601012545352037

theorem tailTrace_230591 : CollatzResearch.WordTrace tailWord_230591 prefixEnd_230591 118404017601012545352037 := by
  unfold tailWord_230591
  simp only [CollatzResearch.WordTrace]
  refine ⟨8410344707615663652563627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5606896471743775768375751 8410344707615663652563627)
  ·
    refine ⟨12615517061423495478845441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8410344707615663652563627 12615517061423495478845441)
    ·
      refine ⟨9461637796067621609134081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12615517061423495478845441 9461637796067621609134081)
      ·
        refine ⟨7096228347050716206850561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9461637796067621609134081 7096228347050716206850561)
        ·
          refine ⟨5322171260288037155137921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7096228347050716206850561 5322171260288037155137921)
          ·
            refine ⟨3991628445216027866353441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5322171260288037155137921 3991628445216027866353441)
            ·
              refine ⟨2993721333912020899765081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3991628445216027866353441 2993721333912020899765081)
              ·
                refine ⟨2245291000434015674823811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2993721333912020899765081 2245291000434015674823811)
                ·
                  refine ⟨3367936500651023512235717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2245291000434015674823811 3367936500651023512235717)
                  ·
                    refine ⟨631488093872066908544197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3367936500651023512235717 631488093872066908544197)
                    ·
                      refine ⟨118404017601012545352037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 631488093872066908544197 118404017601012545352037)
                      ·
                        rfl

theorem cell23_230591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_230591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230591 prefixEnd_230591 := by exact prefixLift 230591
  have htrace : WordTrace (prefixWord ++ tailWord_230591) baseStart_230591 baseEnd_230591 := by
    simpa [prefixWord, tailWord_230591, baseEnd_230591] using wordTrace_append hprefix tailTrace_230591
  have hstable : (prefixWord ++ tailWord_230591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230591).length < 2 ^ (prefixWord ++ tailWord_230591).sum := by decide
  have hdescent : baseEnd_230591 < baseStart_230591 := by decide
  rcases family_descends (prefixWord ++ tailWord_230591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230628 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 2, 3, 3]
def baseStart_230628 : Nat := 118140960795 + 230628 * 2 ^ 59
def prefixEnd_230628 : Nat := 4983230072969 + 3 ^ 40 * 230628 * 2
def baseEnd_230628 : Nat := 118423016385228900589367

theorem tailTrace_230628 : CollatzResearch.WordTrace tailWord_230628 prefixEnd_230628 118423016385228900589367 := by
  unfold tailWord_230628
  simp only [CollatzResearch.WordTrace]
  refine ⟨4205847104240809485830269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5607796138987745981107025 4205847104240809485830269)
  ·
    refine ⟨1577192664090303557186351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4205847104240809485830269 1577192664090303557186351)
    ·
      refine ⟨2365788996135455335779527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1577192664090303557186351 2365788996135455335779527)
      ·
        refine ⟨3548683494203183003669291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2365788996135455335779527 3548683494203183003669291)
        ·
          refine ⟨5323025241304774505503937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3548683494203183003669291 5323025241304774505503937)
          ·
            refine ⟨3992268930978580879127953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5323025241304774505503937 3992268930978580879127953)
            ·
              refine ⟨2994201698233935659345965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3992268930978580879127953 2994201698233935659345965)
              ·
                refine ⟨1122825636837725872254737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2994201698233935659345965 1122825636837725872254737)
                ·
                  refine ⟨842119227628294404191053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1122825636837725872254737 842119227628294404191053)
                  ·
                    refine ⟨315794710360610401571645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 842119227628294404191053 315794710360610401571645)
                    ·
                      refine ⟨118423016385228900589367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 315794710360610401571645 118423016385228900589367)
                      ·
                        rfl

theorem cell23_230628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_230628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230628 prefixEnd_230628 := by exact prefixLift 230628
  have htrace : WordTrace (prefixWord ++ tailWord_230628) baseStart_230628 baseEnd_230628 := by
    simpa [prefixWord, tailWord_230628, baseEnd_230628] using wordTrace_append hprefix tailTrace_230628
  have hstable : (prefixWord ++ tailWord_230628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230628).length < 2 ^ (prefixWord ++ tailWord_230628).sum := by decide
  have hdescent : baseEnd_230628 < baseStart_230628 := by decide
  rcases family_descends (prefixWord ++ tailWord_230628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230629 : List Nat := [1, 3, 1, 4, 3, 1, 1, 3, 2, 2, 2]
def baseStart_230629 : Nat := 118140960795 + 230629 * 2 ^ 59
def prefixEnd_230629 : Nat := 4983230072969 + 3 ^ 40 * 230629 * 2
def baseEnd_230629 : Nat := 118423529865883396676863

theorem tailTrace_230629 : CollatzResearch.WordTrace tailWord_230629 prefixEnd_230629 118423529865883396676863 := by
  unfold tailWord_230629
  simp only [CollatzResearch.WordTrace]
  refine ⟨8411730681477996142446941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5607820454318664094964627 8411730681477996142446941)
  ·
    refine ⟨3154399005554248553417603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8411730681477996142446941 3154399005554248553417603)
    ·
      refine ⟨4731598508331372830126405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3154399005554248553417603 4731598508331372830126405)
      ·
        refine ⟨887174720312132405648701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4731598508331372830126405 887174720312132405648701)
        ·
          refine ⟨332690520117049652118263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 887174720312132405648701 332690520117049652118263)
          ·
            refine ⟨499035780175574478177395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332690520117049652118263 499035780175574478177395)
            ·
              refine ⟨748553670263361717266093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499035780175574478177395 748553670263361717266093)
              ·
                refine ⟨280707626348760643974785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 748553670263361717266093 280707626348760643974785)
                ·
                  refine ⟨210530719761570482981089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280707626348760643974785 210530719761570482981089)
                  ·
                    refine ⟨157898039821177862235817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 210530719761570482981089 157898039821177862235817)
                    ·
                      refine ⟨118423529865883396676863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 157898039821177862235817 118423529865883396676863)
                      ·
                        rfl

theorem cell23_230629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_230629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230629 prefixEnd_230629 := by exact prefixLift 230629
  have htrace : WordTrace (prefixWord ++ tailWord_230629) baseStart_230629 baseEnd_230629 := by
    simpa [prefixWord, tailWord_230629, baseEnd_230629] using wordTrace_append hprefix tailTrace_230629
  have hstable : (prefixWord ++ tailWord_230629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230629).length < 2 ^ (prefixWord ++ tailWord_230629).sum := by decide
  have hdescent : baseEnd_230629 < baseStart_230629 := by decide
  rcases family_descends (prefixWord ++ tailWord_230629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230641 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 7]
def baseStart_230641 : Nat := 118140960795 + 230641 * 2 ^ 59
def prefixEnd_230641 : Nat := 4983230072969 + 3 ^ 40 * 230641 * 2
def baseEnd_230641 : Nat := 118429691633737349726807

theorem tailTrace_230641 : CollatzResearch.WordTrace tailWord_230641 prefixEnd_230641 118429691633737349726807 := by
  unfold tailWord_230641
  simp only [CollatzResearch.WordTrace]
  refine ⟨8412168357434522191883777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5608112238289681461255851 8412168357434522191883777)
  ·
    refine ⟨6309126268075891643912833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8412168357434522191883777 6309126268075891643912833)
    ·
      refine ⟨4731844701056918732934625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6309126268075891643912833 4731844701056918732934625)
      ·
        refine ⟨3548883525792689049700969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4731844701056918732934625 3548883525792689049700969)
        ·
          refine ⟨2661662644344516787275727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3548883525792689049700969 2661662644344516787275727)
          ·
            refine ⟨3992493966516775180913591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2661662644344516787275727 3992493966516775180913591)
            ·
              refine ⟨5988740949775162771370387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992493966516775180913591 5988740949775162771370387)
              ·
                refine ⟨8983111424662744157055581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5988740949775162771370387 8983111424662744157055581)
                ·
                  refine ⟨3368666784248529058895843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8983111424662744157055581 3368666784248529058895843)
                  ·
                    refine ⟨5053000176372793588343765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3368666784248529058895843 5053000176372793588343765)
                    ·
                      refine ⟨118429691633737349726807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5053000176372793588343765 118429691633737349726807)
                      ·
                        rfl

theorem cell23_230641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_230641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230641 prefixEnd_230641 := by exact prefixLift 230641
  have htrace : WordTrace (prefixWord ++ tailWord_230641) baseStart_230641 baseEnd_230641 := by
    simpa [prefixWord, tailWord_230641, baseEnd_230641] using wordTrace_append hprefix tailTrace_230641
  have hstable : (prefixWord ++ tailWord_230641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230641).length < 2 ^ (prefixWord ++ tailWord_230641).sum := by decide
  have hdescent : baseEnd_230641 < baseStart_230641 := by decide
  rcases family_descends (prefixWord ++ tailWord_230641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230705 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 1, 4, 3]
def baseStart_230705 : Nat := 118140960795 + 230705 * 2 ^ 59
def prefixEnd_230705 : Nat := 4983230072969 + 3 ^ 40 * 230705 * 2
def baseEnd_230705 : Nat := 118462554395625099326513

theorem tailTrace_230705 : CollatzResearch.WordTrace tailWord_230705 prefixEnd_230705 118462554395625099326513 := by
  unfold tailWord_230705
  simp only [CollatzResearch.WordTrace]
  refine ⟨8414502629202661122213569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5609668419468440748142379 8414502629202661122213569)
  ·
    refine ⟨6310876971901995841660177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8414502629202661122213569 6310876971901995841660177)
    ·
      refine ⟨4733157728926496881245133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6310876971901995841660177 4733157728926496881245133)
      ·
        refine ⟨1774934148347436330466925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4733157728926496881245133 1774934148347436330466925)
        ·
          refine ⟨665600305630288623925097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1774934148347436330466925 665600305630288623925097)
          ·
            refine ⟨499200229222716467943823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665600305630288623925097 499200229222716467943823)
            ·
              refine ⟨748800343834074701915735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499200229222716467943823 748800343834074701915735)
              ·
                refine ⟨1123200515751112052873603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748800343834074701915735 1123200515751112052873603)
                ·
                  refine ⟨1684800773626668079310405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1123200515751112052873603 1684800773626668079310405)
                  ·
                    refine ⟨315900145055000264870701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1684800773626668079310405 315900145055000264870701)
                    ·
                      refine ⟨118462554395625099326513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 315900145055000264870701 118462554395625099326513)
                      ·
                        rfl

theorem cell23_230705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_230705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230705 prefixEnd_230705 := by exact prefixLift 230705
  have htrace : WordTrace (prefixWord ++ tailWord_230705) baseStart_230705 baseEnd_230705 := by
    simpa [prefixWord, tailWord_230705, baseEnd_230705] using wordTrace_append hprefix tailTrace_230705
  have hstable : (prefixWord ++ tailWord_230705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230705).length < 2 ^ (prefixWord ++ tailWord_230705).sum := by decide
  have hdescent : baseEnd_230705 < baseStart_230705 := by decide
  rcases family_descends (prefixWord ++ tailWord_230705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230745 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 1, 5, 2]
def baseStart_230745 : Nat := 118140960795 + 230745 * 2 ^ 59
def prefixEnd_230745 : Nat := 4983230072969 + 3 ^ 40 * 230745 * 2
def baseEnd_230745 : Nat := 118483093621804942826329

theorem tailTrace_230745 : CollatzResearch.WordTrace tailWord_230745 prefixEnd_230745 118483093621804942826329 := by
  unfold tailWord_230745
  simp only [CollatzResearch.WordTrace]
  refine ⟨8415961549057747953669689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5610641032705165302446459 8415961549057747953669689)
  ·
    refine ⟨6311971161793310965252267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8415961549057747953669689 6311971161793310965252267)
    ·
      refine ⟨9467956742689966447878401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6311971161793310965252267 9467956742689966447878401)
      ·
        refine ⟨7100967557017474835908801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9467956742689966447878401 7100967557017474835908801)
        ·
          refine ⟨5325725667763106126931601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7100967557017474835908801 5325725667763106126931601)
          ·
            refine ⟨3994294250822329595198701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5325725667763106126931601 3994294250822329595198701)
            ·
              refine ⟨1497860344058373598199513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3994294250822329595198701 1497860344058373598199513)
              ·
                refine ⟨1123395258043780198649635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497860344058373598199513 1123395258043780198649635)
                ·
                  refine ⟨1685092887065670297974453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1123395258043780198649635 1685092887065670297974453)
                  ·
                    refine ⟨157977458162406590435105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1685092887065670297974453 157977458162406590435105)
                    ·
                      refine ⟨118483093621804942826329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 157977458162406590435105 118483093621804942826329)
                      ·
                        rfl

theorem cell23_230745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 5, 2].length) (baseStart_230745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230745 prefixEnd_230745 := by exact prefixLift 230745
  have htrace : WordTrace (prefixWord ++ tailWord_230745) baseStart_230745 baseEnd_230745 := by
    simpa [prefixWord, tailWord_230745, baseEnd_230745] using wordTrace_append hprefix tailTrace_230745
  have hstable : (prefixWord ++ tailWord_230745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230745).length < 2 ^ (prefixWord ++ tailWord_230745).sum := by decide
  have hdescent : baseEnd_230745 < baseStart_230745 := by decide
  rcases family_descends (prefixWord ++ tailWord_230745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230752 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 3, 1, 3]
def baseStart_230752 : Nat := 118140960795 + 230752 * 2 ^ 59
def prefixEnd_230752 : Nat := 4983230072969 + 3 ^ 40 * 230752 * 2
def baseEnd_230752 : Nat := 118486687986386415438797

theorem tailTrace_230752 : CollatzResearch.WordTrace tailWord_230752 prefixEnd_230752 118486687986386415438797 := by
  unfold tailWord_230752
  simp only [CollatzResearch.WordTrace]
  refine ⟨4208108430016194074587255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5610811240021592099449673 4208108430016194074587255)
  ·
    refine ⟨6312162645024291111880883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4208108430016194074587255 6312162645024291111880883)
    ·
      refine ⟨9468243967536436667821325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6312162645024291111880883 9468243967536436667821325)
      ·
        refine ⟨3550591487826163750432997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9468243967536436667821325 3550591487826163750432997)
        ·
          refine ⟨665735903967405703206187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3550591487826163750432997 665735903967405703206187)
          ·
            refine ⟨998603855951108554809281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665735903967405703206187 998603855951108554809281)
            ·
              refine ⟨748952891963331416106961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 998603855951108554809281 748952891963331416106961)
              ·
                refine ⟨561714668972498562080221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 748952891963331416106961 561714668972498562080221)
                ·
                  refine ⟨210643000864686960780083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561714668972498562080221 210643000864686960780083)
                  ·
                    refine ⟨315964501297030441170125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 210643000864686960780083 315964501297030441170125)
                    ·
                      refine ⟨118486687986386415438797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 315964501297030441170125 118486687986386415438797)
                      ·
                        rfl

theorem cell23_230752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_230752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230752 prefixEnd_230752 := by exact prefixLift 230752
  have htrace : WordTrace (prefixWord ++ tailWord_230752) baseStart_230752 baseEnd_230752 := by
    simpa [prefixWord, tailWord_230752, baseEnd_230752] using wordTrace_append hprefix tailTrace_230752
  have hstable : (prefixWord ++ tailWord_230752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230752).length < 2 ^ (prefixWord ++ tailWord_230752).sum := by decide
  have hdescent : baseEnd_230752 < baseStart_230752 := by decide
  rcases family_descends (prefixWord ++ tailWord_230752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230755 : List Nat := [1, 1, 1, 5, 2, 2, 1, 4, 1, 5]
def baseStart_230755 : Nat := 118140960795 + 230755 * 2 ^ 59
def prefixEnd_230755 : Nat := 4983230072969 + 3 ^ 40 * 230755 * 2
def baseEnd_230755 : Nat := 39496076142783301233761

theorem tailTrace_230755 : CollatzResearch.WordTrace tailWord_230755 prefixEnd_230755 39496076142783301233761 := by
  unfold tailWord_230755
  simp only [CollatzResearch.WordTrace]
  refine ⟨8416326279021519661533719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5610884186014346441022479 8416326279021519661533719)
  ·
    refine ⟨12624489418532279492300579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8416326279021519661533719 12624489418532279492300579)
    ·
      refine ⟨18936734127798419238450869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12624489418532279492300579 18936734127798419238450869)
      ·
        refine ⟨1775318824481101803604769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18936734127798419238450869 1775318824481101803604769)
        ·
          refine ⟨1331489118360826352703577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1775318824481101803604769 1331489118360826352703577)
          ·
            refine ⟨998616838770619764527683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1331489118360826352703577 998616838770619764527683)
            ·
              refine ⟨1497925258155929646791525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998616838770619764527683 1497925258155929646791525)
              ·
                refine ⟨280860985904236808773411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1497925258155929646791525 280860985904236808773411)
                ·
                  refine ⟨421291478856355213160117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280860985904236808773411 421291478856355213160117)
                  ·
                    refine ⟨39496076142783301233761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 421291478856355213160117 39496076142783301233761)
                    ·
                      rfl

theorem cell23_230755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 5].length) (baseStart_230755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230755 prefixEnd_230755 := by exact prefixLift 230755
  have htrace : WordTrace (prefixWord ++ tailWord_230755) baseStart_230755 baseEnd_230755 := by
    simpa [prefixWord, tailWord_230755, baseEnd_230755] using wordTrace_append hprefix tailTrace_230755
  have hstable : (prefixWord ++ tailWord_230755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230755).length < 2 ^ (prefixWord ++ tailWord_230755).sum := by decide
  have hdescent : baseEnd_230755 < baseStart_230755 := by decide
  rcases family_descends (prefixWord ++ tailWord_230755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230768 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 3, 6]
def baseStart_230768 : Nat := 118140960795 + 230768 * 2 ^ 59
def prefixEnd_230768 : Nat := 4983230072969 + 3 ^ 40 * 230768 * 2
def baseEnd_230768 : Nat := 39498301225619450946241

theorem tailTrace_230768 : CollatzResearch.WordTrace tailWord_230768 prefixEnd_230768 39498301225619450946241 := by
  unfold tailWord_230768
  simp only [CollatzResearch.WordTrace]
  refine ⟨4208400213987211440878479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5611200285316281921171305 4208400213987211440878479)
  ·
    refine ⟨6312600320980817161317719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4208400213987211440878479 6312600320980817161317719)
    ·
      refine ⟨9468900481471225741976579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6312600320980817161317719 9468900481471225741976579)
      ·
        refine ⟨14203350722206838612964869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9468900481471225741976579 14203350722206838612964869)
        ·
          refine ⟨2663128260413782239930913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14203350722206838612964869 2663128260413782239930913)
          ·
            refine ⟨1997346195310336679948185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2663128260413782239930913 1997346195310336679948185)
            ·
              refine ⟨1498009646482752509961139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1997346195310336679948185 1498009646482752509961139)
              ·
                refine ⟨2247014469724128764941709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1498009646482752509961139 2247014469724128764941709)
                ·
                  refine ⟨842630426146548286853141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2247014469724128764941709 842630426146548286853141)
                  ·
                    refine ⟨39498301225619450946241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 842630426146548286853141 39498301225619450946241)
                    ·
                      rfl

theorem cell23_230768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 3, 6].length) (baseStart_230768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230768 prefixEnd_230768 := by exact prefixLift 230768
  have htrace : WordTrace (prefixWord ++ tailWord_230768) baseStart_230768 baseEnd_230768 := by
    simpa [prefixWord, tailWord_230768, baseEnd_230768] using wordTrace_append hprefix tailTrace_230768
  have hstable : (prefixWord ++ tailWord_230768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230768).length < 2 ^ (prefixWord ++ tailWord_230768).sum := by decide
  have hdescent : baseEnd_230768 < baseStart_230768 := by decide
  rcases family_descends (prefixWord ++ tailWord_230768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230769 : List Nat := [1, 2, 2, 2, 1, 2, 5, 3, 1, 1, 3]
def baseStart_230769 : Nat := 118140960795 + 230769 * 2 ^ 59
def prefixEnd_230769 : Nat := 4983230072969 + 3 ^ 40 * 230769 * 2
def baseEnd_230769 : Nat := 118495417157512848926219

theorem tailTrace_230769 : CollatzResearch.WordTrace tailWord_230769 prefixEnd_230769 118495417157512848926219 := by
  unfold tailWord_230769
  simp only [CollatzResearch.WordTrace]
  refine ⟨8416836900970800052543361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5611224600647200035028907 8416836900970800052543361)
  ·
    refine ⟨6312627675728100039407521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8416836900970800052543361 6312627675728100039407521)
    ·
      refine ⟨4734470756796075029555641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6312627675728100039407521 4734470756796075029555641)
      ·
        refine ⟨3550853067597056272166731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4734470756796075029555641 3550853067597056272166731)
        ·
          refine ⟨5326279601395584408250097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3550853067597056272166731 5326279601395584408250097)
          ·
            refine ⟨3994709701046688306187573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5326279601395584408250097 3994709701046688306187573)
            ·
              refine ⟨374504034473127028705085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3994709701046688306187573 374504034473127028705085)
              ·
                refine ⟨140439012927422635764407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374504034473127028705085 140439012927422635764407)
                ·
                  refine ⟨210658519391133953646611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140439012927422635764407 210658519391133953646611)
                  ·
                    refine ⟨315987779086700930469917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 210658519391133953646611 315987779086700930469917)
                    ·
                      refine ⟨118495417157512848926219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 315987779086700930469917 118495417157512848926219)
                      ·
                        rfl

theorem cell23_230769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_230769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230769 prefixEnd_230769 := by exact prefixLift 230769
  have htrace : WordTrace (prefixWord ++ tailWord_230769) baseStart_230769 baseEnd_230769 := by
    simpa [prefixWord, tailWord_230769, baseEnd_230769] using wordTrace_append hprefix tailTrace_230769
  have hstable : (prefixWord ++ tailWord_230769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230769).length < 2 ^ (prefixWord ++ tailWord_230769).sum := by decide
  have hdescent : baseEnd_230769 < baseStart_230769 := by decide
  rcases family_descends (prefixWord ++ tailWord_230769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230775 : List Nat := [1, 1, 3, 1, 1, 2, 3, 5, 1, 1, 4]
def baseStart_230775 : Nat := 118140960795 + 230775 * 2 ^ 59
def prefixEnd_230775 : Nat := 4983230072969 + 3 ^ 40 * 230775 * 2
def baseEnd_230775 : Nat := 118498498041439825451191

theorem tailTrace_230775 : CollatzResearch.WordTrace tailWord_230775 prefixEnd_230775 118498498041439825451191 := by
  unfold tailWord_230775
  simp only [CollatzResearch.WordTrace]
  refine ⟨8417055738949063077261779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5611370492632708718174519 8417055738949063077261779)
  ·
    refine ⟨12625583608423594615892669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8417055738949063077261779 12625583608423594615892669)
    ·
      refine ⟨4734593853158847980959751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12625583608423594615892669 4734593853158847980959751)
      ·
        refine ⟨7101890779738271971439627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4734593853158847980959751 7101890779738271971439627)
        ·
          refine ⟨10652836169607407957159441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7101890779738271971439627 10652836169607407957159441)
          ·
            refine ⟨7989627127205555967869581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10652836169607407957159441 7989627127205555967869581)
            ·
              refine ⟨2996110172702083487951093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7989627127205555967869581 2996110172702083487951093)
              ·
                refine ⟨280885328690820326995415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2996110172702083487951093 280885328690820326995415)
                ·
                  refine ⟨421327993036230490493123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280885328690820326995415 421327993036230490493123)
                  ·
                    refine ⟨631991989554345735739685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 421327993036230490493123 631991989554345735739685)
                    ·
                      refine ⟨118498498041439825451191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 631991989554345735739685 118498498041439825451191)
                      ·
                        rfl

theorem cell23_230775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_230775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230775 prefixEnd_230775 := by exact prefixLift 230775
  have htrace : WordTrace (prefixWord ++ tailWord_230775) baseStart_230775 baseEnd_230775 := by
    simpa [prefixWord, tailWord_230775, baseEnd_230775] using wordTrace_append hprefix tailTrace_230775
  have hstable : (prefixWord ++ tailWord_230775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230775).length < 2 ^ (prefixWord ++ tailWord_230775).sum := by decide
  have hdescent : baseEnd_230775 < baseStart_230775 := by decide
  rcases family_descends (prefixWord ++ tailWord_230775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230778 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5]
def baseStart_230778 : Nat := 118140960795 + 230778 * 2 ^ 59
def prefixEnd_230778 : Nat := 4983230072969 + 3 ^ 40 * 230778 * 2
def baseEnd_230778 : Nat := 118500038483403313713677

theorem tailTrace_230778 : CollatzResearch.WordTrace tailWord_230778 prefixEnd_230778 118500038483403313713677 := by
  unfold tailWord_230778
  simp only [CollatzResearch.WordTrace]
  refine ⟨2104291289484548647405247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5611443438625463059747325 2104291289484548647405247)
  ·
    refine ⟨3156436934226822971107871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2104291289484548647405247 3156436934226822971107871)
    ·
      refine ⟨4734655401340234456661807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3156436934226822971107871 4734655401340234456661807)
      ·
        refine ⟨7101983102010351684992711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4734655401340234456661807 7101983102010351684992711)
        ·
          refine ⟨10652974653015527527489067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7101983102010351684992711 10652974653015527527489067)
          ·
            refine ⟨15979461979523291291233601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10652974653015527527489067 15979461979523291291233601)
            ·
              refine ⟨11984596484642468468425201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15979461979523291291233601 11984596484642468468425201)
              ·
                refine ⟨8988447363481851351318901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11984596484642468468425201 8988447363481851351318901)
                ·
                  refine ⟨842666940326423564186147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8988447363481851351318901 842666940326423564186147)
                  ·
                    refine ⟨1264000410489635346279221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 842666940326423564186147 1264000410489635346279221)
                    ·
                      refine ⟨118500038483403313713677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1264000410489635346279221 118500038483403313713677)
                      ·
                        rfl

theorem cell23_230778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_230778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230778 prefixEnd_230778 := by exact prefixLift 230778
  have htrace : WordTrace (prefixWord ++ tailWord_230778) baseStart_230778 baseEnd_230778 := by
    simpa [prefixWord, tailWord_230778, baseEnd_230778] using wordTrace_append hprefix tailTrace_230778
  have hstable : (prefixWord ++ tailWord_230778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230778).length < 2 ^ (prefixWord ++ tailWord_230778).sum := by decide
  have hdescent : baseEnd_230778 < baseStart_230778 := by decide
  rcases family_descends (prefixWord ++ tailWord_230778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230786 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_230786 : Nat := 118140960795 + 230786 * 2 ^ 59
def prefixEnd_230786 : Nat := 4983230072969 + 3 ^ 40 * 230786 * 2
def baseEnd_230786 : Nat := 118504146328639282413641

theorem tailTrace_230786 : CollatzResearch.WordTrace tailWord_230786 prefixEnd_230786 118504146328639282413641 := by
  unfold tailWord_230786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2104364235477302988978053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5611637961272807970608141 2104364235477302988978053)
  ·
    refine ⟨394568294151994310433385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2104364235477302988978053 394568294151994310433385)
    ·
      refine ⟨295926220613995732825039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394568294151994310433385 295926220613995732825039)
      ·
        refine ⟨443889330920993599237559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295926220613995732825039 443889330920993599237559)
        ·
          refine ⟨665833996381490398856339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443889330920993599237559 665833996381490398856339)
          ·
            refine ⟨998750994572235598284509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665833996381490398856339 998750994572235598284509)
            ·
              refine ⟨374531622964588349356691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 998750994572235598284509 374531622964588349356691)
              ·
                refine ⟨561797434446882524035037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374531622964588349356691 561797434446882524035037)
                ·
                  refine ⟨210674037917580946513139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561797434446882524035037 210674037917580946513139)
                  ·
                    refine ⟨316011056876371419769709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 210674037917580946513139 316011056876371419769709)
                    ·
                      refine ⟨118504146328639282413641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 316011056876371419769709 118504146328639282413641)
                      ·
                        rfl

theorem cell23_230786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_230786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230786 prefixEnd_230786 := by exact prefixLift 230786
  have htrace : WordTrace (prefixWord ++ tailWord_230786) baseStart_230786 baseEnd_230786 := by
    simpa [prefixWord, tailWord_230786, baseEnd_230786] using wordTrace_append hprefix tailTrace_230786
  have hstable : (prefixWord ++ tailWord_230786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230786).length < 2 ^ (prefixWord ++ tailWord_230786).sum := by decide
  have hdescent : baseEnd_230786 < baseStart_230786 := by decide
  rcases family_descends (prefixWord ++ tailWord_230786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230795 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 3]
def baseStart_230795 : Nat := 118140960795 + 230795 * 2 ^ 59
def prefixEnd_230795 : Nat := 4983230072969 + 3 ^ 40 * 230795 * 2
def baseEnd_230795 : Nat := 118508767654529747201099

theorem tailTrace_230795 : CollatzResearch.WordTrace tailWord_230795 prefixEnd_230795 118508767654529747201099 := by
  unfold tailWord_230795
  simp only [CollatzResearch.WordTrace]
  refine ⟨8417785198876606492989839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5611856799251070995326559 8417785198876606492989839)
  ·
    refine ⟨12626677798314909739484759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8417785198876606492989839 12626677798314909739484759)
    ·
      refine ⟨18940016697472364609227139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12626677798314909739484759 18940016697472364609227139)
      ·
        refine ⟨28410025046208546913840709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18940016697472364609227139 28410025046208546913840709)
        ·
          refine ⟨5326879696164102546345133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28410025046208546913840709 5326879696164102546345133)
          ·
            refine ⟨1997579886061538454879425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5326879696164102546345133 1997579886061538454879425)
            ·
              refine ⟨1498184914546153841159569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1997579886061538454879425 1498184914546153841159569)
              ·
                refine ⟨1123638685909615380869677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1498184914546153841159569 1123638685909615380869677)
                ·
                  refine ⟨421364507216105767826129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1123638685909615380869677 421364507216105767826129)
                  ·
                    refine ⟨316023380412079325869597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 421364507216105767826129 316023380412079325869597)
                    ·
                      refine ⟨118508767654529747201099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 316023380412079325869597 118508767654529747201099)
                      ·
                        rfl

theorem cell23_230795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 3].length) (baseStart_230795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230795 prefixEnd_230795 := by exact prefixLift 230795
  have htrace : WordTrace (prefixWord ++ tailWord_230795) baseStart_230795 baseEnd_230795 := by
    simpa [prefixWord, tailWord_230795, baseEnd_230795] using wordTrace_append hprefix tailTrace_230795
  have hstable : (prefixWord ++ tailWord_230795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230795).length < 2 ^ (prefixWord ++ tailWord_230795).sum := by decide
  have hdescent : baseEnd_230795 < baseStart_230795 := by decide
  rcases family_descends (prefixWord ++ tailWord_230795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230829 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_230829 : Nat := 118140960795 + 230829 * 2 ^ 59
def prefixEnd_230829 : Nat := 4983230072969 + 3 ^ 40 * 230829 * 2
def baseEnd_230829 : Nat := 118526225996782614175943

theorem tailTrace_230829 : CollatzResearch.WordTrace tailWord_230829 prefixEnd_230829 118526225996782614175943 := by
  unfold tailWord_230829
  simp only [CollatzResearch.WordTrace]
  refine ⟨8419025280753430299727541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5612683520502286866485027 8419025280753430299727541)
  ·
    refine ⟨789283620070634090599457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8419025280753430299727541 789283620070634090599457)
    ·
      refine ⟨591962715052975567949593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 789283620070634090599457 591962715052975567949593)
      ·
        refine ⟨443972036289731675962195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591962715052975567949593 443972036289731675962195)
        ·
          refine ⟨665958054434597513943293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443972036289731675962195 665958054434597513943293)
          ·
            refine ⟨249734270412974067728735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 665958054434597513943293 249734270412974067728735)
            ·
              refine ⟨374601405619461101593103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249734270412974067728735 374601405619461101593103)
              ·
                refine ⟨561902108429191652389655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374601405619461101593103 561902108429191652389655)
                ·
                  refine ⟨842853162643787478584483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561902108429191652389655 842853162643787478584483)
                  ·
                    refine ⟨1264279743965681217876725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 842853162643787478584483 1264279743965681217876725)
                    ·
                      refine ⟨118526225996782614175943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1264279743965681217876725 118526225996782614175943)
                      ·
                        rfl

theorem cell23_230829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_230829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230829 prefixEnd_230829 := by exact prefixLift 230829
  have htrace : WordTrace (prefixWord ++ tailWord_230829) baseStart_230829 baseEnd_230829 := by
    simpa [prefixWord, tailWord_230829, baseEnd_230829] using wordTrace_append hprefix tailTrace_230829
  have hstable : (prefixWord ++ tailWord_230829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230829).length < 2 ^ (prefixWord ++ tailWord_230829).sum := by decide
  have hdescent : baseEnd_230829 < baseStart_230829 := by decide
  rcases family_descends (prefixWord ++ tailWord_230829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230869 : List Nat := [1, 3, 2, 3, 1, 1, 2, 4, 1, 3, 2]
def baseStart_230869 : Nat := 118140960795 + 230869 * 2 ^ 59
def prefixEnd_230869 : Nat := 4983230072969 + 3 ^ 40 * 230869 * 2
def baseEnd_230869 : Nat := 118546765222962457675759

theorem tailTrace_230869 : CollatzResearch.WordTrace tailWord_230869 prefixEnd_230869 118546765222962457675759 := by
  unfold tailWord_230869
  simp only [CollatzResearch.WordTrace]
  refine ⟨8420484200608517131183661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5613656133739011420789107 8420484200608517131183661)
  ·
    refine ⟨3157681575228193924193873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8420484200608517131183661 3157681575228193924193873)
    ·
      refine ⟨2368261181421145443145405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3157681575228193924193873 2368261181421145443145405)
      ·
        refine ⟨888097943032929541179527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2368261181421145443145405 888097943032929541179527)
        ·
          refine ⟨1332146914549394311769291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888097943032929541179527 1332146914549394311769291)
          ·
            refine ⟨1998220371824091467653937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332146914549394311769291 1998220371824091467653937)
            ·
              refine ⟨1498665278868068600740453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1998220371824091467653937 1498665278868068600740453)
              ·
                refine ⟨280999739787762862638835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1498665278868068600740453 280999739787762862638835)
                ·
                  refine ⟨421499609681644293958253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280999739787762862638835 421499609681644293958253)
                  ·
                    refine ⟨158062353630616610234345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 421499609681644293958253 158062353630616610234345)
                    ·
                      refine ⟨118546765222962457675759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 158062353630616610234345 118546765222962457675759)
                      ·
                        rfl

theorem cell23_230869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_230869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230869 prefixEnd_230869 := by exact prefixLift 230869
  have htrace : WordTrace (prefixWord ++ tailWord_230869) baseStart_230869 baseEnd_230869 := by
    simpa [prefixWord, tailWord_230869, baseEnd_230869] using wordTrace_append hprefix tailTrace_230869
  have hstable : (prefixWord ++ tailWord_230869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230869).length < 2 ^ (prefixWord ++ tailWord_230869).sum := by decide
  have hdescent : baseEnd_230869 < baseStart_230869 := by decide
  rcases family_descends (prefixWord ++ tailWord_230869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230893 : List Nat := [1, 5, 1, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_230893 : Nat := 118140960795 + 230893 * 2 ^ 59
def prefixEnd_230893 : Nat := 4983230072969 + 3 ^ 40 * 230893 * 2
def baseEnd_230893 : Nat := 118559088758670363775649

theorem tailTrace_230893 : CollatzResearch.WordTrace tailWord_230893 prefixEnd_230893 118559088758670363775649 := by
  unfold tailWord_230893
  simp only [CollatzResearch.WordTrace]
  refine ⟨8421359552521569230057333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5614239701681046153371555 8421359552521569230057333)
  ·
    refine ⟨789502458048897115317875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8421359552521569230057333 789502458048897115317875)
    ·
      refine ⟨1184253687073345672976813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 789502458048897115317875 1184253687073345672976813)
      ·
        refine ⟨444095132652504627366305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1184253687073345672976813 444095132652504627366305)
        ·
          refine ⟨333071349489378470524729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444095132652504627366305 333071349489378470524729)
          ·
            refine ⟨249803512117033852893547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333071349489378470524729 249803512117033852893547)
            ·
              refine ⟨374705268175550779340321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249803512117033852893547 374705268175550779340321)
              ·
                refine ⟨281028951131663084505241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374705268175550779340321 281028951131663084505241)
                ·
                  refine ⟨210771713348747313378931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281028951131663084505241 210771713348747313378931)
                  ·
                    refine ⟨316157570023120970068397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 210771713348747313378931 316157570023120970068397)
                    ·
                      refine ⟨118559088758670363775649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 316157570023120970068397 118559088758670363775649)
                      ·
                        rfl

theorem cell23_230893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_230893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230893 prefixEnd_230893 := by exact prefixLift 230893
  have htrace : WordTrace (prefixWord ++ tailWord_230893) baseStart_230893 baseEnd_230893 := by
    simpa [prefixWord, tailWord_230893, baseEnd_230893] using wordTrace_append hprefix tailTrace_230893
  have hstable : (prefixWord ++ tailWord_230893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230893).length < 2 ^ (prefixWord ++ tailWord_230893).sum := by decide
  have hdescent : baseEnd_230893 < baseStart_230893 := by decide
  rcases family_descends (prefixWord ++ tailWord_230893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230895 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 4]
def baseStart_230895 : Nat := 118140960795 + 230895 * 2 ^ 59
def prefixEnd_230895 : Nat := 4983230072969 + 3 ^ 40 * 230895 * 2
def baseEnd_230895 : Nat := 118560115719979355950639

theorem tailTrace_230895 : CollatzResearch.WordTrace tailWord_230895 prefixEnd_230895 118560115719979355950639 := by
  unfold tailWord_230895
  simp only [CollatzResearch.WordTrace]
  refine ⟨8421432498514323571630139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5614288332342882381086759 8421432498514323571630139)
  ·
    refine ⟨12632148747771485357445209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8421432498514323571630139 12632148747771485357445209)
    ·
      refine ⟨9474111560828614018083907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12632148747771485357445209 9474111560828614018083907)
      ·
        refine ⟨14211167341242921027125861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9474111560828614018083907 14211167341242921027125861)
        ·
          refine ⟨2664593876483047692586099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14211167341242921027125861 2664593876483047692586099)
          ·
            refine ⟨3996890814724571538879149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2664593876483047692586099 3996890814724571538879149)
            ·
              refine ⟨1498834055521714327079681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3996890814724571538879149 1498834055521714327079681)
              ·
                refine ⟨1124125541641285745309761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1498834055521714327079681 1124125541641285745309761)
                ·
                  refine ⟨843094156230964308982321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1124125541641285745309761 843094156230964308982321)
                  ·
                    refine ⟨632320617173223231736741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 843094156230964308982321 632320617173223231736741)
                    ·
                      refine ⟨118560115719979355950639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 632320617173223231736741 118560115719979355950639)
                      ·
                        rfl

theorem cell23_230895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_230895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230895 prefixEnd_230895 := by exact prefixLift 230895
  have htrace : WordTrace (prefixWord ++ tailWord_230895) baseStart_230895 baseEnd_230895 := by
    simpa [prefixWord, tailWord_230895, baseEnd_230895] using wordTrace_append hprefix tailTrace_230895
  have hstable : (prefixWord ++ tailWord_230895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230895).length < 2 ^ (prefixWord ++ tailWord_230895).sum := by decide
  have hdescent : baseEnd_230895 < baseStart_230895 := by decide
  rcases family_descends (prefixWord ++ tailWord_230895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230899 : List Nat := [1, 1, 1, 2, 2, 2, 2, 6, 2, 2, 2]
def baseStart_230899 : Nat := 118140960795 + 230899 * 2 ^ 59
def prefixEnd_230899 : Nat := 4983230072969 + 3 ^ 40 * 230899 * 2
def baseEnd_230899 : Nat := 118562169642597340300621

theorem tailTrace_230899 : CollatzResearch.WordTrace tailWord_230899 prefixEnd_230899 118562169642597340300621 := by
  unfold tailWord_230899
  simp only [CollatzResearch.WordTrace]
  refine ⟨8421578390499832254775751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5614385593666554836517167 8421578390499832254775751)
  ·
    refine ⟨12632367585749748382163627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8421578390499832254775751 12632367585749748382163627)
    ·
      refine ⟨18948551378624622573245441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12632367585749748382163627 18948551378624622573245441)
      ·
        refine ⟨14211413533968466929934081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18948551378624622573245441 14211413533968466929934081)
        ·
          refine ⟨10658560150476350197450561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14211413533968466929934081 10658560150476350197450561)
          ·
            refine ⟨7993920112857262648087921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10658560150476350197450561 7993920112857262648087921)
            ·
              refine ⟨5995440084642946986065941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7993920112857262648087921 5995440084642946986065941)
              ·
                refine ⟨281036253967638139971841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5995440084642946986065941 281036253967638139971841)
                ·
                  refine ⟨210777190475728604978881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281036253967638139971841 210777190475728604978881)
                  ·
                    refine ⟨158082892856796453734161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 210777190475728604978881 158082892856796453734161)
                    ·
                      refine ⟨118562169642597340300621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 158082892856796453734161 118562169642597340300621)
                      ·
                        rfl

theorem cell23_230899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 2, 2].length) (baseStart_230899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230899 prefixEnd_230899 := by exact prefixLift 230899
  have htrace : WordTrace (prefixWord ++ tailWord_230899) baseStart_230899 baseEnd_230899 := by
    simpa [prefixWord, tailWord_230899, baseEnd_230899] using wordTrace_append hprefix tailTrace_230899
  have hstable : (prefixWord ++ tailWord_230899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230899).length < 2 ^ (prefixWord ++ tailWord_230899).sum := by decide
  have hdescent : baseEnd_230899 < baseStart_230899 := by decide
  rcases family_descends (prefixWord ++ tailWord_230899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230910 : List Nat := [4, 2, 2, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_230910 : Nat := 118140960795 + 230910 * 2 ^ 59
def prefixEnd_230910 : Nat := 4983230072969 + 3 ^ 40 * 230910 * 2
def baseEnd_230910 : Nat := 118567817929796797263071

theorem tailTrace_230910 : CollatzResearch.WordTrace tailWord_230910 prefixEnd_230910 118567817929796797263071 := by
  unfold tailWord_230910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1052747449182497641678273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5614653062306654088950789 1052747449182497641678273)
  ·
    refine ⟨789560586886873231258705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1052747449182497641678273 789560586886873231258705)
    ·
      refine ⟨592170440165154923444029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 789560586886873231258705 592170440165154923444029)
      ·
        refine ⟨222063915061933096291511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 592170440165154923444029 222063915061933096291511)
        ·
          refine ⟨333095872592899644437267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222063915061933096291511 333095872592899644437267)
          ·
            refine ⟨499643808889349466655901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333095872592899644437267 499643808889349466655901)
            ·
              refine ⟨187366428333506049995963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 499643808889349466655901 187366428333506049995963)
              ·
                refine ⟨281049642500259074993945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187366428333506049995963 281049642500259074993945)
                ·
                  refine ⟨210787231875194306245459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281049642500259074993945 210787231875194306245459)
                  ·
                    refine ⟨316180847812791459368189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 210787231875194306245459 316180847812791459368189)
                    ·
                      refine ⟨118567817929796797263071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 316180847812791459368189 118567817929796797263071)
                      ·
                        rfl

theorem cell23_230910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_230910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230910 prefixEnd_230910 := by exact prefixLift 230910
  have htrace : WordTrace (prefixWord ++ tailWord_230910) baseStart_230910 baseEnd_230910 := by
    simpa [prefixWord, tailWord_230910, baseEnd_230910] using wordTrace_append hprefix tailTrace_230910
  have hstable : (prefixWord ++ tailWord_230910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230910).length < 2 ^ (prefixWord ++ tailWord_230910).sum := by decide
  have hdescent : baseEnd_230910 < baseStart_230910 := by decide
  rcases family_descends (prefixWord ++ tailWord_230910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230915 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 3]
def baseStart_230915 : Nat := 118140960795 + 230915 * 2 ^ 59
def prefixEnd_230915 : Nat := 4983230072969 + 3 ^ 40 * 230915 * 2
def baseEnd_230915 : Nat := 118570385333069277700547

theorem tailTrace_230915 : CollatzResearch.WordTrace tailWord_230915 prefixEnd_230915 118570385333069277700547 := by
  unfold tailWord_230915
  simp only [CollatzResearch.WordTrace]
  refine ⟨8422161958441866987358199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5614774638961244658238799 8422161958441866987358199)
  ·
    refine ⟨12633242937662800481037299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8422161958441866987358199 12633242937662800481037299)
    ·
      refine ⟨18949864406494200721555949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12633242937662800481037299 18949864406494200721555949)
      ·
        refine ⟨7106199152435325270583481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18949864406494200721555949 7106199152435325270583481)
        ·
          refine ⟨5329649364326493952937611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7106199152435325270583481 5329649364326493952937611)
          ·
            refine ⟨7994474046489740929406417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5329649364326493952937611 7994474046489740929406417)
            ·
              refine ⟨5995855534867305697054813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7994474046489740929406417 5995855534867305697054813)
              ·
                refine ⟨2248445825575239636395555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5995855534867305697054813 2248445825575239636395555)
                ·
                  refine ⟨3372668738362859454593333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2248445825575239636395555 3372668738362859454593333)
                  ·
                    refine ⟨316187694221518073868125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3372668738362859454593333 316187694221518073868125)
                    ·
                      refine ⟨118570385333069277700547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 316187694221518073868125 118570385333069277700547)
                      ·
                        rfl

theorem cell23_230915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_230915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230915 prefixEnd_230915 := by exact prefixLift 230915
  have htrace : WordTrace (prefixWord ++ tailWord_230915) baseStart_230915 baseEnd_230915 := by
    simpa [prefixWord, tailWord_230915, baseEnd_230915] using wordTrace_append hprefix tailTrace_230915
  have hstable : (prefixWord ++ tailWord_230915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230915).length < 2 ^ (prefixWord ++ tailWord_230915).sum := by decide
  have hdescent : baseEnd_230915 < baseStart_230915 := by decide
  rcases family_descends (prefixWord ++ tailWord_230915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230985 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 2, 4, 4]
def baseStart_230985 : Nat := 118140960795 + 230985 * 2 ^ 59
def prefixEnd_230985 : Nat := 4983230072969 + 3 ^ 40 * 230985 * 2
def baseEnd_230985 : Nat := 118606328978884003825225

theorem tailTrace_230985 : CollatzResearch.WordTrace tailWord_230985 prefixEnd_230985 118606328978884003825225 := by
  unfold tailWord_230985
  simp only [CollatzResearch.WordTrace]
  refine ⟨8424715068188268942406409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5616476712125512628270939 8424715068188268942406409)
  ·
    refine ⟨6318536301141201706804807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8424715068188268942406409 6318536301141201706804807)
    ·
      refine ⟨9477804451711802560207211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6318536301141201706804807 9477804451711802560207211)
      ·
        refine ⟨14216706677567703840310817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9477804451711802560207211 14216706677567703840310817)
        ·
          refine ⟨10662530008175777880233113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14216706677567703840310817 10662530008175777880233113)
          ·
            refine ⟨7996897506131833410174835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10662530008175777880233113 7996897506131833410174835)
            ·
              refine ⟨11995346259197750115262253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7996897506131833410174835 11995346259197750115262253)
              ·
                refine ⟨4498254847199156293223345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11995346259197750115262253 4498254847199156293223345)
                ·
                  refine ⟨3373691135399367219917509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4498254847199156293223345 3373691135399367219917509)
                  ·
                    refine ⟨632567087887381353734533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3373691135399367219917509 632567087887381353734533)
                    ·
                      refine ⟨118606328978884003825225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 632567087887381353734533 118606328978884003825225)
                      ·
                        rfl

theorem cell23_230985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_230985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_230985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_230985 prefixEnd_230985 := by exact prefixLift 230985
  have htrace : WordTrace (prefixWord ++ tailWord_230985) baseStart_230985 baseEnd_230985 := by
    simpa [prefixWord, tailWord_230985, baseEnd_230985] using wordTrace_append hprefix tailTrace_230985
  have hstable : (prefixWord ++ tailWord_230985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230985).length < 2 ^ (prefixWord ++ tailWord_230985).sum := by decide
  have hdescent : baseEnd_230985 < baseStart_230985 := by decide
  rcases family_descends (prefixWord ++ tailWord_230985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231012 : List Nat := [2, 3, 1, 1, 2, 3, 1, 4, 6]
def baseStart_231012 : Nat := 118140960795 + 231012 * 2 ^ 59
def prefixEnd_231012 : Nat := 4983230072969 + 3 ^ 40 * 231012 * 2
def baseEnd_231012 : Nat := 13180021439617266465289

theorem tailTrace_231012 : CollatzResearch.WordTrace tailWord_231012 prefixEnd_231012 13180021439617266465289 := by
  unfold tailWord_231012
  simp only [CollatzResearch.WordTrace]
  refine ⟨4212849919545226276819645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5617133226060301702426193 4212849919545226276819645)
  ·
    refine ⟨1579818719829459853807367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4212849919545226276819645 1579818719829459853807367)
    ·
      refine ⟨2369728079744189780711051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1579818719829459853807367 2369728079744189780711051)
      ·
        refine ⟨3554592119616284671066577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2369728079744189780711051 3554592119616284671066577)
        ·
          refine ⟨2665944089712213503299933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3554592119616284671066577 2665944089712213503299933)
          ·
            refine ⟨999729033642080063737475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2665944089712213503299933 999729033642080063737475)
            ·
              refine ⟨1499593550463120095606213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999729033642080063737475 1499593550463120095606213)
              ·
                refine ⟨281173790711835017926165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1499593550463120095606213 281173790711835017926165)
                ·
                  refine ⟨13180021439617266465289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 281173790711835017926165 13180021439617266465289)
                  ·
                    rfl

theorem cell23_231012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_231012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231012 prefixEnd_231012 := by exact prefixLift 231012
  have htrace : WordTrace (prefixWord ++ tailWord_231012) baseStart_231012 baseEnd_231012 := by
    simpa [prefixWord, tailWord_231012, baseEnd_231012] using wordTrace_append hprefix tailTrace_231012
  have hstable : (prefixWord ++ tailWord_231012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231012).length < 2 ^ (prefixWord ++ tailWord_231012).sum := by decide
  have hdescent : baseEnd_231012 < baseStart_231012 := by decide
  rcases family_descends (prefixWord ++ tailWord_231012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231029 : List Nat := [1, 3, 4, 2, 1, 1, 2, 3, 6]
def baseStart_231029 : Nat := 118140960795 + 231029 * 2 ^ 59
def prefixEnd_231029 : Nat := 4983230072969 + 3 ^ 40 * 231029 * 2
def baseEnd_231029 : Nat := 13180991347520203519447

theorem tailTrace_231029 : CollatzResearch.WordTrace tailWord_231029 prefixEnd_231029 13180991347520203519447 := by
  unfold tailWord_231029
  simp only [CollatzResearch.WordTrace]
  refine ⟨8426319880028864457008141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5617546586685909638005427 8426319880028864457008141)
  ·
    refine ⟨3159869955010824171378053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8426319880028864457008141 3159869955010824171378053)
    ·
      refine ⟨592475616564529532133385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3159869955010824171378053 592475616564529532133385)
      ·
        refine ⟨444356712423397149100039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592475616564529532133385 444356712423397149100039)
        ·
          refine ⟨666535068635095723650059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444356712423397149100039 666535068635095723650059)
          ·
            refine ⟨999802602952643585475089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666535068635095723650059 999802602952643585475089)
            ·
              refine ⟨749851952214482689106317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 999802602952643585475089 749851952214482689106317)
              ·
                refine ⟨281194482080431008414869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 749851952214482689106317 281194482080431008414869)
                ·
                  refine ⟨13180991347520203519447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 281194482080431008414869 13180991347520203519447)
                  ·
                    rfl

theorem cell23_231029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 6].length) (baseStart_231029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231029 prefixEnd_231029 := by exact prefixLift 231029
  have htrace : WordTrace (prefixWord ++ tailWord_231029) baseStart_231029 baseEnd_231029 := by
    simpa [prefixWord, tailWord_231029, baseEnd_231029] using wordTrace_append hprefix tailTrace_231029
  have hstable : (prefixWord ++ tailWord_231029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231029).length < 2 ^ (prefixWord ++ tailWord_231029).sum := by decide
  have hdescent : baseEnd_231029 < baseStart_231029 := by decide
  rcases family_descends (prefixWord ++ tailWord_231029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231035 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 7]
def baseStart_231035 : Nat := 118140960795 + 231035 * 2 ^ 59
def prefixEnd_231035 : Nat := 4983230072969 + 3 ^ 40 * 231035 * 2
def baseEnd_231035 : Nat := 118632003011608808199995

theorem tailTrace_231035 : CollatzResearch.WordTrace tailWord_231035 prefixEnd_231035 118632003011608808199995 := by
  unfold tailWord_231035
  simp only [CollatzResearch.WordTrace]
  refine ⟨8426538718007127481726559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5617692478671418321151039 8426538718007127481726559)
  ·
    refine ⟨12639808077010691222589839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8426538718007127481726559 12639808077010691222589839)
    ·
      refine ⟨18959712115516036833884759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12639808077010691222589839 18959712115516036833884759)
      ·
        refine ⟨28439568173274055250827139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18959712115516036833884759 28439568173274055250827139)
        ·
          refine ⟨42659352259911082876240709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28439568173274055250827139 42659352259911082876240709)
          ·
            refine ⟨7998628548733328039295133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42659352259911082876240709 7998628548733328039295133)
            ·
              refine ⟨2999485705774998014735675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7998628548733328039295133 2999485705774998014735675)
              ·
                refine ⟨4499228558662497022103513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2999485705774998014735675 4499228558662497022103513)
                ·
                  refine ⟨3374421418996872766577635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4499228558662497022103513 3374421418996872766577635)
                  ·
                    refine ⟨5061632128495309149866453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3374421418996872766577635 5061632128495309149866453)
                    ·
                      refine ⟨118632003011608808199995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5061632128495309149866453 118632003011608808199995)
                      ·
                        rfl

theorem cell23_231035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 7].length) (baseStart_231035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231035 prefixEnd_231035 := by exact prefixLift 231035
  have htrace : WordTrace (prefixWord ++ tailWord_231035) baseStart_231035 baseEnd_231035 := by
    simpa [prefixWord, tailWord_231035, baseEnd_231035] using wordTrace_append hprefix tailTrace_231035
  have hstable : (prefixWord ++ tailWord_231035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231035).length < 2 ^ (prefixWord ++ tailWord_231035).sum := by decide
  have hdescent : baseEnd_231035 < baseStart_231035 := by decide
  rcases family_descends (prefixWord ++ tailWord_231035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231073 : List Nat := [1, 2, 3, 3, 2, 1, 2, 4, 1, 1, 3]
def baseStart_231073 : Nat := 118140960795 + 231073 * 2 ^ 59
def prefixEnd_231073 : Nat := 4983230072969 + 3 ^ 40 * 231073 * 2
def baseEnd_231073 : Nat := 118651515276479659524821

theorem tailTrace_231073 : CollatzResearch.WordTrace tailWord_231073 prefixEnd_231073 118651515276479659524821 := by
  unfold tailWord_231073
  simp only [CollatzResearch.WordTrace]
  refine ⟨8427924691869459971609873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5618616461246306647739915 8427924691869459971609873)
  ·
    refine ⟨6320943518902094978707405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8427924691869459971609873 6320943518902094978707405)
    ·
      refine ⟨2370353819588285617015277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6320943518902094978707405 2370353819588285617015277)
      ·
        refine ⟨888882682345607106380729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2370353819588285617015277 888882682345607106380729)
        ·
          refine ⟨666662011759205329785547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 888882682345607106380729 666662011759205329785547)
          ·
            refine ⟨999993017638807994678321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666662011759205329785547 999993017638807994678321)
            ·
              refine ⟨749994763229105996008741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 999993017638807994678321 749994763229105996008741)
              ·
                refine ⟨140624018105457374251639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 749994763229105996008741 140624018105457374251639)
                ·
                  refine ⟨210936027158186061377459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140624018105457374251639 210936027158186061377459)
                  ·
                    refine ⟨316404040737279092066189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 210936027158186061377459 316404040737279092066189)
                    ·
                      refine ⟨118651515276479659524821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 316404040737279092066189 118651515276479659524821)
                      ·
                        rfl

theorem cell23_231073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_231073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231073 prefixEnd_231073 := by exact prefixLift 231073
  have htrace : WordTrace (prefixWord ++ tailWord_231073) baseStart_231073 baseEnd_231073 := by
    simpa [prefixWord, tailWord_231073, baseEnd_231073] using wordTrace_append hprefix tailTrace_231073
  have hstable : (prefixWord ++ tailWord_231073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231073).length < 2 ^ (prefixWord ++ tailWord_231073).sum := by decide
  have hdescent : baseEnd_231073 < baseStart_231073 := by decide
  rcases family_descends (prefixWord ++ tailWord_231073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231080 : List Nat := [2, 1, 7, 1, 1, 1, 3, 1, 6]
def baseStart_231080 : Nat := 118140960795 + 231080 * 2 ^ 59
def prefixEnd_231080 : Nat := 4983230072969 + 3 ^ 40 * 231080 * 2
def baseEnd_231080 : Nat := 13183901071229014681921

theorem tailTrace_231080 : CollatzResearch.WordTrace tailWord_231080 prefixEnd_231080 13183901071229014681921 := by
  unfold tailWord_231080
  simp only [CollatzResearch.WordTrace]
  refine ⟨4214090001422050083557347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5618786668562733444743129 4214090001422050083557347)
  ·
    refine ⟨6321135002133075125336021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4214090001422050083557347 6321135002133075125336021)
    ·
      refine ⟨148151601612493948250063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 6321135002133075125336021 148151601612493948250063)
      ·
        refine ⟨222227402418740922375095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148151601612493948250063 222227402418740922375095)
        ·
          refine ⟨333341103628111383562643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222227402418740922375095 333341103628111383562643)
          ·
            refine ⟨500011655442167075343965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333341103628111383562643 500011655442167075343965)
            ·
              refine ⟨187504370790812653253987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 500011655442167075343965 187504370790812653253987)
              ·
                refine ⟨281256556186218979880981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187504370790812653253987 281256556186218979880981)
                ·
                  refine ⟨13183901071229014681921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 281256556186218979880981 13183901071229014681921)
                  ·
                    rfl

theorem cell23_231080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 6].length) (baseStart_231080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231080 prefixEnd_231080 := by exact prefixLift 231080
  have htrace : WordTrace (prefixWord ++ tailWord_231080) baseStart_231080 baseEnd_231080 := by
    simpa [prefixWord, tailWord_231080, baseEnd_231080] using wordTrace_append hprefix tailTrace_231080
  have hstable : (prefixWord ++ tailWord_231080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231080).length < 2 ^ (prefixWord ++ tailWord_231080).sum := by decide
  have hdescent : baseEnd_231080 < baseStart_231080 := by decide
  rcases family_descends (prefixWord ++ tailWord_231080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231116 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 1, 1, 5]
def baseStart_231116 : Nat := 118140960795 + 231116 * 2 ^ 59
def prefixEnd_231116 : Nat := 4983230072969 + 3 ^ 40 * 231116 * 2
def baseEnd_231116 : Nat := 118673594944622991287123

theorem tailTrace_231116 : CollatzResearch.WordTrace tailWord_231116 prefixEnd_231116 118673594944622991287123 := by
  unfold tailWord_231116
  simp only [CollatzResearch.WordTrace]
  refine ⟨4214746515356839157712601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5619662020475785543616801 4214746515356839157712601)
  ·
    refine ⟨3161059886517629368284451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4214746515356839157712601 3161059886517629368284451)
    ·
      refine ⟨4741589829776444052426677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3161059886517629368284451 4741589829776444052426677)
      ·
        refine ⟨444524046541541629915001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4741589829776444052426677 444524046541541629915001)
        ·
          refine ⟨333393034906156222436251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444524046541541629915001 333393034906156222436251)
          ·
            refine ⟨500089552359234333654377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333393034906156222436251 500089552359234333654377)
            ·
              refine ⟨375067164269425750240783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500089552359234333654377 375067164269425750240783)
              ·
                refine ⟨562600746404138625361175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375067164269425750240783 562600746404138625361175)
                ·
                  refine ⟨843901119606207938041763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562600746404138625361175 843901119606207938041763)
                  ·
                    refine ⟨1265851679409311907062645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 843901119606207938041763 1265851679409311907062645)
                    ·
                      refine ⟨118673594944622991287123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1265851679409311907062645 118673594944622991287123)
                      ·
                        rfl

theorem cell23_231116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_231116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231116 prefixEnd_231116 := by exact prefixLift 231116
  have htrace : WordTrace (prefixWord ++ tailWord_231116) baseStart_231116 baseEnd_231116 := by
    simpa [prefixWord, tailWord_231116, baseEnd_231116] using wordTrace_append hprefix tailTrace_231116
  have hstable : (prefixWord ++ tailWord_231116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231116).length < 2 ^ (prefixWord ++ tailWord_231116).sum := by decide
  have hdescent : baseEnd_231116 < baseStart_231116 := by decide
  rcases family_descends (prefixWord ++ tailWord_231116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231152 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 4]
def baseStart_231152 : Nat := 118140960795 + 231152 * 2 ^ 59
def prefixEnd_231152 : Nat := 4983230072969 + 3 ^ 40 * 231152 * 2
def baseEnd_231152 : Nat := 118692080248184850436957

theorem tailTrace_231152 : CollatzResearch.WordTrace tailWord_231152 prefixEnd_231152 118692080248184850436957 := by
  unfold tailWord_231152
  simp only [CollatzResearch.WordTrace]
  refine ⟨4215403029291628231867855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5620537372388837642490473 4215403029291628231867855)
  ·
    refine ⟨6323104543937442347801783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4215403029291628231867855 6323104543937442347801783)
    ·
      refine ⟨9484656815906163521702675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6323104543937442347801783 9484656815906163521702675)
      ·
        refine ⟨14226985223859245282554013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9484656815906163521702675 14226985223859245282554013)
        ·
          refine ⟨5335119458947216980957755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14226985223859245282554013 5335119458947216980957755)
          ·
            refine ⟨8002679188420825471436633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5335119458947216980957755 8002679188420825471436633)
            ·
              refine ⟨6002009391315619103577475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8002679188420825471436633 6002009391315619103577475)
              ·
                refine ⟨9003014086973428655366213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6002009391315619103577475 9003014086973428655366213)
                ·
                  refine ⟨1688065141307517872881165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9003014086973428655366213 1688065141307517872881165)
                  ·
                    refine ⟨633024427990319202330437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1688065141307517872881165 633024427990319202330437)
                    ·
                      refine ⟨118692080248184850436957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 633024427990319202330437 118692080248184850436957)
                      ·
                        rfl

theorem cell23_231152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_231152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231152 prefixEnd_231152 := by exact prefixLift 231152
  have htrace : WordTrace (prefixWord ++ tailWord_231152) baseStart_231152 baseEnd_231152 := by
    simpa [prefixWord, tailWord_231152, baseEnd_231152] using wordTrace_append hprefix tailTrace_231152
  have hstable : (prefixWord ++ tailWord_231152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231152).length < 2 ^ (prefixWord ++ tailWord_231152).sum := by decide
  have hdescent : baseEnd_231152 < baseStart_231152 := by decide
  rcases family_descends (prefixWord ++ tailWord_231152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231162 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 4, 6]
def baseStart_231162 : Nat := 118140960795 + 231162 * 2 ^ 59
def prefixEnd_231162 : Nat := 4983230072969 + 3 ^ 40 * 231162 * 2
def baseEnd_231162 : Nat := 39565738351576603770637

theorem tailTrace_231162 : CollatzResearch.WordTrace tailWord_231162 prefixEnd_231162 39565738351576603770637 := by
  unfold tailWord_231162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2107792697136757042899935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5620780525698018781066493 2107792697136757042899935)
  ·
    refine ⟨3161689045705135564349903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2107792697136757042899935 3161689045705135564349903)
    ·
      refine ⟨4742533568557703346524855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3161689045705135564349903 4742533568557703346524855)
      ·
        refine ⟨7113800352836555019787283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4742533568557703346524855 7113800352836555019787283)
        ·
          refine ⟨10670700529254832529680925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7113800352836555019787283 10670700529254832529680925)
          ·
            refine ⟨4001512698470562198630347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10670700529254832529680925 4001512698470562198630347)
            ·
              refine ⟨6002269047705843297945521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4001512698470562198630347 6002269047705843297945521)
              ·
                refine ⟨4501701785779382473459141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6002269047705843297945521 4501701785779382473459141)
                ·
                  refine ⟨844069084833634213773589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4501701785779382473459141 844069084833634213773589)
                  ·
                    refine ⟨39565738351576603770637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 844069084833634213773589 39565738351576603770637)
                    ·
                      rfl

theorem cell23_231162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_231162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231162 prefixEnd_231162 := by exact prefixLift 231162
  have htrace : WordTrace (prefixWord ++ tailWord_231162) baseStart_231162 baseEnd_231162 := by
    simpa [prefixWord, tailWord_231162, baseEnd_231162] using wordTrace_append hprefix tailTrace_231162
  have hstable : (prefixWord ++ tailWord_231162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231162).length < 2 ^ (prefixWord ++ tailWord_231162).sum := by decide
  have hdescent : baseEnd_231162 < baseStart_231162 := by decide
  rcases family_descends (prefixWord ++ tailWord_231162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231186 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_231186 : Nat := 118140960795 + 231186 * 2 ^ 59
def prefixEnd_231186 : Nat := 4983230072969 + 3 ^ 40 * 231186 * 2
def baseEnd_231186 : Nat := 118709538590437717411801

theorem tailTrace_231186 : CollatzResearch.WordTrace tailWord_231186 prefixEnd_231186 118709538590437717411801 := by
  unfold tailWord_231186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2108011535115020067618353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5621364093640053513648941 2108011535115020067618353)
  ·
    refine ⟨1581008651336265050713765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2108011535115020067618353 1581008651336265050713765)
    ·
      refine ⟨296439122125549697008831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1581008651336265050713765 296439122125549697008831)
      ·
        refine ⟨444658683188324545513247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296439122125549697008831 444658683188324545513247)
        ·
          refine ⟨666988024782486818269871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444658683188324545513247 666988024782486818269871)
          ·
            refine ⟨1000482037173730227404807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666988024782486818269871 1000482037173730227404807)
            ·
              refine ⟨1500723055760595341107211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000482037173730227404807 1500723055760595341107211)
              ·
                refine ⟨2251084583640893011660817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1500723055760595341107211 2251084583640893011660817)
                ·
                  refine ⟨1688313437730669758745613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2251084583640893011660817 1688313437730669758745613)
                  ·
                    refine ⟨633117539149001159529605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1688313437730669758745613 633117539149001159529605)
                    ·
                      refine ⟨118709538590437717411801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 633117539149001159529605 118709538590437717411801)
                      ·
                        rfl

theorem cell23_231186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_231186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231186 prefixEnd_231186 := by exact prefixLift 231186
  have htrace : WordTrace (prefixWord ++ tailWord_231186) baseStart_231186 baseEnd_231186 := by
    simpa [prefixWord, tailWord_231186, baseEnd_231186] using wordTrace_append hprefix tailTrace_231186
  have hstable : (prefixWord ++ tailWord_231186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231186).length < 2 ^ (prefixWord ++ tailWord_231186).sum := by decide
  have hdescent : baseEnd_231186 < baseStart_231186 := by decide
  rcases family_descends (prefixWord ++ tailWord_231186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231189 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 2, 4, 3]
def baseStart_231189 : Nat := 118140960795 + 231189 * 2 ^ 59
def prefixEnd_231189 : Nat := 4983230072969 + 3 ^ 40 * 231189 * 2
def baseEnd_231189 : Nat := 118711079032401205674287

theorem tailTrace_231189 : CollatzResearch.WordTrace tailWord_231189 prefixEnd_231189 118711079032401205674287 := by
  unfold tailWord_231189
  simp only [CollatzResearch.WordTrace]
  refine ⟨8432155559449211782832621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5621437039632807855221747 8432155559449211782832621)
  ·
    refine ⟨3162058334793454418562233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8432155559449211782832621 3162058334793454418562233)
    ·
      refine ⟨2371543751095090813921675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3162058334793454418562233 2371543751095090813921675)
      ·
        refine ⟨3557315626642636220882513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2371543751095090813921675 3557315626642636220882513)
        ·
          refine ⟨2667986719981977165661885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3557315626642636220882513 2667986719981977165661885)
          ·
            refine ⟨1000495019993241437123207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2667986719981977165661885 1000495019993241437123207)
            ·
              refine ⟨1500742529989862155684811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000495019993241437123207 1500742529989862155684811)
              ·
                refine ⟨2251113794984793233527217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1500742529989862155684811 2251113794984793233527217)
                ·
                  refine ⟨1688335346238594925145413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2251113794984793233527217 1688335346238594925145413)
                  ·
                    refine ⟨316562877419736548464765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1688335346238594925145413 316562877419736548464765)
                    ·
                      refine ⟨118711079032401205674287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 316562877419736548464765 118711079032401205674287)
                      ·
                        rfl

theorem cell23_231189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_231189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231189 prefixEnd_231189 := by exact prefixLift 231189
  have htrace : WordTrace (prefixWord ++ tailWord_231189) baseStart_231189 baseEnd_231189 := by
    simpa [prefixWord, tailWord_231189, baseEnd_231189] using wordTrace_append hprefix tailTrace_231189
  have hstable : (prefixWord ++ tailWord_231189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231189).length < 2 ^ (prefixWord ++ tailWord_231189).sum := by decide
  have hdescent : baseEnd_231189 < baseStart_231189 := by decide
  rcases family_descends (prefixWord ++ tailWord_231189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231199 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 4]
def baseStart_231199 : Nat := 118140960795 + 231199 * 2 ^ 59
def prefixEnd_231199 : Nat := 4983230072969 + 3 ^ 40 * 231199 * 2
def baseEnd_231199 : Nat := 118716213838946166549241

theorem tailTrace_231199 : CollatzResearch.WordTrace tailWord_231199 prefixEnd_231199 118716213838946166549241 := by
  unfold tailWord_231199
  simp only [CollatzResearch.WordTrace]
  refine ⟨8432520289412983490696651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5621680192941988993797767 8432520289412983490696651)
  ·
    refine ⟨12648780434119475236044977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8432520289412983490696651 12648780434119475236044977)
    ·
      refine ⟨9486585325589606427033733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12648780434119475236044977 9486585325589606427033733)
      ·
        refine ⟨1778734748548051205068825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9486585325589606427033733 1778734748548051205068825)
        ·
          refine ⟨1334051061411038403801619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1778734748548051205068825 1334051061411038403801619)
          ·
            refine ⟨2001076592116557605702429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334051061411038403801619 2001076592116557605702429)
            ·
              refine ⟨750403722043709102138411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2001076592116557605702429 750403722043709102138411)
              ·
                refine ⟨1125605583065563653207617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750403722043709102138411 1125605583065563653207617)
                ·
                  refine ⟨844204187299172739905713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1125605583065563653207617 844204187299172739905713)
                  ·
                    refine ⟨633153140474379554929285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 844204187299172739905713 633153140474379554929285)
                    ·
                      refine ⟨118716213838946166549241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 633153140474379554929285 118716213838946166549241)
                      ·
                        rfl

theorem cell23_231199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_231199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231199 prefixEnd_231199 := by exact prefixLift 231199
  have htrace : WordTrace (prefixWord ++ tailWord_231199) baseStart_231199 baseEnd_231199 := by
    simpa [prefixWord, tailWord_231199, baseEnd_231199] using wordTrace_append hprefix tailTrace_231199
  have hstable : (prefixWord ++ tailWord_231199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231199).length < 2 ^ (prefixWord ++ tailWord_231199).sum := by decide
  have hdescent : baseEnd_231199 < baseStart_231199 := by decide
  rcases family_descends (prefixWord ++ tailWord_231199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231203 : List Nat := [1, 1, 1, 4, 2, 1, 4, 3, 2, 2, 2]
def baseStart_231203 : Nat := 118140960795 + 231203 * 2 ^ 59
def prefixEnd_231203 : Nat := 4983230072969 + 3 ^ 40 * 231203 * 2
def baseEnd_231203 : Nat := 118718267761564150899223

theorem tailTrace_231203 : CollatzResearch.WordTrace tailWord_231203 prefixEnd_231203 118718267761564150899223 := by
  unfold tailWord_231203
  simp only [CollatzResearch.WordTrace]
  refine ⟨8432666181398492173842263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5621777454265661449228175 8432666181398492173842263)
  ·
    refine ⟨12648999272097738260763395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8432666181398492173842263 12648999272097738260763395)
    ·
      refine ⟨18973498908146607391145093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12648999272097738260763395 18973498908146607391145093)
      ·
        refine ⟨3557531045277488885839705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18973498908146607391145093 3557531045277488885839705)
        ·
          refine ⟨2668148283958116664379779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3557531045277488885839705 2668148283958116664379779)
          ·
            refine ⟨4002222425937174996569669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2668148283958116664379779 4002222425937174996569669)
            ·
              refine ⟨750416704863220311856813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4002222425937174996569669 750416704863220311856813)
              ·
                refine ⟨281406264323707616946305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 750416704863220311856813 281406264323707616946305)
                ·
                  refine ⟨211054698242780712709729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281406264323707616946305 211054698242780712709729)
                  ·
                    refine ⟨158291023682085534532297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 211054698242780712709729 158291023682085534532297)
                    ·
                      refine ⟨118718267761564150899223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 158291023682085534532297 118718267761564150899223)
                      ·
                        rfl

theorem cell23_231203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_231203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231203 prefixEnd_231203 := by exact prefixLift 231203
  have htrace : WordTrace (prefixWord ++ tailWord_231203) baseStart_231203 baseEnd_231203 := by
    simpa [prefixWord, tailWord_231203, baseEnd_231203] using wordTrace_append hprefix tailTrace_231203
  have hstable : (prefixWord ++ tailWord_231203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231203).length < 2 ^ (prefixWord ++ tailWord_231203).sum := by decide
  have hdescent : baseEnd_231203 < baseStart_231203 := by decide
  rcases family_descends (prefixWord ++ tailWord_231203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231226 : List Nat := [3, 1, 1, 1, 5, 1, 1, 5, 5]
def baseStart_231226 : Nat := 118140960795 + 231226 * 2 ^ 59
def prefixEnd_231226 : Nat := 4983230072969 + 3 ^ 40 * 231226 * 2
def baseEnd_231226 : Nat := 13192230868513062323513

theorem tailTrace_231226 : CollatzResearch.WordTrace tailWord_231226 prefixEnd_231226 13192230868513062323513 := by
  unfold tailWord_231226
  simp only [CollatzResearch.WordTrace]
  refine ⟨2108376265078791775482383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5622336706876778067953021 2108376265078791775482383)
  ·
    refine ⟨3162564397618187663223575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2108376265078791775482383 3162564397618187663223575)
    ·
      refine ⟨4743846596427281494835363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3162564397618187663223575 4743846596427281494835363)
      ·
        refine ⟨7115769894640922242253045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4743846596427281494835363 7115769894640922242253045)
        ·
          refine ⟨667103427622586460211223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7115769894640922242253045 667103427622586460211223)
          ·
            refine ⟨1000655141433879690316835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667103427622586460211223 1000655141433879690316835)
            ·
              refine ⟨1500982712150819535475253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000655141433879690316835 1500982712150819535475253)
              ·
                refine ⟨140717129264139331450805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1500982712150819535475253 140717129264139331450805)
                ·
                  refine ⟨13192230868513062323513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140717129264139331450805 13192230868513062323513)
                  ·
                    rfl

theorem cell23_231226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 5].length) (baseStart_231226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231226 prefixEnd_231226 := by exact prefixLift 231226
  have htrace : WordTrace (prefixWord ++ tailWord_231226) baseStart_231226 baseEnd_231226 := by
    simpa [prefixWord, tailWord_231226, baseEnd_231226] using wordTrace_append hprefix tailTrace_231226
  have hstable : (prefixWord ++ tailWord_231226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231226).length < 2 ^ (prefixWord ++ tailWord_231226).sum := by decide
  have hdescent : baseEnd_231226 < baseStart_231226 := by decide
  rcases family_descends (prefixWord ++ tailWord_231226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231239 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 2, 5]
def baseStart_231239 : Nat := 118140960795 + 231239 * 2 ^ 59
def prefixEnd_231239 : Nat := 4983230072969 + 3 ^ 40 * 231239 * 2
def baseEnd_231239 : Nat := 39578917688375336683019

theorem tailTrace_231239 : CollatzResearch.WordTrace tailWord_231239 prefixEnd_231239 39578917688375336683019 := by
  unfold tailWord_231239
  simp only [CollatzResearch.WordTrace]
  refine ⟨8433979209268070322152771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5622652806178713548101847 8433979209268070322152771)
  ·
    refine ⟨12650968813902105483229157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8433979209268070322152771 12650968813902105483229157)
    ·
      refine ⟨2372056652606644778105467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12650968813902105483229157 2372056652606644778105467)
      ·
        refine ⟨3558084978909967167158201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2372056652606644778105467 3558084978909967167158201)
        ·
          refine ⟨2668563734182475375368651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3558084978909967167158201 2668563734182475375368651)
          ·
            refine ⟨4002845601273713063052977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2668563734182475375368651 4002845601273713063052977)
            ·
              refine ⟨3002134200955284797289733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4002845601273713063052977 3002134200955284797289733)
              ·
                refine ⟨562900162679115899491825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3002134200955284797289733 562900162679115899491825)
                ·
                  refine ⟨422175122009336924618869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562900162679115899491825 422175122009336924618869)
                  ·
                    refine ⟨39578917688375336683019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 422175122009336924618869 39578917688375336683019)
                    ·
                      rfl

theorem cell23_231239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_231239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231239 prefixEnd_231239 := by exact prefixLift 231239
  have htrace : WordTrace (prefixWord ++ tailWord_231239) baseStart_231239 baseEnd_231239 := by
    simpa [prefixWord, tailWord_231239, baseEnd_231239] using wordTrace_append hprefix tailTrace_231239
  have hstable : (prefixWord ++ tailWord_231239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231239).length < 2 ^ (prefixWord ++ tailWord_231239).sum := by decide
  have hdescent : baseEnd_231239 < baseStart_231239 := by decide
  rcases family_descends (prefixWord ++ tailWord_231239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231296 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 3]
def baseStart_231296 : Nat := 118140960795 + 231296 * 2 ^ 59
def prefixEnd_231296 : Nat := 4983230072969 + 3 ^ 40 * 231296 * 2
def baseEnd_231296 : Nat := 118766021462432287036295

theorem tailTrace_231296 : CollatzResearch.WordTrace tailWord_231296 prefixEnd_231296 118766021462432287036295 := by
  unfold tailWord_231296
  simp only [CollatzResearch.WordTrace]
  refine ⟨4218029085030784528488871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5624038780041046037985161 4218029085030784528488871)
  ·
    refine ⟨6327043627546176792733307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4218029085030784528488871 6327043627546176792733307)
    ·
      refine ⟨9490565441319265189099961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6327043627546176792733307 9490565441319265189099961)
      ·
        refine ⟨7117924080989448891824971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9490565441319265189099961 7117924080989448891824971)
        ·
          refine ⟨10676886121484173337737457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7117924080989448891824971 10676886121484173337737457)
          ·
            refine ⟨8007664591113130003303093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10676886121484173337737457 8007664591113130003303093)
            ·
              refine ⟨750718555416855937809665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8007664591113130003303093 750718555416855937809665)
              ·
                refine ⟨563038916562641953357249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750718555416855937809665 563038916562641953357249)
                ·
                  refine ⟨422279187421981465017937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563038916562641953357249 422279187421981465017937)
                  ·
                    refine ⟨316709390566486098763453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 422279187421981465017937 316709390566486098763453)
                    ·
                      refine ⟨118766021462432287036295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 316709390566486098763453 118766021462432287036295)
                      ·
                        rfl

theorem cell23_231296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_231296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231296 prefixEnd_231296 := by exact prefixLift 231296
  have htrace : WordTrace (prefixWord ++ tailWord_231296) baseStart_231296 baseEnd_231296 := by
    simpa [prefixWord, tailWord_231296, baseEnd_231296] using wordTrace_append hprefix tailTrace_231296
  have hstable : (prefixWord ++ tailWord_231296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231296).length < 2 ^ (prefixWord ++ tailWord_231296).sum := by decide
  have hdescent : baseEnd_231296 < baseStart_231296 := by decide
  rcases family_descends (prefixWord ++ tailWord_231296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231299 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 8]
def baseStart_231299 : Nat := 118140960795 + 231299 * 2 ^ 59
def prefixEnd_231299 : Nat := 4983230072969 + 3 ^ 40 * 231299 * 2
def baseEnd_231299 : Nat := 13196395767155086144309

theorem tailTrace_231299 : CollatzResearch.WordTrace tailWord_231299 prefixEnd_231299 13196395767155086144309 := by
  unfold tailWord_231299
  simp only [CollatzResearch.WordTrace]
  refine ⟨8436167589050700569336951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5624111726033800379557967 8436167589050700569336951)
  ·
    refine ⟨12654251383576050854005427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8436167589050700569336951 12654251383576050854005427)
    ·
      refine ⟨18981377075364076281008141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12654251383576050854005427 18981377075364076281008141)
      ·
        refine ⟨7118016403261528605378053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18981377075364076281008141 7118016403261528605378053)
        ·
          refine ⟨1334628075611536613508385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7118016403261528605378053 1334628075611536613508385)
          ·
            refine ⟨1000971056708652460131289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1334628075611536613508385 1000971056708652460131289)
            ·
              refine ⟨750728292531489345098467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1000971056708652460131289 750728292531489345098467)
              ·
                refine ⟨1126092438797234017647701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750728292531489345098467 1126092438797234017647701)
                ·
                  refine ⟨13196395767155086144309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1126092438797234017647701 13196395767155086144309)
                  ·
                    rfl

theorem cell23_231299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 8].length) (baseStart_231299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231299 prefixEnd_231299 := by exact prefixLift 231299
  have htrace : WordTrace (prefixWord ++ tailWord_231299) baseStart_231299 baseEnd_231299 := by
    simpa [prefixWord, tailWord_231299, baseEnd_231299] using wordTrace_append hprefix tailTrace_231299
  have hstable : (prefixWord ++ tailWord_231299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231299).length < 2 ^ (prefixWord ++ tailWord_231299).sum := by decide
  have hdescent : baseEnd_231299 < baseStart_231299 := by decide
  rcases family_descends (prefixWord ++ tailWord_231299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231330 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_231330 : Nat := 118140960795 + 231330 * 2 ^ 59
def prefixEnd_231330 : Nat := 4983230072969 + 3 ^ 40 * 231330 * 2
def baseEnd_231330 : Nat := 118783479804685154011139

theorem tailTrace_231330 : CollatzResearch.WordTrace tailWord_231330 prefixEnd_231330 118783479804685154011139 := by
  unfold tailWord_231330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2109324562984598215928861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5624865501292261909143629 2109324562984598215928861)
  ·
    refine ⟨790996711119224330973323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2109324562984598215928861 790996711119224330973323)
    ·
      refine ⟨1186495066678836496459985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 790996711119224330973323 1186495066678836496459985)
      ·
        refine ⟨889871300009127372344989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1186495066678836496459985 889871300009127372344989)
        ·
          refine ⟨333701737503422764629371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 889871300009127372344989 333701737503422764629371)
          ·
            refine ⟨500552606255134146944057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333701737503422764629371 500552606255134146944057)
            ·
              refine ⟨375414454691350610208043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500552606255134146944057 375414454691350610208043)
              ·
                refine ⟨563121682037025915312065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375414454691350610208043 563121682037025915312065)
                ·
                  refine ⟨422341261527769436484049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563121682037025915312065 422341261527769436484049)
                  ·
                    refine ⟨316755946145827077363037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 422341261527769436484049 316755946145827077363037)
                    ·
                      refine ⟨118783479804685154011139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 316755946145827077363037 118783479804685154011139)
                      ·
                        rfl

theorem cell23_231330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_231330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231330 prefixEnd_231330 := by exact prefixLift 231330
  have htrace : WordTrace (prefixWord ++ tailWord_231330) baseStart_231330 baseEnd_231330 := by
    simpa [prefixWord, tailWord_231330, baseEnd_231330] using wordTrace_append hprefix tailTrace_231330
  have hstable : (prefixWord ++ tailWord_231330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231330).length < 2 ^ (prefixWord ++ tailWord_231330).sum := by decide
  have hdescent : baseEnd_231330 < baseStart_231330 := by decide
  rcases family_descends (prefixWord ++ tailWord_231330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231346 : List Nat := [3, 2, 1, 1, 1, 1, 1, 7, 1, 5]
def baseStart_231346 : Nat := 118140960795 + 231346 * 2 ^ 59
def prefixEnd_231346 : Nat := 4983230072969 + 3 ^ 40 * 231346 * 2
def baseEnd_231346 : Nat := 39597231831719030470355

theorem tailTrace_231346 : CollatzResearch.WordTrace tailWord_231346 prefixEnd_231346 39597231831719030470355 := by
  unfold tailWord_231346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2109470454970106899074473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5625254546586951730865261 2109470454970106899074473)
  ·
    refine ⟨1582102841227580174305855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2109470454970106899074473 1582102841227580174305855)
    ·
      refine ⟨2373154261841370261458783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1582102841227580174305855 2373154261841370261458783)
      ·
        refine ⟨3559731392762055392188175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2373154261841370261458783 3559731392762055392188175)
        ·
          refine ⟨5339597089143083088282263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3559731392762055392188175 5339597089143083088282263)
          ·
            refine ⟨8009395633714624632423395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5339597089143083088282263 8009395633714624632423395)
            ·
              refine ⟨12014093450571936948635093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8009395633714624632423395 12014093450571936948635093)
              ·
                refine ⟨281580315247779772233635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12014093450571936948635093 281580315247779772233635)
                ·
                  refine ⟨422370472871669658350453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281580315247779772233635 422370472871669658350453)
                  ·
                    refine ⟨39597231831719030470355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 422370472871669658350453 39597231831719030470355)
                    ·
                      rfl

theorem cell23_231346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_231346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231346 prefixEnd_231346 := by exact prefixLift 231346
  have htrace : WordTrace (prefixWord ++ tailWord_231346) baseStart_231346 baseEnd_231346 := by
    simpa [prefixWord, tailWord_231346, baseEnd_231346] using wordTrace_append hprefix tailTrace_231346
  have hstable : (prefixWord ++ tailWord_231346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231346).length < 2 ^ (prefixWord ++ tailWord_231346).sum := by decide
  have hdescent : baseEnd_231346 < baseStart_231346 := by decide
  rcases family_descends (prefixWord ++ tailWord_231346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
