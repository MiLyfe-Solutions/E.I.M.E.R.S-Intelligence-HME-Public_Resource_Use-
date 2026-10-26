import V185TrunkScan23Chunk0224

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1330431 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 4]
def baseStart_1330431 : Nat := 118140960795 + 1330431 * 2 ^ 59
def prefixEnd_1330431 : Nat := 4983230072969 + 3 ^ 40 * 1330431 * 2
def baseEnd_1330431 : Nat := 683150580641989416293965

theorem tailTrace_1330431 : CollatzResearch.WordTrace tailWord_1330431 prefixEnd_1330431 683150580641989416293965 := by
  unfold tailWord_1330431
  simp only [CollatzResearch.WordTrace]
  refine ⟨48524805043083181370039147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32349870028722120913359431 48524805043083181370039147)
  ·
    refine ⟨72787207564624772055058721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48524805043083181370039147 72787207564624772055058721)
    ·
      refine ⟨54590405673468579041294041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72787207564624772055058721 54590405673468579041294041)
      ·
        refine ⟨40942804255101434280970531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54590405673468579041294041 40942804255101434280970531)
        ·
          refine ⟨61414206382652151421455797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40942804255101434280970531 61414206382652151421455797)
          ·
            refine ⟨5757581848373639195761481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61414206382652151421455797 5757581848373639195761481)
            ·
              refine ⟨4318186386280229396821111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5757581848373639195761481 4318186386280229396821111)
              ·
                refine ⟨6477279579420344095231667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4318186386280229396821111 6477279579420344095231667)
                ·
                  refine ⟨9715919369130516142847501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6477279579420344095231667 9715919369130516142847501)
                  ·
                    refine ⟨3643469763423943553567813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9715919369130516142847501 3643469763423943553567813)
                    ·
                      refine ⟨683150580641989416293965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3643469763423943553567813 683150580641989416293965)
                      ·
                        rfl

theorem cell23_1330431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_1330431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330431 prefixEnd_1330431 := by exact prefixLift 1330431
  have htrace : WordTrace (prefixWord ++ tailWord_1330431) baseStart_1330431 baseEnd_1330431 := by
    simpa [prefixWord, tailWord_1330431, baseEnd_1330431] using wordTrace_append hprefix tailTrace_1330431
  have hstable : (prefixWord ++ tailWord_1330431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330431).length < 2 ^ (prefixWord ++ tailWord_1330431).sum := by decide
  have hdescent : baseEnd_1330431 < baseStart_1330431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330468 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 4, 2, 3]
def baseStart_1330468 : Nat := 118140960795 + 1330468 * 2 ^ 59
def prefixEnd_1330468 : Nat := 4983230072969 + 3 ^ 40 * 1330468 * 2
def baseEnd_1330468 : Nat := 683169579426205771531295

theorem tailTrace_1330468 : CollatzResearch.WordTrace tailWord_1330468 prefixEnd_1330468 683169579426205771531295 := by
  unfold tailWord_1330468
  simp only [CollatzResearch.WordTrace]
  refine ⟨24263077271974568344568029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32350769695966091126090705 24263077271974568344568029)
  ·
    refine ⟨9098653976990463129213011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24263077271974568344568029 9098653976990463129213011)
    ·
      refine ⟨13647980965485694693819517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9098653976990463129213011 13647980965485694693819517)
      ·
        refine ⟨5117992862057135510182319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13647980965485694693819517 5117992862057135510182319)
        ·
          refine ⟨7676989293085703265273479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5117992862057135510182319 7676989293085703265273479)
          ·
            refine ⟨11515483939628554897910219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7676989293085703265273479 11515483939628554897910219)
            ·
              refine ⟨17273225909442832346865329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11515483939628554897910219 17273225909442832346865329)
              ·
                refine ⟨12954919432082124260148997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17273225909442832346865329 12954919432082124260148997)
                ·
                  refine ⟨2429047393515398298777937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12954919432082124260148997 2429047393515398298777937)
                  ·
                    refine ⟨1821785545136548724083453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2429047393515398298777937 1821785545136548724083453)
                    ·
                      refine ⟨683169579426205771531295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1821785545136548724083453 683169579426205771531295)
                      ·
                        rfl

theorem cell23_1330468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_1330468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330468 prefixEnd_1330468 := by exact prefixLift 1330468
  have htrace : WordTrace (prefixWord ++ tailWord_1330468) baseStart_1330468 baseEnd_1330468 := by
    simpa [prefixWord, tailWord_1330468, baseEnd_1330468] using wordTrace_append hprefix tailTrace_1330468
  have hstable : (prefixWord ++ tailWord_1330468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330468).length < 2 ^ (prefixWord ++ tailWord_1330468).sum := by decide
  have hdescent : baseEnd_1330468 < baseStart_1330468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330485 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_1330485 : Nat := 118140960795 + 1330485 * 2 ^ 59
def prefixEnd_1330485 : Nat := 4983230072969 + 3 ^ 40 * 1330485 * 2
def baseEnd_1330485 : Nat := 683178308597332205018717

theorem tailTrace_1330485 : CollatzResearch.WordTrace tailWord_1330485 prefixEnd_1330485 683178308597332205018717 := by
  unfold tailWord_1330485
  simp only [CollatzResearch.WordTrace]
  refine ⟨48526774584887548592504909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32351183056591699061669939 48526774584887548592504909)
  ·
    refine ⟨18197540469332830722189341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48526774584887548592504909 18197540469332830722189341)
    ·
      refine ⟨6824077675999811520821003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18197540469332830722189341 6824077675999811520821003)
      ·
        refine ⟨10236116513999717281231505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6824077675999811520821003 10236116513999717281231505)
        ·
          refine ⟨7677087385499787960923629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10236116513999717281231505 7677087385499787960923629)
          ·
            refine ⟨2878907769562420485346361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7677087385499787960923629 2878907769562420485346361)
            ·
              refine ⟨2159180827171815364009771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2878907769562420485346361 2159180827171815364009771)
              ·
                refine ⟨3238771240757723046014657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159180827171815364009771 3238771240757723046014657)
                ·
                  refine ⟨2429078430568292284510993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3238771240757723046014657 2429078430568292284510993)
                  ·
                    refine ⟨1821808822926219213383245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2429078430568292284510993 1821808822926219213383245)
                    ·
                      refine ⟨683178308597332205018717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1821808822926219213383245 683178308597332205018717)
                      ·
                        rfl

theorem cell23_1330485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_1330485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330485 prefixEnd_1330485 := by exact prefixLift 1330485
  have htrace : WordTrace (prefixWord ++ tailWord_1330485) baseStart_1330485 baseEnd_1330485 := by
    simpa [prefixWord, tailWord_1330485, baseEnd_1330485] using wordTrace_append hprefix tailTrace_1330485
  have hstable : (prefixWord ++ tailWord_1330485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330485).length < 2 ^ (prefixWord ++ tailWord_1330485).sum := by decide
  have hdescent : baseEnd_1330485 < baseStart_1330485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330555 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 5, 2, 2]
def baseStart_1330555 : Nat := 118140960795 + 1330555 * 2 ^ 59
def prefixEnd_1330555 : Nat := 4983230072969 + 3 ^ 40 * 1330555 * 2
def baseEnd_1330555 : Nat := 683214252243146931143395

theorem tailTrace_1330555 : CollatzResearch.WordTrace tailWord_1330555 prefixEnd_1330555 683214252243146931143395 := by
  unfold tailWord_1330555
  simp only [CollatzResearch.WordTrace]
  refine ⟨48529327694633950547553119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32352885129755967031702079 48529327694633950547553119)
  ·
    refine ⟨72793991541950925821329679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48529327694633950547553119 72793991541950925821329679)
    ·
      refine ⟨109190987312926388731994519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72793991541950925821329679 109190987312926388731994519)
      ·
        refine ⟨163786480969389583097991779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109190987312926388731994519 163786480969389583097991779)
        ·
          refine ⟨245679721454084374646987669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163786480969389583097991779 245679721454084374646987669)
          ·
            refine ⟨11516236943160205061577547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 245679721454084374646987669 11516236943160205061577547)
            ·
              refine ⟨17274355414740307592366321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11516236943160205061577547 17274355414740307592366321)
              ·
                refine ⟨12955766561055230694274741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17274355414740307592366321 12955766561055230694274741)
                ·
                  refine ⟨1214603115098927877588257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12955766561055230694274741 1214603115098927877588257)
                  ·
                    refine ⟨910952336324195908191193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1214603115098927877588257 910952336324195908191193)
                    ·
                      refine ⟨683214252243146931143395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 910952336324195908191193 683214252243146931143395)
                      ·
                        rfl

theorem cell23_1330555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 2, 2].length) (baseStart_1330555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330555 prefixEnd_1330555 := by exact prefixLift 1330555
  have htrace : WordTrace (prefixWord ++ tailWord_1330555) baseStart_1330555 baseEnd_1330555 := by
    simpa [prefixWord, tailWord_1330555, baseEnd_1330555] using wordTrace_append hprefix tailTrace_1330555
  have hstable : (prefixWord ++ tailWord_1330555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330555).length < 2 ^ (prefixWord ++ tailWord_1330555).sum := by decide
  have hdescent : baseEnd_1330555 < baseStart_1330555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330565 : List Nat := [1, 3, 1, 1, 3, 1, 5, 2, 2, 4]
def baseStart_1330565 : Nat := 118140960795 + 1330565 * 2 ^ 59
def prefixEnd_1330565 : Nat := 4983230072969 + 3 ^ 40 * 1330565 * 2
def baseEnd_1330565 : Nat := 227739795683230630672783

theorem tailTrace_1330565 : CollatzResearch.WordTrace tailWord_1330565 prefixEnd_1330565 227739795683230630672783 := by
  unfold tailWord_1330565
  simp only [CollatzResearch.WordTrace]
  refine ⟨48529692424597722255417149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32353128283065148170278099 48529692424597722255417149)
  ·
    refine ⟨18198634659224145845781431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48529692424597722255417149 18198634659224145845781431)
    ·
      refine ⟨27297951988836218768672147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18198634659224145845781431 27297951988836218768672147)
      ·
        refine ⟨40946927983254328153008221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27297951988836218768672147 40946927983254328153008221)
        ·
          refine ⟨15355097993720373057378083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40946927983254328153008221 15355097993720373057378083)
          ·
            refine ⟨23032646990580559586067125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15355097993720373057378083 23032646990580559586067125)
            ·
              refine ⟨2159310655366927461193793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23032646990580559586067125 2159310655366927461193793)
              ·
                refine ⟨1619482991525195595895345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2159310655366927461193793 1619482991525195595895345)
                ·
                  refine ⟨1214612243643896696921509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1619482991525195595895345 1214612243643896696921509)
                  ·
                    refine ⟨227739795683230630672783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1214612243643896696921509 227739795683230630672783)
                    ·
                      rfl

theorem cell23_1330565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_1330565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330565 prefixEnd_1330565 := by exact prefixLift 1330565
  have htrace : WordTrace (prefixWord ++ tailWord_1330565) baseStart_1330565 baseEnd_1330565 := by
    simpa [prefixWord, tailWord_1330565, baseEnd_1330565] using wordTrace_append hprefix tailTrace_1330565
  have hstable : (prefixWord ++ tailWord_1330565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330565).length < 2 ^ (prefixWord ++ tailWord_1330565).sum := by decide
  have hdescent : baseEnd_1330565 < baseStart_1330565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330572 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 3, 2, 2]
def baseStart_1330572 : Nat := 118140960795 + 1330572 * 2 ^ 59
def prefixEnd_1330572 : Nat := 4983230072969 + 3 ^ 40 * 1330572 * 2
def baseEnd_1330572 : Nat := 683222981414273364630817

theorem tailTrace_1330572 : CollatzResearch.WordTrace tailWord_1330572 prefixEnd_1330572 683222981414273364630817 := by
  unfold tailWord_1330572
  simp only [CollatzResearch.WordTrace]
  refine ⟨24264973867786181225460985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32353298490381574967281313 24264973867786181225460985)
  ·
    refine ⟨18198730400839635919095739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24264973867786181225460985 18198730400839635919095739)
    ·
      refine ⟨27298095601259453878643609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18198730400839635919095739 27298095601259453878643609)
      ·
        refine ⟨20473571700944590408982707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27298095601259453878643609 20473571700944590408982707)
        ·
          refine ⟨30710357551416885613474061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20473571700944590408982707 30710357551416885613474061)
          ·
            refine ⟨11516384081781332105052773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30710357551416885613474061 11516384081781332105052773)
            ·
              refine ⟨2159322015333999769697395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11516384081781332105052773 2159322015333999769697395)
              ·
                refine ⟨3238983023000999654546093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159322015333999769697395 3238983023000999654546093)
                ·
                  refine ⟨1214618633625374870454785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3238983023000999654546093 1214618633625374870454785)
                  ·
                    refine ⟨910963975219031152841089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1214618633625374870454785 910963975219031152841089)
                    ·
                      refine ⟨683222981414273364630817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 910963975219031152841089 683222981414273364630817)
                      ·
                        rfl

theorem cell23_1330572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_1330572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330572 prefixEnd_1330572 := by exact prefixLift 1330572
  have htrace : WordTrace (prefixWord ++ tailWord_1330572) baseStart_1330572 baseEnd_1330572 := by
    simpa [prefixWord, tailWord_1330572, baseEnd_1330572] using wordTrace_append hprefix tailTrace_1330572
  have hstable : (prefixWord ++ tailWord_1330572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330572).length < 2 ^ (prefixWord ++ tailWord_1330572).sum := by decide
  have hdescent : baseEnd_1330572 < baseStart_1330572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330585 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 1, 2, 4]
def baseStart_1330585 : Nat := 118140960795 + 1330585 * 2 ^ 59
def prefixEnd_1330585 : Nat := 4983230072969 + 3 ^ 40 * 1330585 * 2
def baseEnd_1330585 : Nat := 683229656662781813768257

theorem tailTrace_1330585 : CollatzResearch.WordTrace tailWord_1330585 prefixEnd_1330585 683229656662781813768257 := by
  unfold tailWord_1330585
  simp only [CollatzResearch.WordTrace]
  refine ⟨48530421884525265671145209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32353614589683510447430139 48530421884525265671145209)
  ·
    refine ⟨36397816413393949253358907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48530421884525265671145209 36397816413393949253358907)
    ·
      refine ⟨54596724620090923880038361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36397816413393949253358907 54596724620090923880038361)
      ·
        refine ⟨40947543465068192910028771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54596724620090923880038361 40947543465068192910028771)
        ·
          refine ⟨61421315197602289365043157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40947543465068192910028771 61421315197602289365043157)
          ·
            refine ⟨1439562074943803656993199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 61421315197602289365043157 1439562074943803656993199)
            ·
              refine ⟨2159343112415705485489799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439562074943803656993199 2159343112415705485489799)
              ·
                refine ⟨3239014668623558228234699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159343112415705485489799 3239014668623558228234699)
                ·
                  refine ⟨4858522002935337342352049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3239014668623558228234699 4858522002935337342352049)
                  ·
                    refine ⟨3643891502201503006764037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4858522002935337342352049 3643891502201503006764037)
                    ·
                      refine ⟨683229656662781813768257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3643891502201503006764037 683229656662781813768257)
                      ·
                        rfl

theorem cell23_1330585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_1330585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330585 prefixEnd_1330585 := by exact prefixLift 1330585
  have htrace : WordTrace (prefixWord ++ tailWord_1330585) baseStart_1330585 baseEnd_1330585 := by
    simpa [prefixWord, tailWord_1330585, baseEnd_1330585] using wordTrace_append hprefix tailTrace_1330585
  have hstable : (prefixWord ++ tailWord_1330585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330585).length < 2 ^ (prefixWord ++ tailWord_1330585).sum := by decide
  have hdescent : baseEnd_1330585 < baseStart_1330585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330611 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 8]
def baseStart_1330611 : Nat := 118140960795 + 1330611 * 2 ^ 59
def prefixEnd_1330611 : Nat := 4983230072969 + 3 ^ 40 * 1330611 * 2
def baseEnd_1330611 : Nat := 683243007159798712043137

theorem tailTrace_1330611 : CollatzResearch.WordTrace tailWord_1330611 prefixEnd_1330611 683243007159798712043137 := by
  unfold tailWord_1330611
  simp only [CollatzResearch.WordTrace]
  refine ⟨48531370182431072111591687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32354246788287381407727791 48531370182431072111591687)
  ·
    refine ⟨72797055273646608167387531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48531370182431072111591687 72797055273646608167387531)
    ·
      refine ⟨109195582910469912251081297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72797055273646608167387531 109195582910469912251081297)
      ·
        refine ⟨81896687182852434188310973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109195582910469912251081297 81896687182852434188310973)
        ·
          refine ⟨30711257693569662820616615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81896687182852434188310973 30711257693569662820616615)
          ·
            refine ⟨46066886540354494230924923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30711257693569662820616615 46066886540354494230924923)
            ·
              refine ⟨69100329810531741346387385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46066886540354494230924923 69100329810531741346387385)
              ·
                refine ⟨51825247357898806009790539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69100329810531741346387385 51825247357898806009790539)
                ·
                  refine ⟨77737871036848209014685809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51825247357898806009790539 77737871036848209014685809)
                  ·
                    refine ⟨58303403277636156761014357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77737871036848209014685809 58303403277636156761014357)
                    ·
                      refine ⟨683243007159798712043137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 58303403277636156761014357 683243007159798712043137)
                      ·
                        rfl

theorem cell23_1330611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_1330611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330611 prefixEnd_1330611 := by exact prefixLift 1330611
  have htrace : WordTrace (prefixWord ++ tailWord_1330611) baseStart_1330611 baseEnd_1330611 := by
    simpa [prefixWord, tailWord_1330611, baseEnd_1330611] using wordTrace_append hprefix tailTrace_1330611
  have hstable : (prefixWord ++ tailWord_1330611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330611).length < 2 ^ (prefixWord ++ tailWord_1330611).sum := by decide
  have hdescent : baseEnd_1330611 < baseStart_1330611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330622 : List Nat := [4, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_1330622 : Nat := 118140960795 + 1330622 * 2 ^ 59
def prefixEnd_1330622 : Nat := 4983230072969 + 3 ^ 40 * 1330622 * 2
def baseEnd_1330622 : Nat := 683248655446998169005587

theorem tailTrace_1330622 : CollatzResearch.WordTrace tailWord_1330622 prefixEnd_1330622 683248655446998169005587 := by
  unfold tailWord_1330622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6066471423173902623780265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32354514256927480660161413 6066471423173902623780265)
  ·
    refine ⟨4549853567380426967835199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6066471423173902623780265 4549853567380426967835199)
    ·
      refine ⟨6824780351070640451752799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4549853567380426967835199 6824780351070640451752799)
      ·
        refine ⟨10237170526605960677629199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6824780351070640451752799 10237170526605960677629199)
        ·
          refine ⟨15355755789908941016443799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10237170526605960677629199 15355755789908941016443799)
          ·
            refine ⟨23033633684863411524665699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15355755789908941016443799 23033633684863411524665699)
            ·
              refine ⟨34550450527295117286998549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23033633684863411524665699 34550450527295117286998549)
              ·
                refine ⟨1619552368466958622828057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34550450527295117286998549 1619552368466958622828057)
                ·
                  refine ⟨1214664276350218967121043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1619552368466958622828057 1214664276350218967121043)
                  ·
                    refine ⟨1821996414525328450681565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1214664276350218967121043 1821996414525328450681565)
                    ·
                      refine ⟨683248655446998169005587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1821996414525328450681565 683248655446998169005587)
                      ·
                        rfl

theorem cell23_1330622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_1330622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330622 prefixEnd_1330622 := by exact prefixLift 1330622
  have htrace : WordTrace (prefixWord ++ tailWord_1330622) baseStart_1330622 baseEnd_1330622 := by
    simpa [prefixWord, tailWord_1330622, baseEnd_1330622] using wordTrace_append hprefix tailTrace_1330622
  have hstable : (prefixWord ++ tailWord_1330622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330622).length < 2 ^ (prefixWord ++ tailWord_1330622).sum := by decide
  have hdescent : baseEnd_1330622 < baseStart_1330622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330638 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 2, 6]
def baseStart_1330638 : Nat := 118140960795 + 1330638 * 2 ^ 59
def prefixEnd_1330638 : Nat := 4983230072969 + 3 ^ 40 * 1330638 * 2
def baseEnd_1330638 : Nat := 227752290379156702135171

theorem tailTrace_1330638 : CollatzResearch.WordTrace tailWord_1330638 prefixEnd_1330638 227752290379156702135171 := by
  unfold tailWord_1330638
  simp only [CollatzResearch.WordTrace]
  refine ⟨6066544369166656965353071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32354903302222170481883045 6066544369166656965353071)
  ·
    refine ⟨9099816553749985448029607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6066544369166656965353071 9099816553749985448029607)
    ·
      refine ⟨13649724830624978172044411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9099816553749985448029607 13649724830624978172044411)
      ·
        refine ⟨20474587245937467258066617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13649724830624978172044411 20474587245937467258066617)
        ·
          refine ⟨15355940434453100443549963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20474587245937467258066617 15355940434453100443549963)
          ·
            refine ⟨23033910651679650665324945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15355940434453100443549963 23033910651679650665324945)
            ·
              refine ⟨17275432988759737998993709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23033910651679650665324945 17275432988759737998993709)
              ·
                refine ⟨6478287370784901749622641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17275432988759737998993709 6478287370784901749622641)
                ·
                  refine ⟨4858715528088676312216981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6478287370784901749622641 4858715528088676312216981)
                  ·
                    refine ⟨227752290379156702135171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4858715528088676312216981 227752290379156702135171)
                    ·
                      rfl

theorem cell23_1330638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_1330638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330638 prefixEnd_1330638 := by exact prefixLift 1330638
  have htrace : WordTrace (prefixWord ++ tailWord_1330638) baseStart_1330638 baseEnd_1330638 := by
    simpa [prefixWord, tailWord_1330638, baseEnd_1330638] using wordTrace_append hprefix tailTrace_1330638
  have hstable : (prefixWord ++ tailWord_1330638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330638).length < 2 ^ (prefixWord ++ tailWord_1330638).sum := by decide
  have hdescent : baseEnd_1330638 < baseStart_1330638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330648 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 2, 1, 5]
def baseStart_1330648 : Nat := 118140960795 + 1330648 * 2 ^ 59
def prefixEnd_1330648 : Nat := 4983230072969 + 3 ^ 40 * 1330648 * 2
def baseEnd_1330648 : Nat := 683262005944015067280467

theorem tailTrace_1330648 : CollatzResearch.WordTrace tailWord_1330648 prefixEnd_1330648 683262005944015067280467 := by
  unfold tailWord_1330648
  simp only [CollatzResearch.WordTrace]
  refine ⟨24266359841648513715344299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32355146455531351620459065 24266359841648513715344299)
  ·
    refine ⟨36399539762472770573016449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24266359841648513715344299 36399539762472770573016449)
    ·
      refine ⟨27299654821854577929762337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36399539762472770573016449 27299654821854577929762337)
      ·
        refine ⟨20474741116390933447321753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27299654821854577929762337 20474741116390933447321753)
        ·
          refine ⟨15356055837293200085491315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20474741116390933447321753 15356055837293200085491315)
          ·
            refine ⟨23034083755939800128236973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15356055837293200085491315 23034083755939800128236973)
            ·
              refine ⟨8637781408477425048088865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23034083755939800128236973 8637781408477425048088865)
              ·
                refine ⟨6478336056358068786066649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8637781408477425048088865 6478336056358068786066649)
                ·
                  refine ⟨4858752042268551589549987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6478336056358068786066649 4858752042268551589549987)
                  ·
                    refine ⟨7288128063402827384324981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4858752042268551589549987 7288128063402827384324981)
                    ·
                      refine ⟨683262005944015067280467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7288128063402827384324981 683262005944015067280467)
                      ·
                        rfl

theorem cell23_1330648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_1330648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330648 prefixEnd_1330648 := by exact prefixLift 1330648
  have htrace : WordTrace (prefixWord ++ tailWord_1330648) baseStart_1330648 baseEnd_1330648 := by
    simpa [prefixWord, tailWord_1330648, baseEnd_1330648] using wordTrace_append hprefix tailTrace_1330648
  have hstable : (prefixWord ++ tailWord_1330648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330648).length < 2 ^ (prefixWord ++ tailWord_1330648).sum := by decide
  have hdescent : baseEnd_1330648 < baseStart_1330648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330649 : List Nat := [1, 2, 1, 2, 4, 4, 1, 2, 1, 3, 2]
def baseStart_1330649 : Nat := 118140960795 + 1330649 * 2 ^ 59
def prefixEnd_1330649 : Nat := 4983230072969 + 3 ^ 40 * 1330649 * 2
def baseEnd_1330649 : Nat := 683262519424669563367963

theorem tailTrace_1330649 : CollatzResearch.WordTrace tailWord_1330649 prefixEnd_1330649 683262519424669563367963 := by
  unfold tailWord_1330649
  simp only [CollatzResearch.WordTrace]
  refine ⟨48532756156293404601475001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32355170770862269734316667 48532756156293404601475001)
  ·
    refine ⟨36399567117220053451106251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48532756156293404601475001 36399567117220053451106251)
    ·
      refine ⟨54599350675830080176659377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36399567117220053451106251 54599350675830080176659377)
      ·
        refine ⟨40949513006872560132494533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54599350675830080176659377 40949513006872560132494533)
        ·
          refine ⟨7678033688788605024842725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40949513006872560132494533 7678033688788605024842725)
          ·
            refine ⟨1439631316647863442158011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7678033688788605024842725 1439631316647863442158011)
            ·
              refine ⟨2159446974971795163237017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439631316647863442158011 2159446974971795163237017)
              ·
                refine ⟨1619585231228846372427763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2159446974971795163237017 1619585231228846372427763)
                ·
                  refine ⟨2429377846843269558641645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619585231228846372427763 2429377846843269558641645)
                  ·
                    refine ⟨911016692566226084490617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2429377846843269558641645 911016692566226084490617)
                    ·
                      refine ⟨683262519424669563367963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 911016692566226084490617 683262519424669563367963)
                      ·
                        rfl

theorem cell23_1330649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 3, 2].length) (baseStart_1330649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330649 prefixEnd_1330649 := by exact prefixLift 1330649
  have htrace : WordTrace (prefixWord ++ tailWord_1330649) baseStart_1330649 baseEnd_1330649 := by
    simpa [prefixWord, tailWord_1330649, baseEnd_1330649] using wordTrace_append hprefix tailTrace_1330649
  have hstable : (prefixWord ++ tailWord_1330649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330649).length < 2 ^ (prefixWord ++ tailWord_1330649).sum := by decide
  have hdescent : baseEnd_1330649 < baseStart_1330649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330666 : List Nat := [3, 1, 3, 1, 4, 1, 3, 1, 1, 3, 2]
def baseStart_1330666 : Nat := 118140960795 + 1330666 * 2 ^ 59
def prefixEnd_1330666 : Nat := 4983230072969 + 3 ^ 40 * 1330666 * 2
def baseEnd_1330666 : Nat := 683271248595795996855385

theorem tailTrace_1330666 : CollatzResearch.WordTrace tailWord_1330666 prefixEnd_1330666 683271248595795996855385 := by
  unfold tailWord_1330666
  simp only [CollatzResearch.WordTrace]
  refine ⟨12133344049307954126210963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32355584131487877669895901 12133344049307954126210963)
  ·
    refine ⟨18200016073961931189316445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12133344049307954126210963 18200016073961931189316445)
    ·
      refine ⟨6825006027735724195993667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18200016073961931189316445 6825006027735724195993667)
      ·
        refine ⟨10237509041603586293990501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6825006027735724195993667 10237509041603586293990501)
        ·
          refine ⟨1919532945300672430123219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10237509041603586293990501 1919532945300672430123219)
          ·
            refine ⟨2879299417951008645184829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919532945300672430123219 2879299417951008645184829)
            ·
              refine ⟨1079737281731628241944311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2879299417951008645184829 1079737281731628241944311)
              ·
                refine ⟨1619605922597442362916467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079737281731628241944311 1619605922597442362916467)
                ·
                  refine ⟨2429408883896163544374701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619605922597442362916467 2429408883896163544374701)
                  ·
                    refine ⟨911028331461061329140513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2429408883896163544374701 911028331461061329140513)
                    ·
                      refine ⟨683271248595795996855385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 911028331461061329140513 683271248595795996855385)
                      ·
                        rfl

theorem cell23_1330666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_1330666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330666 prefixEnd_1330666 := by exact prefixLift 1330666
  have htrace : WordTrace (prefixWord ++ tailWord_1330666) baseStart_1330666 baseEnd_1330666 := by
    simpa [prefixWord, tailWord_1330666, baseEnd_1330666] using wordTrace_append hprefix tailTrace_1330666
  have hstable : (prefixWord ++ tailWord_1330666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330666).length < 2 ^ (prefixWord ++ tailWord_1330666).sum := by decide
  have hdescent : baseEnd_1330666 < baseStart_1330666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330692 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1330692 : Nat := 118140960795 + 1330692 * 2 ^ 59
def prefixEnd_1330692 : Nat := 4983230072969 + 3 ^ 40 * 1330692 * 2
def baseEnd_1330692 : Nat := 683284599092812895130265

theorem tailTrace_1330692 : CollatzResearch.WordTrace tailWord_1330692 prefixEnd_1330692 683284599092812895130265 := by
  unfold tailWord_1330692
  simp only [CollatzResearch.WordTrace]
  refine ⟨24267162247568811472645165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32356216330091748630193553 24267162247568811472645165)
  ·
    refine ⟨9100185842838304302241937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24267162247568811472645165 9100185842838304302241937)
    ·
      refine ⟨6825139382128728226681453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9100185842838304302241937 6825139382128728226681453)
      ·
        refine ⟨2559427268298273085005545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6825139382128728226681453 2559427268298273085005545)
        ·
          refine ⟨1919570451223704813754159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2559427268298273085005545 1919570451223704813754159)
          ·
            refine ⟨2879355676835557220631239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919570451223704813754159 2879355676835557220631239)
            ·
              refine ⟨4319033515253335830946859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2879355676835557220631239 4319033515253335830946859)
              ·
                refine ⟨6478550272880003746420289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4319033515253335830946859 6478550272880003746420289)
                ·
                  refine ⟨4858912704660002809815217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6478550272880003746420289 4858912704660002809815217)
                  ·
                    refine ⟨3644184528495002107361413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4858912704660002809815217 3644184528495002107361413)
                    ·
                      refine ⟨683284599092812895130265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3644184528495002107361413 683284599092812895130265)
                      ·
                        rfl

theorem cell23_1330692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1330692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330692 prefixEnd_1330692 := by exact prefixLift 1330692
  have htrace : WordTrace (prefixWord ++ tailWord_1330692) baseStart_1330692 baseEnd_1330692 := by
    simpa [prefixWord, tailWord_1330692, baseEnd_1330692] using wordTrace_append hprefix tailTrace_1330692
  have hstable : (prefixWord ++ tailWord_1330692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330692).length < 2 ^ (prefixWord ++ tailWord_1330692).sum := by decide
  have hdescent : baseEnd_1330692 < baseStart_1330692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330695 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1330695 : Nat := 118140960795 + 1330695 * 2 ^ 59
def prefixEnd_1330695 : Nat := 4983230072969 + 3 ^ 40 * 1330695 * 2
def baseEnd_1330695 : Nat := 683286139534776383392751

theorem tailTrace_1330695 : CollatzResearch.WordTrace tailWord_1330695 prefixEnd_1330695 683286139534776383392751 := by
  unfold tailWord_1330695
  simp only [CollatzResearch.WordTrace]
  refine ⟨48534433914126754457649539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32356289276084502971766359 48534433914126754457649539)
  ·
    refine ⟨72801650871190131686474309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48534433914126754457649539 72801650871190131686474309)
    ·
      refine ⟨13650309538348149691213933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72801650871190131686474309 13650309538348149691213933)
      ·
        refine ⟨5118866076880556134205225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13650309538348149691213933 5118866076880556134205225)
        ·
          refine ⟨3839149557660417100653919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5118866076880556134205225 3839149557660417100653919)
          ·
            refine ⟨5758724336490625650980879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3839149557660417100653919 5758724336490625650980879)
            ·
              refine ⟨8638086504735938476471319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5758724336490625650980879 8638086504735938476471319)
              ·
                refine ⟨12957129757103907714706979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8638086504735938476471319 12957129757103907714706979)
                ·
                  refine ⟨19435694635655861572060469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12957129757103907714706979 19435694635655861572060469)
                  ·
                    refine ⟨1822096372092737022380669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19435694635655861572060469 1822096372092737022380669)
                    ·
                      refine ⟨683286139534776383392751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1822096372092737022380669 683286139534776383392751)
                      ·
                        rfl

theorem cell23_1330695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1330695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330695 prefixEnd_1330695 := by exact prefixLift 1330695
  have htrace : WordTrace (prefixWord ++ tailWord_1330695) baseStart_1330695 baseEnd_1330695 := by
    simpa [prefixWord, tailWord_1330695, baseEnd_1330695] using wordTrace_append hprefix tailTrace_1330695
  have hstable : (prefixWord ++ tailWord_1330695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330695).length < 2 ^ (prefixWord ++ tailWord_1330695).sum := by decide
  have hdescent : baseEnd_1330695 < baseStart_1330695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330705 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 2, 5, 2]
def baseStart_1330705 : Nat := 118140960795 + 1330705 * 2 ^ 59
def prefixEnd_1330705 : Nat := 4983230072969 + 3 ^ 40 * 1330705 * 2
def baseEnd_1330705 : Nat := 683291274341321344267705

theorem tailTrace_1330705 : CollatzResearch.WordTrace tailWord_1330705 prefixEnd_1330705 683291274341321344267705 := by
  unfold tailWord_1330705
  simp only [CollatzResearch.WordTrace]
  refine ⟨48534798644090526165513569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32356532429393684110342379 48534798644090526165513569)
  ·
    refine ⟨36401098983067894624135177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48534798644090526165513569 36401098983067894624135177)
    ·
      refine ⟨27300824237300920968101383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36401098983067894624135177 27300824237300920968101383)
      ·
        refine ⟨40951236355951381452152075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27300824237300920968101383 40951236355951381452152075)
        ·
          refine ⟨61426854533927072178228113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40951236355951381452152075 61426854533927072178228113)
          ·
            refine ⟨46070140900445304133671085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61426854533927072178228113 46070140900445304133671085)
            ·
              refine ⟨17276302837666989050126657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46070140900445304133671085 17276302837666989050126657)
              ·
                refine ⟨12957227128250241787594993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17276302837666989050126657 12957227128250241787594993)
                ·
                  refine ⟨9717920346187681340696245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12957227128250241787594993 9717920346187681340696245)
                  ·
                    refine ⟨911055032455095125690273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9717920346187681340696245 911055032455095125690273)
                    ·
                      refine ⟨683291274341321344267705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 911055032455095125690273 683291274341321344267705)
                      ·
                        rfl

theorem cell23_1330705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 5, 2].length) (baseStart_1330705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330705 prefixEnd_1330705 := by exact prefixLift 1330705
  have htrace : WordTrace (prefixWord ++ tailWord_1330705) baseStart_1330705 baseEnd_1330705 := by
    simpa [prefixWord, tailWord_1330705, baseEnd_1330705] using wordTrace_append hprefix tailTrace_1330705
  have hstable : (prefixWord ++ tailWord_1330705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330705).length < 2 ^ (prefixWord ++ tailWord_1330705).sum := by decide
  have hdescent : baseEnd_1330705 < baseStart_1330705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330772 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_1330772 : Nat := 118140960795 + 1330772 * 2 ^ 59
def prefixEnd_1330772 : Nat := 4983230072969 + 3 ^ 40 * 1330772 * 2
def baseEnd_1330772 : Nat := 683325677545172582129897

theorem tailTrace_1330772 : CollatzResearch.WordTrace tailWord_1330772 prefixEnd_1330772 683325677545172582129897 := by
  unfold tailWord_1330772
  simp only [CollatzResearch.WordTrace]
  refine ⟨24268621167423898304101285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32358161556565197738801713 24268621167423898304101285)
  ·
    refine ⟨4550366468891980932018991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24268621167423898304101285 4550366468891980932018991)
    ·
      refine ⟨6825549703337971398028487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4550366468891980932018991 6825549703337971398028487)
      ·
        refine ⟨10238324555006957097042731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6825549703337971398028487 10238324555006957097042731)
        ·
          refine ⟨15357486832510435645564097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10238324555006957097042731 15357486832510435645564097)
          ·
            refine ⟨11518115124382826734173073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15357486832510435645564097 11518115124382826734173073)
            ·
              refine ⟨8638586343287120050629805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11518115124382826734173073 8638586343287120050629805)
              ·
                refine ⟨3239469878732670018986177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8638586343287120050629805 3239469878732670018986177)
                ·
                  refine ⟨2429602409049502514239633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3239469878732670018986177 2429602409049502514239633)
                  ·
                    refine ⟨1822201806787126885679725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2429602409049502514239633 1822201806787126885679725)
                    ·
                      refine ⟨683325677545172582129897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1822201806787126885679725 683325677545172582129897)
                      ·
                        rfl

theorem cell23_1330772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_1330772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330772 prefixEnd_1330772 := by exact prefixLift 1330772
  have htrace : WordTrace (prefixWord ++ tailWord_1330772) baseStart_1330772 baseEnd_1330772 := by
    simpa [prefixWord, tailWord_1330772, baseEnd_1330772] using wordTrace_append hprefix tailTrace_1330772
  have hstable : (prefixWord ++ tailWord_1330772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330772).length < 2 ^ (prefixWord ++ tailWord_1330772).sum := by decide
  have hdescent : baseEnd_1330772 < baseStart_1330772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330812 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 6, 3, 2]
def baseStart_1330812 : Nat := 118140960795 + 1330812 * 2 ^ 59
def prefixEnd_1330812 : Nat := 4983230072969 + 3 ^ 40 * 1330812 * 2
def baseEnd_1330812 : Nat := 683346216771352425629713

theorem tailTrace_1330812 : CollatzResearch.WordTrace tailWord_1330812 prefixEnd_1330812 683346216771352425629713 := by
  unfold tailWord_1330812
  simp only [CollatzResearch.WordTrace]
  refine ⟨24269350627351441719829345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32359134169801922293105793 24269350627351441719829345)
  ·
    refine ⟨18202012970513581289872009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24269350627351441719829345 18202012970513581289872009)
    ·
      refine ⟨13651509727885185967404007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18202012970513581289872009 13651509727885185967404007)
      ·
        refine ⟨20477264591827778951106011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13651509727885185967404007 20477264591827778951106011)
        ·
          refine ⟨30715896887741668426659017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20477264591827778951106011 30715896887741668426659017)
          ·
            refine ⟨23036922665806251319994263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30715896887741668426659017 23036922665806251319994263)
            ·
              refine ⟨34555383998709376979991395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23036922665806251319994263 34555383998709376979991395)
              ·
                refine ⟨51833075998064065469987093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34555383998709376979991395 51833075998064065469987093)
                ·
                  refine ⟨2429675437409253068905645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51833075998064065469987093 2429675437409253068905645)
                  ·
                    refine ⟨911128289028469900839617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2429675437409253068905645 911128289028469900839617)
                    ·
                      refine ⟨683346216771352425629713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 911128289028469900839617 683346216771352425629713)
                      ·
                        rfl

theorem cell23_1330812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_1330812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330812 prefixEnd_1330812 := by exact prefixLift 1330812
  have htrace : WordTrace (prefixWord ++ tailWord_1330812) baseStart_1330812 baseEnd_1330812 := by
    simpa [prefixWord, tailWord_1330812, baseEnd_1330812] using wordTrace_append hprefix tailTrace_1330812
  have hstable : (prefixWord ++ tailWord_1330812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330812).length < 2 ^ (prefixWord ++ tailWord_1330812).sum := by decide
  have hdescent : baseEnd_1330812 < baseStart_1330812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330839 : List Nat := [1, 1, 3, 3, 2, 3, 3, 1, 1, 5]
def baseStart_1330839 : Nat := 118140960795 + 1330839 * 2 ^ 59
def prefixEnd_1330839 : Nat := 4983230072969 + 3 ^ 40 * 1330839 * 2
def baseEnd_1330839 : Nat := 227786693583007939997363

theorem tailTrace_1330839 : CollatzResearch.WordTrace tailWord_1330839 prefixEnd_1330839 227786693583007939997363 := by
  unfold tailWord_1330839
  simp only [CollatzResearch.WordTrace]
  refine ⟨48539686025605067050891571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32359790683736711367261047 48539686025605067050891571)
  ·
    refine ⟨72809529038407600576337357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48539686025605067050891571 72809529038407600576337357)
    ·
      refine ⟨27303573389402850216126509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72809529038407600576337357 27303573389402850216126509)
      ·
        refine ⟨10238840021026068831047441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27303573389402850216126509 10238840021026068831047441)
        ·
          refine ⟨7679130015769551623285581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10238840021026068831047441 7679130015769551623285581)
          ·
            refine ⟨2879673755913581858732093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7679130015769551623285581 2879673755913581858732093)
            ·
              refine ⟨1079877658467593197024535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2879673755913581858732093 1079877658467593197024535)
              ·
                refine ⟨1619816487701389795536803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079877658467593197024535 1619816487701389795536803)
                ·
                  refine ⟨2429724731552084693305205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619816487701389795536803 2429724731552084693305205)
                  ·
                    refine ⟨227786693583007939997363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2429724731552084693305205 227786693583007939997363)
                    ·
                      rfl

theorem cell23_1330839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 1, 5].length) (baseStart_1330839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330839 prefixEnd_1330839 := by exact prefixLift 1330839
  have htrace : WordTrace (prefixWord ++ tailWord_1330839) baseStart_1330839 baseEnd_1330839 := by
    simpa [prefixWord, tailWord_1330839, baseEnd_1330839] using wordTrace_append hprefix tailTrace_1330839
  have hstable : (prefixWord ++ tailWord_1330839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330839).length < 2 ^ (prefixWord ++ tailWord_1330839).sum := by decide
  have hdescent : baseEnd_1330839 < baseStart_1330839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330846 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_1330846 : Nat := 118140960795 + 1330846 * 2 ^ 59
def prefixEnd_1330846 : Nat := 4983230072969 + 3 ^ 40 * 1330846 * 2
def baseEnd_1330846 : Nat := 683363675113605292604557

theorem tailTrace_1330846 : CollatzResearch.WordTrace tailWord_1330846 prefixEnd_1330846 683363675113605292604557 := by
  unfold tailWord_1330846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6067492667072463405799549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32359960891053138164264261 6067492667072463405799549)
  ·
    refine ⟨2275309750152173777174831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6067492667072463405799549 2275309750152173777174831)
    ·
      refine ⟨3412964625228260665762247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2275309750152173777174831 3412964625228260665762247)
      ·
        refine ⟨5119446937842390998643371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3412964625228260665762247 5119446937842390998643371)
        ·
          refine ⟨7679170406763586497965057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5119446937842390998643371 7679170406763586497965057)
          ·
            refine ⟨5759377805072689873473793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7679170406763586497965057 5759377805072689873473793)
            ·
              refine ⟨4319533353804517405105345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5759377805072689873473793 4319533353804517405105345)
              ·
                refine ⟨3239650015353388053829009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4319533353804517405105345 3239650015353388053829009)
                ·
                  refine ⟨2429737511515041040371757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3239650015353388053829009 2429737511515041040371757)
                  ·
                    refine ⟨911151566818140390139409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2429737511515041040371757 911151566818140390139409)
                    ·
                      refine ⟨683363675113605292604557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 911151566818140390139409 683363675113605292604557)
                      ·
                        rfl

theorem cell23_1330846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_1330846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330846 prefixEnd_1330846 := by exact prefixLift 1330846
  have htrace : WordTrace (prefixWord ++ tailWord_1330846) baseStart_1330846 baseEnd_1330846 := by
    simpa [prefixWord, tailWord_1330846, baseEnd_1330846] using wordTrace_append hprefix tailTrace_1330846
  have hstable : (prefixWord ++ tailWord_1330846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330846).length < 2 ^ (prefixWord ++ tailWord_1330846).sum := by decide
  have hdescent : baseEnd_1330846 < baseStart_1330846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330869 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 1, 6]
def baseStart_1330869 : Nat := 118140960795 + 1330869 * 2 ^ 59
def prefixEnd_1330869 : Nat := 4983230072969 + 3 ^ 40 * 1330869 * 2
def baseEnd_1330869 : Nat := 227791828389552900872317

theorem tailTrace_1330869 : CollatzResearch.WordTrace tailWord_1330869 prefixEnd_1330869 227791828389552900872317 := by
  unfold tailWord_1330869
  simp only [CollatzResearch.WordTrace]
  refine ⟨48540780215496382174483661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32360520143664254782989107 48540780215496382174483661)
  ·
    refine ⟨18202792580811143315431373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48540780215496382174483661 18202792580811143315431373)
    ·
      refine ⟨6826047217804178743286765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18202792580811143315431373 6826047217804178743286765)
      ·
        refine ⟨2559767706676567028732537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6826047217804178743286765 2559767706676567028732537)
        ·
          refine ⟨1919825780007425271549403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2559767706676567028732537 1919825780007425271549403)
          ·
            refine ⟨2879738670011137907324105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919825780007425271549403 2879738670011137907324105)
            ·
              refine ⟨2159804002508353430493079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2879738670011137907324105 2159804002508353430493079)
              ·
                refine ⟨3239706003762530145739619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159804002508353430493079 3239706003762530145739619)
                ·
                  refine ⟨4859559005643795218609429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3239706003762530145739619 4859559005643795218609429)
                  ·
                    refine ⟨227791828389552900872317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4859559005643795218609429 227791828389552900872317)
                    ·
                      rfl

theorem cell23_1330869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_1330869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330869 prefixEnd_1330869 := by exact prefixLift 1330869
  have htrace : WordTrace (prefixWord ++ tailWord_1330869) baseStart_1330869 baseEnd_1330869 := by
    simpa [prefixWord, tailWord_1330869, baseEnd_1330869] using wordTrace_append hprefix tailTrace_1330869
  have hstable : (prefixWord ++ tailWord_1330869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330869).length < 2 ^ (prefixWord ++ tailWord_1330869).sum := by decide
  have hdescent : baseEnd_1330869 < baseStart_1330869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330876 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 3, 2, 2]
def baseStart_1330876 : Nat := 118140960795 + 1330876 * 2 ^ 59
def prefixEnd_1330876 : Nat := 4983230072969 + 3 ^ 40 * 1330876 * 2
def baseEnd_1330876 : Nat := 683379079533240175229419

theorem tailTrace_1330876 : CollatzResearch.WordTrace tailWord_1330876 prefixEnd_1330876 683379079533240175229419 := by
  unfold tailWord_1330876
  simp only [CollatzResearch.WordTrace]
  refine ⟨24270517763235511184994241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32360690350980681579992321 24270517763235511184994241)
  ·
    refine ⟨18202888322426633388745681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24270517763235511184994241 18202888322426633388745681)
    ·
      refine ⟨13652166241819975041559261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18202888322426633388745681 13652166241819975041559261)
      ·
        refine ⟨5119562340682490640584723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13652166241819975041559261 5119562340682490640584723)
        ·
          refine ⟨7679343511023735960877085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5119562340682490640584723 7679343511023735960877085)
          ·
            refine ⟨2879753816633900985328907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7679343511023735960877085 2879753816633900985328907)
            ·
              refine ⟨4319630724950851477993361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2879753816633900985328907 4319630724950851477993361)
              ·
                refine ⟨3239723043713138608495021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4319630724950851477993361 3239723043713138608495021)
                ·
                  refine ⟨1214896141392426978185633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3239723043713138608495021 1214896141392426978185633)
                  ·
                    refine ⟨911172106044320233639225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1214896141392426978185633 911172106044320233639225)
                    ·
                      refine ⟨683379079533240175229419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 911172106044320233639225 683379079533240175229419)
                      ·
                        rfl

theorem cell23_1330876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_1330876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330876 prefixEnd_1330876 := by exact prefixLift 1330876
  have htrace : WordTrace (prefixWord ++ tailWord_1330876) baseStart_1330876 baseEnd_1330876 := by
    simpa [prefixWord, tailWord_1330876, baseEnd_1330876] using wordTrace_append hprefix tailTrace_1330876
  have hstable : (prefixWord ++ tailWord_1330876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330876).length < 2 ^ (prefixWord ++ tailWord_1330876).sum := by decide
  have hdescent : baseEnd_1330876 < baseStart_1330876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330886 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1330886 : Nat := 118140960795 + 1330886 * 2 ^ 59
def prefixEnd_1330886 : Nat := 4983230072969 + 3 ^ 40 * 1330886 * 2
def baseEnd_1330886 : Nat := 227794738113261712034791

theorem tailTrace_1330886 : CollatzResearch.WordTrace tailWord_1330886 prefixEnd_1330886 227794738113261712034791 := by
  unfold tailWord_1330886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1516918758013587314932891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32360933504289862718568341 1516918758013587314932891)
  ·
    refine ⟨2275378137020380972399337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1516918758013587314932891 2275378137020380972399337)
    ·
      refine ⟨1706533602765285729299503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2275378137020380972399337 1706533602765285729299503)
      ·
        refine ⟨2559800404147928593949255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1706533602765285729299503 2559800404147928593949255)
        ·
          refine ⟨3839700606221892890923883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2559800404147928593949255 3839700606221892890923883)
          ·
            refine ⟨5759550909332839336385825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3839700606221892890923883 5759550909332839336385825)
            ·
              refine ⟨4319663181999629502289369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5759550909332839336385825 4319663181999629502289369)
              ·
                refine ⟨3239747386499722126717027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4319663181999629502289369 3239747386499722126717027)
                ·
                  refine ⟨4859621079749583190075541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3239747386499722126717027 4859621079749583190075541)
                  ·
                    refine ⟨227794738113261712034791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4859621079749583190075541 227794738113261712034791)
                    ·
                      rfl

theorem cell23_1330886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1330886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330886 prefixEnd_1330886 := by exact prefixLift 1330886
  have htrace : WordTrace (prefixWord ++ tailWord_1330886) baseStart_1330886 baseEnd_1330886 := by
    simpa [prefixWord, tailWord_1330886, baseEnd_1330886] using wordTrace_append hprefix tailTrace_1330886
  have hstable : (prefixWord ++ tailWord_1330886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330886).length < 2 ^ (prefixWord ++ tailWord_1330886).sum := by decide
  have hdescent : baseEnd_1330886 < baseStart_1330886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330893 : List Nat := [1, 6, 2, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_1330893 : Nat := 118140960795 + 1330893 * 2 ^ 59
def prefixEnd_1330893 : Nat := 4983230072969 + 3 ^ 40 * 1330893 * 2
def baseEnd_1330893 : Nat := 683387808704366608716841

theorem tailTrace_1330893 : CollatzResearch.WordTrace tailWord_1330893 prefixEnd_1330893 683387808704366608716841 := by
  unfold tailWord_1330893
  simp only [CollatzResearch.WordTrace]
  refine ⟨48541655567409434273357333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32361103711606289515571555 48541655567409434273357333)
  ·
    refine ⟨2275390104722317231563625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48541655567409434273357333 2275390104722317231563625)
    ·
      refine ⟨1706542578541737923672719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2275390104722317231563625 1706542578541737923672719)
      ·
        refine ⟨2559813867812606885509079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1706542578541737923672719 2559813867812606885509079)
        ·
          refine ⟨3839720801718910328263619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2559813867812606885509079 3839720801718910328263619)
          ·
            refine ⟨5759581202578365492395429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3839720801718910328263619 5759581202578365492395429)
            ·
              refine ⟨1079921475483443529824143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5759581202578365492395429 1079921475483443529824143)
              ·
                refine ⟨1619882213225165294736215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079921475483443529824143 1619882213225165294736215)
                ·
                  refine ⟨2429823319837747942104323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619882213225165294736215 2429823319837747942104323)
                  ·
                    refine ⟨3644734979756621913156485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2429823319837747942104323 3644734979756621913156485)
                    ·
                      refine ⟨683387808704366608716841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3644734979756621913156485 683387808704366608716841)
                      ·
                        rfl

theorem cell23_1330893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_1330893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330893 prefixEnd_1330893 := by exact prefixLift 1330893
  have htrace : WordTrace (prefixWord ++ tailWord_1330893) baseStart_1330893 baseEnd_1330893 := by
    simpa [prefixWord, tailWord_1330893, baseEnd_1330893] using wordTrace_append hprefix tailTrace_1330893
  have hstable : (prefixWord ++ tailWord_1330893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330893).length < 2 ^ (prefixWord ++ tailWord_1330893).sum := by decide
  have hdescent : baseEnd_1330893 < baseStart_1330893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330950 : List Nat := [6, 2, 2, 1, 1, 2, 9]
def baseStart_1330950 : Nat := 118140960795 + 1330950 * 2 ^ 59
def prefixEnd_1330950 : Nat := 4983230072969 + 3 ^ 40 * 1330950 * 2
def baseEnd_1330950 : Nat := 8437247865452751675359

theorem tailTrace_1330950 : CollatzResearch.WordTrace tailWord_1330950 prefixEnd_1330950 8437247865452751675359 := by
  unfold tailWord_1330950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1516991704006341656505697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32362489685468622005454869 1516991704006341656505697)
  ·
    refine ⟨1137743778004756242379273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1516991704006341656505697 1137743778004756242379273)
    ·
      refine ⟨853307833503567181784455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1137743778004756242379273 853307833503567181784455)
      ·
        refine ⟨1279961750255350772676683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 853307833503567181784455 1279961750255350772676683)
        ·
          refine ⟨1919942625383026159015025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279961750255350772676683 1919942625383026159015025)
          ·
            refine ⟨1439956969037269619261269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1919942625383026159015025 1439956969037269619261269)
            ·
              refine ⟨8437247865452751675359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1439956969037269619261269 8437247865452751675359)
              ·
                rfl

theorem cell23_1330950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 9].length) (baseStart_1330950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330950 prefixEnd_1330950 := by exact prefixLift 1330950
  have htrace : WordTrace (prefixWord ++ tailWord_1330950) baseStart_1330950 baseEnd_1330950 := by
    simpa [prefixWord, tailWord_1330950, baseEnd_1330950] using wordTrace_append hprefix tailTrace_1330950
  have hstable : (prefixWord ++ tailWord_1330950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330950).length < 2 ^ (prefixWord ++ tailWord_1330950).sum := by decide
  have hdescent : baseEnd_1330950 < baseStart_1330950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330952 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_1330952 : Nat := 118140960795 + 1330952 * 2 ^ 59
def prefixEnd_1330952 : Nat := 4983230072969 + 3 ^ 40 * 1330952 * 2
def baseEnd_1330952 : Nat := 683418104062981877879069

theorem tailTrace_1330952 : CollatzResearch.WordTrace tailWord_1330952 prefixEnd_1330952 683418104062981877879069 := by
  unfold tailWord_1330952
  simp only [CollatzResearch.WordTrace]
  refine ⟨24271903737097843674877555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32362538316130458233170073 24271903737097843674877555)
  ·
    refine ⟨36407855605646765512316333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24271903737097843674877555 36407855605646765512316333)
    ·
      refine ⟨13652945852117537067118625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36407855605646765512316333 13652945852117537067118625)
      ·
        refine ⟨10239709389088152800338969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13652945852117537067118625 10239709389088152800338969)
        ·
          refine ⟨7679782041816114600254227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10239709389088152800338969 7679782041816114600254227)
          ·
            refine ⟨11519673062724171900381341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7679782041816114600254227 11519673062724171900381341)
            ·
              refine ⟨4319877398521564462643003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11519673062724171900381341 4319877398521564462643003)
              ·
                refine ⟨6479816097782346693964505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4319877398521564462643003 6479816097782346693964505)
                ·
                  refine ⟨4859862073336760020473379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6479816097782346693964505 4859862073336760020473379)
                  ·
                    refine ⟨7289793110005140030710069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4859862073336760020473379 7289793110005140030710069)
                    ·
                      refine ⟨683418104062981877879069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7289793110005140030710069 683418104062981877879069)
                      ·
                        rfl

theorem cell23_1330952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_1330952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330952 prefixEnd_1330952 := by exact prefixLift 1330952
  have htrace : WordTrace (prefixWord ++ tailWord_1330952) baseStart_1330952 baseEnd_1330952 := by
    simpa [prefixWord, tailWord_1330952, baseEnd_1330952] using wordTrace_append hprefix tailTrace_1330952
  have hstable : (prefixWord ++ tailWord_1330952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330952).length < 2 ^ (prefixWord ++ tailWord_1330952).sum := by decide
  have hdescent : baseEnd_1330952 < baseStart_1330952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330955 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 9]
def baseStart_1330955 : Nat := 118140960795 + 1330955 * 2 ^ 59
def prefixEnd_1330955 : Nat := 4983230072969 + 3 ^ 40 * 1330955 * 2
def baseEnd_1330955 : Nat := 75935516056105040682395

theorem tailTrace_1330955 : CollatzResearch.WordTrace tailWord_1330955 prefixEnd_1330955 75935516056105040682395 := by
  unfold tailWord_1330955
  simp only [CollatzResearch.WordTrace]
  refine ⟨48543916893184818862114319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32362611262123212574742879 48543916893184818862114319)
  ·
    refine ⟨72815875339777228293171479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48543916893184818862114319 72815875339777228293171479)
    ·
      refine ⟨109223813009665842439757219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72815875339777228293171479 109223813009665842439757219)
      ·
        refine ⟨163835719514498763659635829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109223813009665842439757219 163835719514498763659635829)
        ·
          refine ⟨15359598704484259093090859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163835719514498763659635829 15359598704484259093090859)
          ·
            refine ⟨23039398056726388639636289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15359598704484259093090859 23039398056726388639636289)
            ·
              refine ⟨17279548542544791479727217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23039398056726388639636289 17279548542544791479727217)
              ·
                refine ⟨12959661406908593609795413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17279548542544791479727217 12959661406908593609795413)
                ·
                  refine ⟨75935516056105040682395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12959661406908593609795413 75935516056105040682395)
                  ·
                    rfl

theorem cell23_1330955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 9].length) (baseStart_1330955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330955 prefixEnd_1330955 := by exact prefixLift 1330955
  have htrace : WordTrace (prefixWord ++ tailWord_1330955) baseStart_1330955 baseEnd_1330955 := by
    simpa [prefixWord, tailWord_1330955, baseEnd_1330955] using wordTrace_append hprefix tailTrace_1330955
  have hstable : (prefixWord ++ tailWord_1330955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330955).length < 2 ^ (prefixWord ++ tailWord_1330955).sum := by decide
  have hdescent : baseEnd_1330955 < baseStart_1330955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331022 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_1331022 : Nat := 118140960795 + 1331022 * 2 ^ 59
def prefixEnd_1331022 : Nat := 4983230072969 + 3 ^ 40 * 1331022 * 2
def baseEnd_1331022 : Nat := 683454047708796604003747

theorem tailTrace_1331022 : CollatzResearch.WordTrace tailWord_1331022 prefixEnd_1331022 683454047708796604003747 := by
  unfold tailWord_1331022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6068295072992761163100415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32364240389294726203202213 6068295072992761163100415)
  ·
    refine ⟨9102442609489141744650623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6068295072992761163100415 9102442609489141744650623)
    ·
      refine ⟨13653663914233712616975935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9102442609489141744650623 13653663914233712616975935)
      ·
        refine ⟨20480495871350568925463903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13653663914233712616975935 20480495871350568925463903)
        ·
          refine ⟨30720743807025853388195855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20480495871350568925463903 30720743807025853388195855)
          ·
            refine ⟨46081115710538780082293783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30720743807025853388195855 46081115710538780082293783)
            ·
              refine ⟨69121673565808170123440675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46081115710538780082293783 69121673565808170123440675)
              ·
                refine ⟨103682510348712255185161013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69121673565808170123440675 103682510348712255185161013)
                ·
                  refine ⟨9720235345191773923608845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103682510348712255185161013 9720235345191773923608845)
                  ·
                    refine ⟨3645088254446915221353317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9720235345191773923608845 3645088254446915221353317)
                    ·
                      refine ⟨683454047708796604003747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3645088254446915221353317 683454047708796604003747)
                      ·
                        rfl

theorem cell23_1331022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_1331022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331022 prefixEnd_1331022 := by exact prefixLift 1331022
  have htrace : WordTrace (prefixWord ++ tailWord_1331022) baseStart_1331022 baseEnd_1331022 := by
    simpa [prefixWord, tailWord_1331022, baseEnd_1331022] using wordTrace_append hprefix tailTrace_1331022
  have hstable : (prefixWord ++ tailWord_1331022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331022).length < 2 ^ (prefixWord ++ tailWord_1331022).sum := by decide
  have hdescent : baseEnd_1331022 < baseStart_1331022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331039 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 1, 6, 2]
def baseStart_1331039 : Nat := 118140960795 + 1331039 * 2 ^ 59
def prefixEnd_1331039 : Nat := 4983230072969 + 3 ^ 40 * 1331039 * 2
def baseEnd_1331039 : Nat := 683462776879923037491169

theorem tailTrace_1331039 : CollatzResearch.WordTrace tailWord_1331039 prefixEnd_1331039 683462776879923037491169 := by
  unfold tailWord_1331039
  simp only [CollatzResearch.WordTrace]
  refine ⟨48546980624880501208172171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32364653749920334138781447 48546980624880501208172171)
  ·
    refine ⟨72820470937320751812258257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48546980624880501208172171 72820470937320751812258257)
    ·
      refine ⟨54615353202990563859193693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72820470937320751812258257 54615353202990563859193693)
      ·
        refine ⟨20480757451121461447197635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54615353202990563859193693 20480757451121461447197635)
        ·
          refine ⟨30721136176682192170796453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20480757451121461447197635 30721136176682192170796453)
          ·
            refine ⟨5760213033127911032024335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30721136176682192170796453 5760213033127911032024335)
            ·
              refine ⟨8640319549691866548036503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5760213033127911032024335 8640319549691866548036503)
              ·
                refine ⟨12960479324537799822054755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8640319549691866548036503 12960479324537799822054755)
                ·
                  refine ⟨19440718986806699733082133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12960479324537799822054755 19440718986806699733082133)
                  ·
                    refine ⟨911283702506564049988225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19440718986806699733082133 911283702506564049988225)
                    ·
                      refine ⟨683462776879923037491169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 911283702506564049988225 683462776879923037491169)
                      ·
                        rfl

theorem cell23_1331039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_1331039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331039 prefixEnd_1331039 := by exact prefixLift 1331039
  have htrace : WordTrace (prefixWord ++ tailWord_1331039) baseStart_1331039 baseEnd_1331039 := by
    simpa [prefixWord, tailWord_1331039, baseEnd_1331039] using wordTrace_append hprefix tailTrace_1331039
  have hstable : (prefixWord ++ tailWord_1331039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331039).length < 2 ^ (prefixWord ++ tailWord_1331039).sum := by decide
  have hdescent : baseEnd_1331039 < baseStart_1331039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331066 : List Nat := [3, 1, 1, 1, 1, 1, 5, 5, 1, 4]
def baseStart_1331066 : Nat := 118140960795 + 1331066 * 2 ^ 59
def prefixEnd_1331066 : Nat := 4983230072969 + 3 ^ 40 * 1331066 * 2
def baseEnd_1331066 : Nat := 227825546952531477284515

theorem tailTrace_1331066 : CollatzResearch.WordTrace tailWord_1331066 prefixEnd_1331066 227825546952531477284515 := by
  unfold tailWord_1331066
  simp only [CollatzResearch.WordTrace]
  refine ⟨12136991348945671204851263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32365310263855123212936701 12136991348945671204851263)
  ·
    refine ⟨18205487023418506807276895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12136991348945671204851263 18205487023418506807276895)
    ·
      refine ⟨27308230535127760210915343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18205487023418506807276895 27308230535127760210915343)
      ·
        refine ⟨40962345802691640316373015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27308230535127760210915343 40962345802691640316373015)
        ·
          refine ⟨61443518704037460474559523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40962345802691640316373015 61443518704037460474559523)
          ·
            refine ⟨92165278056056190711839285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61443518704037460474559523 92165278056056190711839285)
            ·
              refine ⟨8640494817755267879234933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92165278056056190711839285 8640494817755267879234933)
              ·
                refine ⟨810046389164556363678275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8640494817755267879234933 810046389164556363678275)
                ·
                  refine ⟨1215069583746834545517413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810046389164556363678275 1215069583746834545517413)
                  ·
                    refine ⟨227825546952531477284515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1215069583746834545517413 227825546952531477284515)
                    ·
                      rfl

theorem cell23_1331066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 1, 4].length) (baseStart_1331066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331066 prefixEnd_1331066 := by exact prefixLift 1331066
  have htrace : WordTrace (prefixWord ++ tailWord_1331066) baseStart_1331066 baseEnd_1331066 := by
    simpa [prefixWord, tailWord_1331066, baseEnd_1331066] using wordTrace_append hprefix tailTrace_1331066
  have hstable : (prefixWord ++ tailWord_1331066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331066).length < 2 ^ (prefixWord ++ tailWord_1331066).sum := by decide
  have hdescent : baseEnd_1331066 < baseStart_1331066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331079 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 8]
def baseStart_1331079 : Nat := 118140960795 + 1331079 * 2 ^ 59
def prefixEnd_1331079 : Nat := 4983230072969 + 3 ^ 40 * 1331079 * 2
def baseEnd_1331079 : Nat := 75942590678455875665665

theorem tailTrace_1331079 : CollatzResearch.WordTrace tailWord_1331079 prefixEnd_1331079 75942590678455875665665 := by
  unfold tailWord_1331079
  simp only [CollatzResearch.WordTrace]
  refine ⟨48548439544735588039628291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32365626363157058693085527 48548439544735588039628291)
  ·
    refine ⟨72822659317103382059442437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48548439544735588039628291 72822659317103382059442437)
    ·
      refine ⟨13654248621956884136145457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72822659317103382059442437 13654248621956884136145457)
      ·
        refine ⟨10240686466467663102109093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13654248621956884136145457 10240686466467663102109093)
        ·
          refine ⟨1920128712462686831645455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10240686466467663102109093 1920128712462686831645455)
          ·
            refine ⟨2880193068694030247468183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920128712462686831645455 2880193068694030247468183)
            ·
              refine ⟨4320289603041045371202275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2880193068694030247468183 4320289603041045371202275)
              ·
                refine ⟨6480434404561568056803413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4320289603041045371202275 6480434404561568056803413)
                ·
                  refine ⟨75942590678455875665665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6480434404561568056803413 75942590678455875665665)
                  ·
                    rfl

theorem cell23_1331079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 8].length) (baseStart_1331079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331079 prefixEnd_1331079 := by exact prefixLift 1331079
  have htrace : WordTrace (prefixWord ++ tailWord_1331079) baseStart_1331079 baseEnd_1331079 := by
    simpa [prefixWord, tailWord_1331079, baseEnd_1331079] using wordTrace_append hprefix tailTrace_1331079
  have hstable : (prefixWord ++ tailWord_1331079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331079).length < 2 ^ (prefixWord ++ tailWord_1331079).sum := by decide
  have hdescent : baseEnd_1331079 < baseStart_1331079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331133 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 2, 3, 2]
def baseStart_1331133 : Nat := 118140960795 + 1331133 * 2 ^ 59
def prefixEnd_1331133 : Nat := 4983230072969 + 3 ^ 40 * 1331133 * 2
def baseEnd_1331133 : Nat := 683511044061445669715737

theorem tailTrace_1331133 : CollatzResearch.WordTrace tailWord_1331133 prefixEnd_1331133 683511044061445669715737 := by
  unfold tailWord_1331133
  simp only [CollatzResearch.WordTrace]
  refine ⟨48550409086539955262094053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32366939391026636841396035 48550409086539955262094053)
  ·
    refine ⟨9103201703726241611642635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48550409086539955262094053 9103201703726241611642635)
    ·
      refine ⟨13654802555589362417463953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9103201703726241611642635 13654802555589362417463953)
      ·
        refine ⟨10241101916692021813097965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13654802555589362417463953 10241101916692021813097965)
        ·
          refine ⟨3840413218759508179911737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10241101916692021813097965 3840413218759508179911737)
          ·
            refine ⟨2880309914069631134933803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3840413218759508179911737 2880309914069631134933803)
            ·
              refine ⟨4320464871104446702400705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2880309914069631134933803 4320464871104446702400705)
              ·
                refine ⟨3240348653328335026800529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4320464871104446702400705 3240348653328335026800529)
                ·
                  refine ⟨2430261489996251270100397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3240348653328335026800529 2430261489996251270100397)
                  ·
                    refine ⟨911348058748594226287649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2430261489996251270100397 911348058748594226287649)
                    ·
                      refine ⟨683511044061445669715737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 911348058748594226287649 683511044061445669715737)
                      ·
                        rfl

theorem cell23_1331133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_1331133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331133 prefixEnd_1331133 := by exact prefixLift 1331133
  have htrace : WordTrace (prefixWord ++ tailWord_1331133) baseStart_1331133 baseEnd_1331133 := by
    simpa [prefixWord, tailWord_1331133, baseEnd_1331133] using wordTrace_append hprefix tailTrace_1331133
  have hstable : (prefixWord ++ tailWord_1331133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331133).length < 2 ^ (prefixWord ++ tailWord_1331133).sum := by decide
  have hdescent : baseEnd_1331133 < baseStart_1331133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331152 : List Nat := [2, 1, 1, 1, 1, 2, 5, 10]
def baseStart_1331152 : Nat := 118140960795 + 1331152 * 2 ^ 59
def prefixEnd_1331152 : Nat := 4983230072969 + 3 ^ 40 * 1331152 * 2
def baseEnd_1331152 : Nat := 25315585192365966495487

theorem tailTrace_1331152 : CollatzResearch.WordTrace tailWord_1331152 prefixEnd_1331152 25315585192365966495487 := by
  unfold tailWord_1331152
  simp only [CollatzResearch.WordTrace]
  refine ⟨24275551036735560753517855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32367401382314081004690473 24275551036735560753517855)
  ·
    refine ⟨36413326555103341130276783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24275551036735560753517855 36413326555103341130276783)
    ·
      refine ⟨54619989832655011695415175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36413326555103341130276783 54619989832655011695415175)
      ·
        refine ⟨81929984748982517543122763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54619989832655011695415175 81929984748982517543122763)
        ·
          refine ⟨122894977123473776314684145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81929984748982517543122763 122894977123473776314684145)
          ·
            refine ⟨92171232842605332236013109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122894977123473776314684145 92171232842605332236013109)
            ·
              refine ⟨8641053078994249897126229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92171232842605332236013109 8641053078994249897126229)
              ·
                refine ⟨25315585192365966495487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8641053078994249897126229 25315585192365966495487)
                ·
                  rfl

theorem cell23_1331152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 10].length) (baseStart_1331152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331152 prefixEnd_1331152 := by exact prefixLift 1331152
  have htrace : WordTrace (prefixWord ++ tailWord_1331152) baseStart_1331152 baseEnd_1331152 := by
    simpa [prefixWord, tailWord_1331152, baseEnd_1331152] using wordTrace_append hprefix tailTrace_1331152
  have hstable : (prefixWord ++ tailWord_1331152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331152).length < 2 ^ (prefixWord ++ tailWord_1331152).sum := by decide
  have hdescent : baseEnd_1331152 < baseStart_1331152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331159 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 4]
def baseStart_1331159 : Nat := 118140960795 + 1331159 * 2 ^ 59
def prefixEnd_1331159 : Nat := 4983230072969 + 3 ^ 40 * 1331159 * 2
def baseEnd_1331159 : Nat := 683524394558462567990617

theorem tailTrace_1331159 : CollatzResearch.WordTrace tailWord_1331159 prefixEnd_1331159 683524394558462567990617 := by
  unfold tailWord_1331159
  simp only [CollatzResearch.WordTrace]
  refine ⟨48551357384445761702540531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32367571589630507801693687 48551357384445761702540531)
  ·
    refine ⟨72827036076668642553810797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48551357384445761702540531 72827036076668642553810797)
    ·
      refine ⟨27310138528750740957679049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72827036076668642553810797 27310138528750740957679049)
      ·
        refine ⟨20482603896563055718259287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27310138528750740957679049 20482603896563055718259287)
        ·
          refine ⟨30723905844844583577388931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20482603896563055718259287 30723905844844583577388931)
          ·
            refine ⟨46085858767266875366083397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30723905844844583577388931 46085858767266875366083397)
            ·
              refine ⟨8641098518862539131140637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46085858767266875366083397 8641098518862539131140637)
              ·
                refine ⟨3240411944573452174177739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8641098518862539131140637 3240411944573452174177739)
                ·
                  refine ⟨4860617916860178261266609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3240411944573452174177739 4860617916860178261266609)
                  ·
                    refine ⟨3645463437645133695949957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4860617916860178261266609 3645463437645133695949957)
                    ·
                      refine ⟨683524394558462567990617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3645463437645133695949957 683524394558462567990617)
                      ·
                        rfl

theorem cell23_1331159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_1331159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331159 prefixEnd_1331159 := by exact prefixLift 1331159
  have htrace : WordTrace (prefixWord ++ tailWord_1331159) baseStart_1331159 baseEnd_1331159 := by
    simpa [prefixWord, tailWord_1331159, baseEnd_1331159] using wordTrace_append hprefix tailTrace_1331159
  have hstable : (prefixWord ++ tailWord_1331159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331159).length < 2 ^ (prefixWord ++ tailWord_1331159).sum := by decide
  have hdescent : baseEnd_1331159 < baseStart_1331159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331183 : List Nat := [1, 1, 2, 1, 4, 2, 5, 1, 1, 2, 3]
def baseStart_1331183 : Nat := 118140960795 + 1331183 * 2 ^ 59
def prefixEnd_1331183 : Nat := 4983230072969 + 3 ^ 40 * 1331183 * 2
def baseEnd_1331183 : Nat := 683536718094170474090507

theorem tailTrace_1331183 : CollatzResearch.WordTrace tailWord_1331183 prefixEnd_1331183 683536718094170474090507 := by
  unfold tailWord_1331183
  simp only [CollatzResearch.WordTrace]
  refine ⟨48552232736358813801414203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32368155157572542534276135 48552232736358813801414203)
  ·
    refine ⟨72828349104538220702121305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48552232736358813801414203 72828349104538220702121305)
    ·
      refine ⟨54621261828403665526590979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72828349104538220702121305 54621261828403665526590979)
      ·
        refine ⟨81931892742605498289886469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54621261828403665526590979 81931892742605498289886469)
        ·
          refine ⟨15362229889238530929353713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81931892742605498289886469 15362229889238530929353713)
          ·
            refine ⟨11521672416928898197015285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15362229889238530929353713 11521672416928898197015285)
            ·
              refine ⟨1080156789087084205970183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11521672416928898197015285 1080156789087084205970183)
              ·
                refine ⟨1620235183630626308955275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080156789087084205970183 1620235183630626308955275)
                ·
                  refine ⟨2430352775445939463432913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620235183630626308955275 2430352775445939463432913)
                  ·
                    refine ⟨1822764581584454597574685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2430352775445939463432913 1822764581584454597574685)
                    ·
                      refine ⟨683536718094170474090507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1822764581584454597574685 683536718094170474090507)
                      ·
                        rfl

theorem cell23_1331183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 1, 2, 3].length) (baseStart_1331183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331183 prefixEnd_1331183 := by exact prefixLift 1331183
  have htrace : WordTrace (prefixWord ++ tailWord_1331183) baseStart_1331183 baseEnd_1331183 := by
    simpa [prefixWord, tailWord_1331183, baseEnd_1331183] using wordTrace_append hprefix tailTrace_1331183
  have hstable : (prefixWord ++ tailWord_1331183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331183).length < 2 ^ (prefixWord ++ tailWord_1331183).sum := by decide
  have hdescent : baseEnd_1331183 < baseStart_1331183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331190 : List Nat := [5, 1, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_1331190 : Nat := 118140960795 + 1331190 * 2 ^ 59
def prefixEnd_1331190 : Nat := 4983230072969 + 3 ^ 40 * 1331190 * 2
def baseEnd_1331190 : Nat := 227846770819583982234325

theorem tailTrace_1331190 : CollatzResearch.WordTrace tailWord_1331190 prefixEnd_1331190 227846770819583982234325 := by
  unfold tailWord_1331190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3034530502958340874807439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32368325364888969331279349 3034530502958340874807439)
  ·
    refine ⟨4551795754437511312211159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3034530502958340874807439 4551795754437511312211159)
    ·
      refine ⟨6827693631656266968316739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4551795754437511312211159 6827693631656266968316739)
      ·
        refine ⟨10241540447484400452475109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6827693631656266968316739 10241540447484400452475109)
        ·
          refine ⟨1920288833903325084839083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10241540447484400452475109 1920288833903325084839083)
          ·
            refine ⟨2880433250854987627258625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920288833903325084839083 2880433250854987627258625)
            ·
              refine ⟨2160324938141240720443969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2880433250854987627258625 2160324938141240720443969)
              ·
                refine ⟨1620243703605930540332977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2160324938141240720443969 1620243703605930540332977)
                ·
                  refine ⟨1215182777704447905249733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1620243703605930540332977 1215182777704447905249733)
                  ·
                    refine ⟨227846770819583982234325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1215182777704447905249733 227846770819583982234325)
                    ·
                      rfl

theorem cell23_1331190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_1331190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331190 prefixEnd_1331190 := by exact prefixLift 1331190
  have htrace : WordTrace (prefixWord ++ tailWord_1331190) baseStart_1331190 baseEnd_1331190 := by
    simpa [prefixWord, tailWord_1331190, baseEnd_1331190] using wordTrace_append hprefix tailTrace_1331190
  have hstable : (prefixWord ++ tailWord_1331190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331190).length < 2 ^ (prefixWord ++ tailWord_1331190).sum := by decide
  have hdescent : baseEnd_1331190 < baseStart_1331190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331197 : List Nat := [1, 4, 1, 1, 1, 2, 6, 2, 1, 2, 2]
def baseStart_1331197 : Nat := 118140960795 + 1331197 * 2 ^ 59
def prefixEnd_1331197 : Nat := 4983230072969 + 3 ^ 40 * 1331197 * 2
def baseEnd_1331197 : Nat := 683543906823333419315443

theorem tailTrace_1331197 : CollatzResearch.WordTrace tailWord_1331197 prefixEnd_1331197 683543906823333419315443 := by
  unfold tailWord_1331197
  simp only [CollatzResearch.WordTrace]
  refine ⟨48552743358308094192423845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32368495572205396128282563 48552743358308094192423845)
  ·
    refine ⟨9103639379682767661079471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48552743358308094192423845 9103639379682767661079471)
    ·
      refine ⟨13655459069524151491619207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9103639379682767661079471 13655459069524151491619207)
      ·
        refine ⟨20483188604286227237428811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13655459069524151491619207 20483188604286227237428811)
        ·
          refine ⟨30724782906429340856143217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20483188604286227237428811 30724782906429340856143217)
          ·
            refine ⟨23043587179822005642107413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30724782906429340856143217 23043587179822005642107413)
            ·
              refine ⟨1080168149054156514473785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23043587179822005642107413 1080168149054156514473785)
              ·
                refine ⟨810126111790617385855339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1080168149054156514473785 810126111790617385855339)
                ·
                  refine ⟨1215189167685926078783009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810126111790617385855339 1215189167685926078783009)
                  ·
                    refine ⟨911391875764444559087257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1215189167685926078783009 911391875764444559087257)
                    ·
                      refine ⟨683543906823333419315443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 911391875764444559087257 683543906823333419315443)
                      ·
                        rfl

theorem cell23_1331197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_1331197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331197 prefixEnd_1331197 := by exact prefixLift 1331197
  have htrace : WordTrace (prefixWord ++ tailWord_1331197) baseStart_1331197 baseEnd_1331197 := by
    simpa [prefixWord, tailWord_1331197, baseEnd_1331197] using wordTrace_append hprefix tailTrace_1331197
  have hstable : (prefixWord ++ tailWord_1331197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331197).length < 2 ^ (prefixWord ++ tailWord_1331197).sum := by decide
  have hdescent : baseEnd_1331197 < baseStart_1331197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331220 : List Nat := [2, 4, 3, 2, 1, 1, 3, 7]
def baseStart_1331220 : Nat := 118140960795 + 1331220 * 2 ^ 59
def prefixEnd_1331220 : Nat := 4983230072969 + 3 ^ 40 * 1331220 * 2
def baseEnd_1331220 : Nat := 25316878402903215901031

theorem tailTrace_1331220 : CollatzResearch.WordTrace tailWord_1331220 prefixEnd_1331220 25316878402903215901031 := by
  unfold tailWord_1331220
  simp only [CollatzResearch.WordTrace]
  refine ⟨24276791118612384560255557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32369054824816512747007409 24276791118612384560255557)
  ·
    refine ⟨4551898334739822105047917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24276791118612384560255557 4551898334739822105047917)
    ·
      refine ⟨1706961875527433289392969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4551898334739822105047917 1706961875527433289392969)
      ·
        refine ⟨1280221406645574967044727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1706961875527433289392969 1280221406645574967044727)
        ·
          refine ⟨1920332109968362450567091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1280221406645574967044727 1920332109968362450567091)
          ·
            refine ⟨2880498164952543675850637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920332109968362450567091 2880498164952543675850637)
            ·
              refine ⟨1080186811857203878443989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2880498164952543675850637 1080186811857203878443989)
              ·
                refine ⟨25316878402903215901031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1080186811857203878443989 25316878402903215901031)
                ·
                  rfl

theorem cell23_1331220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 7].length) (baseStart_1331220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331220 prefixEnd_1331220 := by exact prefixLift 1331220
  have htrace : WordTrace (prefixWord ++ tailWord_1331220) baseStart_1331220 baseEnd_1331220 := by
    simpa [prefixWord, tailWord_1331220, baseEnd_1331220] using wordTrace_append hprefix tailTrace_1331220
  have hstable : (prefixWord ++ tailWord_1331220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331220).length < 2 ^ (prefixWord ++ tailWord_1331220).sum := by decide
  have hdescent : baseEnd_1331220 < baseStart_1331220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331246 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 2, 6]
def baseStart_1331246 : Nat := 118140960795 + 1331246 * 2 ^ 59
def prefixEnd_1331246 : Nat := 4983230072969 + 3 ^ 40 * 1331246 * 2
def baseEnd_1331246 : Nat := 227856355791801242534239

theorem tailTrace_1331246 : CollatzResearch.WordTrace tailWord_1331246 prefixEnd_1331246 227856355791801242534239 := by
  unfold tailWord_1331246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6069316316891321945119699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32369687023420383707305061 6069316316891321945119699)
  ·
    refine ⟨9103974475336982917679549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6069316316891321945119699 9103974475336982917679549)
    ·
      refine ⟨3413990428251368594129831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9103974475336982917679549 3413990428251368594129831)
      ·
        refine ⟨5120985642377052891194747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3413990428251368594129831 5120985642377052891194747)
        ·
          refine ⟨7681478463565579336792121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5120985642377052891194747 7681478463565579336792121)
          ·
            refine ⟨5761108847674184502594091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7681478463565579336792121 5761108847674184502594091)
            ·
              refine ⟨8641663271511276753891137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5761108847674184502594091 8641663271511276753891137)
              ·
                refine ⟨6481247453633457565418353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8641663271511276753891137 6481247453633457565418353)
                ·
                  refine ⟨4860935590225093174063765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6481247453633457565418353 4860935590225093174063765)
                  ·
                    refine ⟨227856355791801242534239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4860935590225093174063765 227856355791801242534239)
                    ·
                      rfl

theorem cell23_1331246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_1331246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331246 prefixEnd_1331246 := by exact prefixLift 1331246
  have htrace : WordTrace (prefixWord ++ tailWord_1331246) baseStart_1331246 baseEnd_1331246 := by
    simpa [prefixWord, tailWord_1331246, baseEnd_1331246] using wordTrace_append hprefix tailTrace_1331246
  have hstable : (prefixWord ++ tailWord_1331246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331246).length < 2 ^ (prefixWord ++ tailWord_1331246).sum := by decide
  have hdescent : baseEnd_1331246 < baseStart_1331246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331289 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 1, 7]
def baseStart_1331289 : Nat := 118140960795 + 1331289 * 2 ^ 59
def prefixEnd_1331289 : Nat := 4983230072969 + 3 ^ 40 * 1331289 * 2
def baseEnd_1331289 : Nat := 227863715681182353121673

theorem tailTrace_1331289 : CollatzResearch.WordTrace tailWord_1331289 prefixEnd_1331289 227863715681182353121673 := by
  unfold tailWord_1331289
  simp only [CollatzResearch.WordTrace]
  refine ⟨48556098873974793904772921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32370732582649862603181947 48556098873974793904772921)
  ·
    refine ⟨36417074155481095428579691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48556098873974793904772921 36417074155481095428579691)
    ·
      refine ⟨54625611233221643142869537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36417074155481095428579691 54625611233221643142869537)
      ·
        refine ⟨40969208424916232357152153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54625611233221643142869537 40969208424916232357152153)
        ·
          refine ⟨30726906318687174267864115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40969208424916232357152153 30726906318687174267864115)
          ·
            refine ⟨46090359478030761401796173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30726906318687174267864115 46090359478030761401796173)
            ·
              refine ⟨17283884804261535525673565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46090359478030761401796173 17283884804261535525673565)
              ·
                refine ⟨6481456801598075822127587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17283884804261535525673565 6481456801598075822127587)
                ·
                  refine ⟨9722185202397113733191381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6481456801598075822127587 9722185202397113733191381)
                  ·
                    refine ⟨227863715681182353121673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9722185202397113733191381 227863715681182353121673)
                    ·
                      rfl

theorem cell23_1331289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 7].length) (baseStart_1331289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331289 prefixEnd_1331289 := by exact prefixLift 1331289
  have htrace : WordTrace (prefixWord ++ tailWord_1331289) baseStart_1331289 baseEnd_1331289 := by
    simpa [prefixWord, tailWord_1331289, baseEnd_1331289] using wordTrace_append hprefix tailTrace_1331289
  have hstable : (prefixWord ++ tailWord_1331289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331289).length < 2 ^ (prefixWord ++ tailWord_1331289).sum := by decide
  have hdescent : baseEnd_1331289 < baseStart_1331289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331310 : List Nat := [4, 1, 2, 2, 1, 1, 5, 2, 5]
def baseStart_1331310 : Nat := 118140960795 + 1331310 * 2 ^ 59
def prefixEnd_1331310 : Nat := 4983230072969 + 3 ^ 40 * 1331310 * 2
def baseEnd_1331310 : Nat := 75955770015254608578047

theorem tailTrace_1331310 : CollatzResearch.WordTrace tailWord_1331310 prefixEnd_1331310 75955770015254608578047 := by
  unfold tailWord_1331310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6069608100862339311410923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32371243204599142994191589 6069608100862339311410923)
  ·
    refine ⟨9104412151293508967116385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6069608100862339311410923 9104412151293508967116385)
    ·
      refine ⟨6828309113470131725337289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9104412151293508967116385 6828309113470131725337289)
      ·
        refine ⟨5121231835102598794002967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6828309113470131725337289 5121231835102598794002967)
        ·
          refine ⟨7681847752653898191004451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5121231835102598794002967 7681847752653898191004451)
          ·
            refine ⟨11522771628980847286506677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7681847752653898191004451 11522771628980847286506677)
            ·
              refine ⟨1080259840216954433110001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11522771628980847286506677 1080259840216954433110001)
              ·
                refine ⟨810194880162715824832501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1080259840216954433110001 810194880162715824832501)
                ·
                  refine ⟨75955770015254608578047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 810194880162715824832501 75955770015254608578047)
                  ·
                    rfl

theorem cell23_1331310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_1331310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331310 prefixEnd_1331310 := by exact prefixLift 1331310
  have htrace : WordTrace (prefixWord ++ tailWord_1331310) baseStart_1331310 baseEnd_1331310 := by
    simpa [prefixWord, tailWord_1331310, baseEnd_1331310] using wordTrace_append hprefix tailTrace_1331310
  have hstable : (prefixWord ++ tailWord_1331310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331310).length < 2 ^ (prefixWord ++ tailWord_1331310).sum := by decide
  have hdescent : baseEnd_1331310 < baseStart_1331310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331339 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 6]
def baseStart_1331339 : Nat := 118140960795 + 1331339 * 2 ^ 59
def prefixEnd_1331339 : Nat := 4983230072969 + 3 ^ 40 * 1331339 * 2
def baseEnd_1331339 : Nat := 683616821076271863739789

theorem tailTrace_1331339 : CollatzResearch.WordTrace tailWord_1331339 prefixEnd_1331339 683616821076271863739789 := by
  unfold tailWord_1331339
  simp only [CollatzResearch.WordTrace]
  refine ⟨48557922523793652444093071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32371948349195768296062047 48557922523793652444093071)
  ·
    refine ⟨72836883785690478666139607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48557922523793652444093071 72836883785690478666139607)
    ·
      refine ⟨109255325678535717999209411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72836883785690478666139607 109255325678535717999209411)
      ·
        refine ⟨163882988517803576998814117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109255325678535717999209411 163882988517803576998814117)
        ·
          refine ⟨30728060347088170687277647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163882988517803576998814117 30728060347088170687277647)
          ·
            refine ⟨46092090520632256030916471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30728060347088170687277647 46092090520632256030916471)
            ·
              refine ⟨69138135780948384046374707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46092090520632256030916471 69138135780948384046374707)
              ·
                refine ⟨103707203671422576069562061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69138135780948384046374707 103707203671422576069562061)
                ·
                  refine ⟨38890201376783466026085773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103707203671422576069562061 38890201376783466026085773)
                  ·
                    refine ⟨14583825516293799759782165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38890201376783466026085773 14583825516293799759782165)
                    ·
                      refine ⟨683616821076271863739789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14583825516293799759782165 683616821076271863739789)
                      ·
                        rfl

theorem cell23_1331339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 6].length) (baseStart_1331339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331339 prefixEnd_1331339 := by exact prefixLift 1331339
  have htrace : WordTrace (prefixWord ++ tailWord_1331339) baseStart_1331339 baseEnd_1331339 := by
    simpa [prefixWord, tailWord_1331339, baseEnd_1331339] using wordTrace_append hprefix tailTrace_1331339
  have hstable : (prefixWord ++ tailWord_1331339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331339).length < 2 ^ (prefixWord ++ tailWord_1331339).sum := by decide
  have hdescent : baseEnd_1331339 < baseStart_1331339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331356 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1331356 : Nat := 118140960795 + 1331356 * 2 ^ 59
def prefixEnd_1331356 : Nat := 4983230072969 + 3 ^ 40 * 1331356 * 2
def baseEnd_1331356 : Nat := 683625550247398297227211

theorem tailTrace_1331356 : CollatzResearch.WordTrace tailWord_1331356 prefixEnd_1331356 683625550247398297227211 := by
  unfold tailWord_1331356
  simp only [CollatzResearch.WordTrace]
  refine ⟨24279271282366032173730961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32372361709821376231641281 24279271282366032173730961)
  ·
    refine ⟨18209453461774524130298221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24279271282366032173730961 18209453461774524130298221)
    ·
      refine ⟨6828545048165446548861833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18209453461774524130298221 6828545048165446548861833)
      ·
        refine ⟨5121408786124084911646375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6828545048165446548861833 5121408786124084911646375)
        ·
          refine ⟨7682113179186127367469563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5121408786124084911646375 7682113179186127367469563)
          ·
            refine ⟨11523169768779191051204345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7682113179186127367469563 11523169768779191051204345)
            ·
              refine ⟨8642377326584393288403259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11523169768779191051204345 8642377326584393288403259)
              ·
                refine ⟨12963565989876589932604889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8642377326584393288403259 12963565989876589932604889)
                ·
                  refine ⟨9722674492407442449453667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12963565989876589932604889 9722674492407442449453667)
                  ·
                    refine ⟨14584011738611163674180501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9722674492407442449453667 14584011738611163674180501)
                    ·
                      refine ⟨683625550247398297227211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14584011738611163674180501 683625550247398297227211)
                      ·
                        rfl

theorem cell23_1331356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1331356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331356 prefixEnd_1331356 := by exact prefixLift 1331356
  have htrace : WordTrace (prefixWord ++ tailWord_1331356) baseStart_1331356 baseEnd_1331356 := by
    simpa [prefixWord, tailWord_1331356, baseEnd_1331356] using wordTrace_append hprefix tailTrace_1331356
  have hstable : (prefixWord ++ tailWord_1331356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331356).length < 2 ^ (prefixWord ++ tailWord_1331356).sum := by decide
  have hdescent : baseEnd_1331356 < baseStart_1331356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331394 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_1331394 : Nat := 118140960795 + 1331394 * 2 ^ 59
def prefixEnd_1331394 : Nat := 4983230072969 + 3 ^ 40 * 1331394 * 2
def baseEnd_1331394 : Nat := 683645062512269148552037

theorem tailTrace_1331394 : CollatzResearch.WordTrace tailWord_1331394 prefixEnd_1331394 683645062512269148552037 := by
  unfold tailWord_1331394
  simp only [CollatzResearch.WordTrace]
  refine ⟨12139982134648599209336309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32373285692396264558230157 12139982134648599209336309)
  ·
    refine ⟨1138123325123306175875279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12139982134648599209336309 1138123325123306175875279)
    ·
      refine ⟨1707184987684959263812919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1138123325123306175875279 1707184987684959263812919)
      ·
        refine ⟨2560777481527438895719379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1707184987684959263812919 2560777481527438895719379)
        ·
          refine ⟨3841166222291158343579069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2560777481527438895719379 3841166222291158343579069)
          ·
            refine ⟨1440437333359184378842151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3841166222291158343579069 1440437333359184378842151)
            ·
              refine ⟨2160656000038776568263227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1440437333359184378842151 2160656000038776568263227)
              ·
                refine ⟨3240984000058164852394841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2160656000038776568263227 3240984000058164852394841)
                ·
                  refine ⟨2430738000043623639296131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3240984000058164852394841 2430738000043623639296131)
                  ·
                    refine ⟨3646107000065435458944197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2430738000043623639296131 3646107000065435458944197)
                    ·
                      refine ⟨683645062512269148552037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3646107000065435458944197 683645062512269148552037)
                      ·
                        rfl

theorem cell23_1331394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_1331394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331394 prefixEnd_1331394 := by exact prefixLift 1331394
  have htrace : WordTrace (prefixWord ++ tailWord_1331394) baseStart_1331394 baseEnd_1331394 := by
    simpa [prefixWord, tailWord_1331394, baseEnd_1331394] using wordTrace_append hprefix tailTrace_1331394
  have hstable : (prefixWord ++ tailWord_1331394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331394).length < 2 ^ (prefixWord ++ tailWord_1331394).sum := by decide
  have hdescent : baseEnd_1331394 < baseStart_1331394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331403 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 1, 5, 2]
def baseStart_1331403 : Nat := 118140960795 + 1331403 * 2 ^ 59
def prefixEnd_1331403 : Nat := 4983230072969 + 3 ^ 40 * 1331403 * 2
def baseEnd_1331403 : Nat := 683649683838159613339495

theorem tailTrace_1331403 : CollatzResearch.WordTrace tailWord_1331403 prefixEnd_1331403 683649683838159613339495 := by
  unfold tailWord_1331403
  simp only [CollatzResearch.WordTrace]
  refine ⟨48560256795561791374422863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32373504530374527582948575 48560256795561791374422863)
  ·
    refine ⟨72840385193342687061634295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48560256795561791374422863 72840385193342687061634295)
    ·
      refine ⟨109260577790014030592451443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72840385193342687061634295 109260577790014030592451443)
      ·
        refine ⟨163890866685021045888677165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109260577790014030592451443 163890866685021045888677165)
        ·
          refine ⟨61459075006882892208253937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163890866685021045888677165 61459075006882892208253937)
          ·
            refine ⟨46094306255162169156190453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61459075006882892208253937 46094306255162169156190453)
            ·
              refine ⟨4321341211421453358392855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46094306255162169156190453 4321341211421453358392855)
              ·
                refine ⟨6482011817132180037589283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4321341211421453358392855 6482011817132180037589283)
                ·
                  refine ⟨9723017725698270056383925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6482011817132180037589283 9723017725698270056383925)
                  ·
                    refine ⟨911532911784212817785993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9723017725698270056383925 911532911784212817785993)
                    ·
                      refine ⟨683649683838159613339495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 911532911784212817785993 683649683838159613339495)
                      ·
                        rfl

theorem cell23_1331403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 5, 2].length) (baseStart_1331403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331403 prefixEnd_1331403 := by exact prefixLift 1331403
  have htrace : WordTrace (prefixWord ++ tailWord_1331403) baseStart_1331403 baseEnd_1331403 := by
    simpa [prefixWord, tailWord_1331403, baseEnd_1331403] using wordTrace_append hprefix tailTrace_1331403
  have hstable : (prefixWord ++ tailWord_1331403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331403).length < 2 ^ (prefixWord ++ tailWord_1331403).sum := by decide
  have hdescent : baseEnd_1331403 < baseStart_1331403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331404 : List Nat := [2, 2, 1, 6, 1, 1, 2, 3, 1, 4]
def baseStart_1331404 : Nat := 118140960795 + 1331404 * 2 ^ 59
def prefixEnd_1331404 : Nat := 4983230072969 + 3 ^ 40 * 1331404 * 2
def baseEnd_1331404 : Nat := 227883399106271369808997

theorem tailTrace_1331404 : CollatzResearch.WordTrace tailWord_1331404 prefixEnd_1331404 227883399106271369808997 := by
  unfold tailWord_1331404
  simp only [CollatzResearch.WordTrace]
  refine ⟨24280146634279084272604633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32373528845705445696806177 24280146634279084272604633)
  ·
    refine ⟨18210109975709313204453475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24280146634279084272604633 18210109975709313204453475)
    ·
      refine ⟨27315164963563969806680213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18210109975709313204453475 27315164963563969806680213)
      ·
        refine ⟨1280398357667061084688135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27315164963563969806680213 1280398357667061084688135)
        ·
          refine ⟨1920597536500591627032203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1280398357667061084688135 1920597536500591627032203)
          ·
            refine ⟨2880896304750887440548305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920597536500591627032203 2880896304750887440548305)
            ·
              refine ⟨2160672228563165580411229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2880896304750887440548305 2160672228563165580411229)
              ·
                refine ⟨810252085711187092654211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2160672228563165580411229 810252085711187092654211)
                ·
                  refine ⟨1215378128566780638981317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810252085711187092654211 1215378128566780638981317)
                  ·
                    refine ⟨227883399106271369808997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1215378128566780638981317 227883399106271369808997)
                    ·
                      rfl

theorem cell23_1331404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 1, 4].length) (baseStart_1331404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331404 prefixEnd_1331404 := by exact prefixLift 1331404
  have htrace : WordTrace (prefixWord ++ tailWord_1331404) baseStart_1331404 baseEnd_1331404 := by
    simpa [prefixWord, tailWord_1331404, baseEnd_1331404] using wordTrace_append hprefix tailTrace_1331404
  have hstable : (prefixWord ++ tailWord_1331404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331404).length < 2 ^ (prefixWord ++ tailWord_1331404).sum := by decide
  have hdescent : baseEnd_1331404 < baseStart_1331404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331450 : List Nat := [3, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4]
def baseStart_1331450 : Nat := 118140960795 + 1331450 * 2 ^ 59
def prefixEnd_1331450 : Nat := 4983230072969 + 3 ^ 40 * 1331450 * 2
def baseEnd_1331450 : Nat := 683673817428920929451779

theorem tailTrace_1331450 : CollatzResearch.WordTrace tailWord_1331450 prefixEnd_1331450 683673817428920929451779 := by
  unfold tailWord_1331450
  simp only [CollatzResearch.WordTrace]
  refine ⟨12140492756597879600345951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32374647350927678934255869 12140492756597879600345951)
  ·
    refine ⟨18210739134896819400518927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12140492756597879600345951 18210739134896819400518927)
    ·
      refine ⟨27316108702345229100778391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18210739134896819400518927 27316108702345229100778391)
      ·
        refine ⟨40974163053517843651167587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27316108702345229100778391 40974163053517843651167587)
        ·
          refine ⟨61461244580276765476751381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40974163053517843651167587 61461244580276765476751381)
          ·
            refine ⟨2880995839700473381722721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61461244580276765476751381 2880995839700473381722721)
            ·
              refine ⟨2160746879775355036292041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2880995839700473381722721 2160746879775355036292041)
              ·
                refine ⟨1620560159831516277219031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2160746879775355036292041 1620560159831516277219031)
                ·
                  refine ⟨2430840239747274415828547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620560159831516277219031 2430840239747274415828547)
                  ·
                    refine ⟨3646260359620911623742821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2430840239747274415828547 3646260359620911623742821)
                    ·
                      refine ⟨683673817428920929451779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3646260359620911623742821 683673817428920929451779)
                      ·
                        rfl

theorem cell23_1331450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_1331450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331450 prefixEnd_1331450 := by exact prefixLift 1331450
  have htrace : WordTrace (prefixWord ++ tailWord_1331450) baseStart_1331450 baseEnd_1331450 := by
    simpa [prefixWord, tailWord_1331450, baseEnd_1331450] using wordTrace_append hprefix tailTrace_1331450
  have hstable : (prefixWord ++ tailWord_1331450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331450).length < 2 ^ (prefixWord ++ tailWord_1331450).sum := by decide
  have hdescent : baseEnd_1331450 < baseStart_1331450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331453 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 3, 2, 3]
def baseStart_1331453 : Nat := 118140960795 + 1331453 * 2 ^ 59
def prefixEnd_1331453 : Nat := 4983230072969 + 3 ^ 40 * 1331453 * 2
def baseEnd_1331453 : Nat := 683675357870884417714265

theorem tailTrace_1331453 : CollatzResearch.WordTrace tailWord_1331453 prefixEnd_1331453 683675357870884417714265 := by
  unfold tailWord_1331453
  simp only [CollatzResearch.WordTrace]
  refine ⟨48562080445380649913743013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32374720296920433275828675 48562080445380649913743013)
  ·
    refine ⟨9105390083508871858826815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48562080445380649913743013 9105390083508871858826815)
    ·
      refine ⟨13658085125263307788240223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9105390083508871858826815 13658085125263307788240223)
      ·
        refine ⟨20487127687894961682360335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13658085125263307788240223 20487127687894961682360335)
        ·
          refine ⟨30730691531842442523540503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20487127687894961682360335 30730691531842442523540503)
          ·
            refine ⟨46096037297763663785310755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30730691531842442523540503 46096037297763663785310755)
            ·
              refine ⟨69144055946645495677966133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46096037297763663785310755 69144055946645495677966133)
              ·
                refine ⟨6482255244998015219809325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69144055946645495677966133 6482255244998015219809325)
                ·
                  refine ⟨2430845716874255707428497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6482255244998015219809325 2430845716874255707428497)
                  ·
                    refine ⟨1823134287655691780571373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2430845716874255707428497 1823134287655691780571373)
                    ·
                      refine ⟨683675357870884417714265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1823134287655691780571373 683675357870884417714265)
                      ·
                        rfl

theorem cell23_1331453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_1331453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331453 prefixEnd_1331453 := by exact prefixLift 1331453
  have htrace : WordTrace (prefixWord ++ tailWord_1331453) baseStart_1331453 baseEnd_1331453 := by
    simpa [prefixWord, tailWord_1331453, baseEnd_1331453] using wordTrace_append hprefix tailTrace_1331453
  have hstable : (prefixWord ++ tailWord_1331453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331453).length < 2 ^ (prefixWord ++ tailWord_1331453).sum := by decide
  have hdescent : baseEnd_1331453 < baseStart_1331453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331470 : List Nat := [4, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3]
def baseStart_1331470 : Nat := 118140960795 + 1331470 * 2 ^ 59
def prefixEnd_1331470 : Nat := 4983230072969 + 3 ^ 40 * 1331470 * 2
def baseEnd_1331470 : Nat := 683684087042010851201687

theorem tailTrace_1331470 : CollatzResearch.WordTrace tailWord_1331470 prefixEnd_1331470 683684087042010851201687 := by
  unfold tailWord_1331470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6070337560789882727138983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32375133657546041211407909 6070337560789882727138983)
  ·
    refine ⟨9105506341184824090708475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6070337560789882727138983 9105506341184824090708475)
    ·
      refine ⟨13658259511777236136062713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9105506341184824090708475 13658259511777236136062713)
      ·
        refine ⟨10243694633832927102047035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13658259511777236136062713 10243694633832927102047035)
        ·
          refine ⟨15365541950749390653070553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10243694633832927102047035 15365541950749390653070553)
          ·
            refine ⟨11524156463062042989802915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15365541950749390653070553 11524156463062042989802915)
            ·
              refine ⟨17286234694593064484704373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11524156463062042989802915 17286234694593064484704373)
              ·
                refine ⟨1620584502618099795441035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17286234694593064484704373 1620584502618099795441035)
                ·
                  refine ⟨2430876753927149693161553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620584502618099795441035 2430876753927149693161553)
                  ·
                    refine ⟨1823157565445362269871165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2430876753927149693161553 1823157565445362269871165)
                    ·
                      refine ⟨683684087042010851201687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1823157565445362269871165 683684087042010851201687)
                      ·
                        rfl

theorem cell23_1331470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_1331470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331470 prefixEnd_1331470 := by exact prefixLift 1331470
  have htrace : WordTrace (prefixWord ++ tailWord_1331470) baseStart_1331470 baseEnd_1331470 := by
    simpa [prefixWord, tailWord_1331470, baseEnd_1331470] using wordTrace_append hprefix tailTrace_1331470
  have hstable : (prefixWord ++ tailWord_1331470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331470).length < 2 ^ (prefixWord ++ tailWord_1331470).sum := by decide
  have hdescent : baseEnd_1331470 < baseStart_1331470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331501 : List Nat := [1, 5, 3, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_1331501 : Nat := 118140960795 + 1331501 * 2 ^ 59
def prefixEnd_1331501 : Nat := 4983230072969 + 3 ^ 40 * 1331501 * 2
def baseEnd_1331501 : Nat := 683700004942300229914045

theorem tailTrace_1331501 : CollatzResearch.WordTrace tailWord_1331501 prefixEnd_1331501 683700004942300229914045 := by
  unfold tailWord_1331501
  simp only [CollatzResearch.WordTrace]
  refine ⟨48563831149206754111490357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32375887432804502740993571 48563831149206754111490357)
  ·
    refine ⟨4552859170238133197952221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48563831149206754111490357 4552859170238133197952221)
    ·
      refine ⟨1707322188839299949232083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4552859170238133197952221 1707322188839299949232083)
      ·
        refine ⟨2560983283258949923848125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1707322188839299949232083 2560983283258949923848125)
        ·
          refine ⟨960368731222106221443047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2560983283258949923848125 960368731222106221443047)
          ·
            refine ⟨1440553096833159332164571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960368731222106221443047 1440553096833159332164571)
            ·
              refine ⟨2160829645249738998246857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1440553096833159332164571 2160829645249738998246857)
              ·
                refine ⟨1620622233937304248685143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2160829645249738998246857 1620622233937304248685143)
                ·
                  refine ⟨2430933350905956373027715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620622233937304248685143 2430933350905956373027715)
                  ·
                    refine ⟨3646400026358934559541573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2430933350905956373027715 3646400026358934559541573)
                    ·
                      refine ⟨683700004942300229914045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3646400026358934559541573 683700004942300229914045)
                      ·
                        rfl

theorem cell23_1331501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_1331501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331501 prefixEnd_1331501 := by exact prefixLift 1331501
  have htrace : WordTrace (prefixWord ++ tailWord_1331501) baseStart_1331501 baseEnd_1331501 := by
    simpa [prefixWord, tailWord_1331501, baseEnd_1331501] using wordTrace_append hprefix tailTrace_1331501
  have hstable : (prefixWord ++ tailWord_1331501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331501).length < 2 ^ (prefixWord ++ tailWord_1331501).sum := by decide
  have hdescent : baseEnd_1331501 < baseStart_1331501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331543 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 3]
def baseStart_1331543 : Nat := 118140960795 + 1331543 * 2 ^ 59
def prefixEnd_1331543 : Nat := 4983230072969 + 3 ^ 40 * 1331543 * 2
def baseEnd_1331543 : Nat := 683721571129789065588851

theorem tailTrace_1331543 : CollatzResearch.WordTrace tailWord_1331543 prefixEnd_1331543 683721571129789065588851 := by
  unfold tailWord_1331543
  simp only [CollatzResearch.WordTrace]
  refine ⟨48565363015054595284519283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32376908676703063523012855 48565363015054595284519283)
  ·
    refine ⟨72848044522581892926778925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48565363015054595284519283 72848044522581892926778925)
    ·
      refine ⟨27318016695968209847542097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72848044522581892926778925 27318016695968209847542097)
      ·
        refine ⟨20488512521976157385656573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27318016695968209847542097 20488512521976157385656573)
        ·
          refine ⟨7683192195741059019621215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20488512521976157385656573 7683192195741059019621215)
          ·
            refine ⟨11524788293611588529431823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7683192195741059019621215 11524788293611588529431823)
            ·
              refine ⟨17287182440417382794147735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11524788293611588529431823 17287182440417382794147735)
              ·
                refine ⟨25930773660626074191221603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17287182440417382794147735 25930773660626074191221603)
                ·
                  refine ⟨38896160490939111286832405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25930773660626074191221603 38896160490939111286832405)
                  ·
                    refine ⟨1823257523012770841570269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38896160490939111286832405 1823257523012770841570269)
                    ·
                      refine ⟨683721571129789065588851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1823257523012770841570269 683721571129789065588851)
                      ·
                        rfl

theorem cell23_1331543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_1331543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331543 prefixEnd_1331543 := by exact prefixLift 1331543
  have htrace : WordTrace (prefixWord ++ tailWord_1331543) baseStart_1331543 baseEnd_1331543 := by
    simpa [prefixWord, tailWord_1331543, baseEnd_1331543] using wordTrace_append hprefix tailTrace_1331543
  have hstable : (prefixWord ++ tailWord_1331543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331543).length < 2 ^ (prefixWord ++ tailWord_1331543).sum := by decide
  have hdescent : baseEnd_1331543 < baseStart_1331543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331557 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 1, 4, 2]
def baseStart_1331557 : Nat := 118140960795 + 1331557 * 2 ^ 59
def prefixEnd_1331557 : Nat := 4983230072969 + 3 ^ 40 * 1331557 * 2
def baseEnd_1331557 : Nat := 683728759858952010813787

theorem tailTrace_1331557 : CollatzResearch.WordTrace tailWord_1331557 prefixEnd_1331557 683728759858952010813787 := by
  unfold tailWord_1331557
  simp only [CollatzResearch.WordTrace]
  refine ⟨48565873637003875675528925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32377249091335917117019283 48565873637003875675528925)
  ·
    refine ⟨18212202613876453378323347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48565873637003875675528925 18212202613876453378323347)
    ·
      refine ⟨27318303920814680067485021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18212202613876453378323347 27318303920814680067485021)
      ·
        refine ⟨10244363970305505025306883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27318303920814680067485021 10244363970305505025306883)
        ·
          refine ⟨15366545955458257537960325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10244363970305505025306883 15366545955458257537960325)
          ·
            refine ⟨2881227366648423288367561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15366545955458257537960325 2881227366648423288367561)
            ·
              refine ⟨2160920524986317466275671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2881227366648423288367561 2160920524986317466275671)
              ·
                refine ⟨3241380787479476199413507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2160920524986317466275671 3241380787479476199413507)
                ·
                  refine ⟨4862071181219214299120261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3241380787479476199413507 4862071181219214299120261)
                  ·
                    refine ⟨911638346478602681085049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4862071181219214299120261 911638346478602681085049)
                    ·
                      refine ⟨683728759858952010813787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 911638346478602681085049 683728759858952010813787)
                      ·
                        rfl

theorem cell23_1331557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_1331557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331557 prefixEnd_1331557 := by exact prefixLift 1331557
  have htrace : WordTrace (prefixWord ++ tailWord_1331557) baseStart_1331557 baseEnd_1331557 := by
    simpa [prefixWord, tailWord_1331557, baseEnd_1331557] using wordTrace_append hprefix tailTrace_1331557
  have hstable : (prefixWord ++ tailWord_1331557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331557).length < 2 ^ (prefixWord ++ tailWord_1331557).sum := by decide
  have hdescent : baseEnd_1331557 < baseStart_1331557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331657 : List Nat := [1, 2, 1, 1, 2, 1, 4, 6, 1, 4]
def baseStart_1331657 : Nat := 118140960795 + 1331657 * 2 ^ 59
def prefixEnd_1331657 : Nat := 4983230072969 + 3 ^ 40 * 1331657 * 2
def baseEnd_1331657 : Nat := 227926702641467206521109

theorem tailTrace_1331657 : CollatzResearch.WordTrace tailWord_1331657 prefixEnd_1331657 227926702641467206521109 := by
  unfold tailWord_1331657
  simp only [CollatzResearch.WordTrace]
  refine ⟨48569520936641592754169225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32379680624427728502779483 48569520936641592754169225)
  ·
    refine ⟨36427140702481194565626919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48569520936641592754169225 36427140702481194565626919)
    ·
      refine ⟨54640711053721791848440379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36427140702481194565626919 54640711053721791848440379)
      ·
        refine ⟨81961066580582687772660569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54640711053721791848440379 81961066580582687772660569)
        ·
          refine ⟨61470799935437015829495427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81961066580582687772660569 61470799935437015829495427)
          ·
            refine ⟨92206199903155523744243141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61470799935437015829495427 92206199903155523744243141)
            ·
              refine ⟨17288662481841660702045589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92206199903155523744243141 17288662481841660702045589)
              ·
                refine ⟨810406053836327845408387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17288662481841660702045589 810406053836327845408387)
                ·
                  refine ⟨1215609080754491768112581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810406053836327845408387 1215609080754491768112581)
                  ·
                    refine ⟨227926702641467206521109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1215609080754491768112581 227926702641467206521109)
                    ·
                      rfl

theorem cell23_1331657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 1, 4].length) (baseStart_1331657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331657 prefixEnd_1331657 := by exact prefixLift 1331657
  have htrace : WordTrace (prefixWord ++ tailWord_1331657) baseStart_1331657 baseEnd_1331657 := by
    simpa [prefixWord, tailWord_1331657, baseEnd_1331657] using wordTrace_append hprefix tailTrace_1331657
  have hstable : (prefixWord ++ tailWord_1331657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331657).length < 2 ^ (prefixWord ++ tailWord_1331657).sum := by decide
  have hdescent : baseEnd_1331657 < baseStart_1331657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331741 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 2, 3, 2]
def baseStart_1331741 : Nat := 118140960795 + 1331741 * 2 ^ 59
def prefixEnd_1331741 : Nat := 4983230072969 + 3 ^ 40 * 1331741 * 2
def baseEnd_1331741 : Nat := 683823240299379290912941

theorem tailTrace_1331741 : CollatzResearch.WordTrace tailWord_1331741 prefixEnd_1331741 683823240299379290912941 := by
  unfold tailWord_1331741
  simp only [CollatzResearch.WordTrace]
  refine ⟨48572584668337275100227077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32381723112224850066818051 48572584668337275100227077)
  ·
    refine ⟨9107359625313239081292577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48572584668337275100227077 9107359625313239081292577)
    ·
      refine ⟨6830519718984929310969433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9107359625313239081292577 6830519718984929310969433)
      ·
        refine ⟨5122889789238696983227075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6830519718984929310969433 5122889789238696983227075)
        ·
          refine ⟨7684334683858045474840613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5122889789238696983227075 7684334683858045474840613)
          ·
            refine ⟨1440812753223383526532615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7684334683858045474840613 1440812753223383526532615)
            ·
              refine ⟨2161219129835075289798923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1440812753223383526532615 2161219129835075289798923)
              ·
                refine ⟨3241828694752612934698385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161219129835075289798923 3241828694752612934698385)
                ·
                  refine ⟨2431371521064459701023789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3241828694752612934698385 2431371521064459701023789)
                  ·
                    refine ⟨911764320399172387883921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2431371521064459701023789 911764320399172387883921)
                    ·
                      refine ⟨683823240299379290912941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 911764320399172387883921 683823240299379290912941)
                      ·
                        rfl

theorem cell23_1331741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_1331741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331741 prefixEnd_1331741 := by exact prefixLift 1331741
  have htrace : WordTrace (prefixWord ++ tailWord_1331741) baseStart_1331741 baseEnd_1331741 := by
    simpa [prefixWord, tailWord_1331741, baseEnd_1331741] using wordTrace_append hprefix tailTrace_1331741
  have hstable : (prefixWord ++ tailWord_1331741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331741).length < 2 ^ (prefixWord ++ tailWord_1331741).sum := by decide
  have hdescent : baseEnd_1331741 < baseStart_1331741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331751 : List Nat := [1, 1, 7, 2, 1, 1, 1, 3, 1, 5]
def baseStart_1331751 : Nat := 118140960795 + 1331751 * 2 ^ 59
def prefixEnd_1331751 : Nat := 4983230072969 + 3 ^ 40 * 1331751 * 2
def baseEnd_1331751 : Nat := 227942791701974750595965

theorem tailTrace_1331751 : CollatzResearch.WordTrace tailWord_1331751 prefixEnd_1331751 227942791701974750595965 := by
  unfold tailWord_1331751
  simp only [CollatzResearch.WordTrace]
  refine ⟨48572949398301046808091107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32381966265534031205394071 48572949398301046808091107)
  ·
    refine ⟨72859424097451570212136661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48572949398301046808091107 72859424097451570212136661)
    ·
      refine ⟨1707642752284021176846953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 72859424097451570212136661 1707642752284021176846953)
      ·
        refine ⟨1280732064213015882635215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1707642752284021176846953 1280732064213015882635215)
        ·
          refine ⟨1921098096319523823952823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1280732064213015882635215 1921098096319523823952823)
          ·
            refine ⟨2881647144479285735929235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1921098096319523823952823 2881647144479285735929235)
            ·
              refine ⟨4322470716718928603893853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2881647144479285735929235 4322470716718928603893853)
              ·
                refine ⟨1620926518769598226460195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4322470716718928603893853 1620926518769598226460195)
                ·
                  refine ⟨2431389778154397339690293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620926518769598226460195 2431389778154397339690293)
                  ·
                    refine ⟨227942791701974750595965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2431389778154397339690293 227942791701974750595965)
                    ·
                      rfl

theorem cell23_1331751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_1331751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331751 prefixEnd_1331751 := by exact prefixLift 1331751
  have htrace : WordTrace (prefixWord ++ tailWord_1331751) baseStart_1331751 baseEnd_1331751 := by
    simpa [prefixWord, tailWord_1331751, baseEnd_1331751] using wordTrace_append hprefix tailTrace_1331751
  have hstable : (prefixWord ++ tailWord_1331751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331751).length < 2 ^ (prefixWord ++ tailWord_1331751).sum := by decide
  have hdescent : baseEnd_1331751 < baseStart_1331751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331754 : List Nat := [3, 1, 4, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_1331754 : Nat := 118140960795 + 1331754 * 2 ^ 59
def prefixEnd_1331754 : Nat := 4983230072969 + 3 ^ 40 * 1331754 * 2
def baseEnd_1331754 : Nat := 683829915547887740050381

theorem tailTrace_1331754 : CollatzResearch.WordTrace tailWord_1331754 prefixEnd_1331754 683829915547887740050381 := by
  unfold tailWord_1331754
  simp only [CollatzResearch.WordTrace]
  refine ⟨12143264704322544580112579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32382039211526785546966877 12143264704322544580112579)
  ·
    refine ⟨18214897056483816870168869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12143264704322544580112579 18214897056483816870168869)
    ·
      refine ⟨3415293198090715663156663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18214897056483816870168869 3415293198090715663156663)
      ·
        refine ⟨5122939797136073494734995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3415293198090715663156663 5122939797136073494734995)
        ·
          refine ⟨7684409695704110242102493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5122939797136073494734995 7684409695704110242102493)
          ·
            refine ⟨2881653635889041340788435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7684409695704110242102493 2881653635889041340788435)
            ·
              refine ⟨4322480453833562011182653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2881653635889041340788435 4322480453833562011182653)
              ·
                refine ⟨1620930170187585754193495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4322480453833562011182653 1620930170187585754193495)
                ·
                  refine ⟨2431395255281378631290243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620930170187585754193495 2431395255281378631290243)
                  ·
                    refine ⟨3647092882922067946935365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2431395255281378631290243 3647092882922067946935365)
                    ·
                      refine ⟨683829915547887740050381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3647092882922067946935365 683829915547887740050381)
                      ·
                        rfl

theorem cell23_1331754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_1331754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331754 prefixEnd_1331754 := by exact prefixLift 1331754
  have htrace : WordTrace (prefixWord ++ tailWord_1331754) baseStart_1331754 baseEnd_1331754 := by
    simpa [prefixWord, tailWord_1331754, baseEnd_1331754] using wordTrace_append hprefix tailTrace_1331754
  have hstable : (prefixWord ++ tailWord_1331754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331754).length < 2 ^ (prefixWord ++ tailWord_1331754).sum := by decide
  have hdescent : baseEnd_1331754 < baseStart_1331754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331787 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 3]
def baseStart_1331787 : Nat := 118140960795 + 1331787 * 2 ^ 59
def prefixEnd_1331787 : Nat := 4983230072969 + 3 ^ 40 * 1331787 * 2
def baseEnd_1331787 : Nat := 683846860409486110937729

theorem tailTrace_1331787 : CollatzResearch.WordTrace tailWord_1331787 prefixEnd_1331787 683846860409486110937729 := by
  unfold tailWord_1331787
  simp only [CollatzResearch.WordTrace]
  refine ⟨48574262426170624956401615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32382841617447083304267743 48574262426170624956401615)
  ·
    refine ⟨72861393639255937434602423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48574262426170624956401615 72861393639255937434602423)
    ·
      refine ⟨109292090458883906151903635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72861393639255937434602423 109292090458883906151903635)
      ·
        refine ⟨163938135688325859227855453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109292090458883906151903635 163938135688325859227855453)
        ·
          refine ⟨61476800883122197210445795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163938135688325859227855453 61476800883122197210445795)
          ·
            refine ⟨92215201324683295815668693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61476800883122197210445795 92215201324683295815668693)
            ·
              refine ⟨2161293781047264745679735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 92215201324683295815668693 2161293781047264745679735)
              ·
                refine ⟨3241940671570897118519603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161293781047264745679735 3241940671570897118519603)
                ·
                  refine ⟨4862911007356345677779405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3241940671570897118519603 4862911007356345677779405)
                  ·
                    refine ⟨1823591627758629629167277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4862911007356345677779405 1823591627758629629167277)
                    ·
                      refine ⟨683846860409486110937729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1823591627758629629167277 683846860409486110937729)
                      ·
                        rfl

theorem cell23_1331787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 3].length) (baseStart_1331787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331787 prefixEnd_1331787 := by exact prefixLift 1331787
  have htrace : WordTrace (prefixWord ++ tailWord_1331787) baseStart_1331787 baseEnd_1331787 := by
    simpa [prefixWord, tailWord_1331787, baseEnd_1331787] using wordTrace_append hprefix tailTrace_1331787
  have hstable : (prefixWord ++ tailWord_1331787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331787).length < 2 ^ (prefixWord ++ tailWord_1331787).sum := by decide
  have hdescent : baseEnd_1331787 < baseStart_1331787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331790 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 2, 7]
def baseStart_1331790 : Nat := 118140960795 + 1331790 * 2 ^ 59
def prefixEnd_1331790 : Nat := 4983230072969 + 3 ^ 40 * 1331790 * 2
def baseEnd_1331790 : Nat := 227949466950483199733405

theorem tailTrace_1331790 : CollatzResearch.WordTrace tailWord_1331790 prefixEnd_1331790 227949466950483199733405 := by
  unfold tailWord_1331790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6071796480644969558595103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32382914563439837645840549 6071796480644969558595103)
  ·
    refine ⟨9107694720967454337892655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6071796480644969558595103 9107694720967454337892655)
    ·
      refine ⟨13661542081451181506838983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9107694720967454337892655 13661542081451181506838983)
      ·
        refine ⟨20492313122176772260258475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13661542081451181506838983 20492313122176772260258475)
        ·
          refine ⟨30738469683265158390387713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20492313122176772260258475 30738469683265158390387713)
          ·
            refine ⟨23053852262448868792790785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30738469683265158390387713 23053852262448868792790785)
            ·
              refine ⟨17290389196836651594593089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23053852262448868792790785 17290389196836651594593089)
              ·
                refine ⟨12967791897627488695944817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17290389196836651594593089 12967791897627488695944817)
                ·
                  refine ⟨9725843923220616521958613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12967791897627488695944817 9725843923220616521958613)
                  ·
                    refine ⟨227949466950483199733405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9725843923220616521958613 227949466950483199733405)
                    ·
                      rfl

theorem cell23_1331790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_1331790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331790 prefixEnd_1331790 := by exact prefixLift 1331790
  have htrace : WordTrace (prefixWord ++ tailWord_1331790) baseStart_1331790 baseEnd_1331790 := by
    simpa [prefixWord, tailWord_1331790, baseEnd_1331790] using wordTrace_append hprefix tailTrace_1331790
  have hstable : (prefixWord ++ tailWord_1331790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331790).length < 2 ^ (prefixWord ++ tailWord_1331790).sum := by decide
  have hdescent : baseEnd_1331790 < baseStart_1331790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331800 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 2, 2, 5]
def baseStart_1331800 : Nat := 118140960795 + 1331800 * 2 ^ 59
def prefixEnd_1331800 : Nat := 4983230072969 + 3 ^ 40 * 1331800 * 2
def baseEnd_1331800 : Nat := 683853535657994560075169

theorem tailTrace_1331800 : CollatzResearch.WordTrace tailWord_1331800 prefixEnd_1331800 683853535657994560075169 := by
  unfold tailWord_1331800
  simp only [CollatzResearch.WordTrace]
  refine ⟨24287368287561764088312427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32383157716749018784416569 24287368287561764088312427)
  ·
    refine ⟨36431052431342646132468641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24287368287561764088312427 36431052431342646132468641)
    ·
      refine ⟨27323289323506984599351481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36431052431342646132468641 27323289323506984599351481)
      ·
        refine ⟨20492466992630238449513611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27323289323506984599351481 20492466992630238449513611)
        ·
          refine ⟨30738700488945357674270417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20492466992630238449513611 30738700488945357674270417)
          ·
            refine ⟨23054025366709018255702813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30738700488945357674270417 23054025366709018255702813)
            ·
              refine ⟨8645259512515881845888555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23054025366709018255702813 8645259512515881845888555)
              ·
                refine ⟨12967889268773822768832833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8645259512515881845888555 12967889268773822768832833)
                ·
                  refine ⟨9725916951580367076624625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12967889268773822768832833 9725916951580367076624625)
                  ·
                    refine ⟨7294437713685275307468469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9725916951580367076624625 7294437713685275307468469)
                    ·
                      refine ⟨683853535657994560075169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7294437713685275307468469 683853535657994560075169)
                      ·
                        rfl

theorem cell23_1331800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_1331800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331800 prefixEnd_1331800 := by exact prefixLift 1331800
  have htrace : WordTrace (prefixWord ++ tailWord_1331800) baseStart_1331800 baseEnd_1331800 := by
    simpa [prefixWord, tailWord_1331800, baseEnd_1331800] using wordTrace_append hprefix tailTrace_1331800
  have hstable : (prefixWord ++ tailWord_1331800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331800).length < 2 ^ (prefixWord ++ tailWord_1331800).sum := by decide
  have hdescent : baseEnd_1331800 < baseStart_1331800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331820 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 4, 6]
def baseStart_1331820 : Nat := 118140960795 + 1331820 * 2 ^ 59
def prefixEnd_1331820 : Nat := 4983230072969 + 3 ^ 40 * 1331820 * 2
def baseEnd_1331820 : Nat := 227954601757028160608359

theorem tailTrace_1331820 : CollatzResearch.WordTrace tailWord_1331820 prefixEnd_1331820 227954601757028160608359 := by
  unfold tailWord_1331820
  simp only [CollatzResearch.WordTrace]
  refine ⟨24287733017525535796176457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32383644023367381061568609 24287733017525535796176457)
  ·
    refine ⟨18215799763144151847132343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24287733017525535796176457 18215799763144151847132343)
    ·
      refine ⟨27323699644716227770698515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18215799763144151847132343 27323699644716227770698515)
      ·
        refine ⟨40985549467074341656047773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27323699644716227770698515 40985549467074341656047773)
        ·
          refine ⟨15369581050152878121017915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40985549467074341656047773 15369581050152878121017915)
          ·
            refine ⟨23054371575229317181526873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15369581050152878121017915 23054371575229317181526873)
            ·
              refine ⟨17290778681421987886145155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23054371575229317181526873 17290778681421987886145155)
              ·
                refine ⟨25936168022132981829217733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17290778681421987886145155 25936168022132981829217733)
                ·
                  refine ⟨4863031504149934092978325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25936168022132981829217733 4863031504149934092978325)
                  ·
                    refine ⟨227954601757028160608359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4863031504149934092978325 227954601757028160608359)
                    ·
                      rfl

theorem cell23_1331820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_1331820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331820 prefixEnd_1331820 := by exact prefixLift 1331820
  have htrace : WordTrace (prefixWord ++ tailWord_1331820) baseStart_1331820 baseEnd_1331820 := by
    simpa [prefixWord, tailWord_1331820, baseEnd_1331820] using wordTrace_append hprefix tailTrace_1331820
  have hstable : (prefixWord ++ tailWord_1331820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331820).length < 2 ^ (prefixWord ++ tailWord_1331820).sum := by decide
  have hdescent : baseEnd_1331820 < baseStart_1331820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331827 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 5, 4, 2]
def baseStart_1331827 : Nat := 118140960795 + 1331827 * 2 ^ 59
def prefixEnd_1331827 : Nat := 4983230072969 + 3 ^ 40 * 1331827 * 2
def baseEnd_1331827 : Nat := 683867399635665954437545

theorem tailTrace_1331827 : CollatzResearch.WordTrace tailWord_1331827 prefixEnd_1331827 683867399635665954437545 := by
  unfold tailWord_1331827
  simp only [CollatzResearch.WordTrace]
  refine ⟨48575721346025711787857735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32383814230683807858571823 48575721346025711787857735)
  ·
    refine ⟨72863582019038567681786603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48575721346025711787857735 72863582019038567681786603)
    ·
      refine ⟨109295373028557851522679905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72863582019038567681786603 109295373028557851522679905)
      ·
        refine ⟨81971529771418388642009929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109295373028557851522679905 81971529771418388642009929)
        ·
          refine ⟨61478647328563791481507447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81971529771418388642009929 61478647328563791481507447)
          ·
            refine ⟨92217970992845687222261171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61478647328563791481507447 92217970992845687222261171)
            ·
              refine ⟨138326956489268530833391757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92217970992845687222261171 138326956489268530833391757)
              ·
                refine ⟨51872608683475699062521909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138326956489268530833391757 51872608683475699062521909)
                ·
                  refine ⟨4863057064075846787111429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51872608683475699062521909 4863057064075846787111429)
                  ·
                    refine ⟨911823199514221272583393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4863057064075846787111429 911823199514221272583393)
                    ·
                      refine ⟨683867399635665954437545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 911823199514221272583393 683867399635665954437545)
                      ·
                        rfl

theorem cell23_1331827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 4, 2].length) (baseStart_1331827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331827 prefixEnd_1331827 := by exact prefixLift 1331827
  have htrace : WordTrace (prefixWord ++ tailWord_1331827) baseStart_1331827 baseEnd_1331827 := by
    simpa [prefixWord, tailWord_1331827, baseEnd_1331827] using wordTrace_append hprefix tailTrace_1331827
  have hstable : (prefixWord ++ tailWord_1331827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331827).length < 2 ^ (prefixWord ++ tailWord_1331827).sum := by decide
  have hdescent : baseEnd_1331827 < baseStart_1331827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331842 : List Nat := [3, 4, 3, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1331842 : Nat := 118140960795 + 1331842 * 2 ^ 59
def prefixEnd_1331842 : Nat := 4983230072969 + 3 ^ 40 * 1331842 * 2
def baseEnd_1331842 : Nat := 683875101845483395749977

theorem tailTrace_1331842 : CollatzResearch.WordTrace tailWord_1331842 prefixEnd_1331842 683875101845483395749977 := by
  unfold tailWord_1331842
  simp only [CollatzResearch.WordTrace]
  refine ⟨12144067110242842337413445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32384178960647579566435853 12144067110242842337413445)
  ·
    refine ⟨2277012583170532938265021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12144067110242842337413445 2277012583170532938265021)
    ·
      refine ⟨853879718688949851849383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2277012583170532938265021 853879718688949851849383)
      ·
        refine ⟨1280819578033424777774075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 853879718688949851849383 1280819578033424777774075)
        ·
          refine ⟨1921229367050137166661113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1280819578033424777774075 1921229367050137166661113)
          ·
            refine ⟨1440922025287602874995835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1921229367050137166661113 1440922025287602874995835)
            ·
              refine ⟨2161383037931404312493753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1440922025287602874995835 2161383037931404312493753)
              ·
                refine ⟨1621037278448553234370315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2161383037931404312493753 1621037278448553234370315)
                ·
                  refine ⟨2431555917672829851555473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1621037278448553234370315 2431555917672829851555473)
                  ·
                    refine ⟨1823666938254622388666605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2431555917672829851555473 1823666938254622388666605)
                    ·
                      refine ⟨683875101845483395749977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1823666938254622388666605 683875101845483395749977)
                      ·
                        rfl

theorem cell23_1331842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1331842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331842 prefixEnd_1331842 := by exact prefixLift 1331842
  have htrace : WordTrace (prefixWord ++ tailWord_1331842) baseStart_1331842 baseEnd_1331842 := by
    simpa [prefixWord, tailWord_1331842, baseEnd_1331842] using wordTrace_append hprefix tailTrace_1331842
  have hstable : (prefixWord ++ tailWord_1331842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331842).length < 2 ^ (prefixWord ++ tailWord_1331842).sum := by decide
  have hdescent : baseEnd_1331842 < baseStart_1331842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331877 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 2, 3, 3]
def baseStart_1331877 : Nat := 118140960795 + 1331877 * 2 ^ 59
def prefixEnd_1331877 : Nat := 4983230072969 + 3 ^ 40 * 1331877 * 2
def baseEnd_1331877 : Nat := 683893073668390758812315

theorem tailTrace_1331877 : CollatzResearch.WordTrace tailWord_1331877 prefixEnd_1331877 683893073668390758812315 := by
  unfold tailWord_1331877
  simp only [CollatzResearch.WordTrace]
  refine ⟨48577544995844570327177885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32385029997229713551451923 48577544995844570327177885)
  ·
    refine ⟨18216579373441713872691707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48577544995844570327177885 18216579373441713872691707)
    ·
      refine ⟨27324869060162570809037561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18216579373441713872691707 27324869060162570809037561)
      ·
        refine ⟨20493651795121928106778171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27324869060162570809037561 20493651795121928106778171)
        ·
          refine ⟨30740477692682892160167257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20493651795121928106778171 30740477692682892160167257)
          ·
            refine ⟨23055358269512169120125443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30740477692682892160167257 23055358269512169120125443)
            ·
              refine ⟨34583037404268253680188165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23055358269512169120125443 34583037404268253680188165)
              ·
                refine ⟨6484319513300297565035281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34583037404268253680188165 6484319513300297565035281)
                ·
                  refine ⟨4863239634975223173776461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6484319513300297565035281 4863239634975223173776461)
                  ·
                    refine ⟨1823714863115708690166173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4863239634975223173776461 1823714863115708690166173)
                    ·
                      refine ⟨683893073668390758812315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1823714863115708690166173 683893073668390758812315)
                      ·
                        rfl

theorem cell23_1331877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_1331877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331877 prefixEnd_1331877 := by exact prefixLift 1331877
  have htrace : WordTrace (prefixWord ++ tailWord_1331877) baseStart_1331877 baseEnd_1331877 := by
    simpa [prefixWord, tailWord_1331877, baseEnd_1331877] using wordTrace_append hprefix tailTrace_1331877
  have hstable : (prefixWord ++ tailWord_1331877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331877).length < 2 ^ (prefixWord ++ tailWord_1331877).sum := by decide
  have hdescent : baseEnd_1331877 < baseStart_1331877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331914 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 2, 5]
def baseStart_1331914 : Nat := 118140960795 + 1331914 * 2 ^ 59
def prefixEnd_1331914 : Nat := 4983230072969 + 3 ^ 40 * 1331914 * 2
def baseEnd_1331914 : Nat := 227970690817535704683215

theorem tailTrace_1331914 : CollatzResearch.WordTrace tailWord_1331914 prefixEnd_1331914 227970690817535704683215 := by
  unfold tailWord_1331914
  simp only [CollatzResearch.WordTrace]
  refine ⟨12144723624177631411568699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32385929664473683764183197 12144723624177631411568699)
  ·
    refine ⟨18217085436266447117353049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12144723624177631411568699 18217085436266447117353049)
    ·
      refine ⟨13662814077199835338014787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18217085436266447117353049 13662814077199835338014787)
      ·
        refine ⟨20494221115799753007022181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13662814077199835338014787 20494221115799753007022181)
        ·
          refine ⟨3842666459212453688816659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20494221115799753007022181 3842666459212453688816659)
          ·
            refine ⟨5763999688818680533224989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3842666459212453688816659 5763999688818680533224989)
            ·
              refine ⟨2161499883307005199959371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5763999688818680533224989 2161499883307005199959371)
              ·
                refine ⟨3242249824960507799939057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161499883307005199959371 3242249824960507799939057)
                ·
                  refine ⟨2431687368720380849954293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3242249824960507799939057 2431687368720380849954293)
                  ·
                    refine ⟨227970690817535704683215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2431687368720380849954293 227970690817535704683215)
                    ·
                      rfl

theorem cell23_1331914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_1331914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331914 prefixEnd_1331914 := by exact prefixLift 1331914
  have htrace : WordTrace (prefixWord ++ tailWord_1331914) baseStart_1331914 baseEnd_1331914 := by
    simpa [prefixWord, tailWord_1331914, baseEnd_1331914] using wordTrace_append hprefix tailTrace_1331914
  have hstable : (prefixWord ++ tailWord_1331914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331914).length < 2 ^ (prefixWord ++ tailWord_1331914).sum := by decide
  have hdescent : baseEnd_1331914 < baseStart_1331914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331954 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 1, 4, 3]
def baseStart_1331954 : Nat := 118140960795 + 1331954 * 2 ^ 59
def prefixEnd_1331954 : Nat := 4983230072969 + 3 ^ 40 * 1331954 * 2
def baseEnd_1331954 : Nat := 683932611678786957549461

theorem tailTrace_1331954 : CollatzResearch.WordTrace tailWord_1331954 prefixEnd_1331954 683932611678786957549461 := by
  unfold tailWord_1331954
  simp only [CollatzResearch.WordTrace]
  refine ⟨12145088354141403119432729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32386902277710408318487277 12145088354141403119432729)
  ·
    refine ⟨9108816265606052339574547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12145088354141403119432729 9108816265606052339574547)
    ·
      refine ⟨13663224398409078509361821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9108816265606052339574547 13663224398409078509361821)
      ·
        refine ⟨5123709149403404441010683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13663224398409078509361821 5123709149403404441010683)
        ·
          refine ⟨7685563724105106661516025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5123709149403404441010683 7685563724105106661516025)
          ·
            refine ⟨5764172793078829996137019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7685563724105106661516025 5764172793078829996137019)
            ·
              refine ⟨8646259189618244994205529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5764172793078829996137019 8646259189618244994205529)
              ·
                refine ⟨6484694392213683745654147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8646259189618244994205529 6484694392213683745654147)
                ·
                  refine ⟨9727041588320525618481221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6484694392213683745654147 9727041588320525618481221)
                  ·
                    refine ⟨1823820297810098553465229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9727041588320525618481221 1823820297810098553465229)
                    ·
                      refine ⟨683932611678786957549461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1823820297810098553465229 683932611678786957549461)
                      ·
                        rfl

theorem cell23_1331954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_1331954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331954 prefixEnd_1331954 := by exact prefixLift 1331954
  have htrace : WordTrace (prefixWord ++ tailWord_1331954) baseStart_1331954 baseEnd_1331954 := by
    simpa [prefixWord, tailWord_1331954, baseEnd_1331954] using wordTrace_append hprefix tailTrace_1331954
  have hstable : (prefixWord ++ tailWord_1331954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331954).length < 2 ^ (prefixWord ++ tailWord_1331954).sum := by decide
  have hdescent : baseEnd_1331954 < baseStart_1331954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331967 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 3]
def baseStart_1331967 : Nat := 118140960795 + 1331967 * 2 ^ 59
def prefixEnd_1331967 : Nat := 4983230072969 + 3 ^ 40 * 1331967 * 2
def baseEnd_1331967 : Nat := 683939286927295406686901

theorem tailTrace_1331967 : CollatzResearch.WordTrace tailWord_1331967 prefixEnd_1331967 683939286927295406686901 := by
  unfold tailWord_1331967
  simp only [CollatzResearch.WordTrace]
  refine ⟨48580827565518515697954155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32387218377012343798636103 48580827565518515697954155)
  ·
    refine ⟨72871241348277773546931233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48580827565518515697954155 72871241348277773546931233)
    ·
      refine ⟨54653431011208330160198425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72871241348277773546931233 54653431011208330160198425)
      ·
        refine ⟨40990073258406247620148819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54653431011208330160198425 40990073258406247620148819)
        ·
          refine ⟨61485109887609371430223229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40990073258406247620148819 61485109887609371430223229)
          ·
            refine ⟨23056916207853514286333711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61485109887609371430223229 23056916207853514286333711)
            ·
              refine ⟨34585374311780271429500567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23056916207853514286333711 34585374311780271429500567)
              ·
                refine ⟨51878061467670407144250851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34585374311780271429500567 51878061467670407144250851)
                ·
                  refine ⟨77817092201505610716376277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51878061467670407144250851 77817092201505610716376277)
                  ·
                    refine ⟨1823838098472787751165069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 77817092201505610716376277 1823838098472787751165069)
                    ·
                      refine ⟨683939286927295406686901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1823838098472787751165069 683939286927295406686901)
                      ·
                        rfl

theorem cell23_1331967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_1331967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1331967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1331967 prefixEnd_1331967 := by exact prefixLift 1331967
  have htrace : WordTrace (prefixWord ++ tailWord_1331967) baseStart_1331967 baseEnd_1331967 := by
    simpa [prefixWord, tailWord_1331967, baseEnd_1331967] using wordTrace_append hprefix tailTrace_1331967
  have hstable : (prefixWord ++ tailWord_1331967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331967).length < 2 ^ (prefixWord ++ tailWord_1331967).sum := by decide
  have hdescent : baseEnd_1331967 < baseStart_1331967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332021 : List Nat := [1, 3, 3, 1, 3, 1, 3, 2, 1, 5]
def baseStart_1332021 : Nat := 118140960795 + 1332021 * 2 ^ 59
def prefixEnd_1332021 : Nat := 4983230072969 + 3 ^ 40 * 1332021 * 2
def baseEnd_1332021 : Nat := 227989004960879398470551

theorem tailTrace_1332021 : CollatzResearch.WordTrace tailWord_1332021 prefixEnd_1332021 227989004960879398470551 := by
  unfold tailWord_1332021
  simp only [CollatzResearch.WordTrace]
  refine ⟨48582797107322882920419917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32388531404881921946946611 48582797107322882920419917)
  ·
    refine ⟨18218548915246081095157469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48582797107322882920419917 18218548915246081095157469)
    ·
      refine ⟨6831955843217280410684051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18218548915246081095157469 6831955843217280410684051)
      ·
        refine ⟨10247933764825920616026077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6831955843217280410684051 10247933764825920616026077)
        ·
          refine ⟨3842975161809720231009779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10247933764825920616026077 3842975161809720231009779)
          ·
            refine ⟨5764462742714580346514669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3842975161809720231009779 5764462742714580346514669)
            ·
              refine ⟨2161673528517967629943001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5764462742714580346514669 2161673528517967629943001)
              ·
                refine ⟨1621255146388475722457251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2161673528517967629943001 1621255146388475722457251)
                ·
                  refine ⟨2431882719582713583685877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1621255146388475722457251 2431882719582713583685877)
                  ·
                    refine ⟨227989004960879398470551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2431882719582713583685877 227989004960879398470551)
                    ·
                      rfl

theorem cell23_1332021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_1332021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332021 prefixEnd_1332021 := by exact prefixLift 1332021
  have htrace : WordTrace (prefixWord ++ tailWord_1332021) baseStart_1332021 baseEnd_1332021 := by
    simpa [prefixWord, tailWord_1332021, baseEnd_1332021] using wordTrace_append hprefix tailTrace_1332021
  have hstable : (prefixWord ++ tailWord_1332021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332021).length < 2 ^ (prefixWord ++ tailWord_1332021).sum := by decide
  have hdescent : baseEnd_1332021 < baseStart_1332021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332024 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 3, 1, 4]
def baseStart_1332024 : Nat := 118140960795 + 1332024 * 2 ^ 59
def prefixEnd_1332024 : Nat := 4983230072969 + 3 ^ 40 * 1332024 * 2
def baseEnd_1332024 : Nat := 683968555324601683674139

theorem tailTrace_1332024 : CollatzResearch.WordTrace tailWord_1332024 prefixEnd_1332024 683968555324601683674139 := by
  unfold tailWord_1332024
  simp only [CollatzResearch.WordTrace]
  refine ⟨24291453263156007216389563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32388604350874676288519417 24291453263156007216389563)
  ·
    refine ⟨36437179894734010824584345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24291453263156007216389563 36437179894734010824584345)
    ·
      refine ⟨27327884921050508118438259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36437179894734010824584345 27327884921050508118438259)
      ·
        refine ⟨40991827381575762177657389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27327884921050508118438259 40991827381575762177657389)
        ·
          refine ⟨15371935268090910816621521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40991827381575762177657389 15371935268090910816621521)
          ·
            refine ⟨11528951451068183112466141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15371935268090910816621521 11528951451068183112466141)
            ·
              refine ⟨4323356794150568667174803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11528951451068183112466141 4323356794150568667174803)
              ·
                refine ⟨6485035191225853000762205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4323356794150568667174803 6485035191225853000762205)
                ·
                  refine ⟨2431888196709694875285827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6485035191225853000762205 2431888196709694875285827)
                  ·
                    refine ⟨3647832295064542312928741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2431888196709694875285827 3647832295064542312928741)
                    ·
                      refine ⟨683968555324601683674139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3647832295064542312928741 683968555324601683674139)
                      ·
                        rfl

theorem cell23_1332024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_1332024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332024 prefixEnd_1332024 := by exact prefixLift 1332024
  have htrace : WordTrace (prefixWord ++ tailWord_1332024) baseStart_1332024 baseEnd_1332024 := by
    simpa [prefixWord, tailWord_1332024, baseEnd_1332024] using wordTrace_append hprefix tailTrace_1332024
  have hstable : (prefixWord ++ tailWord_1332024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332024).length < 2 ^ (prefixWord ++ tailWord_1332024).sum := by decide
  have hdescent : baseEnd_1332024 < baseStart_1332024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332037 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 3, 1, 6]
def baseStart_1332037 : Nat := 118140960795 + 1332037 * 2 ^ 59
def prefixEnd_1332037 : Nat := 4983230072969 + 3 ^ 40 * 1332037 * 2
def baseEnd_1332037 : Nat := 683975230573110132811579

theorem tailTrace_1332037 : CollatzResearch.WordTrace tailWord_1332037 prefixEnd_1332037 683975230573110132811579 := by
  unfold tailWord_1332037
  simp only [CollatzResearch.WordTrace]
  refine ⟨48583380675264917653002365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32388920450176611768668243 48583380675264917653002365)
  ·
    refine ⟨18218767753224344119875887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48583380675264917653002365 18218767753224344119875887)
    ·
      refine ⟨27328151629836516179813831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18218767753224344119875887 27328151629836516179813831)
      ·
        refine ⟨40992227444754774269720747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27328151629836516179813831 40992227444754774269720747)
        ·
          refine ⟨61488341167132161404581121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40992227444754774269720747 61488341167132161404581121)
          ·
            refine ⟨46116255875349121053435841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61488341167132161404581121 46116255875349121053435841)
            ·
              refine ⟨34587191906511840790076881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46116255875349121053435841 34587191906511840790076881)
              ·
                refine ⟨25940393929883880592557661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34587191906511840790076881 25940393929883880592557661)
                ·
                  refine ⟨9727647723706455222209123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25940393929883880592557661 9727647723706455222209123)
                  ·
                    refine ⟨14591471585559682833313685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9727647723706455222209123 14591471585559682833313685)
                    ·
                      refine ⟨683975230573110132811579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14591471585559682833313685 683975230573110132811579)
                      ·
                        rfl

theorem cell23_1332037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_1332037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332037 prefixEnd_1332037 := by exact prefixLift 1332037
  have htrace : WordTrace (prefixWord ++ tailWord_1332037) baseStart_1332037 baseEnd_1332037 := by
    simpa [prefixWord, tailWord_1332037, baseEnd_1332037] using wordTrace_append hprefix tailTrace_1332037
  have hstable : (prefixWord ++ tailWord_1332037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332037).length < 2 ^ (prefixWord ++ tailWord_1332037).sum := by decide
  have hdescent : baseEnd_1332037 < baseStart_1332037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332071 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_1332071 : Nat := 118140960795 + 1332071 * 2 ^ 59
def prefixEnd_1332071 : Nat := 4983230072969 + 3 ^ 40 * 1332071 * 2
def baseEnd_1332071 : Nat := 683992688915362999786423

theorem tailTrace_1332071 : CollatzResearch.WordTrace tailWord_1332071 prefixEnd_1332071 683992688915362999786423 := by
  unfold tailWord_1332071
  simp only [CollatzResearch.WordTrace]
  refine ⟨48584620757141741459740067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32389747171427827639826711 48584620757141741459740067)
  ·
    refine ⟨72876931135712612189610101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48584620757141741459740067 72876931135712612189610101)
    ·
      refine ⟨6832212293973057392775947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72876931135712612189610101 6832212293973057392775947)
      ·
        refine ⟨10248318440959586089163921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6832212293973057392775947 10248318440959586089163921)
        ·
          refine ⟨7686238830719689566872941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10248318440959586089163921 7686238830719689566872941)
          ·
            refine ⟨2882339561519883587577353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7686238830719689566872941 2882339561519883587577353)
            ·
              refine ⟨2161754671139912690683015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2882339561519883587577353 2161754671139912690683015)
              ·
                refine ⟨3242632006709869036024523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161754671139912690683015 3242632006709869036024523)
                ·
                  refine ⟨4863948010064803554036785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3242632006709869036024523 4863948010064803554036785)
                  ·
                    refine ⟨3647961007548602665527589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4863948010064803554036785 3647961007548602665527589)
                    ·
                      refine ⟨683992688915362999786423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3647961007548602665527589 683992688915362999786423)
                      ·
                        rfl

theorem cell23_1332071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_1332071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332071 prefixEnd_1332071 := by exact prefixLift 1332071
  have htrace : WordTrace (prefixWord ++ tailWord_1332071) baseStart_1332071 baseEnd_1332071 := by
    simpa [prefixWord, tailWord_1332071, baseEnd_1332071] using wordTrace_append hprefix tailTrace_1332071
  have hstable : (prefixWord ++ tailWord_1332071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332071).length < 2 ^ (prefixWord ++ tailWord_1332071).sum := by decide
  have hdescent : baseEnd_1332071 < baseStart_1332071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332098 : List Nat := [3, 4, 2, 2, 1, 1, 10]
def baseStart_1332098 : Nat := 118140960795 + 1332098 * 2 ^ 59
def prefixEnd_1332098 : Nat := 4983230072969 + 3 ^ 40 * 1332098 * 2
def baseEnd_1332098 : Nat := 8444525344358449310479

theorem tailTrace_1332098 : CollatzResearch.WordTrace tailWord_1332098 prefixEnd_1332098 8444525344358449310479 := by
  unfold tailWord_1332098
  simp only [CollatzResearch.WordTrace]
  refine ⟨12146401382010981267743237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32390403685362616713981965 12146401382010981267743237)
  ·
    refine ⟨2277450259127058987701857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12146401382010981267743237 2277450259127058987701857)
    ·
      refine ⟨1708087694345294240776393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2277450259127058987701857 1708087694345294240776393)
      ·
        refine ⟨1281065770758970680582295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1708087694345294240776393 1281065770758970680582295)
        ·
          refine ⟨1921598656138456020873443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1281065770758970680582295 1921598656138456020873443)
          ·
            refine ⟨2882397984207684031310165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1921598656138456020873443 2882397984207684031310165)
            ·
              refine ⟨8444525344358449310479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2882397984207684031310165 8444525344358449310479)
              ·
                rfl

theorem cell23_1332098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 10].length) (baseStart_1332098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332098 prefixEnd_1332098 := by exact prefixLift 1332098
  have htrace : WordTrace (prefixWord ++ tailWord_1332098) baseStart_1332098 baseEnd_1332098 := by
    simpa [prefixWord, tailWord_1332098, baseEnd_1332098] using wordTrace_append hprefix tailTrace_1332098
  have hstable : (prefixWord ++ tailWord_1332098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332098).length < 2 ^ (prefixWord ++ tailWord_1332098).sum := by decide
  have hdescent : baseEnd_1332098 < baseStart_1332098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332108 : List Nat := [2, 2, 1, 2, 1, 2, 5, 2, 2, 1, 3]
def baseStart_1332108 : Nat := 118140960795 + 1332108 * 2 ^ 59
def prefixEnd_1332108 : Nat := 4983230072969 + 3 ^ 40 * 1332108 * 2
def baseEnd_1332108 : Nat := 684011687699579355023753

theorem tailTrace_1332108 : CollatzResearch.WordTrace tailWord_1332108 prefixEnd_1332108 684011687699579355023753 := by
  unfold tailWord_1332108
  simp only [CollatzResearch.WordTrace]
  refine ⟨24292985129003848389418489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32390646838671797852557985 24292985129003848389418489)
  ·
    refine ⟨18219738846752886292063867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24292985129003848389418489 18219738846752886292063867)
    ·
      refine ⟨27329608270129329438095801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18219738846752886292063867 27329608270129329438095801)
      ·
        refine ⟨20497206202596997078571851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27329608270129329438095801 20497206202596997078571851)
        ·
          refine ⟨30745809303895495617857777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20497206202596997078571851 30745809303895495617857777)
          ·
            refine ⟨23059356977921621713393333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30745809303895495617857777 23059356977921621713393333)
            ·
              refine ⟨2161814716680152035630625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23059356977921621713393333 2161814716680152035630625)
              ·
                refine ⟨1621361037510114026722969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2161814716680152035630625 1621361037510114026722969)
                ·
                  refine ⟨1216020778132585520042227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1621361037510114026722969 1216020778132585520042227)
                  ·
                    refine ⟨1824031167198878280063341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1216020778132585520042227 1824031167198878280063341)
                    ·
                      refine ⟨684011687699579355023753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1824031167198878280063341 684011687699579355023753)
                      ·
                        rfl

theorem cell23_1332108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_1332108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332108 prefixEnd_1332108 := by exact prefixLift 1332108
  have htrace : WordTrace (prefixWord ++ tailWord_1332108) baseStart_1332108 baseEnd_1332108 := by
    simpa [prefixWord, tailWord_1332108, baseEnd_1332108] using wordTrace_append hprefix tailTrace_1332108
  have hstable : (prefixWord ++ tailWord_1332108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332108).length < 2 ^ (prefixWord ++ tailWord_1332108).sum := by decide
  have hdescent : baseEnd_1332108 < baseStart_1332108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332125 : List Nat := [1, 4, 2, 1, 2, 1, 5, 1, 2, 1, 3]
def baseStart_1332125 : Nat := 118140960795 + 1332125 * 2 ^ 59
def prefixEnd_1332125 : Nat := 4983230072969 + 3 ^ 40 * 1332125 * 2
def baseEnd_1332125 : Nat := 684020416870705788511175

theorem tailTrace_1332125 : CollatzResearch.WordTrace tailWord_1332125 prefixEnd_1332125 684020416870705788511175 := by
  unfold tailWord_1332125
  simp only [CollatzResearch.WordTrace]
  refine ⟨48586590298946108682205829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32391060199297405788137219 48586590298946108682205829)
  ·
    refine ⟨9109985681052395377913593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48586590298946108682205829 9109985681052395377913593)
    ·
      refine ⟨6832489260789296533435195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9109985681052395377913593 6832489260789296533435195)
      ·
        refine ⟨10248733891183944800152793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6832489260789296533435195 10248733891183944800152793)
        ·
          refine ⟨7686550418387958600114595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10248733891183944800152793 7686550418387958600114595)
          ·
            refine ⟨11529825627581937900171893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7686550418387958600114595 11529825627581937900171893)
            ·
              refine ⟨1080921152585806678141115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11529825627581937900171893 1080921152585806678141115)
              ·
                refine ⟨1621381728878710017211673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080921152585806678141115 1621381728878710017211673)
                ·
                  refine ⟨1216036296659032512908755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1621381728878710017211673 1216036296659032512908755)
                  ·
                    refine ⟨1824054444988548769363133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1216036296659032512908755 1824054444988548769363133)
                    ·
                      refine ⟨684020416870705788511175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1824054444988548769363133 684020416870705788511175)
                      ·
                        rfl

theorem cell23_1332125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_1332125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332125 prefixEnd_1332125 := by exact prefixLift 1332125
  have htrace : WordTrace (prefixWord ++ tailWord_1332125) baseStart_1332125 baseEnd_1332125 := by
    simpa [prefixWord, tailWord_1332125, baseEnd_1332125] using wordTrace_append hprefix tailTrace_1332125
  have hstable : (prefixWord ++ tailWord_1332125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332125).length < 2 ^ (prefixWord ++ tailWord_1332125).sum := by decide
  have hdescent : baseEnd_1332125 < baseStart_1332125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332171 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 7]
def baseStart_1332171 : Nat := 118140960795 + 1332171 * 2 ^ 59
def prefixEnd_1332171 : Nat := 4983230072969 + 3 ^ 40 * 1332171 * 2
def baseEnd_1332171 : Nat := 76004892997868067615107

theorem tailTrace_1332171 : CollatzResearch.WordTrace tailWord_1332171 prefixEnd_1332171 76004892997868067615107 := by
  unfold tailWord_1332171
  simp only [CollatzResearch.WordTrace]
  refine ⟨48588268056779458538380367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32392178704519639025586911 48588268056779458538380367)
  ·
    refine ⟨72882402085169187807570551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48588268056779458538380367 72882402085169187807570551)
    ·
      refine ⟨109323603127753781711355827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72882402085169187807570551 109323603127753781711355827)
      ·
        refine ⟨163985404691630672567033741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109323603127753781711355827 163985404691630672567033741)
        ·
          refine ⟨61494526759361502212637653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163985404691630672567033741 61494526759361502212637653)
          ·
            refine ⟨1441277970922535208108695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 61494526759361502212637653 1441277970922535208108695)
            ·
              refine ⟨2161916956383802812163043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1441277970922535208108695 2161916956383802812163043)
              ·
                refine ⟨3242875434575704218244565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161916956383802812163043 3242875434575704218244565)
                ·
                  refine ⟨76004892997868067615107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3242875434575704218244565 76004892997868067615107)
                  ·
                    rfl

theorem cell23_1332171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 7].length) (baseStart_1332171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332171 prefixEnd_1332171 := by exact prefixLift 1332171
  have htrace : WordTrace (prefixWord ++ tailWord_1332171) baseStart_1332171 baseEnd_1332171 := by
    simpa [prefixWord, tailWord_1332171, baseEnd_1332171] using wordTrace_append hprefix tailTrace_1332171
  have hstable : (prefixWord ++ tailWord_1332171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332171).length < 2 ^ (prefixWord ++ tailWord_1332171).sum := by decide
  have hdescent : baseEnd_1332171 < baseStart_1332171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332238 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2]
def baseStart_1332238 : Nat := 118140960795 + 1332238 * 2 ^ 59
def prefixEnd_1332238 : Nat := 4983230072969 + 3 ^ 40 * 1332238 * 2
def baseEnd_1332238 : Nat := 684078440184663846398155

theorem tailTrace_1332238 : CollatzResearch.WordTrace tailWord_1332238 prefixEnd_1332238 684078440184663846398155 := by
  unfold tailWord_1332238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6073838968442091122633671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32393807831691152654046245 6073838968442091122633671)
  ·
    refine ⟨9110758452663136683950507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6073838968442091122633671 9110758452663136683950507)
    ·
      refine ⟨13666137678994705025925761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9110758452663136683950507 13666137678994705025925761)
      ·
        refine ⟨10249603259246028769444321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13666137678994705025925761 10249603259246028769444321)
        ·
          refine ⟨7687202444434521577083241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10249603259246028769444321 7687202444434521577083241)
          ·
            refine ⟨5765401833325891182812431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7687202444434521577083241 5765401833325891182812431)
            ·
              refine ⟨8648102749988836774218647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5765401833325891182812431 8648102749988836774218647)
              ·
                refine ⟨12972154124983255161327971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8648102749988836774218647 12972154124983255161327971)
                ·
                  refine ⟨19458231187474882741991957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12972154124983255161327971 19458231187474882741991957)
                  ·
                    refine ⟨912104586912885128530873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19458231187474882741991957 912104586912885128530873)
                    ·
                      refine ⟨684078440184663846398155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 912104586912885128530873 684078440184663846398155)
                      ·
                        rfl

theorem cell23_1332238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_1332238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332238 prefixEnd_1332238 := by exact prefixLift 1332238
  have htrace : WordTrace (prefixWord ++ tailWord_1332238) baseStart_1332238 baseEnd_1332238 := by
    simpa [prefixWord, tailWord_1332238, baseEnd_1332238] using wordTrace_append hprefix tailTrace_1332238
  have hstable : (prefixWord ++ tailWord_1332238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332238).length < 2 ^ (prefixWord ++ tailWord_1332238).sum := by decide
  have hdescent : baseEnd_1332238 < baseStart_1332238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332241 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 3]
def baseStart_1332241 : Nat := 118140960795 + 1332241 * 2 ^ 59
def prefixEnd_1332241 : Nat := 4983230072969 + 3 ^ 40 * 1332241 * 2
def baseEnd_1332241 : Nat := 684079980626627334660641

theorem tailTrace_1332241 : CollatzResearch.WordTrace tailWord_1332241 prefixEnd_1332241 684079980626627334660641 := by
  unfold tailWord_1332241
  simp only [CollatzResearch.WordTrace]
  refine ⟨48590821166525860493428577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32393880777683906995619051 48590821166525860493428577)
  ·
    refine ⟨36443115874894395370071433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48590821166525860493428577 36443115874894395370071433)
    ·
      refine ⟨27332336906170796527553575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36443115874894395370071433 27332336906170796527553575)
      ·
        refine ⟨40998505359256194791330363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27332336906170796527553575 40998505359256194791330363)
        ·
          refine ⟨61497758038884292186995545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40998505359256194791330363 61497758038884292186995545)
          ·
            refine ⟨46123318529163219140246659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61497758038884292186995545 46123318529163219140246659)
            ·
              refine ⟨69184977793744828710369989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46123318529163219140246659 69184977793744828710369989)
              ·
                refine ⟨12972183336327155383194373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69184977793744828710369989 12972183336327155383194373)
                ·
                  refine ⟨2432284375561341634348945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12972183336327155383194373 2432284375561341634348945)
                  ·
                    refine ⟨1824213281671006225761709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2432284375561341634348945 1824213281671006225761709)
                    ·
                      refine ⟨684079980626627334660641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1824213281671006225761709 684079980626627334660641)
                      ·
                        rfl

theorem cell23_1332241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_1332241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332241 prefixEnd_1332241 := by exact prefixLift 1332241
  have htrace : WordTrace (prefixWord ++ tailWord_1332241) baseStart_1332241 baseEnd_1332241 := by
    simpa [prefixWord, tailWord_1332241, baseEnd_1332241] using wordTrace_append hprefix tailTrace_1332241
  have hstable : (prefixWord ++ tailWord_1332241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332241).length < 2 ^ (prefixWord ++ tailWord_1332241).sum := by decide
  have hdescent : baseEnd_1332241 < baseStart_1332241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332248 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 3, 4]
def baseStart_1332248 : Nat := 118140960795 + 1332248 * 2 ^ 59
def prefixEnd_1332248 : Nat := 4983230072969 + 3 ^ 40 * 1332248 * 2
def baseEnd_1332248 : Nat := 228027858330402935757703

theorem tailTrace_1332248 : CollatzResearch.WordTrace tailWord_1332248 prefixEnd_1332248 228027858330402935757703 := by
  unfold tailWord_1332248
  simp only [CollatzResearch.WordTrace]
  refine ⟨24295538238750250344466699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32394050985000333792622265 24295538238750250344466699)
  ·
    refine ⟨36443307358125375516700049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24295538238750250344466699 36443307358125375516700049)
    ·
      refine ⟨27332480518594031637525037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36443307358125375516700049 27332480518594031637525037)
      ·
        refine ⟨10249680194472761864071889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27332480518594031637525037 10249680194472761864071889)
        ·
          refine ⟨7687260145854571398053917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10249680194472761864071889 7687260145854571398053917)
          ·
            refine ⟨2882722554695464274270219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7687260145854571398053917 2882722554695464274270219)
            ·
              refine ⟨4324083832043196411405329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2882722554695464274270219 4324083832043196411405329)
              ·
                refine ⟨3243062874032397308553997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4324083832043196411405329 3243062874032397308553997)
                ·
                  refine ⟨1216148577762148990707749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3243062874032397308553997 1216148577762148990707749)
                  ·
                    refine ⟨228027858330402935757703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1216148577762148990707749 228027858330402935757703)
                    ·
                      rfl

theorem cell23_1332248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_1332248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332248 prefixEnd_1332248 := by exact prefixLift 1332248
  have htrace : WordTrace (prefixWord ++ tailWord_1332248) baseStart_1332248 baseEnd_1332248 := by
    simpa [prefixWord, tailWord_1332248, baseEnd_1332248] using wordTrace_append hprefix tailTrace_1332248
  have hstable : (prefixWord ++ tailWord_1332248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332248).length < 2 ^ (prefixWord ++ tailWord_1332248).sum := by decide
  have hdescent : baseEnd_1332248 < baseStart_1332248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332258 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_1332258 : Nat := 118140960795 + 1332258 * 2 ^ 59
def prefixEnd_1332258 : Nat := 4983230072969 + 3 ^ 40 * 1332258 * 2
def baseEnd_1332258 : Nat := 684088709797753768148063

theorem tailTrace_1332258 : CollatzResearch.WordTrace tailWord_1332258 prefixEnd_1332258 684088709797753768148063 := by
  unfold tailWord_1332258
  simp only [CollatzResearch.WordTrace]
  refine ⟨12147860301866068099199357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32394294138309514931198285 12147860301866068099199357)
  ·
    refine ⟨4555447613199775537199759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12147860301866068099199357 4555447613199775537199759)
    ·
      refine ⟨6833171419799663305799639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4555447613199775537199759 6833171419799663305799639)
      ·
        refine ⟨10249757129699494958699459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6833171419799663305799639 10249757129699494958699459)
        ·
          refine ⟨15374635694549242438049189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10249757129699494958699459 15374635694549242438049189)
          ·
            refine ⟨2882744192727982957134223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15374635694549242438049189 2882744192727982957134223)
            ·
              refine ⟨4324116289091974435701335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2882744192727982957134223 4324116289091974435701335)
              ·
                refine ⟨6486174433637961653552003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4324116289091974435701335 6486174433637961653552003)
                ·
                  refine ⟨9729261650456942480328005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6486174433637961653552003 9729261650456942480328005)
                  ·
                    refine ⟨1824236559460676715061501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9729261650456942480328005 1824236559460676715061501)
                    ·
                      refine ⟨684088709797753768148063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1824236559460676715061501 684088709797753768148063)
                      ·
                        rfl

theorem cell23_1332258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_1332258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332258 prefixEnd_1332258 := by exact prefixLift 1332258
  have htrace : WordTrace (prefixWord ++ tailWord_1332258) baseStart_1332258 baseEnd_1332258 := by
    simpa [prefixWord, tailWord_1332258, baseEnd_1332258] using wordTrace_append hprefix tailTrace_1332258
  have hstable : (prefixWord ++ tailWord_1332258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332258).length < 2 ^ (prefixWord ++ tailWord_1332258).sum := by decide
  have hdescent : baseEnd_1332258 < baseStart_1332258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332278 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 8]
def baseStart_1332278 : Nat := 118140960795 + 1332278 * 2 ^ 59
def prefixEnd_1332278 : Nat := 4983230072969 + 3 ^ 40 * 1332278 * 2
def baseEnd_1332278 : Nat := 76010997712315965544219

theorem tailTrace_1332278 : CollatzResearch.WordTrace tailWord_1332278 prefixEnd_1332278 76010997712315965544219 := by
  unfold tailWord_1332278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3037010666711988488282843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32394780444927877208350325 3037010666711988488282843)
  ·
    refine ⟨4555516000067982732424265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3037010666711988488282843 4555516000067982732424265)
    ·
      refine ⟨3416637000050987049318199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4555516000067982732424265 3416637000050987049318199)
      ·
        refine ⟨5124955500076480573977299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3416637000050987049318199 5124955500076480573977299)
        ·
          refine ⟨7687433250114720860965949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5124955500076480573977299 7687433250114720860965949)
          ·
            refine ⟨2882787468793020322862231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7687433250114720860965949 2882787468793020322862231)
            ·
              refine ⟨4324181203189530484293347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2882787468793020322862231 4324181203189530484293347)
              ·
                refine ⟨6486271804784295726440021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4324181203189530484293347 6486271804784295726440021)
                ·
                  refine ⟨76010997712315965544219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6486271804784295726440021 76010997712315965544219)
                  ·
                    rfl

theorem cell23_1332278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_1332278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332278 prefixEnd_1332278 := by exact prefixLift 1332278
  have htrace : WordTrace (prefixWord ++ tailWord_1332278) baseStart_1332278 baseEnd_1332278 := by
    simpa [prefixWord, tailWord_1332278, baseEnd_1332278] using wordTrace_append hprefix tailTrace_1332278
  have hstable : (prefixWord ++ tailWord_1332278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332278).length < 2 ^ (prefixWord ++ tailWord_1332278).sum := by decide
  have hdescent : baseEnd_1332278 < baseStart_1332278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332281 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1332281 : Nat := 118140960795 + 1332281 * 2 ^ 59
def prefixEnd_1332281 : Nat := 4983230072969 + 3 ^ 40 * 1332281 * 2
def baseEnd_1332281 : Nat := 684100519852807178160457

theorem tailTrace_1332281 : CollatzResearch.WordTrace tailWord_1332281 prefixEnd_1332281 684100519852807178160457 := by
  unfold tailWord_1332281
  simp only [CollatzResearch.WordTrace]
  refine ⟨48592280086380947324884697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32394853390920631549923131 48592280086380947324884697)
  ·
    refine ⟨36444210064785710493663523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48592280086380947324884697 36444210064785710493663523)
    ·
      refine ⟨54666315097178565740495285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36444210064785710493663523 54666315097178565740495285)
      ·
        refine ⟨5124967040360490538171433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54666315097178565740495285 5124967040360490538171433)
        ·
          refine ⟨3843725280270367903628575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5124967040360490538171433 3843725280270367903628575)
          ·
            refine ⟨5765587920405551855442863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3843725280270367903628575 5765587920405551855442863)
            ·
              refine ⟨8648381880608327783164295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5765587920405551855442863 8648381880608327783164295)
              ·
                refine ⟨12972572820912491674746443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8648381880608327783164295 12972572820912491674746443)
                ·
                  refine ⟨19458859231368737512119665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12972572820912491674746443 19458859231368737512119665)
                  ·
                    refine ⟨14594144423526553134089749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19458859231368737512119665 14594144423526553134089749)
                    ·
                      refine ⟨684100519852807178160457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14594144423526553134089749 684100519852807178160457)
                      ·
                        rfl

theorem cell23_1332281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1332281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332281 prefixEnd_1332281 := by exact prefixLift 1332281
  have htrace : WordTrace (prefixWord ++ tailWord_1332281) baseStart_1332281 baseEnd_1332281 := by
    simpa [prefixWord, tailWord_1332281, baseEnd_1332281] using wordTrace_append hprefix tailTrace_1332281
  have hstable : (prefixWord ++ tailWord_1332281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332281).length < 2 ^ (prefixWord ++ tailWord_1332281).sum := by decide
  have hdescent : baseEnd_1332281 < baseStart_1332281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332298 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 1, 5, 2]
def baseStart_1332298 : Nat := 118140960795 + 1332298 * 2 ^ 59
def prefixEnd_1332298 : Nat := 4983230072969 + 3 ^ 40 * 1332298 * 2
def baseEnd_1332298 : Nat := 684109249023933611647879

theorem tailTrace_1332298 : CollatzResearch.WordTrace tailWord_1332298 prefixEnd_1332298 684109249023933611647879 := by
  unfold tailWord_1332298
  simp only [CollatzResearch.WordTrace]
  refine ⟨12148225031829839807063387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32395266751546239485502365 12148225031829839807063387)
  ·
    refine ⟨18222337547744759710595081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12148225031829839807063387 18222337547744759710595081)
    ·
      refine ⟨13666753160808569782946311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18222337547744759710595081 13666753160808569782946311)
      ·
        refine ⟨20500129741212854674419467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13666753160808569782946311 20500129741212854674419467)
        ·
          refine ⟨30750194611819282011629201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20500129741212854674419467 30750194611819282011629201)
          ·
            refine ⟨23062645958864461508721901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30750194611819282011629201 23062645958864461508721901)
            ·
              refine ⟨8648492234574173065770713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23062645958864461508721901 8648492234574173065770713)
              ·
                refine ⟨6486369175930629799328035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8648492234574173065770713 6486369175930629799328035)
                ·
                  refine ⟨9729553763895944698992053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6486369175930629799328035 9729553763895944698992053)
                  ·
                    refine ⟨912145665365244815530505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9729553763895944698992053 912145665365244815530505)
                    ·
                      refine ⟨684109249023933611647879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 912145665365244815530505 684109249023933611647879)
                      ·
                        rfl

theorem cell23_1332298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_1332298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332298 prefixEnd_1332298 := by exact prefixLift 1332298
  have htrace : WordTrace (prefixWord ++ tailWord_1332298) baseStart_1332298 baseEnd_1332298 := by
    simpa [prefixWord, tailWord_1332298, baseEnd_1332298] using wordTrace_append hprefix tailTrace_1332298
  have hstable : (prefixWord ++ tailWord_1332298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332298).length < 2 ^ (prefixWord ++ tailWord_1332298).sum := by decide
  have hdescent : baseEnd_1332298 < baseStart_1332298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332308 : List Nat := [2, 4, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_1332308 : Nat := 118140960795 + 1332308 * 2 ^ 59
def prefixEnd_1332308 : Nat := 4983230072969 + 3 ^ 40 * 1332308 * 2
def baseEnd_1332308 : Nat := 228038127943492857507611

theorem tailTrace_1332308 : CollatzResearch.WordTrace tailWord_1332308 prefixEnd_1332308 228038127943492857507611 := by
  unfold tailWord_1332308
  simp only [CollatzResearch.WordTrace]
  refine ⟨24296632428641565468058789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32395509904855420624078385 24296632428641565468058789)
  ·
    refine ⟨4555618580370293525261023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24296632428641565468058789 4555618580370293525261023)
    ·
      refine ⟨6833427870555440287891535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4555618580370293525261023 6833427870555440287891535)
      ·
        refine ⟨10250141805833160431837303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6833427870555440287891535 10250141805833160431837303)
        ·
          refine ⟨15375212708749740647755955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10250141805833160431837303 15375212708749740647755955)
          ·
            refine ⟨23062819063124610971633933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15375212708749740647755955 23062819063124610971633933)
            ·
              refine ⟨8648557148671729114362725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23062819063124610971633933 8648557148671729114362725)
              ·
                refine ⟨1621604465375949208943011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8648557148671729114362725 1621604465375949208943011)
                ·
                  refine ⟨2432406698063923813414517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1621604465375949208943011 2432406698063923813414517)
                  ·
                    refine ⟨228038127943492857507611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2432406698063923813414517 228038127943492857507611)
                    ·
                      rfl

theorem cell23_1332308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_1332308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332308 prefixEnd_1332308 := by exact prefixLift 1332308
  have htrace : WordTrace (prefixWord ++ tailWord_1332308) baseStart_1332308 baseEnd_1332308 := by
    simpa [prefixWord, tailWord_1332308, baseEnd_1332308] using wordTrace_append hprefix tailTrace_1332308
  have hstable : (prefixWord ++ tailWord_1332308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332308).length < 2 ^ (prefixWord ++ tailWord_1332308).sum := by decide
  have hdescent : baseEnd_1332308 < baseStart_1332308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332321 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 1, 6]
def baseStart_1332321 : Nat := 118140960795 + 1332321 * 2 ^ 59
def prefixEnd_1332321 : Nat := 4983230072969 + 3 ^ 40 * 1332321 * 2
def baseEnd_1332321 : Nat := 228040353026329007220091

theorem tailTrace_1332321 : CollatzResearch.WordTrace tailWord_1332321 prefixEnd_1332321 228040353026329007220091 := by
  unfold tailWord_1332321
  simp only [CollatzResearch.WordTrace]
  refine ⟨48593739006236034156340817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32395826004157356104227211 48593739006236034156340817)
  ·
    refine ⟨36445304254677025617255613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48593739006236034156340817 36445304254677025617255613)
    ·
      refine ⟨13666989095503884606470855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36445304254677025617255613 13666989095503884606470855)
      ·
        refine ⟨20500483643255826909706283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13666989095503884606470855 20500483643255826909706283)
        ·
          refine ⟨30750725464883740364559425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20500483643255826909706283 30750725464883740364559425)
          ·
            refine ⟨23063044098662805273419569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30750725464883740364559425 23063044098662805273419569)
            ·
              refine ⟨17297283073997103955064677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23063044098662805273419569 17297283073997103955064677)
              ·
                refine ⟨3243240576374456991574627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17297283073997103955064677 3243240576374456991574627)
                ·
                  refine ⟨4864860864561685487361941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3243240576374456991574627 4864860864561685487361941)
                  ·
                    refine ⟨228040353026329007220091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4864860864561685487361941 228040353026329007220091)
                    ·
                      rfl

theorem cell23_1332321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_1332321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332321 prefixEnd_1332321 := by exact prefixLift 1332321
  have htrace : WordTrace (prefixWord ++ tailWord_1332321) baseStart_1332321 baseEnd_1332321 := by
    simpa [prefixWord, tailWord_1332321, baseEnd_1332321] using wordTrace_append hprefix tailTrace_1332321
  have hstable : (prefixWord ++ tailWord_1332321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332321).length < 2 ^ (prefixWord ++ tailWord_1332321).sum := by decide
  have hdescent : baseEnd_1332321 < baseStart_1332321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332338 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 4, 4]
def baseStart_1332338 : Nat := 118140960795 + 1332338 * 2 ^ 59
def prefixEnd_1332338 : Nat := 4983230072969 + 3 ^ 40 * 1332338 * 2
def baseEnd_1332338 : Nat := 228043262750037818382565

theorem tailTrace_1332338 : CollatzResearch.WordTrace tailWord_1332338 prefixEnd_1332338 228043262750037818382565 := by
  unfold tailWord_1332338
  simp only [CollatzResearch.WordTrace]
  refine ⟨12148589761793611514927417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32396239364782964039806445 12148589761793611514927417)
  ·
    refine ⟨9111442321345208636195563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12148589761793611514927417 9111442321345208636195563)
    ·
      refine ⟨13667163482017812954293345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9111442321345208636195563 13667163482017812954293345)
      ·
        refine ⟨10250372611513359715720009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13667163482017812954293345 10250372611513359715720009)
        ·
          refine ⟨7687779458635019786790007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10250372611513359715720009 7687779458635019786790007)
          ·
            refine ⟨11531669187952529680185011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7687779458635019786790007 11531669187952529680185011)
            ·
              refine ⟨17297503781928794520277517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11531669187952529680185011 17297503781928794520277517)
              ·
                refine ⟨6486563918223297945104069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17297503781928794520277517 6486563918223297945104069)
                ·
                  refine ⟨1216230734666868364707013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6486563918223297945104069 1216230734666868364707013)
                  ·
                    refine ⟨228043262750037818382565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1216230734666868364707013 228043262750037818382565)
                    ·
                      rfl

theorem cell23_1332338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_1332338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332338 prefixEnd_1332338 := by exact prefixLift 1332338
  have htrace : WordTrace (prefixWord ++ tailWord_1332338) baseStart_1332338 baseEnd_1332338 := by
    simpa [prefixWord, tailWord_1332338, baseEnd_1332338] using wordTrace_append hprefix tailTrace_1332338
  have hstable : (prefixWord ++ tailWord_1332338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332338).length < 2 ^ (prefixWord ++ tailWord_1332338).sum := by decide
  have hdescent : baseEnd_1332338 < baseStart_1332338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332348 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 3, 2, 3]
def baseStart_1332348 : Nat := 118140960795 + 1332348 * 2 ^ 59
def prefixEnd_1332348 : Nat := 4983230072969 + 3 ^ 40 * 1332348 * 2
def baseEnd_1332348 : Nat := 684134923056658416022649

theorem tailTrace_1332348 : CollatzResearch.WordTrace tailWord_1332348 prefixEnd_1332348 684134923056658416022649 := by
  unfold tailWord_1332348
  simp only [CollatzResearch.WordTrace]
  refine ⟨24297361888569108883786849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32396482518092145178382465 24297361888569108883786849)
  ·
    refine ⟨18223021416426831662840137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24297361888569108883786849 18223021416426831662840137)
    ·
      refine ⟨13667266062320123747130103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18223021416426831662840137 13667266062320123747130103)
      ·
        refine ⟨20500899093480185620695155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13667266062320123747130103 20500899093480185620695155)
        ·
          refine ⟨30751348640220278431042733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20500899093480185620695155 30751348640220278431042733)
          ·
            refine ⟨11531755740082604411641025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30751348640220278431042733 11531755740082604411641025)
            ·
              refine ⟨8648816805061953308730769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11531755740082604411641025 8648816805061953308730769)
              ·
                refine ⟨6486612603796464981548077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8648816805061953308730769 6486612603796464981548077)
                ·
                  refine ⟨2432479726423674368080529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6486612603796464981548077 2432479726423674368080529)
                  ·
                    refine ⟨1824359794817755776060397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2432479726423674368080529 1824359794817755776060397)
                    ·
                      refine ⟨684134923056658416022649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1824359794817755776060397 684134923056658416022649)
                      ·
                        rfl

theorem cell23_1332348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_1332348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332348 prefixEnd_1332348 := by exact prefixLift 1332348
  have htrace : WordTrace (prefixWord ++ tailWord_1332348) baseStart_1332348 baseEnd_1332348 := by
    simpa [prefixWord, tailWord_1332348, baseEnd_1332348] using wordTrace_append hprefix tailTrace_1332348
  have hstable : (prefixWord ++ tailWord_1332348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332348).length < 2 ^ (prefixWord ++ tailWord_1332348).sum := by decide
  have hdescent : baseEnd_1332348 < baseStart_1332348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332382 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_1332382 : Nat := 118140960795 + 1332382 * 2 ^ 59
def prefixEnd_1332382 : Nat := 4983230072969 + 3 ^ 40 * 1332382 * 2
def baseEnd_1332382 : Nat := 684152381398911282997493

theorem tailTrace_1332382 : CollatzResearch.WordTrace tailWord_1332382 prefixEnd_1332382 684152381398911282997493 := by
  unfold tailWord_1332382
  simp only [CollatzResearch.WordTrace]
  refine ⟨6074495482376880196788925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32397309239343361049540933 6074495482376880196788925)
  ·
    refine ⟨2277935805891330073795847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6074495482376880196788925 2277935805891330073795847)
    ·
      refine ⟨3416903708836995110693771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2277935805891330073795847 3416903708836995110693771)
      ·
        refine ⟨5125355563255492666040657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3416903708836995110693771 5125355563255492666040657)
        ·
          refine ⟨3844016672441619499530493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5125355563255492666040657 3844016672441619499530493)
          ·
            refine ⟨1441506252165607312323935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3844016672441619499530493 1441506252165607312323935)
            ·
              refine ⟨2162259378248410968485903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1441506252165607312323935 2162259378248410968485903)
              ·
                refine ⟨3243389067372616452728855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2162259378248410968485903 3243389067372616452728855)
                ·
                  refine ⟨4865083601058924679093283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3243389067372616452728855 4865083601058924679093283)
                  ·
                    refine ⟨7297625401588387018639925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4865083601058924679093283 7297625401588387018639925)
                    ·
                      refine ⟨684152381398911282997493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7297625401588387018639925 684152381398911282997493)
                      ·
                        rfl

theorem cell23_1332382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_1332382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332382 prefixEnd_1332382 := by exact prefixLift 1332382
  have htrace : WordTrace (prefixWord ++ tailWord_1332382) baseStart_1332382 baseEnd_1332382 := by
    simpa [prefixWord, tailWord_1332382, baseEnd_1332382] using wordTrace_append hprefix tailTrace_1332382
  have hstable : (prefixWord ++ tailWord_1332382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332382).length < 2 ^ (prefixWord ++ tailWord_1332382).sum := by decide
  have hdescent : baseEnd_1332382 < baseStart_1332382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332412 : List Nat := [2, 2, 2, 3, 2, 1, 2, 3, 2, 1, 3]
def baseStart_1332412 : Nat := 118140960795 + 1332412 * 2 ^ 59
def prefixEnd_1332412 : Nat := 4983230072969 + 3 ^ 40 * 1332412 * 2
def baseEnd_1332412 : Nat := 684167785818546165622355

theorem tailTrace_1332412 : CollatzResearch.WordTrace tailWord_1332412 prefixEnd_1332412 684167785818546165622355 := by
  unfold tailWord_1332412
  simp only [CollatzResearch.WordTrace]
  refine ⟨24298529024453178348951745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32398038699270904465268993 24298529024453178348951745)
  ·
    refine ⟨18223896768339883761713809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24298529024453178348951745 18223896768339883761713809)
    ·
      refine ⟨13667922576254912821285357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18223896768339883761713809 13667922576254912821285357)
      ·
        refine ⟨5125470966095592307982009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13667922576254912821285357 5125470966095592307982009)
        ·
          refine ⟨3844103224571694230986507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5125470966095592307982009 3844103224571694230986507)
          ·
            refine ⟨5766154836857541346479761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3844103224571694230986507 5766154836857541346479761)
            ·
              refine ⟨4324616127643156009859821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5766154836857541346479761 4324616127643156009859821)
              ·
                refine ⟨1621731047866183503697433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4324616127643156009859821 1621731047866183503697433)
                ·
                  refine ⟨1216298285899637627773075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1621731047866183503697433 1216298285899637627773075)
                  ·
                    refine ⟨1824447428849456441659613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1216298285899637627773075 1824447428849456441659613)
                    ·
                      refine ⟨684167785818546165622355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1824447428849456441659613 684167785818546165622355)
                      ·
                        rfl

theorem cell23_1332412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_1332412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332412 prefixEnd_1332412 := by exact prefixLift 1332412
  have htrace : WordTrace (prefixWord ++ tailWord_1332412) baseStart_1332412 baseEnd_1332412 := by
    simpa [prefixWord, tailWord_1332412, baseEnd_1332412] using wordTrace_append hprefix tailTrace_1332412
  have hstable : (prefixWord ++ tailWord_1332412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332412).length < 2 ^ (prefixWord ++ tailWord_1332412).sum := by decide
  have hdescent : baseEnd_1332412 < baseStart_1332412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332435 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 6, 2, 2]
def baseStart_1332435 : Nat := 118140960795 + 1332435 * 2 ^ 59
def prefixEnd_1332435 : Nat := 4983230072969 + 3 ^ 40 * 1332435 * 2
def baseEnd_1332435 : Nat := 684179595873599575634749

theorem tailTrace_1332435 : CollatzResearch.WordTrace tailWord_1332435 prefixEnd_1332435 684179595873599575634749 := by
  unfold tailWord_1332435
  simp only [CollatzResearch.WordTrace]
  refine ⟨48597896927823031625990759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32398597951882021083993839 48597896927823031625990759)
  ·
    refine ⟨72896845391734547438986139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48597896927823031625990759 72896845391734547438986139)
    ·
      refine ⟨109345268087601821158479209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72896845391734547438986139 109345268087601821158479209)
      ·
        refine ⟨82008951065701365868859407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109345268087601821158479209 82008951065701365868859407)
        ·
          refine ⟨123013426598552048803289111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82008951065701365868859407 123013426598552048803289111)
          ·
            refine ⟨184520139897828073204933667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123013426598552048803289111 184520139897828073204933667)
            ·
              refine ⟨276780209846742109807400501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184520139897828073204933667 276780209846742109807400501)
              ·
                refine ⟨25948144673132072794443797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 276780209846742109807400501 25948144673132072794443797)
                ·
                  refine ⟨1216319281553065912239553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25948144673132072794443797 1216319281553065912239553)
                  ·
                    refine ⟨912239461164799434179665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1216319281553065912239553 912239461164799434179665)
                    ·
                      refine ⟨684179595873599575634749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 912239461164799434179665 684179595873599575634749)
                      ·
                        rfl

theorem cell23_1332435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 2, 2].length) (baseStart_1332435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332435 prefixEnd_1332435 := by exact prefixLift 1332435
  have htrace : WordTrace (prefixWord ++ tailWord_1332435) baseStart_1332435 baseEnd_1332435 := by
    simpa [prefixWord, tailWord_1332435, baseEnd_1332435] using wordTrace_append hprefix tailTrace_1332435
  have hstable : (prefixWord ++ tailWord_1332435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332435).length < 2 ^ (prefixWord ++ tailWord_1332435).sum := by decide
  have hdescent : baseEnd_1332435 < baseStart_1332435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332441 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 11]
def baseStart_1332441 : Nat := 118140960795 + 1332441 * 2 ^ 59
def prefixEnd_1332441 : Nat := 4983230072969 + 3 ^ 40 * 1332441 * 2
def baseEnd_1332441 : Nat := 76020297417502950239969

theorem tailTrace_1332441 : CollatzResearch.WordTrace tailWord_1332441 prefixEnd_1332441 76020297417502950239969 := by
  unfold tailWord_1332441
  simp only [CollatzResearch.WordTrace]
  refine ⟨48598115765801294650709177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32398743843867529767139451 48598115765801294650709177)
  ·
    refine ⟨36448586824350970988031883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48598115765801294650709177 36448586824350970988031883)
    ·
      refine ⟨54672880236526456482047825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36448586824350970988031883 54672880236526456482047825)
      ·
        refine ⟨41004660177394842361535869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54672880236526456482047825 41004660177394842361535869)
        ·
          refine ⟨15376747566523065885575951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41004660177394842361535869 15376747566523065885575951)
          ·
            refine ⟨23065121349784598828363927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15376747566523065885575951 23065121349784598828363927)
            ·
              refine ⟨34597682024676898242545891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23065121349784598828363927 34597682024676898242545891)
              ·
                refine ⟨51896523037015347363818837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34597682024676898242545891 51896523037015347363818837)
                ·
                  refine ⟨76020297417502950239969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 51896523037015347363818837 76020297417502950239969)
                  ·
                    rfl

theorem cell23_1332441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 11].length) (baseStart_1332441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332441 prefixEnd_1332441 := by exact prefixLift 1332441
  have htrace : WordTrace (prefixWord ++ tailWord_1332441) baseStart_1332441 baseEnd_1332441 := by
    simpa [prefixWord, tailWord_1332441, baseEnd_1332441] using wordTrace_append hprefix tailTrace_1332441
  have hstable : (prefixWord ++ tailWord_1332441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332441).length < 2 ^ (prefixWord ++ tailWord_1332441).sum := by decide
  have hdescent : baseEnd_1332441 < baseStart_1332441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332448 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 4]
def baseStart_1332448 : Nat := 118140960795 + 1332448 * 2 ^ 59
def prefixEnd_1332448 : Nat := 4983230072969 + 3 ^ 40 * 1332448 * 2
def baseEnd_1332448 : Nat := 684186271122108024772189

theorem tailTrace_1332448 : CollatzResearch.WordTrace tailWord_1332448 prefixEnd_1332448 684186271122108024772189 := by
  unfold tailWord_1332448
  simp only [CollatzResearch.WordTrace]
  refine ⟨24299185538387967423106999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32398914051183956564142665 24299185538387967423106999)
  ·
    refine ⟨36448778307581951134660499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24299185538387967423106999 36448778307581951134660499)
    ·
      refine ⟨54673167461372926701990749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36448778307581951134660499 54673167461372926701990749)
      ·
        refine ⟨20502437798014847513246531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54673167461372926701990749 20502437798014847513246531)
        ·
          refine ⟨30753656697022271269869797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20502437798014847513246531 30753656697022271269869797)
          ·
            refine ⟨5766310630691675863100587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30753656697022271269869797 5766310630691675863100587)
            ·
              refine ⟨8649465946037513794650881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5766310630691675863100587 8649465946037513794650881)
              ·
                refine ⟨6487099459528135345988161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8649465946037513794650881 6487099459528135345988161)
                ·
                  refine ⟨4865324594646101509491121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6487099459528135345988161 4865324594646101509491121)
                  ·
                    refine ⟨3648993445984576132118341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4865324594646101509491121 3648993445984576132118341)
                    ·
                      refine ⟨684186271122108024772189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3648993445984576132118341 684186271122108024772189)
                      ·
                        rfl

theorem cell23_1332448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_1332448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332448 prefixEnd_1332448 := by exact prefixLift 1332448
  have htrace : WordTrace (prefixWord ++ tailWord_1332448) baseStart_1332448 baseEnd_1332448 := by
    simpa [prefixWord, tailWord_1332448, baseEnd_1332448] using wordTrace_append hprefix tailTrace_1332448
  have hstable : (prefixWord ++ tailWord_1332448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332448).length < 2 ^ (prefixWord ++ tailWord_1332448).sum := by decide
  have hdescent : baseEnd_1332448 < baseStart_1332448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332458 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 7]
def baseStart_1332458 : Nat := 118140960795 + 1332458 * 2 ^ 59
def prefixEnd_1332458 : Nat := 4983230072969 + 3 ^ 40 * 1332458 * 2
def baseEnd_1332458 : Nat := 76021267325405887294127

theorem tailTrace_1332458 : CollatzResearch.WordTrace tailWord_1332458 prefixEnd_1332458 76021267325405887294127 := by
  unfold tailWord_1332458
  simp only [CollatzResearch.WordTrace]
  refine ⟨12149683951684926638519507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32399157204493137702718685 12149683951684926638519507)
  ·
    refine ⟨18224525927527389957779261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12149683951684926638519507 18224525927527389957779261)
    ·
      refine ⟨6834197222822771234167223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18224525927527389957779261 6834197222822771234167223)
      ·
        refine ⟨10251295834234156851250835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6834197222822771234167223 10251295834234156851250835)
        ·
          refine ⟨15376943751351235276876253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10251295834234156851250835 15376943751351235276876253)
          ·
            refine ⟨5766353906756713228828595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15376943751351235276876253 5766353906756713228828595)
            ·
              refine ⟨8649530860135069843242893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5766353906756713228828595 8649530860135069843242893)
              ·
                refine ⟨3243574072550651191216085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8649530860135069843242893 3243574072550651191216085)
                ·
                  refine ⟨76021267325405887294127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3243574072550651191216085 76021267325405887294127)
                  ·
                    rfl

theorem cell23_1332458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 7].length) (baseStart_1332458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332458 prefixEnd_1332458 := by exact prefixLift 1332458
  have htrace : WordTrace (prefixWord ++ tailWord_1332458) baseStart_1332458 baseEnd_1332458 := by
    simpa [prefixWord, tailWord_1332458, baseEnd_1332458] using wordTrace_append hprefix tailTrace_1332458
  have hstable : (prefixWord ++ tailWord_1332458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332458).length < 2 ^ (prefixWord ++ tailWord_1332458).sum := by decide
  have hdescent : baseEnd_1332458 < baseStart_1332458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332492 : List Nat := [2, 2, 1, 2, 2, 5, 1, 3, 5]
def baseStart_1332492 : Nat := 118140960795 + 1332492 * 2 ^ 59
def prefixEnd_1332492 : Nat := 4983230072969 + 3 ^ 40 * 1332492 * 2
def baseEnd_1332492 : Nat := 76023207141211761402443

theorem tailTrace_1332492 : CollatzResearch.WordTrace tailWord_1332492 prefixEnd_1332492 76023207141211761402443 := by
  unfold tailWord_1332492
  simp only [CollatzResearch.WordTrace]
  refine ⟨24299987944308265180407865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32399983925744353573877153 24299987944308265180407865)
  ·
    refine ⟨18224990958231198885305899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24299987944308265180407865 18224990958231198885305899)
    ·
      refine ⟨27337486437346798327958849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18224990958231198885305899 27337486437346798327958849)
      ·
        refine ⟨20503114828010098745969137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27337486437346798327958849 20503114828010098745969137)
        ·
          refine ⟨15377336121007574059476853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20503114828010098745969137 15377336121007574059476853)
          ·
            refine ⟨1441625261344460068075955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15377336121007574059476853 1441625261344460068075955)
            ·
              refine ⟨2162437892016690102113933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1441625261344460068075955 2162437892016690102113933)
              ·
                refine ⟨810914209506258788292725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2162437892016690102113933 810914209506258788292725)
                ·
                  refine ⟨76023207141211761402443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 810914209506258788292725 76023207141211761402443)
                  ·
                    rfl

theorem cell23_1332492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 5].length) (baseStart_1332492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332492 prefixEnd_1332492 := by exact prefixLift 1332492
  have htrace : WordTrace (prefixWord ++ tailWord_1332492) baseStart_1332492 baseEnd_1332492 := by
    simpa [prefixWord, tailWord_1332492, baseEnd_1332492] using wordTrace_append hprefix tailTrace_1332492
  have hstable : (prefixWord ++ tailWord_1332492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332492).length < 2 ^ (prefixWord ++ tailWord_1332492).sum := by decide
  have hdescent : baseEnd_1332492 < baseStart_1332492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332509 : List Nat := [1, 4, 2, 3, 1, 2, 3, 2, 5]
def baseStart_1332509 : Nat := 118140960795 + 1332509 * 2 ^ 59
def prefixEnd_1332509 : Nat := 4983230072969 + 3 ^ 40 * 1332509 * 2
def baseEnd_1332509 : Nat := 76024177049114698456601

theorem tailTrace_1332509 : CollatzResearch.WordTrace tailWord_1332509 prefixEnd_1332509 76024177049114698456601 := by
  unfold tailWord_1332509
  simp only [CollatzResearch.WordTrace]
  refine ⟨48600595929554942264184581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32400397286369961509456387 48600595929554942264184581)
  ·
    refine ⟨9112611736791551674534609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48600595929554942264184581 9112611736791551674534609)
    ·
      refine ⟨6834458802593663755900957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9112611736791551674534609 6834458802593663755900957)
      ·
        refine ⟨2562922050972623908462859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6834458802593663755900957 2562922050972623908462859)
        ·
          refine ⟨3844383076458935862694289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2562922050972623908462859 3844383076458935862694289)
          ·
            refine ⟨2883287307344201897020717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3844383076458935862694289 2883287307344201897020717)
            ·
              refine ⟨1081232740254075711382769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2883287307344201897020717 1081232740254075711382769)
              ·
                refine ⟨810924555190556783537077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081232740254075711382769 810924555190556783537077)
                ·
                  refine ⟨76024177049114698456601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 810924555190556783537077 76024177049114698456601)
                  ·
                    rfl

theorem cell23_1332509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_1332509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332509 prefixEnd_1332509 := by exact prefixLift 1332509
  have htrace : WordTrace (prefixWord ++ tailWord_1332509) baseStart_1332509 baseEnd_1332509 := by
    simpa [prefixWord, tailWord_1332509, baseEnd_1332509] using wordTrace_append hprefix tailTrace_1332509
  have hstable : (prefixWord ++ tailWord_1332509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332509).length < 2 ^ (prefixWord ++ tailWord_1332509).sum := by decide
  have hdescent : baseEnd_1332509 < baseStart_1332509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332542 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_1332542 : Nat := 118140960795 + 1332542 * 2 ^ 59
def prefixEnd_1332542 : Nat := 4983230072969 + 3 ^ 40 * 1332542 * 2
def baseEnd_1332542 : Nat := 684234538303630656996757

theorem tailTrace_1332542 : CollatzResearch.WordTrace tailWord_1332542 prefixEnd_1332542 684234538303630656996757 := by
  unfold tailWord_1332542
  simp only [CollatzResearch.WordTrace]
  refine ⟨6075224942304423612516985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32401199692290259266757253 6075224942304423612516985)
  ·
    refine ⟨4556418706728317709387739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6075224942304423612516985 4556418706728317709387739)
    ·
      refine ⟨6834628060092476564081609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4556418706728317709387739 6834628060092476564081609)
      ·
        refine ⟨5125971045069357423061207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6834628060092476564081609 5125971045069357423061207)
        ·
          refine ⟨7688956567604036134591811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5125971045069357423061207 7688956567604036134591811)
          ·
            refine ⟨11533434851406054201887717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7688956567604036134591811 11533434851406054201887717)
            ·
              refine ⟨2162519034638635162853947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11533434851406054201887717 2162519034638635162853947)
              ·
                refine ⟨3243778551957952744280921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2162519034638635162853947 3243778551957952744280921)
                ·
                  refine ⟨2432833913968464558210691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3243778551957952744280921 2432833913968464558210691)
                  ·
                    refine ⟨3649250870952696837316037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2432833913968464558210691 3649250870952696837316037)
                    ·
                      refine ⟨684234538303630656996757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3649250870952696837316037 684234538303630656996757)
                      ·
                        rfl

theorem cell23_1332542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_1332542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332542 prefixEnd_1332542 := by exact prefixLift 1332542
  have htrace : WordTrace (prefixWord ++ tailWord_1332542) baseStart_1332542 baseEnd_1332542 := by
    simpa [prefixWord, tailWord_1332542, baseEnd_1332542] using wordTrace_append hprefix tailTrace_1332542
  have hstable : (prefixWord ++ tailWord_1332542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332542).length < 2 ^ (prefixWord ++ tailWord_1332542).sum := by decide
  have hdescent : baseEnd_1332542 < baseStart_1332542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332552 : List Nat := [2, 1, 3, 1, 1, 2, 1, 7, 1, 4]
def baseStart_1332552 : Nat := 118140960795 + 1332552 * 2 ^ 59
def prefixEnd_1332552 : Nat := 4983230072969 + 3 ^ 40 * 1332552 * 2
def baseEnd_1332552 : Nat := 228079891036725205957237

theorem tailTrace_1332552 : CollatzResearch.WordTrace tailWord_1332552 prefixEnd_1332552 228079891036725205957237 := by
  unfold tailWord_1332552
  simp only [CollatzResearch.WordTrace]
  refine ⟨24301082134199580303999955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32401442845599440405333273 24301082134199580303999955)
  ·
    refine ⟨36451623201299370455999933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24301082134199580303999955 36451623201299370455999933)
    ·
      refine ⟨13669358700487263920999975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36451623201299370455999933 13669358700487263920999975)
      ·
        refine ⟨20504038050730895881499963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13669358700487263920999975 20504038050730895881499963)
        ·
          refine ⟨30756057076096343822249945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20504038050730895881499963 30756057076096343822249945)
          ·
            refine ⟨23067042807072257866687459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30756057076096343822249945 23067042807072257866687459)
            ·
              refine ⟨34600564210608386800031189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23067042807072257866687459 34600564210608386800031189)
              ·
                refine ⟨810950723686134065625731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 34600564210608386800031189 810950723686134065625731)
                ·
                  refine ⟨1216426085529201098438597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810950723686134065625731 1216426085529201098438597)
                  ·
                    refine ⟨228079891036725205957237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1216426085529201098438597 228079891036725205957237)
                    ·
                      rfl

theorem cell23_1332552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_1332552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332552 prefixEnd_1332552 := by exact prefixLift 1332552
  have htrace : WordTrace (prefixWord ++ tailWord_1332552) baseStart_1332552 baseEnd_1332552 := by
    simpa [prefixWord, tailWord_1332552, baseEnd_1332552] using wordTrace_append hprefix tailTrace_1332552
  have hstable : (prefixWord ++ tailWord_1332552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332552).length < 2 ^ (prefixWord ++ tailWord_1332552).sum := by decide
  have hdescent : baseEnd_1332552 < baseStart_1332552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332565 : List Nat := [1, 3, 2, 2, 3, 1, 1, 4, 6]
def baseStart_1332565 : Nat := 118140960795 + 1332565 * 2 ^ 59
def prefixEnd_1332565 : Nat := 4983230072969 + 3 ^ 40 * 1332565 * 2
def baseEnd_1332565 : Nat := 76027372039853785223239

theorem tailTrace_1332565 : CollatzResearch.WordTrace tailWord_1332565 prefixEnd_1332565 76027372039853785223239 := by
  unfold tailWord_1332565
  simp only [CollatzResearch.WordTrace]
  refine ⟨48602638417352063828223149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32401758944901375885482099 48602638417352063828223149)
  ·
    refine ⟨18225989406507023935583681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48602638417352063828223149 18225989406507023935583681)
    ·
      refine ⟨13669492054880267951687761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18225989406507023935583681 13669492054880267951687761)
      ·
        refine ⟨10252119041160200963765821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13669492054880267951687761 10252119041160200963765821)
        ·
          refine ⟨3844544640435075361412183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10252119041160200963765821 3844544640435075361412183)
          ·
            refine ⟨5766816960652613042118275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3844544640435075361412183 5766816960652613042118275)
            ·
              refine ⟨8650225440978919563177413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5766816960652613042118275 8650225440978919563177413)
              ·
                refine ⟨1621917270183547418095765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8650225440978919563177413 1621917270183547418095765)
                ·
                  refine ⟨76027372039853785223239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1621917270183547418095765 76027372039853785223239)
                  ·
                    rfl

theorem cell23_1332565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 6].length) (baseStart_1332565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332565 prefixEnd_1332565 := by exact prefixLift 1332565
  have htrace : WordTrace (prefixWord ++ tailWord_1332565) baseStart_1332565 baseEnd_1332565 := by
    simpa [prefixWord, tailWord_1332565, baseEnd_1332565] using wordTrace_append hprefix tailTrace_1332565
  have hstable : (prefixWord ++ tailWord_1332565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332565).length < 2 ^ (prefixWord ++ tailWord_1332565).sum := by decide
  have hdescent : baseEnd_1332565 < baseStart_1332565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332568 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 1, 2, 6]
def baseStart_1332568 : Nat := 118140960795 + 1332568 * 2 ^ 59
def prefixEnd_1332568 : Nat := 4983230072969 + 3 ^ 40 * 1332568 * 2
def baseEnd_1332568 : Nat := 684247888800647555271637

theorem tailTrace_1332568 : CollatzResearch.WordTrace tailWord_1332568 prefixEnd_1332568 684247888800647555271637 := by
  unfold tailWord_1332568
  simp only [CollatzResearch.WordTrace]
  refine ⟨24301373918170597670291179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32401831890894130227054905 24301373918170597670291179)
  ·
    refine ⟨36452060877255896505436769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24301373918170597670291179 36452060877255896505436769)
    ·
      refine ⟨27339045657941922379077577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36452060877255896505436769 27339045657941922379077577)
      ·
        refine ⟨20504284243456441784308183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27339045657941922379077577 20504284243456441784308183)
        ·
          refine ⟨30756426365184662676462275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20504284243456441784308183 30756426365184662676462275)
          ·
            refine ⟨46134639547776994014693413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30756426365184662676462275 46134639547776994014693413)
            ·
              refine ⟨8650244915208186377755015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46134639547776994014693413 8650244915208186377755015)
              ·
                refine ⟨12975367372812279566632523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8650244915208186377755015 12975367372812279566632523)
                ·
                  refine ⟨19463051059218419349948785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12975367372812279566632523 19463051059218419349948785)
                  ·
                    refine ⟨14597288294413814512461589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19463051059218419349948785 14597288294413814512461589)
                    ·
                      refine ⟨684247888800647555271637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14597288294413814512461589 684247888800647555271637)
                      ·
                        rfl

theorem cell23_1332568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_1332568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332568 prefixEnd_1332568 := by exact prefixLift 1332568
  have htrace : WordTrace (prefixWord ++ tailWord_1332568) baseStart_1332568 baseEnd_1332568 := by
    simpa [prefixWord, tailWord_1332568, baseEnd_1332568] using wordTrace_append hprefix tailTrace_1332568
  have hstable : (prefixWord ++ tailWord_1332568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332568).length < 2 ^ (prefixWord ++ tailWord_1332568).sum := by decide
  have hdescent : baseEnd_1332568 < baseStart_1332568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332569 : List Nat := [1, 2, 1, 2, 2, 2, 6, 2, 1, 4]
def baseStart_1332569 : Nat := 118140960795 + 1332569 * 2 ^ 59
def prefixEnd_1332569 : Nat := 4983230072969 + 3 ^ 40 * 1332569 * 2
def baseEnd_1332569 : Nat := 228082800760434017119711

theorem tailTrace_1332569 : CollatzResearch.WordTrace tailWord_1332569 prefixEnd_1332569 228082800760434017119711 := by
  unfold tailWord_1332569
  simp only [CollatzResearch.WordTrace]
  refine ⟨48602784309337572511368761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32401856206225048340912507 48602784309337572511368761)
  ·
    refine ⟨36452088232003179383526571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48602784309337572511368761 36452088232003179383526571)
    ·
      refine ⟨54678132348004769075289857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36452088232003179383526571 54678132348004769075289857)
      ·
        refine ⟨41008599261003576806467393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54678132348004769075289857 41008599261003576806467393)
        ·
          refine ⟨30756449445752682604850545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41008599261003576806467393 30756449445752682604850545)
          ·
            refine ⟨23067337084314511953637909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30756449445752682604850545 23067337084314511953637909)
            ·
              refine ⟨1081281425827242747826777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23067337084314511953637909 1081281425827242747826777)
              ·
                refine ⟨810961069370432060870083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081281425827242747826777 810961069370432060870083)
                ·
                  refine ⟨1216441604055648091305125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810961069370432060870083 1216441604055648091305125)
                  ·
                    refine ⟨228082800760434017119711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1216441604055648091305125 228082800760434017119711)
                    ·
                      rfl

theorem cell23_1332569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 1, 4].length) (baseStart_1332569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332569 prefixEnd_1332569 := by exact prefixLift 1332569
  have htrace : WordTrace (prefixWord ++ tailWord_1332569) baseStart_1332569 baseEnd_1332569 := by
    simpa [prefixWord, tailWord_1332569, baseEnd_1332569] using wordTrace_append hprefix tailTrace_1332569
  have hstable : (prefixWord ++ tailWord_1332569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332569).length < 2 ^ (prefixWord ++ tailWord_1332569).sum := by decide
  have hdescent : baseEnd_1332569 < baseStart_1332569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332592 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 3, 1, 3]
def baseStart_1332592 : Nat := 118140960795 + 1332592 * 2 ^ 59
def prefixEnd_1332592 : Nat := 4983230072969 + 3 ^ 40 * 1332592 * 2
def baseEnd_1332592 : Nat := 684260212336355461371527

theorem tailTrace_1332592 : CollatzResearch.WordTrace tailWord_1332592 prefixEnd_1332592 684260212336355461371527 := by
  unfold tailWord_1332592
  simp only [CollatzResearch.WordTrace]
  refine ⟨24301811594127123719728015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32402415458836164959637353 24301811594127123719728015)
  ·
    refine ⟨36452717391190685579592023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24301811594127123719728015 36452717391190685579592023)
    ·
      refine ⟨54679076086786028369388035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36452717391190685579592023 54679076086786028369388035)
      ·
        refine ⟨82018614130179042554082053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54679076086786028369388035 82018614130179042554082053)
        ·
          refine ⟨15378490149408570478890385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82018614130179042554082053 15378490149408570478890385)
          ·
            refine ⟨11533867612056427859167789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15378490149408570478890385 11533867612056427859167789)
            ·
              refine ⟨4325200354521160447187921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11533867612056427859167789 4325200354521160447187921)
              ·
                refine ⟨3243900265890870335390941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4325200354521160447187921 3243900265890870335390941)
                ·
                  refine ⟨1216462599709076375771603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3243900265890870335390941 1216462599709076375771603)
                  ·
                    refine ⟨1824693899563614563657405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1216462599709076375771603 1824693899563614563657405)
                    ·
                      refine ⟨684260212336355461371527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1824693899563614563657405 684260212336355461371527)
                      ·
                        rfl

theorem cell23_1332592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 3, 1, 3].length) (baseStart_1332592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332592 prefixEnd_1332592 := by exact prefixLift 1332592
  have htrace : WordTrace (prefixWord ++ tailWord_1332592) baseStart_1332592 baseEnd_1332592 := by
    simpa [prefixWord, tailWord_1332592, baseEnd_1332592] using wordTrace_append hprefix tailTrace_1332592
  have hstable : (prefixWord ++ tailWord_1332592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332592).length < 2 ^ (prefixWord ++ tailWord_1332592).sum := by decide
  have hdescent : baseEnd_1332592 < baseStart_1332592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332612 : List Nat := [2, 3, 2, 1, 1, 4, 1, 3, 1, 5]
def baseStart_1332612 : Nat := 118140960795 + 1332612 * 2 ^ 59
def prefixEnd_1332612 : Nat := 4983230072969 + 3 ^ 40 * 1332612 * 2
def baseEnd_1332612 : Nat := 228090160649815127707145

theorem tailTrace_1332612 : CollatzResearch.WordTrace tailWord_1332612 prefixEnd_1332612 228090160649815127707145 := by
  unfold tailWord_1332612
  simp only [CollatzResearch.WordTrace]
  refine ⟨24302176324090895427592045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32402901765454527236789393 24302176324090895427592045)
  ·
    refine ⟨9113316121534085785347017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24302176324090895427592045 9113316121534085785347017)
    ·
      refine ⟨6834987091150564339010263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9113316121534085785347017 6834987091150564339010263)
      ·
        refine ⟨10252480636725846508515395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6834987091150564339010263 10252480636725846508515395)
        ·
          refine ⟨15378720955088769762773093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10252480636725846508515395 15378720955088769762773093)
          ·
            refine ⟨2883510179079144330519955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15378720955088769762773093 2883510179079144330519955)
            ·
              refine ⟨4325265268618716495779933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2883510179079144330519955 4325265268618716495779933)
              ·
                refine ⟨1621974475732018685917475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4325265268618716495779933 1621974475732018685917475)
                ·
                  refine ⟨2432961713598028028876213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1621974475732018685917475 2432961713598028028876213)
                  ·
                    refine ⟨228090160649815127707145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2432961713598028028876213 228090160649815127707145)
                    ·
                      rfl

theorem cell23_1332612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_1332612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332612 prefixEnd_1332612 := by exact prefixLift 1332612
  have htrace : WordTrace (prefixWord ++ tailWord_1332612) baseStart_1332612 baseEnd_1332612 := by
    simpa [prefixWord, tailWord_1332612, baseEnd_1332612] using wordTrace_append hprefix tailTrace_1332612
  have hstable : (prefixWord ++ tailWord_1332612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332612).length < 2 ^ (prefixWord ++ tailWord_1332612).sum := by decide
  have hdescent : baseEnd_1332612 < baseStart_1332612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332625 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 4, 4]
def baseStart_1332625 : Nat := 118140960795 + 1332625 * 2 ^ 59
def prefixEnd_1332625 : Nat := 4983230072969 + 3 ^ 40 * 1332625 * 2
def baseEnd_1332625 : Nat := 228092385732651277419625

theorem tailTrace_1332625 : CollatzResearch.WordTrace tailWord_1332625 prefixEnd_1332625 228092385732651277419625 := by
  unfold tailWord_1332625
  simp only [CollatzResearch.WordTrace]
  refine ⟨48604826797134694075407329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32403217864756462716938219 48604826797134694075407329)
  ·
    refine ⟨36453620097851020556555497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48604826797134694075407329 36453620097851020556555497)
    ·
      refine ⟨27340215073388265417416623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36453620097851020556555497 27340215073388265417416623)
      ·
        refine ⟨41010322610082398126124935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27340215073388265417416623 41010322610082398126124935)
        ·
          refine ⟨61515483915123597189187403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41010322610082398126124935 61515483915123597189187403)
          ·
            refine ⟨92273225872685395783781105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61515483915123597189187403 92273225872685395783781105)
            ·
              refine ⟨69204919404514046837835829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92273225872685395783781105 69204919404514046837835829)
              ·
                refine ⟨6487961194173191891047109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69204919404514046837835829 6487961194173191891047109)
                ·
                  refine ⟨1216492723907473479571333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6487961194173191891047109 1216492723907473479571333)
                  ·
                    refine ⟨228092385732651277419625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1216492723907473479571333 228092385732651277419625)
                    ·
                      rfl

theorem cell23_1332625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_1332625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332625 prefixEnd_1332625 := by exact prefixLift 1332625
  have htrace : WordTrace (prefixWord ++ tailWord_1332625) baseStart_1332625 baseEnd_1332625 := by
    simpa [prefixWord, tailWord_1332625, baseEnd_1332625] using wordTrace_append hprefix tailTrace_1332625
  have hstable : (prefixWord ++ tailWord_1332625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332625).length < 2 ^ (prefixWord ++ tailWord_1332625).sum := by decide
  have hdescent : baseEnd_1332625 < baseStart_1332625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332642 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_1332642 : Nat := 118140960795 + 1332642 * 2 ^ 59
def prefixEnd_1332642 : Nat := 4983230072969 + 3 ^ 40 * 1332642 * 2
def baseEnd_1332642 : Nat := 228095295456360088582099

theorem tailTrace_1332642 : CollatzResearch.WordTrace tailWord_1332642 prefixEnd_1332642 228095295456360088582099 := by
  unfold tailWord_1332642
  simp only [CollatzResearch.WordTrace]
  refine ⟨12151361709518276494694045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32403631225382070652517453 12151361709518276494694045)
  ·
    refine ⟨4556760641069353685510267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12151361709518276494694045 4556760641069353685510267)
    ·
      refine ⟨6835140961604030528265401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4556760641069353685510267 6835140961604030528265401)
      ·
        refine ⟨5126355721203022896199051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6835140961604030528265401 5126355721203022896199051)
        ·
          refine ⟨7689533581804534344298577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5126355721203022896199051 7689533581804534344298577)
          ·
            refine ⟨5767150186353400758223933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7689533581804534344298577 5767150186353400758223933)
            ·
              refine ⟨2162681319882525284333975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5767150186353400758223933 2162681319882525284333975)
              ·
                refine ⟨3244021979823787926500963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2162681319882525284333975 3244021979823787926500963)
                ·
                  refine ⟨4866032969735681889751445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3244021979823787926500963 4866032969735681889751445)
                  ·
                    refine ⟨228095295456360088582099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4866032969735681889751445 228095295456360088582099)
                    ·
                      rfl

theorem cell23_1332642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_1332642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332642 prefixEnd_1332642 := by exact prefixLift 1332642
  have htrace : WordTrace (prefixWord ++ tailWord_1332642) baseStart_1332642 baseEnd_1332642 := by
    simpa [prefixWord, tailWord_1332642, baseEnd_1332642] using wordTrace_append hprefix tailTrace_1332642
  have hstable : (prefixWord ++ tailWord_1332642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332642).length < 2 ^ (prefixWord ++ tailWord_1332642).sum := by decide
  have hdescent : baseEnd_1332642 < baseStart_1332642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332645 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 1, 2, 4]
def baseStart_1332645 : Nat := 118140960795 + 1332645 * 2 ^ 59
def prefixEnd_1332645 : Nat := 4983230072969 + 3 ^ 40 * 1332645 * 2
def baseEnd_1332645 : Nat := 684287426811043754008783

theorem tailTrace_1332645 : CollatzResearch.WordTrace tailWord_1332645 prefixEnd_1332645 684287426811043754008783 := by
  unfold tailWord_1332645
  simp only [CollatzResearch.WordTrace]
  refine ⟨48605556257062237491135389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32403704171374824994090259 48605556257062237491135389)
  ·
    refine ⟨18227083596398339059175771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48605556257062237491135389 18227083596398339059175771)
    ·
      refine ⟨27340625394597508588763657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18227083596398339059175771 27340625394597508588763657)
      ·
        refine ⟨20505469045948131441572743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27340625394597508588763657 20505469045948131441572743)
        ·
          refine ⟨30758203568922197162359115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20505469045948131441572743 30758203568922197162359115)
          ·
            refine ⟨46137305353383295743538673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30758203568922197162359115 46137305353383295743538673)
            ·
              refine ⟨34602979015037471807654005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46137305353383295743538673 34602979015037471807654005)
              ·
                refine ⟨3244029282659762981967563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34602979015037471807654005 3244029282659762981967563)
                ·
                  refine ⟨4866043923989644472951345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3244029282659762981967563 4866043923989644472951345)
                  ·
                    refine ⟨3649532942992233354713509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4866043923989644472951345 3649532942992233354713509)
                    ·
                      refine ⟨684287426811043754008783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3649532942992233354713509 684287426811043754008783)
                      ·
                        rfl

theorem cell23_1332645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_1332645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332645 prefixEnd_1332645 := by exact prefixLift 1332645
  have htrace : WordTrace (prefixWord ++ tailWord_1332645) baseStart_1332645 baseEnd_1332645 := by
    simpa [prefixWord, tailWord_1332645, baseEnd_1332645] using wordTrace_append hprefix tailTrace_1332645
  have hstable : (prefixWord ++ tailWord_1332645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332645).length < 2 ^ (prefixWord ++ tailWord_1332645).sum := by decide
  have hdescent : baseEnd_1332645 < baseStart_1332645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332652 : List Nat := [2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 3]
def baseStart_1332652 : Nat := 118140960795 + 1332652 * 2 ^ 59
def prefixEnd_1332652 : Nat := 4983230072969 + 3 ^ 40 * 1332652 * 2
def baseEnd_1332652 : Nat := 684291021175625226621251

theorem tailTrace_1332652 : CollatzResearch.WordTrace tailWord_1332652 prefixEnd_1332652 684291021175625226621251 := by
  unfold tailWord_1332652
  simp only [CollatzResearch.WordTrace]
  refine ⟨24302905784018438843320105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32403874378691251791093473 24302905784018438843320105)
  ·
    refine ⟨18227179338013829132490079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24302905784018438843320105 18227179338013829132490079)
    ·
      refine ⟨27340769007020743698735119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18227179338013829132490079 27340769007020743698735119)
      ·
        refine ⟨41011153510531115548102679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27340769007020743698735119 41011153510531115548102679)
        ·
          refine ⟨61516730265796673322154019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41011153510531115548102679 61516730265796673322154019)
          ·
            refine ⟨92275095398695009983231029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61516730265796673322154019 92275095398695009983231029)
            ·
              refine ⟨8650790193627657185927909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92275095398695009983231029 8650790193627657185927909)
              ·
                refine ⟨1622023161305185722361483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8650790193627657185927909 1622023161305185722361483)
                ·
                  refine ⟨2433034741957778583542225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622023161305185722361483 2433034741957778583542225)
                  ·
                    refine ⟨1824776056468333937656669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2433034741957778583542225 1824776056468333937656669)
                    ·
                      refine ⟨684291021175625226621251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1824776056468333937656669 684291021175625226621251)
                      ·
                        rfl

theorem cell23_1332652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_1332652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332652 prefixEnd_1332652 := by exact prefixLift 1332652
  have htrace : WordTrace (prefixWord ++ tailWord_1332652) baseStart_1332652 baseEnd_1332652 := by
    simpa [prefixWord, tailWord_1332652, baseEnd_1332652] using wordTrace_append hprefix tailTrace_1332652
  have hstable : (prefixWord ++ tailWord_1332652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332652).length < 2 ^ (prefixWord ++ tailWord_1332652).sum := by decide
  have hdescent : baseEnd_1332652 < baseStart_1332652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332734 : List Nat := [4, 2, 2, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_1332734 : Nat := 118140960795 + 1332734 * 2 ^ 59
def prefixEnd_1332734 : Nat := 4983230072969 + 3 ^ 40 * 1332734 * 2
def baseEnd_1332734 : Nat := 684333126589293905795875

theorem tailTrace_1332734 : CollatzResearch.WordTrace tailWord_1332734 prefixEnd_1332734 684333126589293905795875 := by
  unfold tailWord_1332734
  simp only [CollatzResearch.WordTrace]
  refine ⟨6076100294217475711390657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32405868235826537127416837 6076100294217475711390657)
  ·
    refine ⟨4557075220663106783542993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6076100294217475711390657 4557075220663106783542993)
    ·
      refine ⟨3417806415497330087657245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4557075220663106783542993 3417806415497330087657245)
      ·
        refine ⟨1281677405811498782871467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3417806415497330087657245 1281677405811498782871467)
        ·
          refine ⟨1922516108717248174307201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1281677405811498782871467 1922516108717248174307201)
          ·
            refine ⟨1441887081537936130730401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1922516108717248174307201 1441887081537936130730401)
            ·
              refine ⟨1081415311153452098047801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1441887081537936130730401 1081415311153452098047801)
              ·
                refine ⟨811061483365089073535851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081415311153452098047801 811061483365089073535851)
                ·
                  refine ⟨1216592225047633610303777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 811061483365089073535851 1216592225047633610303777)
                  ·
                    refine ⟨912444168785725207727833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1216592225047633610303777 912444168785725207727833)
                    ·
                      refine ⟨684333126589293905795875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 912444168785725207727833 684333126589293905795875)
                      ·
                        rfl

theorem cell23_1332734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_1332734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332734 prefixEnd_1332734 := by exact prefixLift 1332734
  have htrace : WordTrace (prefixWord ++ tailWord_1332734) baseStart_1332734 baseEnd_1332734 := by
    simpa [prefixWord, tailWord_1332734, baseEnd_1332734] using wordTrace_append hprefix tailTrace_1332734
  have hstable : (prefixWord ++ tailWord_1332734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332734).length < 2 ^ (prefixWord ++ tailWord_1332734).sum := by decide
  have hdescent : baseEnd_1332734 < baseStart_1332734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332745 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 7]
def baseStart_1332745 : Nat := 118140960795 + 1332745 * 2 ^ 59
def prefixEnd_1332745 : Nat := 4983230072969 + 3 ^ 40 * 1332745 * 2
def baseEnd_1332745 : Nat := 76037641652943706973147

theorem tailTrace_1332745 : CollatzResearch.WordTrace tailWord_1332745 prefixEnd_1332745 76037641652943706973147 := by
  unfold tailWord_1332745
  simp only [CollatzResearch.WordTrace]
  refine ⟨48609203556699954569775689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32406135704466636379850459 48609203556699954569775689)
  ·
    refine ⟨36456902667524965927331767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48609203556699954569775689 36456902667524965927331767)
    ·
      refine ⟨54685354001287448890997651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36456902667524965927331767 54685354001287448890997651)
      ·
        refine ⟨82028031001931173336496477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54685354001287448890997651 82028031001931173336496477)
        ·
          refine ⟨30760511625724190001186179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82028031001931173336496477 30760511625724190001186179)
          ·
            refine ⟨46140767438586285001779269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30760511625724190001186179 46140767438586285001779269)
            ·
              refine ⟨8651393894734928437833613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46140767438586285001779269 8651393894734928437833613)
              ·
                refine ⟨3244272710525598164187605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8651393894734928437833613 3244272710525598164187605)
                ·
                  refine ⟨76037641652943706973147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3244272710525598164187605 76037641652943706973147)
                  ·
                    rfl

theorem cell23_1332745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 7].length) (baseStart_1332745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332745 prefixEnd_1332745 := by exact prefixLift 1332745
  have htrace : WordTrace (prefixWord ++ tailWord_1332745) baseStart_1332745 baseEnd_1332745 := by
    simpa [prefixWord, tailWord_1332745, baseEnd_1332745] using wordTrace_append hprefix tailTrace_1332745
  have hstable : (prefixWord ++ tailWord_1332745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332745).length < 2 ^ (prefixWord ++ tailWord_1332745).sum := by decide
  have hdescent : baseEnd_1332745 < baseStart_1332745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332812 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 1, 3, 4]
def baseStart_1332812 : Nat := 118140960795 + 1332812 * 2 ^ 59
def prefixEnd_1332812 : Nat := 4983230072969 + 3 ^ 40 * 1332812 * 2
def baseEnd_1332812 : Nat := 684373178080344600620515

theorem tailTrace_1332812 : CollatzResearch.WordTrace tailWord_1332812 prefixEnd_1332812 684373178080344600620515 := by
  unfold tailWord_1332812
  simp only [CollatzResearch.WordTrace]
  refine ⟨24305823623728612506232345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32407764831638150008309793 24305823623728612506232345)
  ·
    refine ⟨18229367717796459379674259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24305823623728612506232345 18229367717796459379674259)
    ·
      refine ⟨27344051576694689069511389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18229367717796459379674259 27344051576694689069511389)
      ·
        refine ⟨10254019341260508401066771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27344051576694689069511389 10254019341260508401066771)
        ·
          refine ⟨15381029011890762601600157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10254019341260508401066771 15381029011890762601600157)
          ·
            refine ⟨5767885879459035975600059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15381029011890762601600157 5767885879459035975600059)
            ·
              refine ⟨8651828819188553963400089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5767885879459035975600059 8651828819188553963400089)
              ·
                refine ⟨6488871614391415472550067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8651828819188553963400089 6488871614391415472550067)
                ·
                  refine ⟨9733307421587123208825101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6488871614391415472550067 9733307421587123208825101)
                  ·
                    refine ⟨3649990283095171203309413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9733307421587123208825101 3649990283095171203309413)
                    ·
                      refine ⟨684373178080344600620515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3649990283095171203309413 684373178080344600620515)
                      ·
                        rfl

theorem cell23_1332812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_1332812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332812 prefixEnd_1332812 := by exact prefixLift 1332812
  have htrace : WordTrace (prefixWord ++ tailWord_1332812) baseStart_1332812 baseEnd_1332812 := by
    simpa [prefixWord, tailWord_1332812, baseEnd_1332812] using wordTrace_append hprefix tailTrace_1332812
  have hstable : (prefixWord ++ tailWord_1332812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332812).length < 2 ^ (prefixWord ++ tailWord_1332812).sum := by decide
  have hdescent : baseEnd_1332812 < baseStart_1332812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332846 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_1332846 : Nat := 118140960795 + 1332846 * 2 ^ 59
def prefixEnd_1332846 : Nat := 4983230072969 + 3 ^ 40 * 1332846 * 2
def baseEnd_1332846 : Nat := 684390636422597467595359

theorem tailTrace_1332846 : CollatzResearch.WordTrace tailWord_1332846 prefixEnd_1332846 684390636422597467595359 := by
  unfold tailWord_1332846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6076610916166756102400299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32408591552889365879468261 6076610916166756102400299)
  ·
    refine ⟨9114916374250134153600449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6076610916166756102400299 9114916374250134153600449)
    ·
      refine ⟨6836187280687600615200337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9114916374250134153600449 6836187280687600615200337)
      ·
        refine ⟨5127140460515700461400253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6836187280687600615200337 5127140460515700461400253)
        ·
          refine ⟨1922677672693387673025095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5127140460515700461400253 1922677672693387673025095)
          ·
            refine ⟨2884016509040081509537643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922677672693387673025095 2884016509040081509537643)
            ·
              refine ⟨4326024763560122264306465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2884016509040081509537643 4326024763560122264306465)
              ·
                refine ⟨3244518572670091698229849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4326024763560122264306465 3244518572670091698229849)
                ·
                  refine ⟨2433388929502568773672387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3244518572670091698229849 2433388929502568773672387)
                  ·
                    refine ⟨3650083394253853160508581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2433388929502568773672387 3650083394253853160508581)
                    ·
                      refine ⟨684390636422597467595359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3650083394253853160508581 684390636422597467595359)
                      ·
                        rfl

theorem cell23_1332846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_1332846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332846 prefixEnd_1332846 := by exact prefixLift 1332846
  have htrace : WordTrace (prefixWord ++ tailWord_1332846) baseStart_1332846 baseEnd_1332846 := by
    simpa [prefixWord, tailWord_1332846, baseEnd_1332846] using wordTrace_append hprefix tailTrace_1332846
  have hstable : (prefixWord ++ tailWord_1332846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332846).length < 2 ^ (prefixWord ++ tailWord_1332846).sum := by decide
  have hdescent : baseEnd_1332846 < baseStart_1332846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332919 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 4]
def baseStart_1332919 : Nat := 118140960795 + 1332919 * 2 ^ 59
def prefixEnd_1332919 : Nat := 4983230072969 + 3 ^ 40 * 1332919 * 2
def baseEnd_1332919 : Nat := 684428120510375681982523

theorem tailTrace_1332919 : CollatzResearch.WordTrace tailWord_1332919 prefixEnd_1332919 684428120510375681982523 := by
  unfold tailWord_1332919
  simp only [CollatzResearch.WordTrace]
  refine ⟨48615549858069582286609811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32410366572046388191073207 48615549858069582286609811)
  ·
    refine ⟨72923324787104373429914717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48615549858069582286609811 72923324787104373429914717)
    ·
      refine ⟨27346246795164140036218019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72923324787104373429914717 27346246795164140036218019)
      ·
        refine ⟨41019370192746210054327029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27346246795164140036218019 41019370192746210054327029)
        ·
          refine ⟨3845565955569957192593159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41019370192746210054327029 3845565955569957192593159)
          ·
            refine ⟨5768348933354935788889739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3845565955569957192593159 5768348933354935788889739)
            ·
              refine ⟨8652523400032403683334609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5768348933354935788889739 8652523400032403683334609)
              ·
                refine ⟨6489392550024302762500957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8652523400032403683334609 6489392550024302762500957)
                ·
                  refine ⟨2433522206259113535937859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6489392550024302762500957 2433522206259113535937859)
                  ·
                    refine ⟨3650283309388670303906789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2433522206259113535937859 3650283309388670303906789)
                    ·
                      refine ⟨684428120510375681982523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3650283309388670303906789 684428120510375681982523)
                      ·
                        rfl

theorem cell23_1332919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_1332919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332919 prefixEnd_1332919 := by exact prefixLift 1332919
  have htrace : WordTrace (prefixWord ++ tailWord_1332919) baseStart_1332919 baseEnd_1332919 := by
    simpa [prefixWord, tailWord_1332919, baseEnd_1332919] using wordTrace_append hprefix tailTrace_1332919
  have hstable : (prefixWord ++ tailWord_1332919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332919).length < 2 ^ (prefixWord ++ tailWord_1332919).sum := by decide
  have hdescent : baseEnd_1332919 < baseStart_1332919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332940 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 2, 3, 2]
def baseStart_1332940 : Nat := 118140960795 + 1332940 * 2 ^ 59
def prefixEnd_1332940 : Nat := 4983230072969 + 3 ^ 40 * 1332940 * 2
def baseEnd_1332940 : Nat := 684438903604120099819927

theorem tailTrace_1332940 : CollatzResearch.WordTrace tailWord_1332940 prefixEnd_1332940 684438903604120099819927 := by
  unfold tailWord_1332940
  simp only [CollatzResearch.WordTrace]
  refine ⟨24308157895496751436562137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32410877193995668582082849 24308157895496751436562137)
  ·
    refine ⟨18231118421622563577421603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24308157895496751436562137 18231118421622563577421603)
    ·
      refine ⟨27346677632433845366132405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18231118421622563577421603 27346677632433845366132405)
      ·
        refine ⟨2563751028040673003074913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27346677632433845366132405 2563751028040673003074913)
        ·
          refine ⟨1922813271030504752306185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2563751028040673003074913 1922813271030504752306185)
          ·
            refine ⟨1442109953272878564229639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1922813271030504752306185 1442109953272878564229639)
            ·
              refine ⟨2163164929909317846344459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442109953272878564229639 2163164929909317846344459)
              ·
                refine ⟨3244747394863976769516689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2163164929909317846344459 3244747394863976769516689)
                ·
                  refine ⟨2433560546147982577137517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3244747394863976769516689 2433560546147982577137517)
                  ·
                    refine ⟨912585204805493466426569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2433560546147982577137517 912585204805493466426569)
                    ·
                      refine ⟨684438903604120099819927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 912585204805493466426569 684438903604120099819927)
                      ·
                        rfl

theorem cell23_1332940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_1332940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332940 prefixEnd_1332940 := by exact prefixLift 1332940
  have htrace : WordTrace (prefixWord ++ tailWord_1332940) baseStart_1332940 baseEnd_1332940 := by
    simpa [prefixWord, tailWord_1332940, baseEnd_1332940] using wordTrace_append hprefix tailTrace_1332940
  have hstable : (prefixWord ++ tailWord_1332940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332940).length < 2 ^ (prefixWord ++ tailWord_1332940).sum := by decide
  have hdescent : baseEnd_1332940 < baseStart_1332940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332950 : List Nat := [5, 2, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_1332950 : Nat := 118140960795 + 1332950 * 2 ^ 59
def prefixEnd_1332950 : Nat := 4983230072969 + 3 ^ 40 * 1332950 * 2
def baseEnd_1332950 : Nat := 228148012803555020231627

theorem tailTrace_1332950 : CollatzResearch.WordTrace tailWord_1332950 prefixEnd_1332950 228148012803555020231627 := by
  unfold tailWord_1332950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3038542532559829661311769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32411120347304849720658869 3038542532559829661311769)
  ·
    refine ⟨2278906899419872245983827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3038542532559829661311769 2278906899419872245983827)
    ·
      refine ⟨3418360349129808368975741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2278906899419872245983827 3418360349129808368975741)
      ·
        refine ⟨1281885130923678138365903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3418360349129808368975741 1281885130923678138365903)
        ·
          refine ⟨1922827696385517207548855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1281885130923678138365903 1922827696385517207548855)
          ·
            refine ⟨2884241544578275811323283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922827696385517207548855 2884241544578275811323283)
            ·
              refine ⟨4326362316867413716984925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2884241544578275811323283 4326362316867413716984925)
              ·
                refine ⟨1622385868825280143869347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4326362316867413716984925 1622385868825280143869347)
                ·
                  refine ⟨2433578803237920215804021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622385868825280143869347 2433578803237920215804021)
                  ·
                    refine ⟨228148012803555020231627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2433578803237920215804021 228148012803555020231627)
                    ·
                      rfl

theorem cell23_1332950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_1332950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332950 prefixEnd_1332950 := by exact prefixLift 1332950
  have htrace : WordTrace (prefixWord ++ tailWord_1332950) baseStart_1332950 baseEnd_1332950 := by
    simpa [prefixWord, tailWord_1332950, baseEnd_1332950] using wordTrace_append hprefix tailTrace_1332950
  have hstable : (prefixWord ++ tailWord_1332950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332950).length < 2 ^ (prefixWord ++ tailWord_1332950).sum := by decide
  have hdescent : baseEnd_1332950 < baseStart_1332950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332953 : List Nat := [1, 2, 1, 2, 3, 5, 2, 1, 1, 1, 4]
def baseStart_1332953 : Nat := 118140960795 + 1332953 * 2 ^ 59
def prefixEnd_1332953 : Nat := 4983230072969 + 3 ^ 40 * 1332953 * 2
def baseEnd_1332953 : Nat := 684445578852628548957367

theorem tailTrace_1332953 : CollatzResearch.WordTrace tailWord_1332953 prefixEnd_1332953 684445578852628548957367 := by
  unfold tailWord_1332953
  simp only [CollatzResearch.WordTrace]
  refine ⟨48616789939946406093347513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32411193293297604062231675 48616789939946406093347513)
  ·
    refine ⟨36462592454959804570010635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48616789939946406093347513 36462592454959804570010635)
    ·
      refine ⟨54693888682439706855015953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36462592454959804570010635 54693888682439706855015953)
      ·
        refine ⟨41020416511829780141261965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54693888682439706855015953 41020416511829780141261965)
        ·
          refine ⟨15382656191936167552973237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41020416511829780141261965 15382656191936167552973237)
          ·
            refine ⟨1442124017994015708091241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15382656191936167552973237 1442124017994015708091241)
            ·
              refine ⟨1081593013495511781068431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442124017994015708091241 1081593013495511781068431)
              ·
                refine ⟨1622389520243267671602647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1081593013495511781068431 1622389520243267671602647)
                ·
                  refine ⟨2433584280364901507403971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622389520243267671602647 2433584280364901507403971)
                  ·
                    refine ⟨3650376420547352261105957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2433584280364901507403971 3650376420547352261105957)
                    ·
                      refine ⟨684445578852628548957367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3650376420547352261105957 684445578852628548957367)
                      ·
                        rfl

theorem cell23_1332953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 1, 1, 4].length) (baseStart_1332953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332953 prefixEnd_1332953 := by exact prefixLift 1332953
  have htrace : WordTrace (prefixWord ++ tailWord_1332953) baseStart_1332953 baseEnd_1332953 := by
    simpa [prefixWord, tailWord_1332953, baseEnd_1332953] using wordTrace_append hprefix tailTrace_1332953
  have hstable : (prefixWord ++ tailWord_1332953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332953).length < 2 ^ (prefixWord ++ tailWord_1332953).sum := by decide
  have hdescent : baseEnd_1332953 < baseStart_1332953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332970 : List Nat := [3, 1, 3, 1, 1, 1, 4, 4, 1, 2, 2]
def baseStart_1332970 : Nat := 118140960795 + 1332970 * 2 ^ 59
def prefixEnd_1332970 : Nat := 4983230072969 + 3 ^ 40 * 1332970 * 2
def baseEnd_1332970 : Nat := 684454308023754982444789

theorem tailTrace_1332970 : CollatzResearch.WordTrace tailWord_1332970 prefixEnd_1332970 684454308023754982444789 := by
  unfold tailWord_1332970
  simp only [CollatzResearch.WordTrace]
  refine ⟨12154352495221204499179091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32411606653923211997810909 12154352495221204499179091)
  ·
    refine ⟨18231528742831806748768637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12154352495221204499179091 18231528742831806748768637)
    ·
      refine ⟨6836823278561927530788239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18231528742831806748768637 6836823278561927530788239)
      ·
        refine ⟨10255234917842891296182359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6836823278561927530788239 10255234917842891296182359)
        ·
          refine ⟨15382852376764336944273539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10255234917842891296182359 15382852376764336944273539)
          ·
            refine ⟨23074278565146505416410309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15382852376764336944273539 23074278565146505416410309)
            ·
              refine ⟨4326427230964969765576933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23074278565146505416410309 4326427230964969765576933)
              ·
                refine ⟨811205105805931831045675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4326427230964969765576933 811205105805931831045675)
                ·
                  refine ⟨1216807658708897746568513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 811205105805931831045675 1216807658708897746568513)
                  ·
                    refine ⟨912605744031673309926385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1216807658708897746568513 912605744031673309926385)
                    ·
                      refine ⟨684454308023754982444789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 912605744031673309926385 684454308023754982444789)
                      ·
                        rfl

theorem cell23_1332970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_1332970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332970 prefixEnd_1332970 := by exact prefixLift 1332970
  have htrace : WordTrace (prefixWord ++ tailWord_1332970) baseStart_1332970 baseEnd_1332970 := by
    simpa [prefixWord, tailWord_1332970, baseEnd_1332970] using wordTrace_append hprefix tailTrace_1332970
  have hstable : (prefixWord ++ tailWord_1332970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332970).length < 2 ^ (prefixWord ++ tailWord_1332970).sum := by decide
  have hdescent : baseEnd_1332970 < baseStart_1332970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332972 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 1, 9]
def baseStart_1332972 : Nat := 118140960795 + 1332972 * 2 ^ 59
def prefixEnd_1332972 : Nat := 4983230072969 + 3 ^ 40 * 1332972 * 2
def baseEnd_1332972 : Nat := 228151778328354658206593

theorem tailTrace_1332972 : CollatzResearch.WordTrace tailWord_1332972 prefixEnd_1332972 228151778328354658206593 := by
  unfold tailWord_1332972
  simp only [CollatzResearch.WordTrace]
  refine ⟨24308741463438786169144585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32411655284585048225526113 24308741463438786169144585)
  ·
    refine ⟨18231556097579089626858439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24308741463438786169144585 18231556097579089626858439)
    ·
      refine ⟨27347334146368634440287659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18231556097579089626858439 27347334146368634440287659)
      ·
        refine ⟨41021001219552951660431489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27347334146368634440287659 41021001219552951660431489)
        ·
          refine ⟨30765750914664713745323617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41021001219552951660431489 30765750914664713745323617)
          ·
            refine ⟨23074313185998535308992713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30765750914664713745323617 23074313185998535308992713)
            ·
              refine ⟨17305734889498901481744535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23074313185998535308992713 17305734889498901481744535)
              ·
                refine ⟨25958602334248352222616803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17305734889498901481744535 25958602334248352222616803)
                ·
                  refine ⟨38937903501372528333925205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25958602334248352222616803 38937903501372528333925205)
                  ·
                    refine ⟨228151778328354658206593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 38937903501372528333925205 228151778328354658206593)
                    ·
                      rfl

theorem cell23_1332972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_1332972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332972 prefixEnd_1332972 := by exact prefixLift 1332972
  have htrace : WordTrace (prefixWord ++ tailWord_1332972) baseStart_1332972 baseEnd_1332972 := by
    simpa [prefixWord, tailWord_1332972, baseEnd_1332972] using wordTrace_append hprefix tailTrace_1332972
  have hstable : (prefixWord ++ tailWord_1332972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332972).length < 2 ^ (prefixWord ++ tailWord_1332972).sum := by decide
  have hdescent : baseEnd_1332972 < baseStart_1332972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332980 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1332980 : Nat := 118140960795 + 1332980 * 2 ^ 59
def prefixEnd_1332980 : Nat := 4983230072969 + 3 ^ 40 * 1332980 * 2
def baseEnd_1332980 : Nat := 228153147610099981106581

theorem tailTrace_1332980 : CollatzResearch.WordTrace tailWord_1332980 prefixEnd_1332980 228153147610099981106581 := by
  unfold tailWord_1332980
  simp only [CollatzResearch.WordTrace]
  refine ⟨24308887355424294852290197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32411849807232393136386929 24308887355424294852290197)
  ·
    refine ⟨1139479094785513821201103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24308887355424294852290197 1139479094785513821201103)
    ·
      refine ⟨1709218642178270731801655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1139479094785513821201103 1709218642178270731801655)
      ·
        refine ⟨2563827963267406097702483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709218642178270731801655 2563827963267406097702483)
        ·
          refine ⟨3845741944901109146553725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2563827963267406097702483 3845741944901109146553725)
          ·
            refine ⟨1442153229337915929957647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3845741944901109146553725 1442153229337915929957647)
            ·
              refine ⟨2163229844006873894936471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442153229337915929957647 2163229844006873894936471)
              ·
                refine ⟨3244844766010310842404707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2163229844006873894936471 3244844766010310842404707)
                ·
                  refine ⟨4867267149015466263607061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3244844766010310842404707 4867267149015466263607061)
                  ·
                    refine ⟨228153147610099981106581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4867267149015466263607061 228153147610099981106581)
                    ·
                      rfl

theorem cell23_1332980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1332980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332980 prefixEnd_1332980 := by exact prefixLift 1332980
  have htrace : WordTrace (prefixWord ++ tailWord_1332980) baseStart_1332980 baseEnd_1332980 := by
    simpa [prefixWord, tailWord_1332980, baseEnd_1332980] using wordTrace_append hprefix tailTrace_1332980
  have hstable : (prefixWord ++ tailWord_1332980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332980).length < 2 ^ (prefixWord ++ tailWord_1332980).sum := by decide
  have hdescent : baseEnd_1332980 < baseStart_1332980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332990 : List Nat := [4, 2, 2, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_1332990 : Nat := 118140960795 + 1332990 * 2 ^ 59
def prefixEnd_1332990 : Nat := 4983230072969 + 3 ^ 40 * 1332990 * 2
def baseEnd_1332990 : Nat := 684464577636844904194697

theorem tailTrace_1332990 : CollatzResearch.WordTrace tailWord_1332990 prefixEnd_1332990 684464577636844904194697 := by
  unfold tailWord_1332990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6077267430101545176555553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32412092960541574274962949 6077267430101545176555553)
  ·
    refine ⟨4557950572576158882416665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6077267430101545176555553 4557950572576158882416665)
    ·
      refine ⟨3418462929432119161812499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4557950572576158882416665 3418462929432119161812499)
      ·
        refine ⟨5127694394148178742718749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3418462929432119161812499 5127694394148178742718749)
        ·
          refine ⟨1922885397805567028519531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5127694394148178742718749 1922885397805567028519531)
          ·
            refine ⟨2884328096708350542779297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922885397805567028519531 2884328096708350542779297)
            ·
              refine ⟨2163246072531262907084473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2884328096708350542779297 2163246072531262907084473)
              ·
                refine ⟨1622434554398447180313355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2163246072531262907084473 1622434554398447180313355)
                ·
                  refine ⟨2433651831597670770470033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622434554398447180313355 2433651831597670770470033)
                  ·
                    refine ⟨1825238873698253077852525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2433651831597670770470033 1825238873698253077852525)
                    ·
                      refine ⟨684464577636844904194697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1825238873698253077852525 684464577636844904194697)
                      ·
                        rfl

theorem cell23_1332990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_1332990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1332990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1332990 prefixEnd_1332990 := by exact prefixLift 1332990
  have htrace : WordTrace (prefixWord ++ tailWord_1332990) baseStart_1332990 baseEnd_1332990 := by
    simpa [prefixWord, tailWord_1332990, baseEnd_1332990] using wordTrace_append hprefix tailTrace_1332990
  have hstable : (prefixWord ++ tailWord_1332990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332990).length < 2 ^ (prefixWord ++ tailWord_1332990).sum := by decide
  have hdescent : baseEnd_1332990 < baseStart_1332990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333013 : List Nat := [1, 3, 2, 1, 2, 3, 2, 3, 1, 3, 2]
def baseStart_1333013 : Nat := 118140960795 + 1333013 * 2 ^ 59
def prefixEnd_1333013 : Nat := 4983230072969 + 3 ^ 40 * 1333013 * 2
def baseEnd_1333013 : Nat := 684476387691898314207091

theorem tailTrace_1333013 : CollatzResearch.WordTrace tailWord_1333013 prefixEnd_1333013 684476387691898314207091 := by
  unfold tailWord_1333013
  simp only [CollatzResearch.WordTrace]
  refine ⟨48618978319729036340531693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32412652213152690893687795 48618978319729036340531693)
  ·
    refine ⟨18232116869898388627699385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48618978319729036340531693 18232116869898388627699385)
    ·
      refine ⟨13674087652423791470774539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18232116869898388627699385 13674087652423791470774539)
      ·
        refine ⟨20511131478635687206161809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13674087652423791470774539 20511131478635687206161809)
        ·
          refine ⟨15383348608976765404621357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20511131478635687206161809 15383348608976765404621357)
          ·
            refine ⟨5768755728366287026733009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15383348608976765404621357 5768755728366287026733009)
            ·
              refine ⟨4326566796274715270049757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5768755728366287026733009 4326566796274715270049757)
              ·
                refine ⟨1622462548603018226268659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4326566796274715270049757 1622462548603018226268659)
                ·
                  refine ⟨2433693822904527339402989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622462548603018226268659 2433693822904527339402989)
                  ·
                    refine ⟨912635183589197752276121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2433693822904527339402989 912635183589197752276121)
                    ·
                      refine ⟨684476387691898314207091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 912635183589197752276121 684476387691898314207091)
                      ·
                        rfl

theorem cell23_1333013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_1333013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333013 prefixEnd_1333013 := by exact prefixLift 1333013
  have htrace : WordTrace (prefixWord ++ tailWord_1333013) baseStart_1333013 baseEnd_1333013 := by
    simpa [prefixWord, tailWord_1333013, baseEnd_1333013] using wordTrace_append hprefix tailTrace_1333013
  have hstable : (prefixWord ++ tailWord_1333013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333013).length < 2 ^ (prefixWord ++ tailWord_1333013).sum := by decide
  have hdescent : baseEnd_1333013 < baseStart_1333013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333066 : List Nat := [3, 1, 2, 1, 1, 1, 4, 5, 5]
def baseStart_1333066 : Nat := 118140960795 + 1333066 * 2 ^ 59
def prefixEnd_1333066 : Nat := 4983230072969 + 3 ^ 40 * 1333066 * 2
def baseEnd_1333066 : Nat := 76055955796287400760483

theorem tailTrace_1333066 : CollatzResearch.WordTrace tailWord_1333066 prefixEnd_1333066 76055955796287400760483 := by
  unfold tailWord_1333066
  simp only [CollatzResearch.WordTrace]
  refine ⟨12155227847134256598052763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32413940925691350928140701 12155227847134256598052763)
  ·
    refine ⟨18232841770701384897079145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12155227847134256598052763 18232841770701384897079145)
    ·
      refine ⟨13674631328026038672809359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18232841770701384897079145 13674631328026038672809359)
      ·
        refine ⟨20511946992039058009214039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13674631328026038672809359 20511946992039058009214039)
        ·
          refine ⟨30767920488058587013821059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20511946992039058009214039 30767920488058587013821059)
          ·
            refine ⟨46151880732087880520731589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30767920488058587013821059 46151880732087880520731589)
            ·
              refine ⟨8653477637266477597637173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46151880732087880520731589 8653477637266477597637173)
              ·
                refine ⟨811263528493732274778485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8653477637266477597637173 811263528493732274778485)
                ·
                  refine ⟨76055955796287400760483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 811263528493732274778485 76055955796287400760483)
                  ·
                    rfl

theorem cell23_1333066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 5].length) (baseStart_1333066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333066 prefixEnd_1333066 := by exact prefixLift 1333066
  have htrace : WordTrace (prefixWord ++ tailWord_1333066) baseStart_1333066 baseEnd_1333066 := by
    simpa [prefixWord, tailWord_1333066, baseEnd_1333066] using wordTrace_append hprefix tailTrace_1333066
  have hstable : (prefixWord ++ tailWord_1333066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333066).length < 2 ^ (prefixWord ++ tailWord_1333066).sum := by decide
  have hdescent : baseEnd_1333066 < baseStart_1333066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333089 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_1333089 : Nat := 118140960795 + 1333089 * 2 ^ 59
def prefixEnd_1333089 : Nat := 4983230072969 + 3 ^ 40 * 1333089 * 2
def baseEnd_1333089 : Nat := 684515412221640016856741

theorem tailTrace_1333089 : CollatzResearch.WordTrace tailWord_1333089 prefixEnd_1333089 684515412221640016856741 := by
  unfold tailWord_1333089
  simp only [CollatzResearch.WordTrace]
  refine ⟨48621750267453701320298321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32414500178302467546865547 48621750267453701320298321)
  ·
    refine ⟨36466312700590275990223741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48621750267453701320298321 36466312700590275990223741)
    ·
      refine ⟨13674867262721353496333903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36466312700590275990223741 13674867262721353496333903)
      ·
        refine ⟨20512300894082030244500855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13674867262721353496333903 20512300894082030244500855)
        ·
          refine ⟨30768451341123045366751283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20512300894082030244500855 30768451341123045366751283)
          ·
            refine ⟨46152677011684568050126925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30768451341123045366751283 46152677011684568050126925)
            ·
              refine ⟨17307253879381713018797597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46152677011684568050126925 17307253879381713018797597)
              ·
                refine ⟨6490220204768142382049099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17307253879381713018797597 6490220204768142382049099)
                ·
                  refine ⟨9735330307152213573073649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6490220204768142382049099 9735330307152213573073649)
                  ·
                    refine ⟨7301497730364160179805237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9735330307152213573073649 7301497730364160179805237)
                    ·
                      refine ⟨684515412221640016856741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7301497730364160179805237 684515412221640016856741)
                      ·
                        rfl

theorem cell23_1333089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_1333089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333089 prefixEnd_1333089 := by exact prefixLift 1333089
  have htrace : WordTrace (prefixWord ++ tailWord_1333089) baseStart_1333089 baseEnd_1333089 := by
    simpa [prefixWord, tailWord_1333089, baseEnd_1333089] using wordTrace_append hprefix tailTrace_1333089
  have hstable : (prefixWord ++ tailWord_1333089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333089).length < 2 ^ (prefixWord ++ tailWord_1333089).sum := by decide
  have hdescent : baseEnd_1333089 < baseStart_1333089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333099 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 4]
def baseStart_1333099 : Nat := 118140960795 + 1333099 * 2 ^ 59
def prefixEnd_1333099 : Nat := 4983230072969 + 3 ^ 40 * 1333099 * 2
def baseEnd_1333099 : Nat := 684520547028184977731695

theorem tailTrace_1333099 : CollatzResearch.WordTrace tailWord_1333099 prefixEnd_1333099 684520547028184977731695 := by
  unfold tailWord_1333099
  simp only [CollatzResearch.WordTrace]
  refine ⟨48622114997417473028162351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32414743331611648685441567 48622114997417473028162351)
  ·
    refine ⟨72933172496126209542243527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48622114997417473028162351 72933172496126209542243527)
    ·
      refine ⟨109399758744189314313365291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72933172496126209542243527 109399758744189314313365291)
      ·
        refine ⟨164099638116283971470047937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109399758744189314313365291 164099638116283971470047937)
        ·
          refine ⟨123074728587212978602535953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164099638116283971470047937 123074728587212978602535953)
          ·
            refine ⟨92306046440409733951901965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123074728587212978602535953 92306046440409733951901965)
            ·
              refine ⟨34614767415153650231963237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92306046440409733951901965 34614767415153650231963237)
              ·
                refine ⟨6490268890341309418493107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34614767415153650231963237 6490268890341309418493107)
                ·
                  refine ⟨9735403335511964127739661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6490268890341309418493107 9735403335511964127739661)
                  ·
                    refine ⟨3650776250816986547902373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9735403335511964127739661 3650776250816986547902373)
                    ·
                      refine ⟨684520547028184977731695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3650776250816986547902373 684520547028184977731695)
                      ·
                        rfl

theorem cell23_1333099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 4].length) (baseStart_1333099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333099 prefixEnd_1333099 := by exact prefixLift 1333099
  have htrace : WordTrace (prefixWord ++ tailWord_1333099) baseStart_1333099 baseEnd_1333099 := by
    simpa [prefixWord, tailWord_1333099, baseEnd_1333099] using wordTrace_append hprefix tailTrace_1333099
  have hstable : (prefixWord ++ tailWord_1333099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333099).length < 2 ^ (prefixWord ++ tailWord_1333099).sum := by decide
  have hdescent : baseEnd_1333099 < baseStart_1333099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333129 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 1, 3, 6]
def baseStart_1333129 : Nat := 118140960795 + 1333129 * 2 ^ 59
def prefixEnd_1333129 : Nat := 4983230072969 + 3 ^ 40 * 1333129 * 2
def baseEnd_1333129 : Nat := 684535951447819860356557

theorem tailTrace_1333129 : CollatzResearch.WordTrace tailWord_1333129 prefixEnd_1333129 684535951447819860356557 := by
  unfold tailWord_1333129
  simp only [CollatzResearch.WordTrace]
  refine ⟨48623209187308788151754441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32415472791539192101169627 48623209187308788151754441)
  ·
    refine ⟨36467406890481591113815831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48623209187308788151754441 36467406890481591113815831)
    ·
      refine ⟨54701110335722386670723747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36467406890481591113815831 54701110335722386670723747)
      ·
        refine ⟨82051665503583580006085621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54701110335722386670723747 82051665503583580006085621)
        ·
          refine ⟨7692343640960960625570527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82051665503583580006085621 7692343640960960625570527)
          ·
            refine ⟨11538515461441440938355791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7692343640960960625570527 11538515461441440938355791)
            ·
              refine ⟨17307773192162161407533687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11538515461441440938355791 17307773192162161407533687)
              ·
                refine ⟨25961659788243242111300531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17307773192162161407533687 25961659788243242111300531)
                ·
                  refine ⟨38942489682364863166950797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25961659788243242111300531 38942489682364863166950797)
                  ·
                    refine ⟨14603433630886823687606549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38942489682364863166950797 14603433630886823687606549)
                    ·
                      refine ⟨684535951447819860356557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14603433630886823687606549 684535951447819860356557)
                      ·
                        rfl

theorem cell23_1333129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_1333129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333129 prefixEnd_1333129 := by exact prefixLift 1333129
  have htrace : WordTrace (prefixWord ++ tailWord_1333129) baseStart_1333129 baseEnd_1333129 := by
    simpa [prefixWord, tailWord_1333129, baseEnd_1333129] using wordTrace_append hprefix tailTrace_1333129
  have hstable : (prefixWord ++ tailWord_1333129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333129).length < 2 ^ (prefixWord ++ tailWord_1333129).sum := by decide
  have hdescent : baseEnd_1333129 < baseStart_1333129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333143 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 3, 4]
def baseStart_1333143 : Nat := 118140960795 + 1333143 * 2 ^ 59
def prefixEnd_1333143 : Nat := 4983230072969 + 3 ^ 40 * 1333143 * 2
def baseEnd_1333143 : Nat := 228181046725660935193831

theorem tailTrace_1333143 : CollatzResearch.WordTrace tailWord_1333143 prefixEnd_1333143 228181046725660935193831 := by
  unfold tailWord_1333143
  simp only [CollatzResearch.WordTrace]
  refine ⟨48623719809258068542764083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32415813206172045695176055 48623719809258068542764083)
  ·
    refine ⟨72935579713887102814146125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48623719809258068542764083 72935579713887102814146125)
    ·
      refine ⟨27350842392707663555304797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72935579713887102814146125 27350842392707663555304797)
      ·
        refine ⟨10256565897265373833239299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27350842392707663555304797 10256565897265373833239299)
        ·
          refine ⟨15384848845898060749858949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10256565897265373833239299 15384848845898060749858949)
          ·
            refine ⟨2884659158605886390598553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15384848845898060749858949 2884659158605886390598553)
            ·
              refine ⟨2163494368954414792948915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2884659158605886390598553 2163494368954414792948915)
              ·
                refine ⟨3245241553431622189423373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2163494368954414792948915 3245241553431622189423373)
                ·
                  refine ⟨1216965582536858321033765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3245241553431622189423373 1216965582536858321033765)
                  ·
                    refine ⟨228181046725660935193831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1216965582536858321033765 228181046725660935193831)
                    ·
                      rfl

theorem cell23_1333143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_1333143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333143 prefixEnd_1333143 := by exact prefixLift 1333143
  have htrace : WordTrace (prefixWord ++ tailWord_1333143) baseStart_1333143 baseEnd_1333143 := by
    simpa [prefixWord, tailWord_1333143, baseEnd_1333143] using wordTrace_append hprefix tailTrace_1333143
  have hstable : (prefixWord ++ tailWord_1333143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333143).length < 2 ^ (prefixWord ++ tailWord_1333143).sum := by decide
  have hdescent : baseEnd_1333143 < baseStart_1333143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333179 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 5]
def baseStart_1333179 : Nat := 118140960795 + 1333179 * 2 ^ 59
def prefixEnd_1333179 : Nat := 4983230072969 + 3 ^ 40 * 1333179 * 2
def baseEnd_1333179 : Nat := 684561625480544664731327

theorem tailTrace_1333179 : CollatzResearch.WordTrace tailWord_1333179 prefixEnd_1333179 684561625480544664731327 := by
  unfold tailWord_1333179
  simp only [CollatzResearch.WordTrace]
  refine ⟨48625032837127646691074591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32416688558085097794049727 48625032837127646691074591)
  ·
    refine ⟨72937549255691470036611887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48625032837127646691074591 72937549255691470036611887)
    ·
      refine ⟨109406323883537205054917831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72937549255691470036611887 109406323883537205054917831)
      ·
        refine ⟨164109485825305807582376747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109406323883537205054917831 164109485825305807582376747)
        ·
          refine ⟨246164228737958711373565121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164109485825305807582376747 246164228737958711373565121)
          ·
            refine ⟨184623171553469033530173841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246164228737958711373565121 184623171553469033530173841)
            ·
              refine ⟨138467378665101775147630381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184623171553469033530173841 138467378665101775147630381)
              ·
                refine ⟨51925266999413165680361393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138467378665101775147630381 51925266999413165680361393)
                ·
                  refine ⟨38943950249559874260271045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51925266999413165680361393 38943950249559874260271045)
                  ·
                    refine ⟨7301990671792476423800821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38943950249559874260271045 7301990671792476423800821)
                    ·
                      refine ⟨684561625480544664731327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7301990671792476423800821 684561625480544664731327)
                      ·
                        rfl

theorem cell23_1333179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 5].length) (baseStart_1333179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333179 prefixEnd_1333179 := by exact prefixLift 1333179
  have htrace : WordTrace (prefixWord ++ tailWord_1333179) baseStart_1333179 baseEnd_1333179 := by
    simpa [prefixWord, tailWord_1333179, baseEnd_1333179] using wordTrace_append hprefix tailTrace_1333179
  have hstable : (prefixWord ++ tailWord_1333179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333179).length < 2 ^ (prefixWord ++ tailWord_1333179).sum := by decide
  have hdescent : baseEnd_1333179 < baseStart_1333179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333193 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 2, 3, 2]
def baseStart_1333193 : Nat := 118140960795 + 1333193 * 2 ^ 59
def prefixEnd_1333193 : Nat := 4983230072969 + 3 ^ 40 * 1333193 * 2
def baseEnd_1333193 : Nat := 684568814209707609956263

theorem tailTrace_1333193 : CollatzResearch.WordTrace tailWord_1333193 prefixEnd_1333193 684568814209707609956263 := by
  unfold tailWord_1333193
  simp only [CollatzResearch.WordTrace]
  refine ⟨48625543459076927082084233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32417028972717951388056155 48625543459076927082084233)
  ·
    refine ⟨36469157594307695311563175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48625543459076927082084233 36469157594307695311563175)
    ·
      refine ⟨54703736391461542967344763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36469157594307695311563175 54703736391461542967344763)
      ·
        refine ⟨82055604587192314451017145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54703736391461542967344763 82055604587192314451017145)
        ·
          refine ⟨61541703440394235838262859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82055604587192314451017145 61541703440394235838262859)
          ·
            refine ⟨92312555160591353757394289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61541703440394235838262859 92312555160591353757394289)
            ·
              refine ⟨69234416370443515318045717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92312555160591353757394289 69234416370443515318045717)
              ·
                refine ⟨3245363267364539780533393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69234416370443515318045717 3245363267364539780533393)
                ·
                  refine ⟨2434022450523404835400045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3245363267364539780533393 2434022450523404835400045)
                  ·
                    refine ⟨912758418946276813275017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2434022450523404835400045 912758418946276813275017)
                    ·
                      refine ⟨684568814209707609956263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 912758418946276813275017 684568814209707609956263)
                      ·
                        rfl

theorem cell23_1333193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 3, 2].length) (baseStart_1333193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333193 prefixEnd_1333193 := by exact prefixLift 1333193
  have htrace : WordTrace (prefixWord ++ tailWord_1333193) baseStart_1333193 baseEnd_1333193 := by
    simpa [prefixWord, tailWord_1333193, baseEnd_1333193] using wordTrace_append hprefix tailTrace_1333193
  have hstable : (prefixWord ++ tailWord_1333193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333193).length < 2 ^ (prefixWord ++ tailWord_1333193).sum := by decide
  have hdescent : baseEnd_1333193 < baseStart_1333193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333200 : List Nat := [2, 1, 1, 1, 1, 2, 4, 6, 1, 1, 3]
def baseStart_1333200 : Nat := 118140960795 + 1333200 * 2 ^ 59
def prefixEnd_1333200 : Nat := 4983230072969 + 3 ^ 40 * 1333200 * 2
def baseEnd_1333200 : Nat := 684572408574289082568731

theorem tailTrace_1333200 : CollatzResearch.WordTrace tailWord_1333200 prefixEnd_1333200 684572408574289082568731 := by
  unfold tailWord_1333200
  simp only [CollatzResearch.WordTrace]
  refine ⟨24312899385025783638794527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32417199180034378185059369 24312899385025783638794527)
  ·
    refine ⟨36469349077538675458191791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24312899385025783638794527 36469349077538675458191791)
    ·
      refine ⟨54704023616308013187287687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36469349077538675458191791 54704023616308013187287687)
      ·
        refine ⟨82056035424462019780931531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54704023616308013187287687 82056035424462019780931531)
        ·
          refine ⟨123084053136693029671397297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82056035424462019780931531 123084053136693029671397297)
          ·
            refine ⟨92313039852519772253547973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123084053136693029671397297 92313039852519772253547973)
            ·
              refine ⟨17308694972347457297540245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92313039852519772253547973 17308694972347457297540245)
              ·
                refine ⟨811345076828787060822199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17308694972347457297540245 811345076828787060822199)
                ·
                  refine ⟨1217017615243180591233299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 811345076828787060822199 1217017615243180591233299)
                  ·
                    refine ⟨1825526422864770886849949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1217017615243180591233299 1825526422864770886849949)
                    ·
                      refine ⟨684572408574289082568731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1825526422864770886849949 684572408574289082568731)
                      ·
                        rfl

theorem cell23_1333200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 1, 1, 3].length) (baseStart_1333200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333200 prefixEnd_1333200 := by exact prefixLift 1333200
  have htrace : WordTrace (prefixWord ++ tailWord_1333200) baseStart_1333200 baseEnd_1333200 := by
    simpa [prefixWord, tailWord_1333200, baseEnd_1333200] using wordTrace_append hprefix tailTrace_1333200
  have hstable : (prefixWord ++ tailWord_1333200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333200).length < 2 ^ (prefixWord ++ tailWord_1333200).sum := by decide
  have hdescent : baseEnd_1333200 < baseStart_1333200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333233 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 1, 6]
def baseStart_1333233 : Nat := 118140960795 + 1333233 * 2 ^ 59
def prefixEnd_1333233 : Nat := 4983230072969 + 3 ^ 40 * 1333233 * 2
def baseEnd_1333233 : Nat := 228196451145295817818693

theorem tailTrace_1333233 : CollatzResearch.WordTrace tailWord_1333233 prefixEnd_1333233 228196451145295817818693 := by
  unfold tailWord_1333233
  simp only [CollatzResearch.WordTrace]
  refine ⟨48627002378932013913540353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32418001585954675942360235 48627002378932013913540353)
  ·
    refine ⟨36470251784199010435155265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48627002378932013913540353 36470251784199010435155265)
    ·
      refine ⟨27352688838149257826366449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36470251784199010435155265 27352688838149257826366449)
      ·
        refine ⟨20514516628611943369774837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27352688838149257826366449 20514516628611943369774837)
        ·
          refine ⟨1923235933932369690916391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20514516628611943369774837 1923235933932369690916391)
          ·
            refine ⟨2884853900898554536374587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923235933932369690916391 2884853900898554536374587)
            ·
              refine ⟨4327280851347831804561881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2884853900898554536374587 4327280851347831804561881)
              ·
                refine ⟨3245460638510873853421411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4327280851347831804561881 3245460638510873853421411)
                ·
                  refine ⟨4868190957766310780132117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3245460638510873853421411 4868190957766310780132117)
                  ·
                    refine ⟨228196451145295817818693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4868190957766310780132117 228196451145295817818693)
                    ·
                      rfl

theorem cell23_1333233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_1333233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333233 prefixEnd_1333233 := by exact prefixLift 1333233
  have htrace : WordTrace (prefixWord ++ tailWord_1333233) baseStart_1333233 baseEnd_1333233 := by
    simpa [prefixWord, tailWord_1333233, baseEnd_1333233] using wordTrace_append hprefix tailTrace_1333233
  have hstable : (prefixWord ++ tailWord_1333233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333233).length < 2 ^ (prefixWord ++ tailWord_1333233).sum := by decide
  have hdescent : baseEnd_1333233 < baseStart_1333233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333243 : List Nat := [1, 1, 1, 1, 1, 3, 4, 5, 1, 2, 3]
def baseStart_1333243 : Nat := 118140960795 + 1333243 * 2 ^ 59
def prefixEnd_1333243 : Nat := 4983230072969 + 3 ^ 40 * 1333243 * 2
def baseEnd_1333243 : Nat := 684594488242432414331033

theorem tailTrace_1333243 : CollatzResearch.WordTrace tailWord_1333243 prefixEnd_1333243 684594488242432414331033 := by
  unfold tailWord_1333243
  simp only [CollatzResearch.WordTrace]
  refine ⟨48627367108895785621404383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32418244739263857080936255 48627367108895785621404383)
  ·
    refine ⟨72941050663343678432106575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48627367108895785621404383 72941050663343678432106575)
    ·
      refine ⟨109411575995015517648159863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72941050663343678432106575 109411575995015517648159863)
      ·
        refine ⟨164117363992523276472239795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109411575995015517648159863 164117363992523276472239795)
        ·
          refine ⟨246176045988784914708359693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164117363992523276472239795 246176045988784914708359693)
          ·
            refine ⟨92316017245794343015634885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246176045988784914708359693 92316017245794343015634885)
            ·
              refine ⟨17309253233586439315431541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92316017245794343015634885 17309253233586439315431541)
              ·
                refine ⟨1622742490648728685821707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17309253233586439315431541 1622742490648728685821707)
                ·
                  refine ⟨2434113735973093028732561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622742490648728685821707 2434113735973093028732561)
                  ·
                    refine ⟨1825585301979819771549421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2434113735973093028732561 1825585301979819771549421)
                    ·
                      refine ⟨684594488242432414331033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1825585301979819771549421 684594488242432414331033)
                      ·
                        rfl

theorem cell23_1333243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 2, 3].length) (baseStart_1333243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333243 prefixEnd_1333243 := by exact prefixLift 1333243
  have htrace : WordTrace (prefixWord ++ tailWord_1333243) baseStart_1333243 baseEnd_1333243 := by
    simpa [prefixWord, tailWord_1333243, baseEnd_1333243] using wordTrace_append hprefix tailTrace_1333243
  have hstable : (prefixWord ++ tailWord_1333243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333243).length < 2 ^ (prefixWord ++ tailWord_1333243).sum := by decide
  have hdescent : baseEnd_1333243 < baseStart_1333243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333273 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 6, 1, 3]
def baseStart_1333273 : Nat := 118140960795 + 1333273 * 2 ^ 59
def prefixEnd_1333273 : Nat := 4983230072969 + 3 ^ 40 * 1333273 * 2
def baseEnd_1333273 : Nat := 684609892662067296955895

theorem tailTrace_1333273 : CollatzResearch.WordTrace tailWord_1333273 prefixEnd_1333273 684609892662067296955895 := by
  unfold tailWord_1333273
  simp only [CollatzResearch.WordTrace]
  refine ⟨48628461298787100744996473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32418974199191400496664315 48628461298787100744996473)
  ·
    refine ⟨36471345974090325558747355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48628461298787100744996473 36471345974090325558747355)
    ·
      refine ⟨54707018961135488338121033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36471345974090325558747355 54707018961135488338121033)
      ·
        refine ⟨41030264220851616253590775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54707018961135488338121033 41030264220851616253590775)
        ·
          refine ⟨61545396331277424380386163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41030264220851616253590775 61545396331277424380386163)
          ·
            refine ⟨92318094496916136570579245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61545396331277424380386163 92318094496916136570579245)
            ·
              refine ⟨34619285436343551213967217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92318094496916136570579245 34619285436343551213967217)
              ·
                refine ⟨25964464077257663410475413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34619285436343551213967217 25964464077257663410475413)
                ·
                  refine ⟨1217084253621452972366035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25964464077257663410475413 1217084253621452972366035)
                  ·
                    refine ⟨1825626380432179458549053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1217084253621452972366035 1825626380432179458549053)
                    ·
                      refine ⟨684609892662067296955895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1825626380432179458549053 684609892662067296955895)
                      ·
                        rfl

theorem cell23_1333273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 1, 3].length) (baseStart_1333273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333273 prefixEnd_1333273 := by exact prefixLift 1333273
  have htrace : WordTrace (prefixWord ++ tailWord_1333273) baseStart_1333273 baseEnd_1333273 := by
    simpa [prefixWord, tailWord_1333273, baseEnd_1333273] using wordTrace_append hprefix tailTrace_1333273
  have hstable : (prefixWord ++ tailWord_1333273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333273).length < 2 ^ (prefixWord ++ tailWord_1333273).sum := by decide
  have hdescent : baseEnd_1333273 < baseStart_1333273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333290 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1333290 : Nat := 118140960795 + 1333290 * 2 ^ 59
def prefixEnd_1333290 : Nat := 4983230072969 + 3 ^ 40 * 1333290 * 2
def baseEnd_1333290 : Nat := 684618621833193730443317

theorem tailTrace_1333290 : CollatzResearch.WordTrace tailWord_1333290 prefixEnd_1333290 684618621833193730443317 := by
  unfold tailWord_1333290
  simp only [CollatzResearch.WordTrace]
  refine ⟨12157270334931378162091331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32419387559817008432243549 12157270334931378162091331)
  ·
    refine ⟨18235905502397067243136997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12157270334931378162091331 18235905502397067243136997)
    ·
      refine ⟨3419232281699450108088187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18235905502397067243136997 3419232281699450108088187)
      ·
        refine ⟨5128848422549175162132281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3419232281699450108088187 5128848422549175162132281)
        ·
          refine ⟨3846636316911881371599211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5128848422549175162132281 3846636316911881371599211)
          ·
            refine ⟨5769954475367822057398817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3846636316911881371599211 5769954475367822057398817)
            ·
              refine ⟨4327465856525866543049113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5769954475367822057398817 4327465856525866543049113)
              ·
                refine ⟨3245599392394399907286835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4327465856525866543049113 3245599392394399907286835)
                ·
                  refine ⟨4868399088591599860930253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3245599392394399907286835 4868399088591599860930253)
                  ·
                    refine ⟨1825649658221849947848845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4868399088591599860930253 1825649658221849947848845)
                    ·
                      refine ⟨684618621833193730443317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1825649658221849947848845 684618621833193730443317)
                      ·
                        rfl

theorem cell23_1333290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1333290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333290 prefixEnd_1333290 := by exact prefixLift 1333290
  have htrace : WordTrace (prefixWord ++ tailWord_1333290) baseStart_1333290 baseEnd_1333290 := by
    simpa [prefixWord, tailWord_1333290, baseEnd_1333290] using wordTrace_append hprefix tailTrace_1333290
  have hstable : (prefixWord ++ tailWord_1333290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333290).length < 2 ^ (prefixWord ++ tailWord_1333290).sum := by decide
  have hdescent : baseEnd_1333290 < baseStart_1333290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333294 : List Nat := [4, 1, 3, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_1333294 : Nat := 118140960795 + 1333294 * 2 ^ 59
def prefixEnd_1333294 : Nat := 4983230072969 + 3 ^ 40 * 1333294 * 2
def baseEnd_1333294 : Nat := 684620675755811714793299

theorem tailTrace_1333294 : CollatzResearch.WordTrace tailWord_1333294 prefixEnd_1333294 684620675755811714793299 := by
  unfold tailWord_1333294
  simp only [CollatzResearch.WordTrace]
  refine ⟨6078653403963877666438867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32419484821140680887673957 6078653403963877666438867)
  ·
    refine ⟨9117980105945816499658301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6078653403963877666438867 9117980105945816499658301)
    ·
      refine ⟨3419242539729681187371863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9117980105945816499658301 3419242539729681187371863)
      ·
        refine ⟨5128863809594521781057795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3419242539729681187371863 5128863809594521781057795)
        ·
          refine ⟨7693295714391782671586693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5128863809594521781057795 7693295714391782671586693)
          ·
            refine ⟨1442492946448459250922505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7693295714391782671586693 1442492946448459250922505)
            ·
              refine ⟨1081869709836344438191879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442492946448459250922505 1081869709836344438191879)
              ·
                refine ⟨1622804564754516657287819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1081869709836344438191879 1622804564754516657287819)
                ·
                  refine ⟨2434206847131774985931729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622804564754516657287819 2434206847131774985931729)
                  ·
                    refine ⟨1825655135348831239448797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2434206847131774985931729 1825655135348831239448797)
                    ·
                      refine ⟨684620675755811714793299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1825655135348831239448797 684620675755811714793299)
                      ·
                        rfl

theorem cell23_1333294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_1333294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333294 prefixEnd_1333294 := by exact prefixLift 1333294
  have htrace : WordTrace (prefixWord ++ tailWord_1333294) baseStart_1333294 baseEnd_1333294 := by
    simpa [prefixWord, tailWord_1333294, baseEnd_1333294] using wordTrace_append hprefix tailTrace_1333294
  have hstable : (prefixWord ++ tailWord_1333294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333294).length < 2 ^ (prefixWord ++ tailWord_1333294).sum := by decide
  have hdescent : baseEnd_1333294 < baseStart_1333294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333342 : List Nat := [4, 4, 1, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_1333342 : Nat := 118140960795 + 1333342 * 2 ^ 59
def prefixEnd_1333342 : Nat := 4983230072969 + 3 ^ 40 * 1333342 * 2
def baseEnd_1333342 : Nat := 684645322827227526993079

theorem tailTrace_1333342 : CollatzResearch.WordTrace tailWord_1333342 prefixEnd_1333342 684645322827227526993079 := by
  unfold tailWord_1333342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6078872241942140691157285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32420651957024750352838853 6078872241942140691157285)
  ·
    refine ⟨1139788545364151379591991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6078872241942140691157285 1139788545364151379591991)
    ·
      refine ⟨1709682818046227069387987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1139788545364151379591991 1709682818046227069387987)
      ·
        refine ⟨2564524227069340604081981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709682818046227069387987 2564524227069340604081981)
        ·
          refine ⟨961696585151002726530743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2564524227069340604081981 961696585151002726530743)
          ·
            refine ⟨1442544877726504089796115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961696585151002726530743 1442544877726504089796115)
            ·
              refine ⟨2163817316589756134694173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442544877726504089796115 2163817316589756134694173)
              ·
                refine ⟨811431493721158550510315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2163817316589756134694173 811431493721158550510315)
                ·
                  refine ⟨1217147240581737825765473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 811431493721158550510315 1217147240581737825765473)
                  ·
                    refine ⟨912860430436303369324105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1217147240581737825765473 912860430436303369324105)
                    ·
                      refine ⟨684645322827227526993079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 912860430436303369324105 684645322827227526993079)
                      ·
                        rfl

theorem cell23_1333342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_1333342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333342 prefixEnd_1333342 := by exact prefixLift 1333342
  have htrace : WordTrace (prefixWord ++ tailWord_1333342) baseStart_1333342 baseEnd_1333342 := by
    simpa [prefixWord, tailWord_1333342, baseEnd_1333342] using wordTrace_append hprefix tailTrace_1333342
  have hstable : (prefixWord ++ tailWord_1333342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333342).length < 2 ^ (prefixWord ++ tailWord_1333342).sum := by decide
  have hdescent : baseEnd_1333342 < baseStart_1333342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333381 : List Nat := [1, 3, 1, 1, 5, 3, 2, 1, 2, 2, 2]
def baseStart_1333381 : Nat := 118140960795 + 1333381 * 2 ^ 59
def prefixEnd_1333381 : Nat := 4983230072969 + 3 ^ 40 * 1333381 * 2
def baseEnd_1333381 : Nat := 684665348572752874405399

theorem tailTrace_1333381 : CollatzResearch.WordTrace tailWord_1333381 prefixEnd_1333381 684665348572752874405399 := by
  unfold tailWord_1333381
  simp only [CollatzResearch.WordTrace]
  refine ⟨48632400382395835189927997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32421600254930556793285331 48632400382395835189927997)
  ·
    refine ⟨18237150143398438196222999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48632400382395835189927997 18237150143398438196222999)
    ·
      refine ⟨27355725215097657294334499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18237150143398438196222999 27355725215097657294334499)
      ·
        refine ⟨41033587822646485941501749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27355725215097657294334499 41033587822646485941501749)
        ·
          refine ⟨3846898858373108057015789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41033587822646485941501749 3846898858373108057015789)
          ·
            refine ⟨1442587071889915521380921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3846898858373108057015789 1442587071889915521380921)
            ·
              refine ⟨1081940303917436641035691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442587071889915521380921 1081940303917436641035691)
              ·
                refine ⟨1622910455876154961553537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1081940303917436641035691 1622910455876154961553537)
                ·
                  refine ⟨1217182841907116221165153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1622910455876154961553537 1217182841907116221165153)
                  ·
                    refine ⟨912887131430337165873865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1217182841907116221165153 912887131430337165873865)
                    ·
                      refine ⟨684665348572752874405399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 912887131430337165873865 684665348572752874405399)
                      ·
                        rfl

theorem cell23_1333381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 2, 2, 2].length) (baseStart_1333381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333381 prefixEnd_1333381 := by exact prefixLift 1333381
  have htrace : WordTrace (prefixWord ++ tailWord_1333381) baseStart_1333381 baseEnd_1333381 := by
    simpa [prefixWord, tailWord_1333381, baseEnd_1333381] using wordTrace_append hprefix tailTrace_1333381
  have hstable : (prefixWord ++ tailWord_1333381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333381).length < 2 ^ (prefixWord ++ tailWord_1333381).sum := by decide
  have hdescent : baseEnd_1333381 < baseStart_1333381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333410 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1333410 : Nat := 118140960795 + 1333410 * 2 ^ 59
def prefixEnd_1333410 : Nat := 4983230072969 + 3 ^ 40 * 1333410 * 2
def baseEnd_1333410 : Nat := 684680239511733260942765

theorem tailTrace_1333410 : CollatzResearch.WordTrace tailWord_1333410 prefixEnd_1333410 684680239511733260942765 := by
  unfold tailWord_1333410
  simp only [CollatzResearch.WordTrace]
  refine ⟨12158364524822693285683421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32422305399527182095155789 12158364524822693285683421)
  ·
    refine ⟨4559386696808509982131283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12158364524822693285683421 4559386696808509982131283)
    ·
      refine ⟨6839080045212764973196925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4559386696808509982131283 6839080045212764973196925)
      ·
        refine ⟨2564655016954786864948847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6839080045212764973196925 2564655016954786864948847)
        ·
          refine ⟨3846982525432180297423271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2564655016954786864948847 3846982525432180297423271)
          ·
            refine ⟨5770473788148270446134907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3846982525432180297423271 5770473788148270446134907)
            ·
              refine ⟨8655710682222405669202361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5770473788148270446134907 8655710682222405669202361)
              ·
                refine ⟨6491783011666804251901771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8655710682222405669202361 6491783011666804251901771)
                ·
                  refine ⟨9737674517500206377852657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6491783011666804251901771 9737674517500206377852657)
                  ·
                    refine ⟨7303255888125154783389493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9737674517500206377852657 7303255888125154783389493)
                    ·
                      refine ⟨684680239511733260942765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7303255888125154783389493 684680239511733260942765)
                      ·
                        rfl

theorem cell23_1333410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1333410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333410 prefixEnd_1333410 := by exact prefixLift 1333410
  have htrace : WordTrace (prefixWord ++ tailWord_1333410) baseStart_1333410 baseEnd_1333410 := by
    simpa [prefixWord, tailWord_1333410, baseEnd_1333410] using wordTrace_append hprefix tailTrace_1333410
  have hstable : (prefixWord ++ tailWord_1333410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333410).length < 2 ^ (prefixWord ++ tailWord_1333410).sum := by decide
  have hdescent : baseEnd_1333410 < baseStart_1333410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333423 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 3]
def baseStart_1333423 : Nat := 118140960795 + 1333423 * 2 ^ 59
def prefixEnd_1333423 : Nat := 4983230072969 + 3 ^ 40 * 1333423 * 2
def baseEnd_1333423 : Nat := 684686914760241710080205

theorem tailTrace_1333423 : CollatzResearch.WordTrace tailWord_1333423 prefixEnd_1333423 684686914760241710080205 := by
  unfold tailWord_1333423
  simp only [CollatzResearch.WordTrace]
  refine ⟨48633932248243676362956923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32422621498829117575304615 48633932248243676362956923)
  ·
    refine ⟨72950898372365514544435385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48633932248243676362956923 72950898372365514544435385)
    ·
      refine ⟨54713173779274135908326539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72950898372365514544435385 54713173779274135908326539)
      ·
        refine ⟨82069760668911203862489809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54713173779274135908326539 82069760668911203862489809)
        ·
          refine ⟨61552320501683402896867357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82069760668911203862489809 61552320501683402896867357)
          ·
            refine ⟨23082120188131276086325259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61552320501683402896867357 23082120188131276086325259)
            ·
              refine ⟨34623180282196914129487889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23082120188131276086325259 34623180282196914129487889)
              ·
                refine ⟨25967385211647685597115917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34623180282196914129487889 25967385211647685597115917)
                ·
                  refine ⟨9737769454367882098918469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25967385211647685597115917 9737769454367882098918469)
                  ·
                    refine ⟨1825831772693977893547213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9737769454367882098918469 1825831772693977893547213)
                    ·
                      refine ⟨684686914760241710080205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1825831772693977893547213 684686914760241710080205)
                      ·
                        rfl

theorem cell23_1333423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 3].length) (baseStart_1333423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333423 prefixEnd_1333423 := by exact prefixLift 1333423
  have htrace : WordTrace (prefixWord ++ tailWord_1333423) baseStart_1333423 baseEnd_1333423 := by
    simpa [prefixWord, tailWord_1333423, baseEnd_1333423] using wordTrace_append hprefix tailTrace_1333423
  have hstable : (prefixWord ++ tailWord_1333423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333423).length < 2 ^ (prefixWord ++ tailWord_1333423).sum := by decide
  have hdescent : baseEnd_1333423 < baseStart_1333423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333464 : List Nat := [2, 1, 2, 2, 4, 2, 2, 3, 1, 4]
def baseStart_1333464 : Nat := 118140960795 + 1333464 * 2 ^ 59
def prefixEnd_1333464 : Nat := 4983230072969 + 3 ^ 40 * 1333464 * 2
def baseEnd_1333464 : Nat := 228235989155692016555839

theorem tailTrace_1333464 : CollatzResearch.WordTrace tailWord_1333464 prefixEnd_1333464 228235989155692016555839 := by
  unfold tailWord_1333464
  simp only [CollatzResearch.WordTrace]
  refine ⟨24317713820547570182599723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32423618427396760243466297 24317713820547570182599723)
  ·
    refine ⟨36476570730821355273899585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24317713820547570182599723 36476570730821355273899585)
    ·
      refine ⟨27357428048116016455424689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36476570730821355273899585 27357428048116016455424689)
      ·
        refine ⟨20518071036087012341568517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27357428048116016455424689 20518071036087012341568517)
        ·
          refine ⟨3847138319266314814044097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20518071036087012341568517 3847138319266314814044097)
          ·
            refine ⟨2885353739449736110533073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3847138319266314814044097 2885353739449736110533073)
            ·
              refine ⟨2164015304587302082899805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2885353739449736110533073 2164015304587302082899805)
              ·
                refine ⟨811505739220238281087427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2164015304587302082899805 811505739220238281087427)
                ·
                  refine ⟨1217258608830357421631141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 811505739220238281087427 1217258608830357421631141)
                  ·
                    refine ⟨228235989155692016555839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1217258608830357421631141 228235989155692016555839)
                    ·
                      rfl

theorem cell23_1333464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 1, 4].length) (baseStart_1333464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333464 prefixEnd_1333464 := by exact prefixLift 1333464
  have htrace : WordTrace (prefixWord ++ tailWord_1333464) baseStart_1333464 baseEnd_1333464 := by
    simpa [prefixWord, tailWord_1333464, baseEnd_1333464] using wordTrace_append hprefix tailTrace_1333464
  have hstable : (prefixWord ++ tailWord_1333464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333464).length < 2 ^ (prefixWord ++ tailWord_1333464).sum := by decide
  have hdescent : baseEnd_1333464 < baseStart_1333464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333477 : List Nat := [1, 3, 1, 4, 2, 3, 1, 2, 6]
def baseStart_1333477 : Nat := 118140960795 + 1333477 * 2 ^ 59
def prefixEnd_1333477 : Nat := 4983230072969 + 3 ^ 40 * 1333477 * 2
def baseEnd_1333477 : Nat := 76079404746176055422773

theorem tailTrace_1333477 : CollatzResearch.WordTrace tailWord_1333477 prefixEnd_1333477 76079404746176055422773 := by
  unfold tailWord_1333477
  simp only [CollatzResearch.WordTrace]
  refine ⟨48635901790048043585422685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32423934526698695723615123 48635901790048043585422685)
  ·
    refine ⟨18238463171268016344533507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48635901790048043585422685 18238463171268016344533507)
    ·
      refine ⟨27357694756902024516800261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18238463171268016344533507 27357694756902024516800261)
      ·
        refine ⟨5129567766919129596900049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27357694756902024516800261 5129567766919129596900049)
        ·
          refine ⟨3847175825189347197675037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5129567766919129596900049 3847175825189347197675037)
          ·
            refine ⟨1442690934446005199128139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3847175825189347197675037 1442690934446005199128139)
            ·
              refine ⟨2164036401669007798692209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442690934446005199128139 2164036401669007798692209)
              ·
                refine ⟨1623027301251755849019157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2164036401669007798692209 1623027301251755849019157)
                ·
                  refine ⟨76079404746176055422773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1623027301251755849019157 76079404746176055422773)
                  ·
                    rfl

theorem cell23_1333477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 6].length) (baseStart_1333477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333477 prefixEnd_1333477 := by exact prefixLift 1333477
  have htrace : WordTrace (prefixWord ++ tailWord_1333477) baseStart_1333477 baseEnd_1333477 := by
    simpa [prefixWord, tailWord_1333477, baseEnd_1333477] using wordTrace_append hprefix tailTrace_1333477
  have hstable : (prefixWord ++ tailWord_1333477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333477).length < 2 ^ (prefixWord ++ tailWord_1333477).sum := by decide
  have hdescent : baseEnd_1333477 < baseStart_1333477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333487 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 3, 1, 3]
def baseStart_1333487 : Nat := 118140960795 + 1333487 * 2 ^ 59
def prefixEnd_1333487 : Nat := 4983230072969 + 3 ^ 40 * 1333487 * 2
def baseEnd_1333487 : Nat := 684719777522129459679911

theorem tailTrace_1333487 : CollatzResearch.WordTrace tailWord_1333487 prefixEnd_1333487 684719777522129459679911 := by
  unfold tailWord_1333487
  simp only [CollatzResearch.WordTrace]
  refine ⟨48636266520011815293286715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32424177680007876862191143 48636266520011815293286715)
  ·
    refine ⟨72954399780017722939930073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48636266520011815293286715 72954399780017722939930073)
    ·
      refine ⟨54715799835013292204947555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72954399780017722939930073 54715799835013292204947555)
      ·
        refine ⟨82073699752519938307421333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54715799835013292204947555 82073699752519938307421333)
        ·
          refine ⟨3847204675899372108160375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82073699752519938307421333 3847204675899372108160375)
          ·
            refine ⟨5770807013849058162240563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3847204675899372108160375 5770807013849058162240563)
            ·
              refine ⟨8656210520773587243360845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5770807013849058162240563 8656210520773587243360845)
              ·
                refine ⟨3246078945290095216260317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8656210520773587243360845 3246078945290095216260317)
                ·
                  refine ⟨1217279604483785706097619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3246078945290095216260317 1217279604483785706097619)
                  ·
                    refine ⟨1825919406725678559146429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1217279604483785706097619 1825919406725678559146429)
                    ·
                      refine ⟨684719777522129459679911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1825919406725678559146429 684719777522129459679911)
                      ·
                        rfl

theorem cell23_1333487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 1, 3].length) (baseStart_1333487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333487 prefixEnd_1333487 := by exact prefixLift 1333487
  have htrace : WordTrace (prefixWord ++ tailWord_1333487) baseStart_1333487 baseEnd_1333487 := by
    simpa [prefixWord, tailWord_1333487, baseEnd_1333487] using wordTrace_append hprefix tailTrace_1333487
  have hstable : (prefixWord ++ tailWord_1333487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333487).length < 2 ^ (prefixWord ++ tailWord_1333487).sum := by decide
  have hdescent : baseEnd_1333487 < baseStart_1333487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333521 : List Nat := [1, 2, 2, 1, 1, 7, 1, 3, 1, 1, 3]
def baseStart_1333521 : Nat := 118140960795 + 1333521 * 2 ^ 59
def prefixEnd_1333521 : Nat := 4983230072969 + 3 ^ 40 * 1333521 * 2
def baseEnd_1333521 : Nat := 684737235864382326654755

theorem tailTrace_1333521 : CollatzResearch.WordTrace tailWord_1333521 prefixEnd_1333521 684737235864382326654755 := by
  unfold tailWord_1333521
  simp only [CollatzResearch.WordTrace]
  refine ⟨48637506601888639100024417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32425004401259092733349611 48637506601888639100024417)
  ·
    refine ⟨36478129951416479325018313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48637506601888639100024417 36478129951416479325018313)
    ·
      refine ⟨27358597463562359493763735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36478129951416479325018313 27358597463562359493763735)
      ·
        refine ⟨41037896195343539240645603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27358597463562359493763735 41037896195343539240645603)
        ·
          refine ⟨61556844293015308860968405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41037896195343539240645603 61556844293015308860968405)
          ·
            refine ⟨1442738538117546301428947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 61556844293015308860968405 1442738538117546301428947)
            ·
              refine ⟨2164107807176319452143421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442738538117546301428947 2164107807176319452143421)
              ·
                refine ⟨811540427691119794553783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2164107807176319452143421 811540427691119794553783)
                ·
                  refine ⟨1217310641536679691830675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 811540427691119794553783 1217310641536679691830675)
                  ·
                    refine ⟨1825965962305019537746013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1217310641536679691830675 1825965962305019537746013)
                    ·
                      refine ⟨684737235864382326654755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1825965962305019537746013 684737235864382326654755)
                      ·
                        rfl

theorem cell23_1333521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 1, 1, 3].length) (baseStart_1333521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333521 prefixEnd_1333521 := by exact prefixLift 1333521
  have htrace : WordTrace (prefixWord ++ tailWord_1333521) baseStart_1333521 baseEnd_1333521 := by
    simpa [prefixWord, tailWord_1333521, baseEnd_1333521] using wordTrace_append hprefix tailTrace_1333521
  have hstable : (prefixWord ++ tailWord_1333521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333521).length < 2 ^ (prefixWord ++ tailWord_1333521).sum := by decide
  have hdescent : baseEnd_1333521 < baseStart_1333521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333527 : List Nat := [1, 1, 3, 4, 1, 2, 2, 3, 1, 1, 4]
def baseStart_1333527 : Nat := 118140960795 + 1333527 * 2 ^ 59
def prefixEnd_1333527 : Nat := 4983230072969 + 3 ^ 40 * 1333527 * 2
def baseEnd_1333527 : Nat := 684740316748309303179727

theorem tailTrace_1333527 : CollatzResearch.WordTrace tailWord_1333527 prefixEnd_1333527 684740316748309303179727 := by
  unfold tailWord_1333527
  simp only [CollatzResearch.WordTrace]
  refine ⟨48637725439866902124742835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32425150293244601416495223 48637725439866902124742835)
  ·
    refine ⟨72956588159800353187114253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48637725439866902124742835 72956588159800353187114253)
    ·
      refine ⟨27358720559925132445167845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72956588159800353187114253 27358720559925132445167845)
      ·
        refine ⟨5129760104985962333468971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27358720559925132445167845 5129760104985962333468971)
        ·
          refine ⟨7694640157478943500203457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5129760104985962333468971 7694640157478943500203457)
          ·
            refine ⟨5770980118109207625152593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7694640157478943500203457 5770980118109207625152593)
            ·
              refine ⟨4328235088581905718864445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5770980118109207625152593 4328235088581905718864445)
              ·
                refine ⟨1623088158218214644574167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4328235088581905718864445 1623088158218214644574167)
                ·
                  refine ⟨2434632237327321966861251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623088158218214644574167 2434632237327321966861251)
                  ·
                    refine ⟨3651948355990982950291877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2434632237327321966861251 3651948355990982950291877)
                    ·
                      refine ⟨684740316748309303179727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3651948355990982950291877 684740316748309303179727)
                      ·
                        rfl

theorem cell23_1333527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_1333527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333527 prefixEnd_1333527 := by exact prefixLift 1333527
  have htrace : WordTrace (prefixWord ++ tailWord_1333527) baseStart_1333527 baseEnd_1333527 := by
    simpa [prefixWord, tailWord_1333527, baseEnd_1333527] using wordTrace_append hprefix tailTrace_1333527
  have hstable : (prefixWord ++ tailWord_1333527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333527).length < 2 ^ (prefixWord ++ tailWord_1333527).sum := by decide
  have hdescent : baseEnd_1333527 < baseStart_1333527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333538 : List Nat := [3, 3, 1, 1, 3, 2, 3, 2, 1, 1, 3]
def baseStart_1333538 : Nat := 118140960795 + 1333538 * 2 ^ 59
def prefixEnd_1333538 : Nat := 4983230072969 + 3 ^ 40 * 1333538 * 2
def baseEnd_1333538 : Nat := 684745965035508760142177

theorem tailTrace_1333538 : CollatzResearch.WordTrace tailWord_1333538 prefixEnd_1333538 684745965035508760142177 := by
  unfold tailWord_1333538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12159531660706762750848317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32425417761884700668928845 12159531660706762750848317)
  ·
    refine ⟨4559824372765036031568119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12159531660706762750848317 4559824372765036031568119)
    ·
      refine ⟨6839736559147554047352179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4559824372765036031568119 6839736559147554047352179)
      ·
        refine ⟨10259604838721331071028269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6839736559147554047352179 10259604838721331071028269)
        ·
          refine ⟨3847351814520499151635601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10259604838721331071028269 3847351814520499151635601)
          ·
            refine ⟨2885513860890374363726701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3847351814520499151635601 2885513860890374363726701)
            ·
              refine ⟨1082067697833890386397513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2885513860890374363726701 1082067697833890386397513)
              ·
                refine ⟨811550773375417789798135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1082067697833890386397513 811550773375417789798135)
                ·
                  refine ⟨1217326160063126684697203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 811550773375417789798135 1217326160063126684697203)
                  ·
                    refine ⟨1825989240094690027045805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1217326160063126684697203 1825989240094690027045805)
                    ·
                      refine ⟨684745965035508760142177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1825989240094690027045805 684745965035508760142177)
                      ·
                        rfl

theorem cell23_1333538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_1333538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333538 prefixEnd_1333538 := by exact prefixLift 1333538
  have htrace : WordTrace (prefixWord ++ tailWord_1333538) baseStart_1333538 baseEnd_1333538 := by
    simpa [prefixWord, tailWord_1333538, baseEnd_1333538] using wordTrace_append hprefix tailTrace_1333538
  have hstable : (prefixWord ++ tailWord_1333538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333538).length < 2 ^ (prefixWord ++ tailWord_1333538).sum := by decide
  have hdescent : baseEnd_1333538 < baseStart_1333538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333540 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_1333540 : Nat := 118140960795 + 1333540 * 2 ^ 59
def prefixEnd_1333540 : Nat := 4983230072969 + 3 ^ 40 * 1333540 * 2
def baseEnd_1333540 : Nat := 684746991996817752317167

theorem tailTrace_1333540 : CollatzResearch.WordTrace tailWord_1333540 prefixEnd_1333540 684746991996817752317167 := by
  unfold tailWord_1333540
  simp only [CollatzResearch.WordTrace]
  refine ⟨24319099794409902672483037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32425466392546536896644049 24319099794409902672483037)
  ·
    refine ⟨9119662422903713502181139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24319099794409902672483037 9119662422903713502181139)
    ·
      refine ⟨13679493634355570253271709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9119662422903713502181139 13679493634355570253271709)
      ·
        refine ⟨5129810112883338844976891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13679493634355570253271709 5129810112883338844976891)
        ·
          refine ⟨7694715169325008267465337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5129810112883338844976891 7694715169325008267465337)
          ·
            refine ⟨5771036376993756200599003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7694715169325008267465337 5771036376993756200599003)
            ·
              refine ⟨8656554565490634300898505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5771036376993756200599003 8656554565490634300898505)
              ·
                refine ⟨6492415924117975725673879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8656554565490634300898505 6492415924117975725673879)
                ·
                  refine ⟨9738623886176963588510819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6492415924117975725673879 9738623886176963588510819)
                  ·
                    refine ⟨14607935829265445382766229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9738623886176963588510819 14607935829265445382766229)
                    ·
                      refine ⟨684746991996817752317167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14607935829265445382766229 684746991996817752317167)
                      ·
                        rfl

theorem cell23_1333540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_1333540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333540 prefixEnd_1333540 := by exact prefixLift 1333540
  have htrace : WordTrace (prefixWord ++ tailWord_1333540) baseStart_1333540 baseEnd_1333540 := by
    simpa [prefixWord, tailWord_1333540, baseEnd_1333540] using wordTrace_append hprefix tailTrace_1333540
  have hstable : (prefixWord ++ tailWord_1333540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333540).length < 2 ^ (prefixWord ++ tailWord_1333540).sum := by decide
  have hdescent : baseEnd_1333540 < baseStart_1333540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333554 : List Nat := [3, 2, 1, 1, 5, 1, 1, 3, 2, 4]
def baseStart_1333554 : Nat := 118140960795 + 1333554 * 2 ^ 59
def prefixEnd_1333554 : Nat := 4983230072969 + 3 ^ 40 * 1333554 * 2
def baseEnd_1333554 : Nat := 228251393575326899180701

theorem tailTrace_1333554 : CollatzResearch.WordTrace tailWord_1333554 prefixEnd_1333554 228251393575326899180701 := by
  unfold tailWord_1333554
  simp only [CollatzResearch.WordTrace]
  refine ⟨12159677552692271433993929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32425806807179390490650477 12159677552692271433993929)
  ·
    refine ⟨9119758164519203575495447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12159677552692271433993929 9119758164519203575495447)
    ·
      refine ⟨13679637246778805363243171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9119758164519203575495447 13679637246778805363243171)
      ·
        refine ⟨20519455870168208044864757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13679637246778805363243171 20519455870168208044864757)
        ·
          refine ⟨1923698987828269504206071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20519455870168208044864757 1923698987828269504206071)
          ·
            refine ⟨2885548481742404256309107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923698987828269504206071 2885548481742404256309107)
            ·
              refine ⟨4328322722613606384463661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885548481742404256309107 4328322722613606384463661)
              ·
                refine ⟨1623121020980102394173873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4328322722613606384463661 1623121020980102394173873)
                ·
                  refine ⟨1217340765735076795630405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1623121020980102394173873 1217340765735076795630405)
                  ·
                    refine ⟨228251393575326899180701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1217340765735076795630405 228251393575326899180701)
                    ·
                      rfl

theorem cell23_1333554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_1333554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333554 prefixEnd_1333554 := by exact prefixLift 1333554
  have htrace : WordTrace (prefixWord ++ tailWord_1333554) baseStart_1333554 baseEnd_1333554 := by
    simpa [prefixWord, tailWord_1333554, baseEnd_1333554] using wordTrace_append hprefix tailTrace_1333554
  have hstable : (prefixWord ++ tailWord_1333554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333554).length < 2 ^ (prefixWord ++ tailWord_1333554).sum := by decide
  have hdescent : baseEnd_1333554 < baseStart_1333554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333640 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 9]
def baseStart_1333640 : Nat := 118140960795 + 1333640 * 2 ^ 59
def prefixEnd_1333640 : Nat := 4983230072969 + 3 ^ 40 * 1333640 * 2
def baseEnd_1333640 : Nat := 76088704451363040118523

theorem tailTrace_1333640 : CollatzResearch.WordTrace tailWord_1333640 prefixEnd_1333640 76088704451363040118523 := by
  unfold tailWord_1333640
  simp only [CollatzResearch.WordTrace]
  refine ⟨24320923444228761211803187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32427897925638348282404249 24320923444228761211803187)
  ·
    refine ⟨36481385166343141817704781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24320923444228761211803187 36481385166343141817704781)
    ·
      refine ⟨13680519437378678181639293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36481385166343141817704781 13680519437378678181639293)
      ·
        refine ⟨5130194789017004318114735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13680519437378678181639293 5130194789017004318114735)
        ·
          refine ⟨7695292183525506477172103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5130194789017004318114735 7695292183525506477172103)
          ·
            refine ⟨11542938275288259715758155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7695292183525506477172103 11542938275288259715758155)
            ·
              refine ⟨17314407412932389573637233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11542938275288259715758155 17314407412932389573637233)
              ·
                refine ⟨12985805559699292180227925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17314407412932389573637233 12985805559699292180227925)
                ·
                  refine ⟨76088704451363040118523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12985805559699292180227925 76088704451363040118523)
                  ·
                    rfl

theorem cell23_1333640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 9].length) (baseStart_1333640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333640 prefixEnd_1333640 := by exact prefixLift 1333640
  have htrace : WordTrace (prefixWord ++ tailWord_1333640) baseStart_1333640 baseEnd_1333640 := by
    simpa [prefixWord, tailWord_1333640, baseEnd_1333640] using wordTrace_append hprefix tailTrace_1333640
  have hstable : (prefixWord ++ tailWord_1333640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333640).length < 2 ^ (prefixWord ++ tailWord_1333640).sum := by decide
  have hdescent : baseEnd_1333640 < baseStart_1333640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333657 : List Nat := [1, 2, 1, 2, 1, 4, 1, 6, 5]
def baseStart_1333657 : Nat := 118140960795 + 1333657 * 2 ^ 59
def prefixEnd_1333657 : Nat := 4983230072969 + 3 ^ 40 * 1333657 * 2
def baseEnd_1333657 : Nat := 76089674359265977172681

theorem tailTrace_1333657 : CollatzResearch.WordTrace tailWord_1333657 prefixEnd_1333657 76089674359265977172681 := by
  unfold tailWord_1333657
  simp only [CollatzResearch.WordTrace]
  refine ⟨48642466929395934326975225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32428311286263956217983483 48642466929395934326975225)
  ·
    refine ⟨36481850197046950745231419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48642466929395934326975225 36481850197046950745231419)
    ·
      refine ⟨54722775295570426117847129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36481850197046950745231419 54722775295570426117847129)
      ·
        refine ⟨41042081471677819588385347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54722775295570426117847129 41042081471677819588385347)
        ·
          refine ⟨61563122207516729382578021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41042081471677819588385347 61563122207516729382578021)
          ·
            refine ⟨11543085413909386759233379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61563122207516729382578021 11543085413909386759233379)
            ·
              refine ⟨17314628120864080138850069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11543085413909386759233379 17314628120864080138850069)
              ·
                refine ⟨811623193165503756508597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17314628120864080138850069 811623193165503756508597)
                ·
                  refine ⟨76089674359265977172681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 811623193165503756508597 76089674359265977172681)
                  ·
                    rfl

theorem cell23_1333657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 5].length) (baseStart_1333657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333657 prefixEnd_1333657 := by exact prefixLift 1333657
  have htrace : WordTrace (prefixWord ++ tailWord_1333657) baseStart_1333657 baseEnd_1333657 := by
    simpa [prefixWord, tailWord_1333657, baseEnd_1333657] using wordTrace_append hprefix tailTrace_1333657
  have hstable : (prefixWord ++ tailWord_1333657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333657).length < 2 ^ (prefixWord ++ tailWord_1333657).sum := by decide
  have hdescent : baseEnd_1333657 < baseStart_1333657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333667 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 3]
def baseStart_1333667 : Nat := 118140960795 + 1333667 * 2 ^ 59
def prefixEnd_1333667 : Nat := 4983230072969 + 3 ^ 40 * 1333667 * 2
def baseEnd_1333667 : Nat := 684812204039938755429083

theorem tailTrace_1333667 : CollatzResearch.WordTrace tailWord_1333667 prefixEnd_1333667 684812204039938755429083 := by
  unfold tailWord_1333667
  simp only [CollatzResearch.WordTrace]
  refine ⟨48642831659359706034839255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32428554439573137356559503 48642831659359706034839255)
  ·
    refine ⟨72964247489039559052258883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48642831659359706034839255 72964247489039559052258883)
    ·
      refine ⟨109446371233559338578388325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72964247489039559052258883 109446371233559338578388325)
      ·
        refine ⟨20521194606292375983447811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109446371233559338578388325 20521194606292375983447811)
        ·
          refine ⟨30781791909438563975171717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20521194606292375983447811 30781791909438563975171717)
          ·
            refine ⟨5771585983019730745344697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30781791909438563975171717 5771585983019730745344697)
            ·
              refine ⟨4328689487264798059008523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5771585983019730745344697 4328689487264798059008523)
              ·
                refine ⟨6493034230897197088512785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4328689487264798059008523 6493034230897197088512785)
                ·
                  refine ⟨4869775673172897816384589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6493034230897197088512785 4869775673172897816384589)
                  ·
                    refine ⟨1826165877439836681144221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4869775673172897816384589 1826165877439836681144221)
                    ·
                      refine ⟨684812204039938755429083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1826165877439836681144221 684812204039938755429083)
                      ·
                        rfl

theorem cell23_1333667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_1333667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333667 prefixEnd_1333667 := by exact prefixLift 1333667
  have htrace : WordTrace (prefixWord ++ tailWord_1333667) baseStart_1333667 baseEnd_1333667 := by
    simpa [prefixWord, tailWord_1333667, baseEnd_1333667] using wordTrace_append hprefix tailTrace_1333667
  have hstable : (prefixWord ++ tailWord_1333667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333667).length < 2 ^ (prefixWord ++ tailWord_1333667).sum := by decide
  have hdescent : baseEnd_1333667 < baseStart_1333667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333741 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1333741 : Nat := 118140960795 + 1333741 * 2 ^ 59
def prefixEnd_1333741 : Nat := 4983230072969 + 3 ^ 40 * 1333741 * 2
def baseEnd_1333741 : Nat := 684850201608371465903743

theorem tailTrace_1333741 : CollatzResearch.WordTrace tailWord_1333741 prefixEnd_1333741 684850201608371465903743 := by
  unfold tailWord_1333741
  simp only [CollatzResearch.WordTrace]
  refine ⟨48645530661091616673033077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32430353774061077782022051 48645530661091616673033077)
  ·
    refine ⟨4560518499477339063096851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48645530661091616673033077 4560518499477339063096851)
    ·
      refine ⟨6840777749216008594645277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4560518499477339063096851 6840777749216008594645277)
      ·
        refine ⟨2565291655956003222991979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6840777749216008594645277 2565291655956003222991979)
        ·
          refine ⟨3847937483934004834487969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2565291655956003222991979 3847937483934004834487969)
          ·
            refine ⟨2885953112950503625865977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3847937483934004834487969 2885953112950503625865977)
            ·
              refine ⟨2164464834712877719399483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2885953112950503625865977 2164464834712877719399483)
              ·
                refine ⟨3246697252069316579099225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2164464834712877719399483 3246697252069316579099225)
                ·
                  refine ⟨2435022939051987434324419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3246697252069316579099225 2435022939051987434324419)
                  ·
                    refine ⟨3652534408577981151486629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2435022939051987434324419 3652534408577981151486629)
                    ·
                      refine ⟨684850201608371465903743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3652534408577981151486629 684850201608371465903743)
                      ·
                        rfl

theorem cell23_1333741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1333741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333741 prefixEnd_1333741 := by exact prefixLift 1333741
  have htrace : WordTrace (prefixWord ++ tailWord_1333741) baseStart_1333741 baseEnd_1333741 := by
    simpa [prefixWord, tailWord_1333741, baseEnd_1333741] using wordTrace_append hprefix tailTrace_1333741
  have hstable : (prefixWord ++ tailWord_1333741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333741).length < 2 ^ (prefixWord ++ tailWord_1333741).sum := by decide
  have hdescent : baseEnd_1333741 < baseStart_1333741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333744 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 3]
def baseStart_1333744 : Nat := 118140960795 + 1333744 * 2 ^ 59
def prefixEnd_1333744 : Nat := 4983230072969 + 3 ^ 40 * 1333744 * 2
def baseEnd_1333744 : Nat := 684851742050334954166229

theorem tailTrace_1333744 : CollatzResearch.WordTrace tailWord_1333744 prefixEnd_1333744 684851742050334954166229 := by
  unfold tailWord_1333744
  simp only [CollatzResearch.WordTrace]
  refine ⟨24322820040040374092696143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32430426720053832123594857 24322820040040374092696143)
  ·
    refine ⟨36484230060060561139044215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24322820040040374092696143 36484230060060561139044215)
    ·
      refine ⟨54726345090090841708566323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36484230060060561139044215 54726345090090841708566323)
      ·
        refine ⟨82089517635136262562849485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54726345090090841708566323 82089517635136262562849485)
        ·
          refine ⟨30783569113176098461068557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82089517635136262562849485 30783569113176098461068557)
          ·
            refine ⟨11543838417441036922900709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30783569113176098461068557 11543838417441036922900709)
            ·
              refine ⟨2164469703270194423043883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11543838417441036922900709 2164469703270194423043883)
              ·
                refine ⟨3246704554905291634565825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2164469703270194423043883 3246704554905291634565825)
                ·
                  refine ⟨2435028416178968725924369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3246704554905291634565825 2435028416178968725924369)
                  ·
                    refine ⟨1826271312134226544443277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2435028416178968725924369 1826271312134226544443277)
                    ·
                      refine ⟨684851742050334954166229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1826271312134226544443277 684851742050334954166229)
                      ·
                        rfl

theorem cell23_1333744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 3].length) (baseStart_1333744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333744 prefixEnd_1333744 := by exact prefixLift 1333744
  have htrace : WordTrace (prefixWord ++ tailWord_1333744) baseStart_1333744 baseEnd_1333744 := by
    simpa [prefixWord, tailWord_1333744, baseEnd_1333744] using wordTrace_append hprefix tailTrace_1333744
  have hstable : (prefixWord ++ tailWord_1333744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333744).length < 2 ^ (prefixWord ++ tailWord_1333744).sum := by decide
  have hdescent : baseEnd_1333744 < baseStart_1333744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333764 : List Nat := [2, 3, 2, 3, 1, 1, 1, 4, 6]
def baseStart_1333764 : Nat := 118140960795 + 1333764 * 2 ^ 59
def prefixEnd_1333764 : Nat := 4983230072969 + 3 ^ 40 * 1333764 * 2
def baseEnd_1333764 : Nat := 76095779073713875101793

theorem tailTrace_1333764 : CollatzResearch.WordTrace tailWord_1333764 prefixEnd_1333764 76095779073713875101793 := by
  unfold tailWord_1333764
  simp only [CollatzResearch.WordTrace]
  refine ⟨24323184770004145800560173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32430913026672194400746897 24323184770004145800560173)
  ·
    refine ⟨9121194288751554675210065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24323184770004145800560173 9121194288751554675210065)
    ·
      refine ⟨6840895716563666006407549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9121194288751554675210065 6840895716563666006407549)
      ·
        refine ⟨2565335893711374752402831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6840895716563666006407549 2565335893711374752402831)
        ·
          refine ⟨3848003840567062128604247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2565335893711374752402831 3848003840567062128604247)
          ·
            refine ⟨5772005760850593192906371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3848003840567062128604247 5772005760850593192906371)
            ·
              refine ⟨8658008641275889789359557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5772005760850593192906371 8658008641275889789359557)
              ·
                refine ⟨1623376620239229335504917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8658008641275889789359557 1623376620239229335504917)
                ·
                  refine ⟨76095779073713875101793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1623376620239229335504917 76095779073713875101793)
                  ·
                    rfl

theorem cell23_1333764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_1333764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333764 prefixEnd_1333764 := by exact prefixLift 1333764
  have htrace : WordTrace (prefixWord ++ tailWord_1333764) baseStart_1333764 baseEnd_1333764 := by
    simpa [prefixWord, tailWord_1333764, baseEnd_1333764] using wordTrace_append hprefix tailTrace_1333764
  have hstable : (prefixWord ++ tailWord_1333764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333764).length < 2 ^ (prefixWord ++ tailWord_1333764).sum := by decide
  have hdescent : baseEnd_1333764 < baseStart_1333764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333794 : List Nat := [3, 3, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_1333794 : Nat := 118140960795 + 1333794 * 2 ^ 59
def prefixEnd_1333794 : Nat := 4983230072969 + 3 ^ 40 * 1333794 * 2
def baseEnd_1333794 : Nat := 228292472027686586180333

theorem tailTrace_1333794 : CollatzResearch.WordTrace tailWord_1333794 prefixEnd_1333794 228292472027686586180333 := by
  unfold tailWord_1333794
  simp only [CollatzResearch.WordTrace]
  refine ⟨12161865932474901681178109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32431642486599737816474957 12161865932474901681178109)
  ·
    refine ⟨4560699724678088130441791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12161865932474901681178109 4560699724678088130441791)
    ·
      refine ⟨6841049587017132195662687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4560699724678088130441791 6841049587017132195662687)
      ·
        refine ⟨10261574380525698293494031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6841049587017132195662687 10261574380525698293494031)
        ·
          refine ⟨15392361570788547440241047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10261574380525698293494031 15392361570788547440241047)
          ·
            refine ⟨23088542356182821160361571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15392361570788547440241047 23088542356182821160361571)
            ·
              refine ⟨34632813534274231740542357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23088542356182821160361571 34632813534274231740542357)
              ·
                refine ⟨1623413134419104612837923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34632813534274231740542357 1623413134419104612837923)
                ·
                  refine ⟨2435119701628656919256885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623413134419104612837923 2435119701628656919256885)
                  ·
                    refine ⟨228292472027686586180333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2435119701628656919256885 228292472027686586180333)
                    ·
                      rfl

theorem cell23_1333794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_1333794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333794 prefixEnd_1333794 := by exact prefixLift 1333794
  have htrace : WordTrace (prefixWord ++ tailWord_1333794) baseStart_1333794 baseEnd_1333794 := by
    simpa [prefixWord, tailWord_1333794, baseEnd_1333794] using wordTrace_append hprefix tailTrace_1333794
  have hstable : (prefixWord ++ tailWord_1333794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333794).length < 2 ^ (prefixWord ++ tailWord_1333794).sum := by decide
  have hdescent : baseEnd_1333794 < baseStart_1333794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333827 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 4]
def baseStart_1333827 : Nat := 118140960795 + 1333827 * 2 ^ 59
def prefixEnd_1333827 : Nat := 4983230072969 + 3 ^ 40 * 1333827 * 2
def baseEnd_1333827 : Nat := 684894360944658129428347

theorem tailTrace_1333827 : CollatzResearch.WordTrace tailWord_1333827 prefixEnd_1333827 684894360944658129428347 := by
  unfold tailWord_1333827
  simp only [CollatzResearch.WordTrace]
  refine ⟨48648667338780053360663735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32432444892520035573775823 48648667338780053360663735)
  ·
    refine ⟨72973001008170080040995603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48648667338780053360663735 72973001008170080040995603)
    ·
      refine ⟨109459501512255120061493405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72973001008170080040995603 109459501512255120061493405)
      ·
        refine ⟨41047313067095670023060027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109459501512255120061493405 41047313067095670023060027)
        ·
          refine ⟨61570969600643505034590041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41047313067095670023060027 61570969600643505034590041)
          ·
            refine ⟨46178227200482628775942531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61570969600643505034590041 46178227200482628775942531)
            ·
              refine ⟨69267340800723943163913797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46178227200482628775942531 69267340800723943163913797)
              ·
                refine ⟨12987626400135739343233837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69267340800723943163913797 12987626400135739343233837)
                ·
                  refine ⟨4870359900050902253712689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12987626400135739343233837 4870359900050902253712689)
                  ·
                    refine ⟨3652769925038176690284517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4870359900050902253712689 3652769925038176690284517)
                    ·
                      refine ⟨684894360944658129428347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3652769925038176690284517 684894360944658129428347)
                      ·
                        rfl

theorem cell23_1333827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_1333827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333827 prefixEnd_1333827 := by exact prefixLift 1333827
  have htrace : WordTrace (prefixWord ++ tailWord_1333827) baseStart_1333827 baseEnd_1333827 := by
    simpa [prefixWord, tailWord_1333827, baseEnd_1333827] using wordTrace_append hprefix tailTrace_1333827
  have hstable : (prefixWord ++ tailWord_1333827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333827).length < 2 ^ (prefixWord ++ tailWord_1333827).sum := by decide
  have hdescent : baseEnd_1333827 < baseStart_1333827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333834 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_1333834 : Nat := 118140960795 + 1333834 * 2 ^ 59
def prefixEnd_1333834 : Nat := 4983230072969 + 3 ^ 40 * 1333834 * 2
def baseEnd_1333834 : Nat := 684897955309239602040815

theorem tailTrace_1333834 : CollatzResearch.WordTrace tailWord_1333834 prefixEnd_1333834 684897955309239602040815 := by
  unfold tailWord_1333834
  simp only [CollatzResearch.WordTrace]
  refine ⟨12162230662438673389042139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32432615099836462370779037 12162230662438673389042139)
  ·
    refine ⟨18243345993658010083563209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12162230662438673389042139 18243345993658010083563209)
    ·
      refine ⟨13682509495243507562672407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18243345993658010083563209 13682509495243507562672407)
      ·
        refine ⟨20523764242865261344008611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13682509495243507562672407 20523764242865261344008611)
        ·
          refine ⟨30785646364297892016012917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20523764242865261344008611 30785646364297892016012917)
          ·
            refine ⟨2886154346652927376501211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30785646364297892016012917 2886154346652927376501211)
            ·
              refine ⟨4329231519979391064751817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2886154346652927376501211 4329231519979391064751817)
              ·
                refine ⟨3246923639984543298563863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4329231519979391064751817 3246923639984543298563863)
                ·
                  refine ⟨4870385459976814947845795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3246923639984543298563863 4870385459976814947845795)
                  ·
                    refine ⟨7305578189965222421768693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4870385459976814947845795 7305578189965222421768693)
                    ·
                      refine ⟨684897955309239602040815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7305578189965222421768693 684897955309239602040815)
                      ·
                        rfl

theorem cell23_1333834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_1333834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333834 prefixEnd_1333834 := by exact prefixLift 1333834
  have htrace : WordTrace (prefixWord ++ tailWord_1333834) baseStart_1333834 baseEnd_1333834 := by
    simpa [prefixWord, tailWord_1333834, baseEnd_1333834] using wordTrace_append hprefix tailTrace_1333834
  have hstable : (prefixWord ++ tailWord_1333834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333834).length < 2 ^ (prefixWord ++ tailWord_1333834).sum := by decide
  have hdescent : baseEnd_1333834 < baseStart_1333834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333844 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_1333844 : Nat := 118140960795 + 1333844 * 2 ^ 59
def prefixEnd_1333844 : Nat := 4983230072969 + 3 ^ 40 * 1333844 * 2
def baseEnd_1333844 : Nat := 684903090115784562915769

theorem tailTrace_1333844 : CollatzResearch.WordTrace tailWord_1333844 prefixEnd_1333844 684903090115784562915769 := by
  unfold tailWord_1333844
  simp only [CollatzResearch.WordTrace]
  refine ⟨24324643689859232632016293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32432858253145643509355057 24324643689859232632016293)
  ·
    refine ⟨4560870691848606118503055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24324643689859232632016293 4560870691848606118503055)
    ·
      refine ⟨6841306037772909177754583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4560870691848606118503055 6841306037772909177754583)
      ·
        refine ⟨10261959056659363766631875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6841306037772909177754583 10261959056659363766631875)
        ·
          refine ⟨15392938584989045649947813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10261959056659363766631875 15392938584989045649947813)
          ·
            refine ⟨2886175984685446059365215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15392938584989045649947813 2886175984685446059365215)
            ·
              refine ⟨4329263977028169089047823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2886175984685446059365215 4329263977028169089047823)
              ·
                refine ⟨6493895965542253633571735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4329263977028169089047823 6493895965542253633571735)
                ·
                  refine ⟨9740843948313380450357603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6493895965542253633571735 9740843948313380450357603)
                  ·
                    refine ⟨14611265922470070675536405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9740843948313380450357603 14611265922470070675536405)
                    ·
                      refine ⟨684903090115784562915769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14611265922470070675536405 684903090115784562915769)
                      ·
                        rfl

theorem cell23_1333844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_1333844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333844 prefixEnd_1333844 := by exact prefixLift 1333844
  have htrace : WordTrace (prefixWord ++ tailWord_1333844) baseStart_1333844 baseEnd_1333844 := by
    simpa [prefixWord, tailWord_1333844, baseEnd_1333844] using wordTrace_append hprefix tailTrace_1333844
  have hstable : (prefixWord ++ tailWord_1333844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333844).length < 2 ^ (prefixWord ++ tailWord_1333844).sum := by decide
  have hdescent : baseEnd_1333844 < baseStart_1333844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333881 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 4, 1, 3]
def baseStart_1333881 : Nat := 118140960795 + 1333881 * 2 ^ 59
def prefixEnd_1333881 : Nat := 4983230072969 + 3 ^ 40 * 1333881 * 2
def baseEnd_1333881 : Nat := 684922088900000918153099

theorem tailTrace_1333881 : CollatzResearch.WordTrace tailWord_1333881 prefixEnd_1333881 684922088900000918153099 := by
  unfold tailWord_1333881
  simp only [CollatzResearch.WordTrace]
  refine ⟨48650636880584420583129497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32433757920389613722086331 48650636880584420583129497)
  ·
    refine ⟨36487977660438315437347123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48650636880584420583129497 36487977660438315437347123)
    ·
      refine ⟨54731966490657473156020685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36487977660438315437347123 54731966490657473156020685)
      ·
        refine ⟨20524487433996552433507757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54731966490657473156020685 20524487433996552433507757)
        ·
          refine ⟨7696682787748707162565409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20524487433996552433507757 7696682787748707162565409)
          ·
            refine ⟨5772512090811530371924057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7696682787748707162565409 5772512090811530371924057)
            ·
              refine ⟨4329384068108647778943043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5772512090811530371924057 4329384068108647778943043)
              ·
                refine ⟨6494076102162971668414565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4329384068108647778943043 6494076102162971668414565)
                ·
                  refine ⟨1217639269155557187827731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6494076102162971668414565 1217639269155557187827731)
                  ·
                    refine ⟨1826458903733335781741597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1217639269155557187827731 1826458903733335781741597)
                    ·
                      refine ⟨684922088900000918153099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1826458903733335781741597 684922088900000918153099)
                      ·
                        rfl

theorem cell23_1333881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_1333881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333881 prefixEnd_1333881 := by exact prefixLift 1333881
  have htrace : WordTrace (prefixWord ++ tailWord_1333881) baseStart_1333881 baseEnd_1333881 := by
    simpa [prefixWord, tailWord_1333881, baseEnd_1333881] using wordTrace_append hprefix tailTrace_1333881
  have hstable : (prefixWord ++ tailWord_1333881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333881).length < 2 ^ (prefixWord ++ tailWord_1333881).sum := by decide
  have hdescent : baseEnd_1333881 < baseStart_1333881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333897 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 1, 8]
def baseStart_1333897 : Nat := 118140960795 + 1333897 * 2 ^ 59
def prefixEnd_1333897 : Nat := 4983230072969 + 3 ^ 40 * 1333897 * 2
def baseEnd_1333897 : Nat := 228310101530157618517675

theorem tailTrace_1333897 : CollatzResearch.WordTrace tailWord_1333897 prefixEnd_1333897 228310101530157618517675 := by
  unfold tailWord_1333897
  simp only [CollatzResearch.WordTrace]
  refine ⟨48651220448526455315711945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32434146965684303543807963 48651220448526455315711945)
  ·
    refine ⟨36488415336394841486783959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48651220448526455315711945 36488415336394841486783959)
    ·
      refine ⟨54732623004592262230175939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36488415336394841486783959 54732623004592262230175939)
      ·
        refine ⟨82098934506888393345263909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54732623004592262230175939 82098934506888393345263909)
        ·
          refine ⟨15393550220041573752236983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82098934506888393345263909 15393550220041573752236983)
          ·
            refine ⟨23090325330062360628355475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15393550220041573752236983 23090325330062360628355475)
            ·
              refine ⟨34635487995093540942533213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23090325330062360628355475 34635487995093540942533213)
              ·
                refine ⟨12988307998160077853449955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34635487995093540942533213 12988307998160077853449955)
                ·
                  refine ⟨19482461997240116780174933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12988307998160077853449955 19482461997240116780174933)
                  ·
                    refine ⟨228310101530157618517675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19482461997240116780174933 228310101530157618517675)
                    ·
                      rfl

theorem cell23_1333897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 8].length) (baseStart_1333897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333897 prefixEnd_1333897 := by exact prefixLift 1333897
  have htrace : WordTrace (prefixWord ++ tailWord_1333897) baseStart_1333897 baseEnd_1333897 := by
    simpa [prefixWord, tailWord_1333897, baseEnd_1333897] using wordTrace_append hprefix tailTrace_1333897
  have hstable : (prefixWord ++ tailWord_1333897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333897).length < 2 ^ (prefixWord ++ tailWord_1333897).sum := by decide
  have hdescent : baseEnd_1333897 < baseStart_1333897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333907 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 5]
def baseStart_1333907 : Nat := 118140960795 + 1333907 * 2 ^ 59
def prefixEnd_1333907 : Nat := 4983230072969 + 3 ^ 40 * 1333907 * 2
def baseEnd_1333907 : Nat := 684935439397017816427979

theorem tailTrace_1333907 : CollatzResearch.WordTrace tailWord_1333907 prefixEnd_1333907 684935439397017816427979 := by
  unfold tailWord_1333907
  simp only [CollatzResearch.WordTrace]
  refine ⟨48651585178490227023575975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32434390118993484682383983 48651585178490227023575975)
  ·
    refine ⟨72977377767735340535363963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48651585178490227023575975 72977377767735340535363963)
    ·
      refine ⟨109466066651603010803045945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72977377767735340535363963 109466066651603010803045945)
      ·
        refine ⟨82099549988702258102284459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109466066651603010803045945 82099549988702258102284459)
        ·
          refine ⟨123149324983053387153426689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82099549988702258102284459 123149324983053387153426689)
          ·
            refine ⟨92361993737290040365070017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123149324983053387153426689 92361993737290040365070017)
            ·
              refine ⟨69271495302967530273802513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92361993737290040365070017 69271495302967530273802513)
              ·
                refine ⟨51953621477225647705351885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69271495302967530273802513 51953621477225647705351885)
                ·
                  refine ⟨19482608053959617889506957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51953621477225647705351885 19482608053959617889506957)
                  ·
                    refine ⟨7305978020234856708565109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19482608053959617889506957 7305978020234856708565109)
                    ·
                      refine ⟨684935439397017816427979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7305978020234856708565109 684935439397017816427979)
                      ·
                        rfl

theorem cell23_1333907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_1333907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333907 prefixEnd_1333907 := by exact prefixLift 1333907
  have htrace : WordTrace (prefixWord ++ tailWord_1333907) baseStart_1333907 baseEnd_1333907 := by
    simpa [prefixWord, tailWord_1333907, baseEnd_1333907] using wordTrace_append hprefix tailTrace_1333907
  have hstable : (prefixWord ++ tailWord_1333907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333907).length < 2 ^ (prefixWord ++ tailWord_1333907).sum := by decide
  have hdescent : baseEnd_1333907 < baseStart_1333907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333924 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_1333924 : Nat := 118140960795 + 1333924 * 2 ^ 59
def prefixEnd_1333924 : Nat := 4983230072969 + 3 ^ 40 * 1333924 * 2
def baseEnd_1333924 : Nat := 684944168568144249915401

theorem tailTrace_1333924 : CollatzResearch.WordTrace tailWord_1333924 prefixEnd_1333924 684944168568144249915401 := by
  unfold tailWord_1333924
  simp only [CollatzResearch.WordTrace]
  refine ⟨24326102609714319463472413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32434803479619092617963217 24326102609714319463472413)
  ·
    refine ⟨9122288478642869798802155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24326102609714319463472413 9122288478642869798802155)
    ·
      refine ⟨13683432717964304698203233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9122288478642869798802155 13683432717964304698203233)
      ·
        refine ⟨10262574538473228523652425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13683432717964304698203233 10262574538473228523652425)
        ·
          refine ⟨7696930903854921392739319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10262574538473228523652425 7696930903854921392739319)
          ·
            refine ⟨11545396355782382089108979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7696930903854921392739319 11545396355782382089108979)
            ·
              refine ⟨17318094533673573133663469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11545396355782382089108979 17318094533673573133663469)
              ·
                refine ⟨6494285450127589925123801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17318094533673573133663469 6494285450127589925123801)
                ·
                  refine ⟨4870714087595692443842851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6494285450127589925123801 4870714087595692443842851)
                  ·
                    refine ⟨7306071131393538665764277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4870714087595692443842851 7306071131393538665764277)
                    ·
                      refine ⟨684944168568144249915401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7306071131393538665764277 684944168568144249915401)
                      ·
                        rfl

theorem cell23_1333924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_1333924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333924 prefixEnd_1333924 := by exact prefixLift 1333924
  have htrace : WordTrace (prefixWord ++ tailWord_1333924) baseStart_1333924 baseEnd_1333924 := by
    simpa [prefixWord, tailWord_1333924, baseEnd_1333924] using wordTrace_append hprefix tailTrace_1333924
  have hstable : (prefixWord ++ tailWord_1333924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333924).length < 2 ^ (prefixWord ++ tailWord_1333924).sum := by decide
  have hdescent : baseEnd_1333924 < baseStart_1333924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333941 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_1333941 : Nat := 118140960795 + 1333941 * 2 ^ 59
def prefixEnd_1333941 : Nat := 4983230072969 + 3 ^ 40 * 1333941 * 2
def baseEnd_1333941 : Nat := 684952897739270683402823

theorem tailTrace_1333941 : CollatzResearch.WordTrace tailWord_1333941 prefixEnd_1333941 684952897739270683402823 := by
  unfold tailWord_1333941
  simp only [CollatzResearch.WordTrace]
  refine ⟨48652825260367050830313677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32435216840244700553542451 48652825260367050830313677)
  ·
    refine ⟨18244809472637644061367629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48652825260367050830313677 18244809472637644061367629)
    ·
      refine ⟨6841803552239116523012861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18244809472637644061367629 6841803552239116523012861)
      ·
        refine ⟨2565676332089668696129823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6841803552239116523012861 2565676332089668696129823)
        ·
          refine ⟨3848514498134503044194735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2565676332089668696129823 3848514498134503044194735)
          ·
            refine ⟨5772771747201754566292103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3848514498134503044194735 5772771747201754566292103)
            ·
              refine ⟨8659157620802631849438155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5772771747201754566292103 8659157620802631849438155)
              ·
                refine ⟨12988736431203947774157233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8659157620802631849438155 12988736431203947774157233)
                ·
                  refine ⟨9741552323402960830617925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12988736431203947774157233 9741552323402960830617925)
                  ·
                    refine ⟨1826541060638055155740861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9741552323402960830617925 1826541060638055155740861)
                    ·
                      refine ⟨684952897739270683402823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1826541060638055155740861 684952897739270683402823)
                      ·
                        rfl

theorem cell23_1333941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_1333941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333941 prefixEnd_1333941 := by exact prefixLift 1333941
  have htrace : WordTrace (prefixWord ++ tailWord_1333941) baseStart_1333941 baseEnd_1333941 := by
    simpa [prefixWord, tailWord_1333941, baseEnd_1333941] using wordTrace_append hprefix tailTrace_1333941
  have hstable : (prefixWord ++ tailWord_1333941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333941).length < 2 ^ (prefixWord ++ tailWord_1333941).sum := by decide
  have hdescent : baseEnd_1333941 < baseStart_1333941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333947 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 8]
def baseStart_1333947 : Nat := 118140960795 + 1333947 * 2 ^ 59
def prefixEnd_1333947 : Nat := 4983230072969 + 3 ^ 40 * 1333947 * 2
def baseEnd_1333947 : Nat := 684955978623197659927795

theorem tailTrace_1333947 : CollatzResearch.WordTrace tailWord_1333947 prefixEnd_1333947 684955978623197659927795 := by
  unfold tailWord_1333947
  simp only [CollatzResearch.WordTrace]
  refine ⟨48653044098345313855032095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32435362732230209236688063 48653044098345313855032095)
  ·
    refine ⟨72979566147517970782548143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48653044098345313855032095 72979566147517970782548143)
    ·
      refine ⟨109469349221276956173822215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72979566147517970782548143 109469349221276956173822215)
      ·
        refine ⟨164204023831915434260733323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109469349221276956173822215 164204023831915434260733323)
        ·
          refine ⟨246306035747873151391099985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164204023831915434260733323 246306035747873151391099985)
          ·
            refine ⟨184729526810904863543324989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246306035747873151391099985 184729526810904863543324989)
            ·
              refine ⟨69273572554089323828746871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184729526810904863543324989 69273572554089323828746871)
              ·
                refine ⟨103910358831133985743120307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69273572554089323828746871 103910358831133985743120307)
                ·
                  refine ⟨155865538246700978614680461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103910358831133985743120307 155865538246700978614680461)
                  ·
                    refine ⟨58449576842512866980505173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155865538246700978614680461 58449576842512866980505173)
                    ·
                      refine ⟨684955978623197659927795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 58449576842512866980505173 684955978623197659927795)
                      ·
                        rfl

theorem cell23_1333947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 8].length) (baseStart_1333947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1333947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1333947 prefixEnd_1333947 := by exact prefixLift 1333947
  have htrace : WordTrace (prefixWord ++ tailWord_1333947) baseStart_1333947 baseEnd_1333947 := by
    simpa [prefixWord, tailWord_1333947, baseEnd_1333947] using wordTrace_append hprefix tailTrace_1333947
  have hstable : (prefixWord ++ tailWord_1333947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333947).length < 2 ^ (prefixWord ++ tailWord_1333947).sum := by decide
  have hdescent : baseEnd_1333947 < baseStart_1333947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334031 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 3]
def baseStart_1334031 : Nat := 118140960795 + 1334031 * 2 ^ 59
def prefixEnd_1334031 : Nat := 4983230072969 + 3 ^ 40 * 1334031 * 2
def baseEnd_1334031 : Nat := 684999110998175331277409

theorem tailTrace_1334031 : CollatzResearch.WordTrace tailWord_1334031 prefixEnd_1334031 684999110998175331277409 := by
  unfold tailWord_1334031
  simp only [CollatzResearch.WordTrace]
  refine ⟨48656107830040996201089947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32437405220027330800726631 48656107830040996201089947)
  ·
    refine ⟨72984161745061494301634921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48656107830040996201089947 72984161745061494301634921)
    ·
      refine ⟨54738121308796120726226191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72984161745061494301634921 54738121308796120726226191)
      ·
        refine ⟨82107181963194181089339287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54738121308796120726226191 82107181963194181089339287)
        ·
          refine ⟨123160772944791271634008931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82107181963194181089339287 123160772944791271634008931)
          ·
            refine ⟨184741159417186907451013397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123160772944791271634008931 184741159417186907451013397)
            ·
              refine ⟨8659741847680636286766253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 184741159417186907451013397 8659741847680636286766253)
              ·
                refine ⟨3247403192880238607537345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8659741847680636286766253 3247403192880238607537345)
                ·
                  refine ⟨2435552394660178955653009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3247403192880238607537345 2435552394660178955653009)
                  ·
                    refine ⟨1826664295995134216739757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2435552394660178955653009 1826664295995134216739757)
                    ·
                      refine ⟨684999110998175331277409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1826664295995134216739757 684999110998175331277409)
                      ·
                        rfl

theorem cell23_1334031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 3].length) (baseStart_1334031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334031 prefixEnd_1334031 := by exact prefixLift 1334031
  have htrace : WordTrace (prefixWord ++ tailWord_1334031) baseStart_1334031 baseEnd_1334031 := by
    simpa [prefixWord, tailWord_1334031, baseEnd_1334031] using wordTrace_append hprefix tailTrace_1334031
  have hstable : (prefixWord ++ tailWord_1334031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334031).length < 2 ^ (prefixWord ++ tailWord_1334031).sum := by decide
  have hdescent : baseEnd_1334031 < baseStart_1334031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334045 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1334045 : Nat := 118140960795 + 1334045 * 2 ^ 59
def prefixEnd_1334045 : Nat := 4983230072969 + 3 ^ 40 * 1334045 * 2
def baseEnd_1334045 : Nat := 685006299727338276502345

theorem tailTrace_1334045 : CollatzResearch.WordTrace tailWord_1334045 prefixEnd_1334045 685006299727338276502345 := by
  unfold tailWord_1334045
  simp only [CollatzResearch.WordTrace]
  refine ⟨48656618451990276592099589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32437745634660184394733059 48656618451990276592099589)
  ·
    refine ⟨9123115959748176861018673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48656618451990276592099589 9123115959748176861018673)
    ·
      refine ⟨6842336969811132645764005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9123115959748176861018673 6842336969811132645764005)
      ·
        refine ⟨1282938181839587371080751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6842336969811132645764005 1282938181839587371080751)
        ·
          refine ⟨1924407272759381056621127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1282938181839587371080751 1924407272759381056621127)
          ·
            refine ⟨2886610909139071584931691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1924407272759381056621127 2886610909139071584931691)
            ·
              refine ⟨4329916363708607377397537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2886610909139071584931691 4329916363708607377397537)
              ·
                refine ⟨3247437272781455533048153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4329916363708607377397537 3247437272781455533048153)
                ·
                  refine ⟨2435577954586091649786115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3247437272781455533048153 2435577954586091649786115)
                  ·
                    refine ⟨3653366931879137474679173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2435577954586091649786115 3653366931879137474679173)
                    ·
                      refine ⟨685006299727338276502345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3653366931879137474679173 685006299727338276502345)
                      ·
                        rfl

theorem cell23_1334045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1334045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334045 prefixEnd_1334045 := by exact prefixLift 1334045
  have htrace : WordTrace (prefixWord ++ tailWord_1334045) baseStart_1334045 baseEnd_1334045 := by
    simpa [prefixWord, tailWord_1334045, baseEnd_1334045] using wordTrace_append hprefix tailTrace_1334045
  have hstable : (prefixWord ++ tailWord_1334045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334045).length < 2 ^ (prefixWord ++ tailWord_1334045).sum := by decide
  have hdescent : baseEnd_1334045 < baseStart_1334045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334048 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 3]
def baseStart_1334048 : Nat := 118140960795 + 1334048 * 2 ^ 59
def prefixEnd_1334048 : Nat := 4983230072969 + 3 ^ 40 * 1334048 * 2
def baseEnd_1334048 : Nat := 685007840169301764764831

theorem tailTrace_1334048 : CollatzResearch.WordTrace tailWord_1334048 prefixEnd_1334048 685007840169301764764831 := by
  unfold tailWord_1334048
  simp only [CollatzResearch.WordTrace]
  refine ⟨24328363935489704052229399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32437818580652938736305865 24328363935489704052229399)
  ·
    refine ⟨36492545903234556078344099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24328363935489704052229399 36492545903234556078344099)
    ·
      refine ⟨54738818854851834117516149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36492545903234556078344099 54738818854851834117516149)
      ·
        refine ⟨5131764267642359448517139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54738818854851834117516149 5131764267642359448517139)
        ·
          refine ⟨7697646401463539172775709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5131764267642359448517139 7697646401463539172775709)
          ·
            refine ⟨2886617400548827189790891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7697646401463539172775709 2886617400548827189790891)
            ·
              refine ⟨4329926100823240784686337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2886617400548827189790891 4329926100823240784686337)
              ·
                refine ⟨3247444575617430588514753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4329926100823240784686337 3247444575617430588514753)
                ·
                  refine ⟨2435583431713072941386065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3247444575617430588514753 2435583431713072941386065)
                  ·
                    refine ⟨1826687573784804706039549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2435583431713072941386065 1826687573784804706039549)
                    ·
                      refine ⟨685007840169301764764831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1826687573784804706039549 685007840169301764764831)
                      ·
                        rfl

theorem cell23_1334048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_1334048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334048 prefixEnd_1334048 := by exact prefixLift 1334048
  have htrace : WordTrace (prefixWord ++ tailWord_1334048) baseStart_1334048 baseEnd_1334048 := by
    simpa [prefixWord, tailWord_1334048, baseEnd_1334048] using wordTrace_append hprefix tailTrace_1334048
  have hstable : (prefixWord ++ tailWord_1334048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334048).length < 2 ^ (prefixWord ++ tailWord_1334048).sum := by decide
  have hdescent : baseEnd_1334048 < baseStart_1334048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334128 : List Nat := [2, 1, 1, 1, 4, 1, 4, 3, 2, 4]
def baseStart_1334128 : Nat := 118140960795 + 1334128 * 2 ^ 59
def prefixEnd_1334128 : Nat := 4983230072969 + 3 ^ 40 * 1334128 * 2
def baseEnd_1334128 : Nat := 228349639540553817254821

theorem tailTrace_1334128 : CollatzResearch.WordTrace tailWord_1334128 prefixEnd_1334128 228349639540553817254821 := by
  unfold tailWord_1334128
  simp only [CollatzResearch.WordTrace]
  refine ⟨24329822855344790883685519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32439763807126387844914025 24329822855344790883685519)
  ·
    refine ⟨36494734283017186325528279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24329822855344790883685519 36494734283017186325528279)
    ·
      refine ⟨54742101424525779488292419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36494734283017186325528279 54742101424525779488292419)
      ·
        refine ⟨82113152136788669232438629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54742101424525779488292419 82113152136788669232438629)
        ·
          refine ⟨15396216025647875481082243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82113152136788669232438629 15396216025647875481082243)
          ·
            refine ⟨23094324038471813221623365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15396216025647875481082243 23094324038471813221623365)
            ·
              refine ⟨4330185757213464979054381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23094324038471813221623365 4330185757213464979054381)
              ·
                refine ⟨1623819658955049367145393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4330185757213464979054381 1623819658955049367145393)
                ·
                  refine ⟨1217864744216287025359045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1623819658955049367145393 1217864744216287025359045)
                  ·
                    refine ⟨228349639540553817254821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1217864744216287025359045 228349639540553817254821)
                    ·
                      rfl

theorem cell23_1334128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 2, 4].length) (baseStart_1334128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334128 prefixEnd_1334128 := by exact prefixLift 1334128
  have htrace : WordTrace (prefixWord ++ tailWord_1334128) baseStart_1334128 baseEnd_1334128 := by
    simpa [prefixWord, tailWord_1334128, baseEnd_1334128] using wordTrace_append hprefix tailTrace_1334128
  have hstable : (prefixWord ++ tailWord_1334128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334128).length < 2 ^ (prefixWord ++ tailWord_1334128).sum := by decide
  have hdescent : baseEnd_1334128 < baseStart_1334128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334131 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 4]
def baseStart_1334131 : Nat := 118140960795 + 1334131 * 2 ^ 59
def prefixEnd_1334131 : Nat := 4983230072969 + 3 ^ 40 * 1334131 * 2
def baseEnd_1334131 : Nat := 685050459063624940026949

theorem tailTrace_1334131 : CollatzResearch.WordTrace tailWord_1334131 prefixEnd_1334131 685050459063624940026949 := by
  unfold tailWord_1334131
  simp only [CollatzResearch.WordTrace]
  refine ⟨48659755129678713279730247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32439836753119142186486831 48659755129678713279730247)
  ·
    refine ⟨72989632694518069919595371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48659755129678713279730247 72989632694518069919595371)
    ·
      refine ⟨109484449041777104879393057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72989632694518069919595371 109484449041777104879393057)
      ·
        refine ⟨82113336781332828659544793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109484449041777104879393057 82113336781332828659544793)
        ·
          refine ⟨61585002585999621494658595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82113336781332828659544793 61585002585999621494658595)
          ·
            refine ⟨92377503878999432241987893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61585002585999621494658595 92377503878999432241987893)
            ·
              refine ⟨8660390988656196772686365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92377503878999432241987893 8660390988656196772686365)
              ·
                refine ⟨3247646620746073789757387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8660390988656196772686365 3247646620746073789757387)
                ·
                  refine ⟨4871469931119110684636081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3247646620746073789757387 4871469931119110684636081)
                  ·
                    refine ⟨3653602448339333013477061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4871469931119110684636081 3653602448339333013477061)
                    ·
                      refine ⟨685050459063624940026949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3653602448339333013477061 685050459063624940026949)
                      ·
                        rfl

theorem cell23_1334131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 4].length) (baseStart_1334131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334131 prefixEnd_1334131 := by exact prefixLift 1334131
  have htrace : WordTrace (prefixWord ++ tailWord_1334131) baseStart_1334131 baseEnd_1334131 := by
    simpa [prefixWord, tailWord_1334131, baseEnd_1334131] using wordTrace_append hprefix tailTrace_1334131
  have hstable : (prefixWord ++ tailWord_1334131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334131).length < 2 ^ (prefixWord ++ tailWord_1334131).sum := by decide
  have hdescent : baseEnd_1334131 < baseStart_1334131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334138 : List Nat := [3, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3]
def baseStart_1334138 : Nat := 118140960795 + 1334138 * 2 ^ 59
def prefixEnd_1334138 : Nat := 4983230072969 + 3 ^ 40 * 1334138 * 2
def baseEnd_1334138 : Nat := 685054053428206412639417

theorem tailTrace_1334138 : CollatzResearch.WordTrace tailWord_1334138 prefixEnd_1334138 685054053428206412639417 := by
  unfold tailWord_1334138
  simp only [CollatzResearch.WordTrace]
  refine ⟨12165002610163338368808767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32440006960435568983490045 12165002610163338368808767)
  ·
    refine ⟨18247503915245007553213151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12165002610163338368808767 18247503915245007553213151)
    ·
      refine ⟨27371255872867511329819727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18247503915245007553213151 27371255872867511329819727)
      ·
        refine ⟨41056883809301266994729591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27371255872867511329819727 41056883809301266994729591)
        ·
          refine ⟨61585325713951900492094387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41056883809301266994729591 61585325713951900492094387)
          ·
            refine ⟨92377988570927850738141581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61585325713951900492094387 92377988570927850738141581)
            ·
              refine ⟨34641745714097944026803093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92377988570927850738141581 34641745714097944026803093)
              ·
                refine ⟨1623831830348341126256395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34641745714097944026803093 1623831830348341126256395)
                ·
                  refine ⟨2435747745522511689384593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623831830348341126256395 2435747745522511689384593)
                  ·
                    refine ⟨1826810809141883767038445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2435747745522511689384593 1826810809141883767038445)
                    ·
                      refine ⟨685054053428206412639417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1826810809141883767038445 685054053428206412639417)
                      ·
                        rfl

theorem cell23_1334138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_1334138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334138 prefixEnd_1334138 := by exact prefixLift 1334138
  have htrace : WordTrace (prefixWord ++ tailWord_1334138) baseStart_1334138 baseEnd_1334138 := by
    simpa [prefixWord, tailWord_1334138, baseEnd_1334138] using wordTrace_append hprefix tailTrace_1334138
  have hstable : (prefixWord ++ tailWord_1334138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334138).length < 2 ^ (prefixWord ++ tailWord_1334138).sum := by decide
  have hdescent : baseEnd_1334138 < baseStart_1334138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334152 : List Nat := [2, 1, 3, 3, 2, 3, 2, 1, 1, 1, 4]
def baseStart_1334152 : Nat := 118140960795 + 1334152 * 2 ^ 59
def prefixEnd_1334152 : Nat := 4983230072969 + 3 ^ 40 * 1334152 * 2
def baseEnd_1334152 : Nat := 685061242157369357864353

theorem tailTrace_1334152 : CollatzResearch.WordTrace tailWord_1334152 prefixEnd_1334152 685061242157369357864353 := by
  unfold tailWord_1334152
  simp only [CollatzResearch.WordTrace]
  refine ⟨24330260531301316933122355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32440347375068422577496473 24330260531301316933122355)
  ·
    refine ⟨36495390796951975399683533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24330260531301316933122355 36495390796951975399683533)
    ·
      refine ⟨13685771548856990774881325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36495390796951975399683533 13685771548856990774881325)
      ·
        refine ⟨5132164330821371540580497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13685771548856990774881325 5132164330821371540580497)
        ·
          refine ⟨3849123248116028655435373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5132164330821371540580497 3849123248116028655435373)
          ·
            refine ⟨1443421218043510745788265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3849123248116028655435373 1443421218043510745788265)
            ·
              refine ⟨1082565913532633059341199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1443421218043510745788265 1082565913532633059341199)
              ·
                refine ⟨1623848870298949589011799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082565913532633059341199 1623848870298949589011799)
                ·
                  refine ⟨2435773305448424383517699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623848870298949589011799 2435773305448424383517699)
                  ·
                    refine ⟨3653659958172636575276549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2435773305448424383517699 3653659958172636575276549)
                    ·
                      refine ⟨685061242157369357864353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3653659958172636575276549 685061242157369357864353)
                      ·
                        rfl

theorem cell23_1334152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_1334152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334152 prefixEnd_1334152 := by exact prefixLift 1334152
  have htrace : WordTrace (prefixWord ++ tailWord_1334152) baseStart_1334152 baseEnd_1334152 := by
    simpa [prefixWord, tailWord_1334152, baseEnd_1334152] using wordTrace_append hprefix tailTrace_1334152
  have hstable : (prefixWord ++ tailWord_1334152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334152).length < 2 ^ (prefixWord ++ tailWord_1334152).sum := by decide
  have hdescent : baseEnd_1334152 < baseStart_1334152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334155 : List Nat := [1, 1, 1, 1, 4, 2, 6, 1, 1, 2, 3]
def baseStart_1334155 : Nat := 118140960795 + 1334155 * 2 ^ 59
def prefixEnd_1334155 : Nat := 4983230072969 + 3 ^ 40 * 1334155 * 2
def baseEnd_1334155 : Nat := 685062782599332846126839

theorem tailTrace_1334155 : CollatzResearch.WordTrace tailWord_1334155 prefixEnd_1334155 685062782599332846126839 := by
  unfold tailWord_1334155
  simp only [CollatzResearch.WordTrace]
  refine ⟨48660630481591765378603919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32440420321061176919069279 48660630481591765378603919)
  ·
    refine ⟨72990945722387648067905879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48660630481591765378603919 72990945722387648067905879)
    ·
      refine ⟨109486418583581472101858819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72990945722387648067905879 109486418583581472101858819)
      ·
        refine ⟨164229627875372208152788229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109486418583581472101858819 164229627875372208152788229)
        ·
          refine ⟨30793055226632289028647793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164229627875372208152788229 30793055226632289028647793)
          ·
            refine ⟨23094791419974216771485845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30793055226632289028647793 23094791419974216771485845)
            ·
              refine ⟨1082568347811291411163399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23094791419974216771485845 1082568347811291411163399)
              ·
                refine ⟨1623852521716937116745099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082568347811291411163399 1623852521716937116745099)
                ·
                  refine ⟨2435778782575405675117649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623852521716937116745099 2435778782575405675117649)
                  ·
                    refine ⟨1826834086931554256338237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2435778782575405675117649 1826834086931554256338237)
                    ·
                      refine ⟨685062782599332846126839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1826834086931554256338237 685062782599332846126839)
                      ·
                        rfl

theorem cell23_1334155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 1, 2, 3].length) (baseStart_1334155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334155 prefixEnd_1334155 := by exact prefixLift 1334155
  have htrace : WordTrace (prefixWord ++ tailWord_1334155) baseStart_1334155 baseEnd_1334155 := by
    simpa [prefixWord, tailWord_1334155, baseEnd_1334155] using wordTrace_append hprefix tailTrace_1334155
  have hstable : (prefixWord ++ tailWord_1334155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334155).length < 2 ^ (prefixWord ++ tailWord_1334155).sum := by decide
  have hdescent : baseEnd_1334155 < baseStart_1334155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334189 : List Nat := [1, 5, 2, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1334189 : Nat := 118140960795 + 1334189 * 2 ^ 59
def prefixEnd_1334189 : Nat := 4983230072969 + 3 ^ 40 * 1334189 * 2
def baseEnd_1334189 : Nat := 685080240941585713101683

theorem tailTrace_1334189 : CollatzResearch.WordTrace tailWord_1334189 prefixEnd_1334189 685080240941585713101683 := by
  unfold tailWord_1334189
  simp only [CollatzResearch.WordTrace]
  refine ⟨48661870563468589185341621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32441247042312392790227747 48661870563468589185341621)
  ·
    refine ⟨4562050365325180236125777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48661870563468589185341621 4562050365325180236125777)
    ·
      refine ⟨3421537773993885177094333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4562050365325180236125777 3421537773993885177094333)
      ·
        refine ⟨1283076665247706941410375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3421537773993885177094333 1283076665247706941410375)
        ·
          refine ⟨1924614997871560412115563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1283076665247706941410375 1924614997871560412115563)
          ·
            refine ⟨2886922496807340618173345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1924614997871560412115563 2886922496807340618173345)
            ·
              refine ⟨2165191872605505463630009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2886922496807340618173345 2165191872605505463630009)
              ·
                refine ⟨1623893904454129097722507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165191872605505463630009 1623893904454129097722507)
                ·
                  refine ⟨2435840856681193646583761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623893904454129097722507 2435840856681193646583761)
                  ·
                    refine ⟨1826880642510895234937821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2435840856681193646583761 1826880642510895234937821)
                    ·
                      refine ⟨685080240941585713101683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1826880642510895234937821 685080240941585713101683)
                      ·
                        rfl

theorem cell23_1334189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1334189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334189 prefixEnd_1334189 := by exact prefixLift 1334189
  have htrace : WordTrace (prefixWord ++ tailWord_1334189) baseStart_1334189 baseEnd_1334189 := by
    simpa [prefixWord, tailWord_1334189, baseEnd_1334189] using wordTrace_append hprefix tailTrace_1334189
  have hstable : (prefixWord ++ tailWord_1334189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334189).length < 2 ^ (prefixWord ++ tailWord_1334189).sum := by decide
  have hdescent : baseEnd_1334189 < baseStart_1334189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334211 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 5]
def baseStart_1334211 : Nat := 118140960795 + 1334211 * 2 ^ 59
def prefixEnd_1334211 : Nat := 4983230072969 + 3 ^ 40 * 1334211 * 2
def baseEnd_1334211 : Nat := 685091537515984627026581

theorem tailTrace_1334211 : CollatzResearch.WordTrace tailWord_1334211 prefixEnd_1334211 685091537515984627026581 := by
  unfold tailWord_1334211
  simp only [CollatzResearch.WordTrace]
  refine ⟨48662672969388886942642487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32441781979592591295094991 48662672969388886942642487)
  ·
    refine ⟨72994009454083330413963731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48662672969388886942642487 72994009454083330413963731)
    ·
      refine ⟨109491014181124995620945597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72994009454083330413963731 109491014181124995620945597)
      ·
        refine ⟨41059130317921873357854599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109491014181124995620945597 41059130317921873357854599)
        ·
          refine ⟨61588695476882810036781899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41059130317921873357854599 61588695476882810036781899)
          ·
            refine ⟨92383043215324215055172849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61588695476882810036781899 92383043215324215055172849)
            ·
              refine ⟨69287282411493161291379637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92383043215324215055172849 69287282411493161291379637)
              ·
                refine ⟨6495682726077483871066841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69287282411493161291379637 6495682726077483871066841)
                ·
                  refine ⟨4871762044558112903300131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6495682726077483871066841 4871762044558112903300131)
                  ·
                    refine ⟨7307643066837169354950197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4871762044558112903300131 7307643066837169354950197)
                    ·
                      refine ⟨685091537515984627026581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7307643066837169354950197 685091537515984627026581)
                      ·
                        rfl

theorem cell23_1334211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_1334211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334211 prefixEnd_1334211 := by exact prefixLift 1334211
  have htrace : WordTrace (prefixWord ++ tailWord_1334211) baseStart_1334211 baseEnd_1334211 := by
    simpa [prefixWord, tailWord_1334211, baseEnd_1334211] using wordTrace_append hprefix tailTrace_1334211
  have hstable : (prefixWord ++ tailWord_1334211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334211).length < 2 ^ (prefixWord ++ tailWord_1334211).sum := by decide
  have hdescent : baseEnd_1334211 < baseStart_1334211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334225 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 4, 2, 2]
def baseStart_1334225 : Nat := 118140960795 + 1334225 * 2 ^ 59
def prefixEnd_1334225 : Nat := 4983230072969 + 3 ^ 40 * 1334225 * 2
def baseEnd_1334225 : Nat := 685098726245147572251517

theorem tailTrace_1334225 : CollatzResearch.WordTrace tailWord_1334225 prefixEnd_1334225 685098726245147572251517 := by
  unfold tailWord_1334225
  simp only [CollatzResearch.WordTrace]
  refine ⟨48663183591338167333652129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32442122394225444889101419 48663183591338167333652129)
  ·
    refine ⟨36497387693503625500239097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48663183591338167333652129 36497387693503625500239097)
    ·
      refine ⟨27373040770127719125179323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36497387693503625500239097 27373040770127719125179323)
      ·
        refine ⟨41059561155191578687768985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27373040770127719125179323 41059561155191578687768985)
        ·
          refine ⟨30794670866393684015826739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41059561155191578687768985 30794670866393684015826739)
          ·
            refine ⟨46192006299590526023740109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30794670866393684015826739 46192006299590526023740109)
            ·
              refine ⟨17322002362346447258902541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46192006299590526023740109 17322002362346447258902541)
              ·
                refine ⟨6495750885879917722088453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17322002362346447258902541 6495750885879917722088453)
                ·
                  refine ⟨1217953291102484572891585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6495750885879917722088453 1217953291102484572891585)
                  ·
                    refine ⟨913464968326863429668689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1217953291102484572891585 913464968326863429668689)
                    ·
                      refine ⟨685098726245147572251517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 913464968326863429668689 685098726245147572251517)
                      ·
                        rfl

theorem cell23_1334225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 2, 2].length) (baseStart_1334225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334225 prefixEnd_1334225 := by exact prefixLift 1334225
  have htrace : WordTrace (prefixWord ++ tailWord_1334225) baseStart_1334225 baseEnd_1334225 := by
    simpa [prefixWord, tailWord_1334225, baseEnd_1334225] using wordTrace_append hprefix tailTrace_1334225
  have hstable : (prefixWord ++ tailWord_1334225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334225).length < 2 ^ (prefixWord ++ tailWord_1334225).sum := by decide
  have hdescent : baseEnd_1334225 < baseStart_1334225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334231 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 7]
def baseStart_1334231 : Nat := 118140960795 + 1334231 * 2 ^ 59
def prefixEnd_1334231 : Nat := 4983230072969 + 3 ^ 40 * 1334231 * 2
def baseEnd_1334231 : Nat := 76122423014341616530721

theorem tailTrace_1334231 : CollatzResearch.WordTrace tailWord_1334231 prefixEnd_1334231 76122423014341616530721 := by
  unfold tailWord_1334231
  simp only [CollatzResearch.WordTrace]
  refine ⟨48663402429316430358370547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32442268286210953572247031 48663402429316430358370547)
  ·
    refine ⟨72995103643974645537555821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48663402429316430358370547 72995103643974645537555821)
    ·
      refine ⟨27373163866490492076583433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72995103643974645537555821 27373163866490492076583433)
      ·
        refine ⟨20529872899867869057437575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27373163866490492076583433 20529872899867869057437575)
        ·
          refine ⟨30794809349801803586156363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20529872899867869057437575 30794809349801803586156363)
          ·
            refine ⟨46192214024702705379234545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30794809349801803586156363 46192214024702705379234545)
            ·
              refine ⟨34644160518527029034425909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46192214024702705379234545 34644160518527029034425909)
              ·
                refine ⟨3247890048611908971977429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34644160518527029034425909 3247890048611908971977429)
                ·
                  refine ⟨76122423014341616530721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3247890048611908971977429 76122423014341616530721)
                  ·
                    rfl

theorem cell23_1334231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 7].length) (baseStart_1334231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334231 prefixEnd_1334231 := by exact prefixLift 1334231
  have htrace : WordTrace (prefixWord ++ tailWord_1334231) baseStart_1334231 baseEnd_1334231 := by
    simpa [prefixWord, tailWord_1334231, baseEnd_1334231] using wordTrace_append hprefix tailTrace_1334231
  have hstable : (prefixWord ++ tailWord_1334231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334231).length < 2 ^ (prefixWord ++ tailWord_1334231).sum := by decide
  have hdescent : baseEnd_1334231 < baseStart_1334231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334282 : List Nat := [3, 1, 2, 2, 3, 1, 4, 2, 5]
def baseStart_1334282 : Nat := 118140960795 + 1334282 * 2 ^ 59
def prefixEnd_1334282 : Nat := 4983230072969 + 3 ^ 40 * 1334282 * 2
def baseEnd_1334282 : Nat := 76125332738050427693195

theorem tailTrace_1334282 : CollatzResearch.WordTrace tailWord_1334282 prefixEnd_1334282 76125332738050427693195 := by
  unfold tailWord_1334282
  simp only [CollatzResearch.WordTrace]
  refine ⟨12166315638032916517119275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32443508368087777378984733 12166315638032916517119275)
  ·
    refine ⟨18249473457049374775678913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12166315638032916517119275 18249473457049374775678913)
    ·
      refine ⟨13687105092787031081759185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18249473457049374775678913 13687105092787031081759185)
      ·
        refine ⟨10265328819590273311319389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13687105092787031081759185 10265328819590273311319389)
        ·
          refine ⟨3849498307346352491744771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10265328819590273311319389 3849498307346352491744771)
          ·
            refine ⟨5774247461019528737617157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3849498307346352491744771 5774247461019528737617157)
            ·
              refine ⟨1082671398941161638303217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5774247461019528737617157 1082671398941161638303217)
              ·
                refine ⟨812003549205871228727413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1082671398941161638303217 812003549205871228727413)
                ·
                  refine ⟨76125332738050427693195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 812003549205871228727413 76125332738050427693195)
                  ·
                    rfl

theorem cell23_1334282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 5].length) (baseStart_1334282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334282 prefixEnd_1334282 := by exact prefixLift 1334282
  have htrace : WordTrace (prefixWord ++ tailWord_1334282) baseStart_1334282 baseEnd_1334282 := by
    simpa [prefixWord, tailWord_1334282, baseEnd_1334282] using wordTrace_append hprefix tailTrace_1334282
  have hstable : (prefixWord ++ tailWord_1334282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334282).length < 2 ^ (prefixWord ++ tailWord_1334282).sum := by decide
  have hdescent : baseEnd_1334282 < baseStart_1334282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334291 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 2, 8]
def baseStart_1334291 : Nat := 118140960795 + 1334291 * 2 ^ 59
def prefixEnd_1334291 : Nat := 4983230072969 + 3 ^ 40 * 1334291 * 2
def baseEnd_1334291 : Nat := 228377538656114771342071

theorem tailTrace_1334291 : CollatzResearch.WordTrace tailWord_1334291 prefixEnd_1334291 228377538656114771342071 := by
  unfold tailWord_1334291
  simp only [CollatzResearch.WordTrace]
  refine ⟨48665590809099060605554727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32443727206066040403703151 48665590809099060605554727)
  ·
    refine ⟨72998386213648590908332091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48665590809099060605554727 72998386213648590908332091)
    ·
      refine ⟨109497579320472886362498137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72998386213648590908332091 109497579320472886362498137)
      ·
        refine ⟨82123184490354664771873603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109497579320472886362498137 82123184490354664771873603)
        ·
          refine ⟨123184776735531997157810405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82123184490354664771873603 123184776735531997157810405)
          ·
            refine ⟨23097145637912249467089451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123184776735531997157810405 23097145637912249467089451)
            ·
              refine ⟨34645718456868374200634177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23097145637912249467089451 34645718456868374200634177)
              ·
                refine ⟨25984288842651280650475633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34645718456868374200634177 25984288842651280650475633)
                ·
                  refine ⟨19488216631988460487856725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25984288842651280650475633 19488216631988460487856725)
                  ·
                    refine ⟨228377538656114771342071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19488216631988460487856725 228377538656114771342071)
                    ·
                      rfl

theorem cell23_1334291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 8].length) (baseStart_1334291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334291 prefixEnd_1334291 := by exact prefixLift 1334291
  have htrace : WordTrace (prefixWord ++ tailWord_1334291) baseStart_1334291 baseEnd_1334291 := by
    simpa [prefixWord, tailWord_1334291, baseEnd_1334291] using wordTrace_append hprefix tailTrace_1334291
  have hstable : (prefixWord ++ tailWord_1334291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334291).length < 2 ^ (prefixWord ++ tailWord_1334291).sum := by decide
  have hdescent : baseEnd_1334291 < baseStart_1334291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334298 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4]
def baseStart_1334298 : Nat := 118140960795 + 1334298 * 2 ^ 59
def prefixEnd_1334298 : Nat := 4983230072969 + 3 ^ 40 * 1334298 * 2
def baseEnd_1334298 : Nat := 685136210332925786638681

theorem tailTrace_1334298 : CollatzResearch.WordTrace tailWord_1334298 prefixEnd_1334298 685136210332925786638681 := by
  unfold tailWord_1334298
  simp only [CollatzResearch.WordTrace]
  refine ⟨12166461530018425200264887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32443897413382467200706365 12166461530018425200264887)
  ·
    refine ⟨18249692295027637800397331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12166461530018425200264887 18249692295027637800397331)
    ·
      refine ⟨27374538442541456700595997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18249692295027637800397331 27374538442541456700595997)
      ·
        refine ⟨10265451915953046262723499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27374538442541456700595997 10265451915953046262723499)
        ·
          refine ⟨15398177873929569394085249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10265451915953046262723499 15398177873929569394085249)
          ·
            refine ⟨11548633405447177045563937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15398177873929569394085249 11548633405447177045563937)
            ·
              refine ⟨8661475054085382784172953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11548633405447177045563937 8661475054085382784172953)
              ·
                refine ⟨6496106290564037088129715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8661475054085382784172953 6496106290564037088129715)
                ·
                  refine ⟨9744159435846055632194573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6496106290564037088129715 9744159435846055632194573)
                  ·
                    refine ⟨3654059788442270862072965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9744159435846055632194573 3654059788442270862072965)
                    ·
                      refine ⟨685136210332925786638681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3654059788442270862072965 685136210332925786638681)
                      ·
                        rfl

theorem cell23_1334298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_1334298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334298 prefixEnd_1334298 := by exact prefixLift 1334298
  have htrace : WordTrace (prefixWord ++ tailWord_1334298) baseStart_1334298 baseEnd_1334298 := by
    simpa [prefixWord, tailWord_1334298, baseEnd_1334298] using wordTrace_append hprefix tailTrace_1334298
  have hstable : (prefixWord ++ tailWord_1334298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334298).length < 2 ^ (prefixWord ++ tailWord_1334298).sum := by decide
  have hdescent : baseEnd_1334298 < baseStart_1334298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334328 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 2, 1, 6]
def baseStart_1334328 : Nat := 118140960795 + 1334328 * 2 ^ 59
def prefixEnd_1334328 : Nat := 4983230072969 + 3 ^ 40 * 1334328 * 2
def baseEnd_1334328 : Nat := 685151614752560669263543

theorem tailTrace_1334328 : CollatzResearch.WordTrace tailWord_1334328 prefixEnd_1334328 685151614752560669263543 := by
  unfold tailWord_1334328
  simp only [CollatzResearch.WordTrace]
  refine ⟨24333470154982507962325819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32444626873310010616434425 24333470154982507962325819)
  ·
    refine ⟨36500205232473761943488729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24333470154982507962325819 36500205232473761943488729)
    ·
      refine ⟨27375153924355321457616547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36500205232473761943488729 27375153924355321457616547)
      ·
        refine ⟨41062730886532982186424821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27375153924355321457616547 41062730886532982186424821)
        ·
          refine ⟨3849631020612467079977327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41062730886532982186424821 3849631020612467079977327)
          ·
            refine ⟨5774446530918700619965991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3849631020612467079977327 5774446530918700619965991)
            ·
              refine ⟨8661669796378050929948987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5774446530918700619965991 8661669796378050929948987)
              ·
                refine ⟨12992504694567076394923481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8661669796378050929948987 12992504694567076394923481)
                ·
                  refine ⟨9744378520925307296192611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12992504694567076394923481 9744378520925307296192611)
                  ·
                    refine ⟨14616567781387960944288917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9744378520925307296192611 14616567781387960944288917)
                    ·
                      refine ⟨685151614752560669263543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14616567781387960944288917 685151614752560669263543)
                      ·
                        rfl

theorem cell23_1334328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_1334328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334328 prefixEnd_1334328 := by exact prefixLift 1334328
  have htrace : WordTrace (prefixWord ++ tailWord_1334328) baseStart_1334328 baseEnd_1334328 := by
    simpa [prefixWord, tailWord_1334328, baseEnd_1334328] using wordTrace_append hprefix tailTrace_1334328
  have hstable : (prefixWord ++ tailWord_1334328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334328).length < 2 ^ (prefixWord ++ tailWord_1334328).sum := by decide
  have hdescent : baseEnd_1334328 < baseStart_1334328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334445 : List Nat := [1, 5, 2, 1, 3, 11]
def baseStart_1334445 : Nat := 118140960795 + 1334445 * 2 ^ 59
def prefixEnd_1334445 : Nat := 4983230072969 + 3 ^ 40 * 1334445 * 2
def baseEnd_1334445 : Nat := 2819801201601385644035

theorem tailTrace_1334445 : CollatzResearch.WordTrace tailWord_1334445 prefixEnd_1334445 2819801201601385644035 := by
  unfold tailWord_1334445
  simp only [CollatzResearch.WordTrace]
  refine ⟨48671207650541144906660789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32447471767027429937773859 48671207650541144906660789)
  ·
    refine ⟨4562925717238232334999449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48671207650541144906660789 4562925717238232334999449)
    ·
      refine ⟨3422194287928674251249587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4562925717238232334999449 3422194287928674251249587)
      ·
        refine ⟨5133291431893011376874381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3422194287928674251249587 5133291431893011376874381)
        ·
          refine ⟨1924984286959879266327893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5133291431893011376874381 1924984286959879266327893)
          ·
            refine ⟨2819801201601385644035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1924984286959879266327893 2819801201601385644035)
            ·
              rfl

theorem cell23_1334445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 11].length) (baseStart_1334445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334445 prefixEnd_1334445 := by exact prefixLift 1334445
  have htrace : WordTrace (prefixWord ++ tailWord_1334445) baseStart_1334445 baseEnd_1334445 := by
    simpa [prefixWord, tailWord_1334445, baseEnd_1334445] using wordTrace_append hprefix tailTrace_1334445
  have hstable : (prefixWord ++ tailWord_1334445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334445).length < 2 ^ (prefixWord ++ tailWord_1334445).sum := by decide
  have hdescent : baseEnd_1334445 < baseStart_1334445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334449 : List Nat := [1, 2, 2, 5, 1, 2, 2, 2, 2, 4]
def baseStart_1334449 : Nat := 118140960795 + 1334449 * 2 ^ 59
def prefixEnd_1334449 : Nat := 4983230072969 + 3 ^ 40 * 1334449 * 2
def baseEnd_1334449 : Nat := 228404581970584898616829

theorem tailTrace_1334449 : CollatzResearch.WordTrace tailWord_1334449 prefixEnd_1334449 228404581970584898616829 := by
  unfold tailWord_1334449
  simp only [CollatzResearch.WordTrace]
  refine ⟨48671353542526653589806401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32447569028351102393204267 48671353542526653589806401)
  ·
    refine ⟨36503515156894990192354801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48671353542526653589806401 36503515156894990192354801)
    ·
      refine ⟨27377636367671242644266101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36503515156894990192354801 27377636367671242644266101)
      ·
        refine ⟨2566653409469178997899947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27377636367671242644266101 2566653409469178997899947)
        ·
          refine ⟨3849980114203768496849921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2566653409469178997899947 3849980114203768496849921)
          ·
            refine ⟨2887485085652826372637441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3849980114203768496849921 2887485085652826372637441)
            ·
              refine ⟨2165613814239619779478081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2887485085652826372637441 2165613814239619779478081)
              ·
                refine ⟨1624210360679714834608561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165613814239619779478081 1624210360679714834608561)
                ·
                  refine ⟨1218157770509786125956421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1624210360679714834608561 1218157770509786125956421)
                  ·
                    refine ⟨228404581970584898616829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1218157770509786125956421 228404581970584898616829)
                    ·
                      rfl

theorem cell23_1334449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_1334449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334449 prefixEnd_1334449 := by exact prefixLift 1334449
  have htrace : WordTrace (prefixWord ++ tailWord_1334449) baseStart_1334449 baseEnd_1334449 := by
    simpa [prefixWord, tailWord_1334449, baseEnd_1334449] using wordTrace_append hprefix tailTrace_1334449
  have hstable : (prefixWord ++ tailWord_1334449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334449).length < 2 ^ (prefixWord ++ tailWord_1334449).sum := by decide
  have hdescent : baseEnd_1334449 < baseStart_1334449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334455 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 3]
def baseStart_1334455 : Nat := 118140960795 + 1334455 * 2 ^ 59
def prefixEnd_1334455 : Nat := 4983230072969 + 3 ^ 40 * 1334455 * 2
def baseEnd_1334455 : Nat := 685216826795681672375459

theorem tailTrace_1334455 : CollatzResearch.WordTrace tailWord_1334455 prefixEnd_1334455 685216826795681672375459 := by
  unfold tailWord_1334455
  simp only [CollatzResearch.WordTrace]
  refine ⟨48671572380504916614524819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32447714920336611076349879 48671572380504916614524819)
  ·
    refine ⟨73007358570757374921787229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48671572380504916614524819 73007358570757374921787229)
    ·
      refine ⟨27377759464034015595670211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73007358570757374921787229 27377759464034015595670211)
      ·
        refine ⟨41066639196051023393505317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27377759464034015595670211 41066639196051023393505317)
        ·
          refine ⟨7699994849259566886282247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41066639196051023393505317 7699994849259566886282247)
          ·
            refine ⟨11549992273889350329423371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7699994849259566886282247 11549992273889350329423371)
            ·
              refine ⟨17324988410834025494135057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11549992273889350329423371 17324988410834025494135057)
              ·
                refine ⟨12993741308125519120601293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17324988410834025494135057 12993741308125519120601293)
                ·
                  refine ⟨4872652990547069670225485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12993741308125519120601293 4872652990547069670225485)
                  ·
                    refine ⟨1827244871455151126334557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4872652990547069670225485 1827244871455151126334557)
                    ·
                      refine ⟨685216826795681672375459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1827244871455151126334557 685216826795681672375459)
                      ·
                        rfl

theorem cell23_1334455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_1334455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334455 prefixEnd_1334455 := by exact prefixLift 1334455
  have htrace : WordTrace (prefixWord ++ tailWord_1334455) baseStart_1334455 baseEnd_1334455 := by
    simpa [prefixWord, tailWord_1334455, baseEnd_1334455] using wordTrace_append hprefix tailTrace_1334455
  have hstable : (prefixWord ++ tailWord_1334455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334455).length < 2 ^ (prefixWord ++ tailWord_1334455).sum := by decide
  have hdescent : baseEnd_1334455 < baseStart_1334455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334462 : List Nat := [4, 2, 1, 1, 3, 3, 1, 8]
def baseStart_1334462 : Nat := 118140960795 + 1334462 * 2 ^ 59
def prefixEnd_1334462 : Nat := 4983230072969 + 3 ^ 40 * 1334462 * 2
def baseEnd_1334462 : Nat := 25378534117046783147701

theorem tailTrace_1334462 : CollatzResearch.WordTrace tailWord_1334462 prefixEnd_1334462 25378534117046783147701 := by
  unfold tailWord_1334462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6083978461434944601253705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32447885127653037873353093 6083978461434944601253705)
  ·
    refine ⟨4562983846076208450940279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6083978461434944601253705 4562983846076208450940279)
    ·
      refine ⟨6844475769114312676410419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4562983846076208450940279 6844475769114312676410419)
      ·
        refine ⟨10266713653671469014615629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6844475769114312676410419 10266713653671469014615629)
        ·
          refine ⟨3850017620126800880480861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10266713653671469014615629 3850017620126800880480861)
          ·
            refine ⟨1443756607547550330180323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3850017620126800880480861 1443756607547550330180323)
            ·
              refine ⟨2165634911321325495270485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443756607547550330180323 2165634911321325495270485)
              ·
                refine ⟨25378534117046783147701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2165634911321325495270485 25378534117046783147701)
                ·
                  rfl

theorem cell23_1334462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 8].length) (baseStart_1334462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334462 prefixEnd_1334462 := by exact prefixLift 1334462
  have htrace : WordTrace (prefixWord ++ tailWord_1334462) baseStart_1334462 baseEnd_1334462 := by
    simpa [prefixWord, tailWord_1334462, baseEnd_1334462] using wordTrace_append hprefix tailTrace_1334462
  have hstable : (prefixWord ++ tailWord_1334462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334462).length < 2 ^ (prefixWord ++ tailWord_1334462).sum := by decide
  have hdescent : baseEnd_1334462 < baseStart_1334462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334466 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_1334466 : Nat := 118140960795 + 1334466 * 2 ^ 59
def prefixEnd_1334466 : Nat := 4983230072969 + 3 ^ 40 * 1334466 * 2
def baseEnd_1334466 : Nat := 228407491694293709779303

theorem tailTrace_1334466 : CollatzResearch.WordTrace tailWord_1334466 prefixEnd_1334466 228407491694293709779303 := by
  unfold tailWord_1334466
  simp only [CollatzResearch.WordTrace]
  refine ⟨12167993395866266373293813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32447982388976710328783501 12167993395866266373293813)
  ·
    refine ⟨1140749380862462472496295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12167993395866266373293813 1140749380862462472496295)
    ·
      refine ⟨1711124071293693708744443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1140749380862462472496295 1711124071293693708744443)
      ·
        refine ⟨2566686106940540563116665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1711124071293693708744443 2566686106940540563116665)
        ·
          refine ⟨1925014580205405422337499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2566686106940540563116665 1925014580205405422337499)
          ·
            refine ⟨2887521870308108133506249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1925014580205405422337499 2887521870308108133506249)
            ·
              refine ⟨2165641402731081100129687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2887521870308108133506249 2165641402731081100129687)
              ·
                refine ⟨3248462104096621650194531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2165641402731081100129687 3248462104096621650194531)
                ·
                  refine ⟨4872693156144932475291797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3248462104096621650194531 4872693156144932475291797)
                  ·
                    refine ⟨228407491694293709779303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4872693156144932475291797 228407491694293709779303)
                    ·
                      rfl

theorem cell23_1334466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_1334466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334466 prefixEnd_1334466 := by exact prefixLift 1334466
  have htrace : WordTrace (prefixWord ++ tailWord_1334466) baseStart_1334466 baseEnd_1334466 := by
    simpa [prefixWord, tailWord_1334466, baseEnd_1334466] using wordTrace_append hprefix tailTrace_1334466
  have hstable : (prefixWord ++ tailWord_1334466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334466).length < 2 ^ (prefixWord ++ tailWord_1334466).sum := by decide
  have hdescent : baseEnd_1334466 < baseStart_1334466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334493 : List Nat := [1, 4, 3, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_1334493 : Nat := 118140960795 + 1334493 * 2 ^ 59
def prefixEnd_1334493 : Nat := 4983230072969 + 3 ^ 40 * 1334493 * 2
def baseEnd_1334493 : Nat := 685236339060552523700285

theorem tailTrace_1334493 : CollatzResearch.WordTrace tailWord_1334493 prefixEnd_1334493 685236339060552523700285 := by
  unfold tailWord_1334493
  simp only [CollatzResearch.WordTrace]
  refine ⟨48672958354367249104408133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32448638902911499402938755 48672958354367249104408133)
  ·
    refine ⟨9126179691443859207076525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48672958354367249104408133 9126179691443859207076525)
    ·
      refine ⟨3422317384291447202653697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9126179691443859207076525 3422317384291447202653697)
      ·
        refine ⟨2566738038218585401990273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3422317384291447202653697 2566738038218585401990273)
        ·
          refine ⟨1925053528663939051492705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2566738038218585401990273 1925053528663939051492705)
          ·
            refine ⟨1443790146497954288619529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1925053528663939051492705 1443790146497954288619529)
            ·
              refine ⟨1082842609873465716464647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1443790146497954288619529 1082842609873465716464647)
              ·
                refine ⟨1624263914810198574696971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082842609873465716464647 1624263914810198574696971)
                ·
                  refine ⟨2436395872215297862045457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1624263914810198574696971 2436395872215297862045457)
                  ·
                    refine ⟨1827296904161473396534093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2436395872215297862045457 1827296904161473396534093)
                    ·
                      refine ⟨685236339060552523700285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1827296904161473396534093 685236339060552523700285)
                      ·
                        rfl

theorem cell23_1334493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_1334493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334493 prefixEnd_1334493 := by exact prefixLift 1334493
  have htrace : WordTrace (prefixWord ++ tailWord_1334493) baseStart_1334493 baseEnd_1334493 := by
    simpa [prefixWord, tailWord_1334493, baseEnd_1334493] using wordTrace_append hprefix tailTrace_1334493
  have hstable : (prefixWord ++ tailWord_1334493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334493).length < 2 ^ (prefixWord ++ tailWord_1334493).sum := by decide
  have hdescent : baseEnd_1334493 < baseStart_1334493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334506 : List Nat := [3, 1, 3, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_1334506 : Nat := 118140960795 + 1334506 * 2 ^ 59
def prefixEnd_1334506 : Nat := 4983230072969 + 3 ^ 40 * 1334506 * 2
def baseEnd_1334506 : Nat := 685243014309060972837725

theorem tailTrace_1334506 : CollatzResearch.WordTrace tailWord_1334506 prefixEnd_1334506 685243014309060972837725 := by
  unfold tailWord_1334506
  simp only [CollatzResearch.WordTrace]
  refine ⟨12168358125830038081157843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32448955002213434883087581 12168358125830038081157843)
  ·
    refine ⟨18252537188745057121736765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12168358125830038081157843 18252537188745057121736765)
    ·
      refine ⟨6844701445779396420651287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18252537188745057121736765 6844701445779396420651287)
      ·
        refine ⟨10267052168669094630976931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6844701445779396420651287 10267052168669094630976931)
        ·
          refine ⟨15400578253003641946465397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10267052168669094630976931 15400578253003641946465397)
          ·
            refine ⟨1443804211219091432481131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15400578253003641946465397 1443804211219091432481131)
            ·
              refine ⟨2165706316828637148721697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443804211219091432481131 2165706316828637148721697)
              ·
                refine ⟨1624279737621477861541273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165706316828637148721697 1624279737621477861541273)
                ·
                  refine ⟨1218209803216108396155955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1624279737621477861541273 1218209803216108396155955)
                  ·
                    refine ⟨1827314704824162594233933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1218209803216108396155955 1827314704824162594233933)
                    ·
                      refine ⟨685243014309060972837725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1827314704824162594233933 685243014309060972837725)
                      ·
                        rfl

theorem cell23_1334506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_1334506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334506 prefixEnd_1334506 := by exact prefixLift 1334506
  have htrace : WordTrace (prefixWord ++ tailWord_1334506) baseStart_1334506 baseEnd_1334506 := by
    simpa [prefixWord, tailWord_1334506, baseEnd_1334506] using wordTrace_append hprefix tailTrace_1334506
  have hstable : (prefixWord ++ tailWord_1334506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334506).length < 2 ^ (prefixWord ++ tailWord_1334506).sum := by decide
  have hdescent : baseEnd_1334506 < baseStart_1334506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334529 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 1, 4, 2]
def baseStart_1334529 : Nat := 118140960795 + 1334529 * 2 ^ 59
def prefixEnd_1334529 : Nat := 4983230072969 + 3 ^ 40 * 1334529 * 2
def baseEnd_1334529 : Nat := 685254824364114382850119

theorem tailTrace_1334529 : CollatzResearch.WordTrace tailWord_1334529 prefixEnd_1334529 685254824364114382850119 := by
  unfold tailWord_1334529
  simp only [CollatzResearch.WordTrace]
  refine ⟨48674271382236827252718641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32449514254824551501812427 48674271382236827252718641)
  ·
    refine ⟨36505703536677620439538981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48674271382236827252718641 36505703536677620439538981)
    ·
      refine ⟨6844819413127053832413559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36505703536677620439538981 6844819413127053832413559)
      ·
        refine ⟨10267229119690580748620339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6844819413127053832413559 10267229119690580748620339)
        ·
          refine ⟨15400843679535871122930509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10267229119690580748620339 15400843679535871122930509)
          ·
            refine ⟨5775316379825951671098941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15400843679535871122930509 5775316379825951671098941)
            ·
              refine ⟨2165743642434731876662103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5775316379825951671098941 2165743642434731876662103)
              ·
                refine ⟨3248615463652097814993155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2165743642434731876662103 3248615463652097814993155)
                ·
                  refine ⟨4872923195478146722489733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3248615463652097814993155 4872923195478146722489733)
                  ·
                    refine ⟨913673099152152510466825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4872923195478146722489733 913673099152152510466825)
                    ·
                      refine ⟨685254824364114382850119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 913673099152152510466825 685254824364114382850119)
                      ·
                        rfl

theorem cell23_1334529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_1334529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334529 prefixEnd_1334529 := by exact prefixLift 1334529
  have htrace : WordTrace (prefixWord ++ tailWord_1334529) baseStart_1334529 baseEnd_1334529 := by
    simpa [prefixWord, tailWord_1334529, baseEnd_1334529] using wordTrace_append hprefix tailTrace_1334529
  have hstable : (prefixWord ++ tailWord_1334529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334529).length < 2 ^ (prefixWord ++ tailWord_1334529).sum := by decide
  have hdescent : baseEnd_1334529 < baseStart_1334529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334572 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 2, 5, 2]
def baseStart_1334572 : Nat := 118140960795 + 1334572 * 2 ^ 59
def prefixEnd_1334572 : Nat := 4983230072969 + 3 ^ 40 * 1334572 * 2
def baseEnd_1334572 : Nat := 685276904032257714612421

theorem tailTrace_1334572 : CollatzResearch.WordTrace tailWord_1334572 prefixEnd_1334572 685276904032257714612421 := by
  unfold tailWord_1334572
  simp only [CollatzResearch.WordTrace]
  refine ⟨24337919860540522798266985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32450559814054030397689313 24337919860540522798266985)
  ·
    refine ⟨18253439895405392098700239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24337919860540522798266985 18253439895405392098700239)
    ·
      refine ⟨27380159843108088148050359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18253439895405392098700239 27380159843108088148050359)
      ·
        refine ⟨41070239764662132222075539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27380159843108088148050359 41070239764662132222075539)
        ·
          refine ⟨61605359646993198333113309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41070239764662132222075539 61605359646993198333113309)
          ·
            refine ⟨23102009867622449374917491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61605359646993198333113309 23102009867622449374917491)
            ·
              refine ⟨34653014801433674062376237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23102009867622449374917491 34653014801433674062376237)
              ·
                refine ⟨12994880550537627773391089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34653014801433674062376237 12994880550537627773391089)
                ·
                  refine ⟨9746160412903220830043317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12994880550537627773391089 9746160412903220830043317)
                  ·
                    refine ⟨913702538709676952816561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9746160412903220830043317 913702538709676952816561)
                    ·
                      refine ⟨685276904032257714612421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 913702538709676952816561 685276904032257714612421)
                      ·
                        rfl

theorem cell23_1334572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 5, 2].length) (baseStart_1334572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334572 prefixEnd_1334572 := by exact prefixLift 1334572
  have htrace : WordTrace (prefixWord ++ tailWord_1334572) baseStart_1334572 baseEnd_1334572 := by
    simpa [prefixWord, tailWord_1334572, baseEnd_1334572] using wordTrace_append hprefix tailTrace_1334572
  have hstable : (prefixWord ++ tailWord_1334572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334572).length < 2 ^ (prefixWord ++ tailWord_1334572).sum := by decide
  have hdescent : baseEnd_1334572 < baseStart_1334572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334614 : List Nat := [5, 2, 3, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_1334614 : Nat := 118140960795 + 1334614 * 2 ^ 59
def prefixEnd_1334614 : Nat := 4983230072969 + 3 ^ 40 * 1334614 * 2
def baseEnd_1334614 : Nat := 685298470219746550287229

theorem tailTrace_1334614 : CollatzResearch.WordTrace tailWord_1334614 prefixEnd_1334614 685298470219746550287229 := by
  unfold tailWord_1334614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3042335724183055423097681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32451581057952591179708597 3042335724183055423097681)
  ·
    refine ⟨2281751793137291567323261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3042335724183055423097681 2281751793137291567323261)
    ·
      refine ⟨855656922426484337746223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2281751793137291567323261 855656922426484337746223)
      ·
        refine ⟨1283485383639726506619335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 855656922426484337746223 1283485383639726506619335)
        ·
          refine ⟨1925228075459589759929003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1283485383639726506619335 1925228075459589759929003)
          ·
            refine ⟨2887842113189384639893505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1925228075459589759929003 2887842113189384639893505)
            ·
              refine ⟨2165881584892038479920129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2887842113189384639893505 2165881584892038479920129)
              ·
                refine ⟨1624411188669028859940097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165881584892038479920129 1624411188669028859940097)
                ·
                  refine ⟨1218308391501771644955073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1624411188669028859940097 1218308391501771644955073)
                  ·
                    refine ⟨913731293626328733716305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1218308391501771644955073 913731293626328733716305)
                    ·
                      refine ⟨685298470219746550287229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 913731293626328733716305 685298470219746550287229)
                      ·
                        rfl

theorem cell23_1334614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_1334614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334614 prefixEnd_1334614 := by exact prefixLift 1334614
  have htrace : WordTrace (prefixWord ++ tailWord_1334614) baseStart_1334614 baseEnd_1334614 := by
    simpa [prefixWord, tailWord_1334614, baseEnd_1334614] using wordTrace_append hprefix tailTrace_1334614
  have hstable : (prefixWord ++ tailWord_1334614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334614).length < 2 ^ (prefixWord ++ tailWord_1334614).sum := by decide
  have hdescent : baseEnd_1334614 < baseStart_1334614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334625 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 8]
def baseStart_1334625 : Nat := 118140960795 + 1334625 * 2 ^ 59
def prefixEnd_1334625 : Nat := 4983230072969 + 3 ^ 40 * 1334625 * 2
def baseEnd_1334625 : Nat := 76144902056327334138853

theorem tailTrace_1334625 : CollatzResearch.WordTrace tailWord_1334625 prefixEnd_1334625 76144902056327334138853 := by
  unfold tailWord_1334625
  simp only [CollatzResearch.WordTrace]
  refine ⟨48677772789889035648213329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32451848526592690432142219 48677772789889035648213329)
  ·
    refine ⟨36508329592416776736159997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48677772789889035648213329 36508329592416776736159997)
    ·
      refine ⟨13690623597156291276059999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36508329592416776736159997 13690623597156291276059999)
      ·
        refine ⟨20535935395734436914089999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13690623597156291276059999 20535935395734436914089999)
        ·
          refine ⟨30803903093601655371134999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20535935395734436914089999 30803903093601655371134999)
          ·
            refine ⟨46205854640402483056702499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30803903093601655371134999 46205854640402483056702499)
            ·
              refine ⟨69308781960603724585053749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46205854640402483056702499 69308781960603724585053749)
              ·
                refine ⟨6497698308806599179848789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69308781960603724585053749 6497698308806599179848789)
                ·
                  refine ⟨76144902056327334138853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6497698308806599179848789 76144902056327334138853)
                  ·
                    rfl

theorem cell23_1334625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 8].length) (baseStart_1334625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334625 prefixEnd_1334625 := by exact prefixLift 1334625
  have htrace : WordTrace (prefixWord ++ tailWord_1334625) baseStart_1334625 baseEnd_1334625 := by
    simpa [prefixWord, tailWord_1334625, baseEnd_1334625] using wordTrace_append hprefix tailTrace_1334625
  have hstable : (prefixWord ++ tailWord_1334625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334625).length < 2 ^ (prefixWord ++ tailWord_1334625).sum := by decide
  have hdescent : baseEnd_1334625 < baseStart_1334625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334642 : List Nat := [3, 2, 1, 2, 1, 2, 1, 5, 6]
def baseStart_1334642 : Nat := 118140960795 + 1334642 * 2 ^ 59
def prefixEnd_1334642 : Nat := 4983230072969 + 3 ^ 40 * 1334642 * 2
def baseEnd_1334642 : Nat := 76145871964230271193011

theorem tailTrace_1334642 : CollatzResearch.WordTrace tailWord_1334642 prefixEnd_1334642 76145871964230271193011 := by
  unfold tailWord_1334642
  simp only [CollatzResearch.WordTrace]
  refine ⟨12169598207706861887895545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32452261887218298367721453 12169598207706861887895545)
  ·
    refine ⟨9127198655780146415921659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12169598207706861887895545 9127198655780146415921659)
    ·
      refine ⟨13690797983670219623882489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9127198655780146415921659 13690797983670219623882489)
      ·
        refine ⟨10268098487752664717911867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13690797983670219623882489 10268098487752664717911867)
        ·
          refine ⟨15402147731628997076867801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10268098487752664717911867 15402147731628997076867801)
          ·
            refine ⟨11551610798721747807650851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15402147731628997076867801 11551610798721747807650851)
            ·
              refine ⟨17327416198082621711476277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11551610798721747807650851 17327416198082621711476277)
              ·
                refine ⟨1624445268570245785450901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17327416198082621711476277 1624445268570245785450901)
                ·
                  refine ⟨76145871964230271193011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1624445268570245785450901 76145871964230271193011)
                  ·
                    rfl

theorem cell23_1334642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_1334642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334642 prefixEnd_1334642 := by exact prefixLift 1334642
  have htrace : WordTrace (prefixWord ++ tailWord_1334642) baseStart_1334642 baseEnd_1334642 := by
    simpa [prefixWord, tailWord_1334642, baseEnd_1334642] using wordTrace_append hprefix tailTrace_1334642
  have hstable : (prefixWord ++ tailWord_1334642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334642).length < 2 ^ (prefixWord ++ tailWord_1334642).sum := by decide
  have hdescent : baseEnd_1334642 < baseStart_1334642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334676 : List Nat := [2, 4, 2, 1, 2, 3, 1, 2, 6]
def baseStart_1334676 : Nat := 118140960795 + 1334676 * 2 ^ 59
def prefixEnd_1334676 : Nat := 4983230072969 + 3 ^ 40 * 1334676 * 2
def baseEnd_1334676 : Nat := 76147811780036145301327

theorem tailTrace_1334676 : CollatzResearch.WordTrace tailWord_1334676 prefixEnd_1334676 76147811780036145301327 := by
  unfold tailWord_1334676
  simp only [CollatzResearch.WordTrace]
  refine ⟨24339816456352135679159941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32453088608469514238879921 24339816456352135679159941)
  ·
    refine ⟨4563715585566025439842489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24339816456352135679159941 4563715585566025439842489)
    ·
      refine ⟨3422786689174519079881867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4563715585566025439842489 3422786689174519079881867)
      ·
        refine ⟨5134180033761778619822801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3422786689174519079881867 5134180033761778619822801)
        ·
          refine ⟨3850635025321333964867101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5134180033761778619822801 3850635025321333964867101)
          ·
            refine ⟨1443988134495500236825163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3850635025321333964867101 1443988134495500236825163)
            ·
              refine ⟨2165982201743250355237745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443988134495500236825163 2165982201743250355237745)
              ·
                refine ⟨1624486651307437766428309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165982201743250355237745 1624486651307437766428309)
                ·
                  refine ⟨76147811780036145301327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1624486651307437766428309 76147811780036145301327)
                  ·
                    rfl

theorem cell23_1334676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_1334676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334676 prefixEnd_1334676 := by exact prefixLift 1334676
  have htrace : WordTrace (prefixWord ++ tailWord_1334676) baseStart_1334676 baseEnd_1334676 := by
    simpa [prefixWord, tailWord_1334676, baseEnd_1334676] using wordTrace_append hprefix tailTrace_1334676
  have hstable : (prefixWord ++ tailWord_1334676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334676).length < 2 ^ (prefixWord ++ tailWord_1334676).sum := by decide
  have hdescent : baseEnd_1334676 < baseStart_1334676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334679 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 4, 3, 2]
def baseStart_1334679 : Nat := 118140960795 + 1334679 * 2 ^ 59
def prefixEnd_1334679 : Nat := 4983230072969 + 3 ^ 40 * 1334679 * 2
def baseEnd_1334679 : Nat := 685331846462288795974429

theorem tailTrace_1334679 : CollatzResearch.WordTrace tailWord_1334679 prefixEnd_1334679 685331846462288795974429 := by
  unfold tailWord_1334679
  simp only [CollatzResearch.WordTrace]
  refine ⟨48679742331693402870679091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32453161554462268580452727 48679742331693402870679091)
  ·
    refine ⟨73019613497540104306018637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48679742331693402870679091 73019613497540104306018637)
    ·
      refine ⟨27382355061577539114756989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73019613497540104306018637 27382355061577539114756989)
      ·
        refine ⟨10268383148091577168033871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27382355061577539114756989 10268383148091577168033871)
        ·
          refine ⟨15402574722137365752050807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10268383148091577168033871 15402574722137365752050807)
          ·
            refine ⟨23103862083206048628076211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15402574722137365752050807 23103862083206048628076211)
            ·
              refine ⟨34655793124809072942114317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23103862083206048628076211 34655793124809072942114317)
              ·
                refine ⟨12995922421803402353292869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34655793124809072942114317 12995922421803402353292869)
                ·
                  refine ⟨2436735454088137941242413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12995922421803402353292869 2436735454088137941242413)
                  ·
                    refine ⟨913775795283051727965905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2436735454088137941242413 913775795283051727965905)
                    ·
                      refine ⟨685331846462288795974429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 913775795283051727965905 685331846462288795974429)
                      ·
                        rfl

theorem cell23_1334679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_1334679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334679 prefixEnd_1334679 := by exact prefixLift 1334679
  have htrace : WordTrace (prefixWord ++ tailWord_1334679) baseStart_1334679 baseEnd_1334679 := by
    simpa [prefixWord, tailWord_1334679, baseEnd_1334679] using wordTrace_append hprefix tailTrace_1334679
  have hstable : (prefixWord ++ tailWord_1334679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334679).length < 2 ^ (prefixWord ++ tailWord_1334679).sum := by decide
  have hdescent : baseEnd_1334679 < baseStart_1334679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334732 : List Nat := [2, 2, 1, 4, 2, 1, 11]
def baseStart_1334732 : Nat := 118140960795 + 1334732 * 2 ^ 59
def prefixEnd_1334732 : Nat := 4983230072969 + 3 ^ 40 * 1334732 * 2
def baseEnd_1334732 : Nat := 8461222974530581340885

theorem tailTrace_1334732 : CollatzResearch.WordTrace tailWord_1334732 prefixEnd_1334732 8461222974530581340885 := by
  unfold tailWord_1334732
  simp only [CollatzResearch.WordTrace]
  refine ⟨24340837700250696461179225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32454450267000928614905633 24340837700250696461179225)
  ·
    refine ⟨18255628275188022345884419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24340837700250696461179225 18255628275188022345884419)
    ·
      refine ⟨27383442412782033518826629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18255628275188022345884419 27383442412782033518826629)
      ·
        refine ⟨5134395452396631284779993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27383442412782033518826629 5134395452396631284779993)
        ·
          refine ⟨3850796589297473463584995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5134395452396631284779993 3850796589297473463584995)
          ·
            refine ⟨5776194883946210195377493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3850796589297473463584995 5776194883946210195377493)
            ·
              refine ⟨8461222974530581340885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5776194883946210195377493 8461222974530581340885)
              ·
                rfl

theorem cell23_1334732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 11].length) (baseStart_1334732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334732 prefixEnd_1334732 := by exact prefixLift 1334732
  have htrace : WordTrace (prefixWord ++ tailWord_1334732) baseStart_1334732 baseEnd_1334732 := by
    simpa [prefixWord, tailWord_1334732, baseEnd_1334732] using wordTrace_append hprefix tailTrace_1334732
  have hstable : (prefixWord ++ tailWord_1334732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334732).length < 2 ^ (prefixWord ++ tailWord_1334732).sum := by decide
  have hdescent : baseEnd_1334732 < baseStart_1334732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334743 : List Nat := [1, 1, 3, 2, 1, 1, 1, 8, 1, 2, 2]
def baseStart_1334743 : Nat := 118140960795 + 1334743 * 2 ^ 59
def prefixEnd_1334743 : Nat := 4983230072969 + 3 ^ 40 * 1334743 * 2
def baseEnd_1334743 : Nat := 685364709224176545574135

theorem tailTrace_1334743 : CollatzResearch.WordTrace tailWord_1334743 prefixEnd_1334743 685364709224176545574135 := by
  unfold tailWord_1334743
  simp only [CollatzResearch.WordTrace]
  refine ⟨48682076603461541801008883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32454717735641027867339255 48682076603461541801008883)
  ·
    refine ⟨73023114905192312701513325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48682076603461541801008883 73023114905192312701513325)
    ·
      refine ⟨27383668089447117263067497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73023114905192312701513325 27383668089447117263067497)
      ·
        refine ⟨20537751067085337947300623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27383668089447117263067497 20537751067085337947300623)
        ·
          refine ⟨30806626600628006920950935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20537751067085337947300623 30806626600628006920950935)
          ·
            refine ⟨46209939900942010381426403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30806626600628006920950935 46209939900942010381426403)
            ·
              refine ⟨69314909851413015572139605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46209939900942010381426403 69314909851413015572139605)
              ·
                refine ⟨812284099821246276236011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 69314909851413015572139605 812284099821246276236011)
                ·
                  refine ⟨1218426149731869414354017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 812284099821246276236011 1218426149731869414354017)
                  ·
                    refine ⟨913819612298902060765513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1218426149731869414354017 913819612298902060765513)
                    ·
                      refine ⟨685364709224176545574135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 913819612298902060765513 685364709224176545574135)
                      ·
                        rfl

theorem cell23_1334743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_1334743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334743 prefixEnd_1334743 := by exact prefixLift 1334743
  have htrace : WordTrace (prefixWord ++ tailWord_1334743) baseStart_1334743 baseEnd_1334743 := by
    simpa [prefixWord, tailWord_1334743, baseEnd_1334743] using wordTrace_append hprefix tailTrace_1334743
  have hstable : (prefixWord ++ tailWord_1334743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334743).length < 2 ^ (prefixWord ++ tailWord_1334743).sum := by decide
  have hdescent : baseEnd_1334743 < baseStart_1334743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334749 : List Nat := [1, 4, 3, 1, 1, 3, 2, 8]
def baseStart_1334749 : Nat := 118140960795 + 1334749 * 2 ^ 59
def prefixEnd_1334749 : Nat := 4983230072969 + 3 ^ 40 * 1334749 * 2
def baseEnd_1334749 : Nat := 25383992226226056374041

theorem tailTrace_1334749 : CollatzResearch.WordTrace tailWord_1334749 prefixEnd_1334749 25383992226226056374041 := by
  unfold tailWord_1334749
  simp only [CollatzResearch.WordTrace]
  refine ⟨48682295441439804825727301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32454863627626536550484867 48682295441439804825727301)
  ·
    refine ⟨9127930395269963404823869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48682295441439804825727301 9127930395269963404823869)
    ·
      refine ⟨3422973898226236276808951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9127930395269963404823869 3422973898226236276808951)
      ·
        refine ⟨5134460847339354415213427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3422973898226236276808951 5134460847339354415213427)
        ·
          refine ⟨7701691271009031622820141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5134460847339354415213427 7701691271009031622820141)
          ·
            refine ⟨2888134226628386858557553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7701691271009031622820141 2888134226628386858557553)
            ·
              refine ⟨2166100669971290143918165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2888134226628386858557553 2166100669971290143918165)
              ·
                refine ⟨25383992226226056374041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2166100669971290143918165 25383992226226056374041)
                ·
                  rfl

theorem cell23_1334749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 8].length) (baseStart_1334749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334749 prefixEnd_1334749 := by exact prefixLift 1334749
  have htrace : WordTrace (prefixWord ++ tailWord_1334749) baseStart_1334749 baseEnd_1334749 := by
    simpa [prefixWord, tailWord_1334749, baseEnd_1334749] using wordTrace_append hprefix tailTrace_1334749
  have hstable : (prefixWord ++ tailWord_1334749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334749).length < 2 ^ (prefixWord ++ tailWord_1334749).sum := by decide
  have hdescent : baseEnd_1334749 < baseStart_1334749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334753 : List Nat := [1, 2, 3, 1, 2, 5, 2, 1, 2, 4]
def baseStart_1334753 : Nat := 118140960795 + 1334753 * 2 ^ 59
def prefixEnd_1334753 : Nat := 4983230072969 + 3 ^ 40 * 1334753 * 2
def baseEnd_1334753 : Nat := 228456614676907168816363

theorem tailTrace_1334753 : CollatzResearch.WordTrace tailWord_1334753 prefixEnd_1334753 228456614676907168816363 := by
  unfold tailWord_1334753
  simp only [CollatzResearch.WordTrace]
  refine ⟨48682441333425313508872913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32454960888950209005915275 48682441333425313508872913)
  ·
    refine ⟨36511831000068985131654685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48682441333425313508872913 36511831000068985131654685)
    ·
      refine ⟨13691936625025869424370507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36511831000068985131654685 13691936625025869424370507)
      ·
        refine ⟨20537904937538804136555761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13691936625025869424370507 20537904937538804136555761)
        ·
          refine ⟨15403428703154103102416821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20537904937538804136555761 15403428703154103102416821)
          ·
            refine ⟨1444071440920697165851577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15403428703154103102416821 1444071440920697165851577)
            ·
              refine ⟨1083053580690522874388683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1444071440920697165851577 1083053580690522874388683)
              ·
                refine ⟨1624580371035784311583025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083053580690522874388683 1624580371035784311583025)
                ·
                  refine ⟨1218435278276838233687269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1624580371035784311583025 1218435278276838233687269)
                  ·
                    refine ⟨228456614676907168816363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1218435278276838233687269 228456614676907168816363)
                    ·
                      rfl

theorem cell23_1334753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_1334753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334753 prefixEnd_1334753 := by exact prefixLift 1334753
  have htrace : WordTrace (prefixWord ++ tailWord_1334753) baseStart_1334753 baseEnd_1334753 := by
    simpa [prefixWord, tailWord_1334753, baseEnd_1334753] using wordTrace_append hprefix tailTrace_1334753
  have hstable : (prefixWord ++ tailWord_1334753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334753).length < 2 ^ (prefixWord ++ tailWord_1334753).sum := by decide
  have hdescent : baseEnd_1334753 < baseStart_1334753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334832 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 7]
def baseStart_1334832 : Nat := 118140960795 + 1334832 * 2 ^ 59
def prefixEnd_1334832 : Nat := 4983230072969 + 3 ^ 40 * 1334832 * 2
def baseEnd_1334832 : Nat := 685410409002426697361225

theorem tailTrace_1334832 : CollatzResearch.WordTrace tailWord_1334832 prefixEnd_1334832 685410409002426697361225 := by
  unfold tailWord_1334832
  simp only [CollatzResearch.WordTrace]
  refine ⟨24342661350069555000499375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32456881800092740000665833 24342661350069555000499375)
  ·
    refine ⟨36513992025104332500749063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24342661350069555000499375 36513992025104332500749063)
    ·
      refine ⟨54770988037656498751123595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36513992025104332500749063 54770988037656498751123595)
      ·
        refine ⟨82156482056484748126685393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54770988037656498751123595 82156482056484748126685393)
        ·
          refine ⟨61617361542363561095014045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82156482056484748126685393 61617361542363561095014045)
          ·
            refine ⟨23106510578386335410630267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61617361542363561095014045 23106510578386335410630267)
            ·
              refine ⟨34659765867579503115945401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23106510578386335410630267 34659765867579503115945401)
              ·
                refine ⟨25994824400684627336959051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34659765867579503115945401 25994824400684627336959051)
                ·
                  refine ⟨38992236601026941005438577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25994824400684627336959051 38992236601026941005438577)
                  ·
                    refine ⟨29244177450770205754078933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38992236601026941005438577 29244177450770205754078933)
                    ·
                      refine ⟨685410409002426697361225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29244177450770205754078933 685410409002426697361225)
                      ·
                        rfl

theorem cell23_1334832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_1334832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334832 prefixEnd_1334832 := by exact prefixLift 1334832
  have htrace : WordTrace (prefixWord ++ tailWord_1334832) baseStart_1334832 baseEnd_1334832 := by
    simpa [prefixWord, tailWord_1334832, baseEnd_1334832] using wordTrace_append hprefix tailTrace_1334832
  have hstable : (prefixWord ++ tailWord_1334832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334832).length < 2 ^ (prefixWord ++ tailWord_1334832).sum := by decide
  have hdescent : baseEnd_1334832 < baseStart_1334832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334866 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_1334866 : Nat := 118140960795 + 1334866 * 2 ^ 59
def prefixEnd_1334866 : Nat := 4983230072969 + 3 ^ 40 * 1334866 * 2
def baseEnd_1334866 : Nat := 685427867344679564336069

theorem tailTrace_1334866 : CollatzResearch.WordTrace tailWord_1334866 prefixEnd_1334866 685427867344679564336069 := by
  unfold tailWord_1334866
  simp only [CollatzResearch.WordTrace]
  refine ⟨12171640695503983451934113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32457708521343955871824301 12171640695503983451934113)
  ·
    refine ⟨9128730521627987588950585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12171640695503983451934113 9128730521627987588950585)
    ·
      refine ⟨6846547891220990691712939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9128730521627987588950585 6846547891220990691712939)
      ·
        refine ⟨10269821836831486037569409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6846547891220990691712939 10269821836831486037569409)
        ·
          refine ⟨7702366377623614528177057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10269821836831486037569409 7702366377623614528177057)
          ·
            refine ⟨5776774783217710896132793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7702366377623614528177057 5776774783217710896132793)
            ·
              refine ⟨4332581087413283172099595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5776774783217710896132793 4332581087413283172099595)
              ·
                refine ⟨6498871631119924758149393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4332581087413283172099595 6498871631119924758149393)
                ·
                  refine ⟨4874153723339943568612045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6498871631119924758149393 4874153723339943568612045)
                  ·
                    refine ⟨1827807646252478838229517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4874153723339943568612045 1827807646252478838229517)
                    ·
                      refine ⟨685427867344679564336069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1827807646252478838229517 685427867344679564336069)
                      ·
                        rfl

theorem cell23_1334866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_1334866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334866 prefixEnd_1334866 := by exact prefixLift 1334866
  have htrace : WordTrace (prefixWord ++ tailWord_1334866) baseStart_1334866 baseEnd_1334866 := by
    simpa [prefixWord, tailWord_1334866, baseEnd_1334866] using wordTrace_append hprefix tailTrace_1334866
  have hstable : (prefixWord ++ tailWord_1334866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334866).length < 2 ^ (prefixWord ++ tailWord_1334866).sum := by decide
  have hdescent : baseEnd_1334866 < baseStart_1334866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334889 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 1, 3, 4]
def baseStart_1334889 : Nat := 118140960795 + 1334889 * 2 ^ 59
def prefixEnd_1334889 : Nat := 4983230072969 + 3 ^ 40 * 1334889 * 2
def baseEnd_1334889 : Nat := 685439677399732974348463

theorem tailTrace_1334889 : CollatzResearch.WordTrace tailWord_1334889 prefixEnd_1334889 685439677399732974348463 := by
  unfold tailWord_1334889
  simp only [CollatzResearch.WordTrace]
  refine ⟨48687401660932608735823721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32458267773955072490549147 48687401660932608735823721)
  ·
    refine ⟨36515551245699456551867791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48687401660932608735823721 36515551245699456551867791)
    ·
      refine ⟨54773326868549184827801687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36515551245699456551867791 54773326868549184827801687)
      ·
        refine ⟨82159990302823777241702531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54773326868549184827801687 82159990302823777241702531)
        ·
          refine ⟨123239985454235665862553797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82159990302823777241702531 123239985454235665862553797)
          ·
            refine ⟨23107497272669187349228837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123239985454235665862553797 23107497272669187349228837)
            ·
              refine ⟨4332655738625472627980407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23107497272669187349228837 4332655738625472627980407)
              ·
                refine ⟨6498983607938208941970611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4332655738625472627980407 6498983607938208941970611)
                ·
                  refine ⟨9748475411907313412955917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6498983607938208941970611 9748475411907313412955917)
                  ·
                    refine ⟨3655678279465242529858469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9748475411907313412955917 3655678279465242529858469)
                    ·
                      refine ⟨685439677399732974348463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3655678279465242529858469 685439677399732974348463)
                      ·
                        rfl

theorem cell23_1334889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_1334889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334889 prefixEnd_1334889 := by exact prefixLift 1334889
  have htrace : WordTrace (prefixWord ++ tailWord_1334889) baseStart_1334889 baseEnd_1334889 := by
    simpa [prefixWord, tailWord_1334889, baseEnd_1334889] using wordTrace_append hprefix tailTrace_1334889
  have hstable : (prefixWord ++ tailWord_1334889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334889).length < 2 ^ (prefixWord ++ tailWord_1334889).sum := by decide
  have hdescent : baseEnd_1334889 < baseStart_1334889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334906 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2]
def baseStart_1334906 : Nat := 118140960795 + 1334906 * 2 ^ 59
def prefixEnd_1334906 : Nat := 4983230072969 + 3 ^ 40 * 1334906 * 2
def baseEnd_1334906 : Nat := 685448406570859407835885

theorem tailTrace_1334906 : CollatzResearch.WordTrace tailWord_1334906 prefixEnd_1334906 685448406570859407835885 := by
  unfold tailWord_1334906
  simp only [CollatzResearch.WordTrace]
  refine ⟨12172005425467755159798143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32458681134580680426128381 12172005425467755159798143)
  ·
    refine ⟨18258008138201632739697215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12172005425467755159798143 18258008138201632739697215)
    ·
      refine ⟨27387012207302449109545823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18258008138201632739697215 27387012207302449109545823)
      ·
        refine ⟨41080518310953673664318735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27387012207302449109545823 41080518310953673664318735)
        ·
          refine ⟨61620777466430510496478103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41080518310953673664318735 61620777466430510496478103)
          ·
            refine ⟨92431166199645765744717155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61620777466430510496478103 92431166199645765744717155)
            ·
              refine ⟨138646749299468648617075733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92431166199645765744717155 138646749299468648617075733)
              ·
                refine ⟨6499066373412592903925425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 138646749299468648617075733 6499066373412592903925425)
                ·
                  refine ⟨4874299780059444677944069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6499066373412592903925425 4874299780059444677944069)
                  ·
                    refine ⟨913931208761145877114513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4874299780059444677944069 913931208761145877114513)
                    ·
                      refine ⟨685448406570859407835885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 913931208761145877114513 685448406570859407835885)
                      ·
                        rfl

theorem cell23_1334906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2].length) (baseStart_1334906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334906 prefixEnd_1334906 := by exact prefixLift 1334906
  have htrace : WordTrace (prefixWord ++ tailWord_1334906) baseStart_1334906 baseEnd_1334906 := by
    simpa [prefixWord, tailWord_1334906, baseEnd_1334906] using wordTrace_append hprefix tailTrace_1334906
  have hstable : (prefixWord ++ tailWord_1334906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334906).length < 2 ^ (prefixWord ++ tailWord_1334906).sum := by decide
  have hdescent : baseEnd_1334906 < baseStart_1334906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334967 : List Nat := [1, 1, 3, 1, 5, 3, 2, 2, 1, 4]
def baseStart_1334967 : Nat := 118140960795 + 1334967 * 2 ^ 59
def prefixEnd_1334967 : Nat := 4983230072969 + 3 ^ 40 * 1334967 * 2
def baseEnd_1334967 : Nat := 228493242963594556391035

theorem tailTrace_1334967 : CollatzResearch.WordTrace tailWord_1334967 prefixEnd_1334967 228493242963594556391035 := by
  unfold tailWord_1334967
  simp only [CollatzResearch.WordTrace]
  refine ⟨48690246554650028057163155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32460164369766685371442103 48690246554650028057163155)
  ·
    refine ⟨73035369831975042085744733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48690246554650028057163155 73035369831975042085744733)
    ·
      refine ⟨27388263686990640782154275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73035369831975042085744733 27388263686990640782154275)
      ·
        refine ⟨41082395530485961173231413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27388263686990640782154275 41082395530485961173231413)
        ·
          refine ⟨3851474580983058859990445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41082395530485961173231413 3851474580983058859990445)
          ·
            refine ⟨1444302967868647072496417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3851474580983058859990445 1444302967868647072496417)
            ·
              refine ⟨1083227225901485304372313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1444302967868647072496417 1083227225901485304372313)
              ·
                refine ⟨812420419426113978279235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1083227225901485304372313 812420419426113978279235)
                ·
                  refine ⟨1218630629139170967418853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 812420419426113978279235 1218630629139170967418853)
                  ·
                    refine ⟨228493242963594556391035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1218630629139170967418853 228493242963594556391035)
                    ·
                      rfl

theorem cell23_1334967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 1, 4].length) (baseStart_1334967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334967 prefixEnd_1334967 := by exact prefixLift 1334967
  have htrace : WordTrace (prefixWord ++ tailWord_1334967) baseStart_1334967 baseEnd_1334967 := by
    simpa [prefixWord, tailWord_1334967, baseEnd_1334967] using wordTrace_append hprefix tailTrace_1334967
  have hstable : (prefixWord ++ tailWord_1334967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334967).length < 2 ^ (prefixWord ++ tailWord_1334967).sum := by decide
  have hdescent : baseEnd_1334967 < baseStart_1334967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334973 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 3, 1, 3]
def baseStart_1334973 : Nat := 118140960795 + 1334973 * 2 ^ 59
def prefixEnd_1334973 : Nat := 4983230072969 + 3 ^ 40 * 1334973 * 2
def baseEnd_1334973 : Nat := 685482809774710645698077

theorem tailTrace_1334973 : CollatzResearch.WordTrace tailWord_1334973 prefixEnd_1334973 685482809774710645698077 := by
  unfold tailWord_1334973
  simp only [CollatzResearch.WordTrace]
  refine ⟨48690465392628291081881573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32460310261752194054587715 48690465392628291081881573)
  ·
    refine ⟨9129462261117804577852795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48690465392628291081881573 9129462261117804577852795)
    ·
      refine ⟨13694193391676706866779193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9129462261117804577852795 13694193391676706866779193)
      ·
        refine ⟨10270645043757530150084395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13694193391676706866779193 10270645043757530150084395)
        ·
          refine ⟨15405967565636295225126593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10270645043757530150084395 15405967565636295225126593)
          ·
            refine ⟨11554475674227221418844945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15405967565636295225126593 11554475674227221418844945)
            ·
              refine ⟨8665856755670416064133709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11554475674227221418844945 8665856755670416064133709)
              ·
                refine ⟨3249696283376406024050141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8665856755670416064133709 3249696283376406024050141)
                ·
                  refine ⟨1218636106266152259018803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3249696283376406024050141 1218636106266152259018803)
                  ·
                    refine ⟨1827954159399228388528205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1218636106266152259018803 1827954159399228388528205)
                    ·
                      refine ⟨685482809774710645698077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1827954159399228388528205 685482809774710645698077)
                      ·
                        rfl

theorem cell23_1334973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_1334973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1334973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1334973 prefixEnd_1334973 := by exact prefixLift 1334973
  have htrace : WordTrace (prefixWord ++ tailWord_1334973) baseStart_1334973 baseEnd_1334973 := by
    simpa [prefixWord, tailWord_1334973, baseEnd_1334973] using wordTrace_append hprefix tailTrace_1334973
  have hstable : (prefixWord ++ tailWord_1334973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334973).length < 2 ^ (prefixWord ++ tailWord_1334973).sum := by decide
  have hdescent : baseEnd_1334973 < baseStart_1334973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335013 : List Nat := [1, 3, 1, 4, 1, 1, 3, 3, 1, 1, 4]
def baseStart_1335013 : Nat := 118140960795 + 1335013 * 2 ^ 59
def prefixEnd_1335013 : Nat := 4983230072969 + 3 ^ 40 * 1335013 * 2
def baseEnd_1335013 : Nat := 685503349000890489197893

theorem tailTrace_1335013 : CollatzResearch.WordTrace tailWord_1335013 prefixEnd_1335013 685503349000890489197893 := by
  unfold tailWord_1335013
  simp only [CollatzResearch.WordTrace]
  refine ⟨48691924312483377913337693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32461282874988918608891795 48691924312483377913337693)
  ·
    refine ⟨18259471617181266717501635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48691924312483377913337693 18259471617181266717501635)
    ·
      refine ⟨27389207425771900076252453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18259471617181266717501635 27389207425771900076252453)
      ·
        refine ⟨5135476392332231264297335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27389207425771900076252453 5135476392332231264297335)
        ·
          refine ⟨7703214588498346896446003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5135476392332231264297335 7703214588498346896446003)
          ·
            refine ⟨11554821882747520344669005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7703214588498346896446003 11554821882747520344669005)
            ·
              refine ⟨4333058206030320129250877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11554821882747520344669005 4333058206030320129250877)
              ·
                refine ⟨1624896827261370048469079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4333058206030320129250877 1624896827261370048469079)
                ·
                  refine ⟨2437345240892055072703619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1624896827261370048469079 2437345240892055072703619)
                  ·
                    refine ⟨3656017861338082609055429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2437345240892055072703619 3656017861338082609055429)
                    ·
                      refine ⟨685503349000890489197893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3656017861338082609055429 685503349000890489197893)
                      ·
                        rfl

theorem cell23_1335013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_1335013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335013 prefixEnd_1335013 := by exact prefixLift 1335013
  have htrace : WordTrace (prefixWord ++ tailWord_1335013) baseStart_1335013 baseEnd_1335013 := by
    simpa [prefixWord, tailWord_1335013, baseEnd_1335013] using wordTrace_append hprefix tailTrace_1335013
  have hstable : (prefixWord ++ tailWord_1335013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335013).length < 2 ^ (prefixWord ++ tailWord_1335013).sum := by decide
  have hdescent : baseEnd_1335013 < baseStart_1335013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335026 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1335026 : Nat := 118140960795 + 1335026 * 2 ^ 59
def prefixEnd_1335026 : Nat := 4983230072969 + 3 ^ 40 * 1335026 * 2
def baseEnd_1335026 : Nat := 685510024249398938335333

theorem tailTrace_1335026 : CollatzResearch.WordTrace tailWord_1335026 prefixEnd_1335026 685510024249398938335333 := by
  unfold tailWord_1335026
  simp only [CollatzResearch.WordTrace]
  refine ⟨12173099615359070283390233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32461598974290854089040621 12173099615359070283390233)
  ·
    refine ⟨9129824711519302712542675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12173099615359070283390233 9129824711519302712542675)
    ·
      refine ⟨13694737067278954068814013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9129824711519302712542675 13694737067278954068814013)
      ·
        refine ⟨5135526400229607775805255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13694737067278954068814013 5135526400229607775805255)
        ·
          refine ⟨7703289600344411663707883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5135526400229607775805255 7703289600344411663707883)
          ·
            refine ⟨11554934400516617495561825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7703289600344411663707883 11554934400516617495561825)
            ·
              refine ⟨8666200800387463121671369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11554934400516617495561825 8666200800387463121671369)
              ·
                refine ⟨6499650600290597341253527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8666200800387463121671369 6499650600290597341253527)
                ·
                  refine ⟨9749475900435896011880291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6499650600290597341253527 9749475900435896011880291)
                  ·
                    refine ⟨14624213850653844017820437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9749475900435896011880291 14624213850653844017820437)
                    ·
                      refine ⟨685510024249398938335333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14624213850653844017820437 685510024249398938335333)
                      ·
                        rfl

theorem cell23_1335026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1335026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335026 prefixEnd_1335026 := by exact prefixLift 1335026
  have htrace : WordTrace (prefixWord ++ tailWord_1335026) baseStart_1335026 baseEnd_1335026 := by
    simpa [prefixWord, tailWord_1335026, baseEnd_1335026] using wordTrace_append hprefix tailTrace_1335026
  have hstable : (prefixWord ++ tailWord_1335026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335026).length < 2 ^ (prefixWord ++ tailWord_1335026).sum := by decide
  have hdescent : baseEnd_1335026 < baseStart_1335026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335050 : List Nat := [3, 1, 2, 2, 1, 4, 2, 2, 1, 2, 3]
def baseStart_1335050 : Nat := 118140960795 + 1335050 * 2 ^ 59
def prefixEnd_1335050 : Nat := 4983230072969 + 3 ^ 40 * 1335050 * 2
def baseEnd_1335050 : Nat := 685522347785106844435223

theorem tailTrace_1335050 : CollatzResearch.WordTrace tailWord_1335050 prefixEnd_1335050 685522347785106844435223 := by
  unfold tailWord_1335050
  simp only [CollatzResearch.WordTrace]
  refine ⟨12173318453337333308108651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32462182542232888821623069 12173318453337333308108651)
  ·
    refine ⟨18259977680005999962162977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12173318453337333308108651 18259977680005999962162977)
    ·
      refine ⟨13694983260004499971622233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18259977680005999962162977 13694983260004499971622233)
      ·
        refine ⟨10271237445003374978716675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13694983260004499971622233 10271237445003374978716675)
        ·
          refine ⟨15406856167505062468075013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10271237445003374978716675 15406856167505062468075013)
          ·
            refine ⟨2888785531407199212764065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15406856167505062468075013 2888785531407199212764065)
            ·
              refine ⟨2166589148555399409573049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2888785531407199212764065 2166589148555399409573049)
              ·
                refine ⟨1624941861416549557179787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2166589148555399409573049 1624941861416549557179787)
                ·
                  refine ⟨2437412792124824335769681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1624941861416549557179787 2437412792124824335769681)
                  ·
                    refine ⟨1828059594093618251827261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2437412792124824335769681 1828059594093618251827261)
                    ·
                      refine ⟨685522347785106844435223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1828059594093618251827261 685522347785106844435223)
                      ·
                        rfl

theorem cell23_1335050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_1335050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335050 prefixEnd_1335050 := by exact prefixLift 1335050
  have htrace : WordTrace (prefixWord ++ tailWord_1335050) baseStart_1335050 baseEnd_1335050 := by
    simpa [prefixWord, tailWord_1335050, baseEnd_1335050] using wordTrace_append hprefix tailTrace_1335050
  have hstable : (prefixWord ++ tailWord_1335050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335050).length < 2 ^ (prefixWord ++ tailWord_1335050).sum := by decide
  have hdescent : baseEnd_1335050 < baseStart_1335050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335080 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_1335080 : Nat := 118140960795 + 1335080 * 2 ^ 59
def prefixEnd_1335080 : Nat := 4983230072969 + 3 ^ 40 * 1335080 * 2
def baseEnd_1335080 : Nat := 685537752204741727060085

theorem tailTrace_1335080 : CollatzResearch.WordTrace tailWord_1335080 prefixEnd_1335080 685537752204741727060085 := by
  unfold tailWord_1335080
  simp only [CollatzResearch.WordTrace]
  refine ⟨24347184001620324178013347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32462912002160432237351129 24347184001620324178013347)
  ·
    refine ⟨36520776002430486267020021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24347184001620324178013347 36520776002430486267020021)
    ·
      refine ⟨3423822750227858087533127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36520776002430486267020021 3423822750227858087533127)
      ·
        refine ⟨5135734125341787131299691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3423822750227858087533127 5135734125341787131299691)
        ·
          refine ⟨7703601188012680696949537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5135734125341787131299691 7703601188012680696949537)
          ·
            refine ⟨5777700891009510522712153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7703601188012680696949537 5777700891009510522712153)
            ·
              refine ⟨4333275668257132892034115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5777700891009510522712153 4333275668257132892034115)
              ·
                refine ⟨6499913502385699338051173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4333275668257132892034115 6499913502385699338051173)
                ·
                  refine ⟨1218733781697318625884595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6499913502385699338051173 1218733781697318625884595)
                  ·
                    refine ⟨1828100672545977938826893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1218733781697318625884595 1828100672545977938826893)
                    ·
                      refine ⟨685537752204741727060085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1828100672545977938826893 685537752204741727060085)
                      ·
                        rfl

theorem cell23_1335080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_1335080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335080 prefixEnd_1335080 := by exact prefixLift 1335080
  have htrace : WordTrace (prefixWord ++ tailWord_1335080) baseStart_1335080 baseEnd_1335080 := by
    simpa [prefixWord, tailWord_1335080, baseEnd_1335080] using wordTrace_append hprefix tailTrace_1335080
  have hstable : (prefixWord ++ tailWord_1335080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335080).length < 2 ^ (prefixWord ++ tailWord_1335080).sum := by decide
  have hdescent : baseEnd_1335080 < baseStart_1335080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335107 : List Nat := [1, 1, 1, 3, 1, 7, 1, 2, 1, 3, 2]
def baseStart_1335107 : Nat := 118140960795 + 1335107 * 2 ^ 59
def prefixEnd_1335107 : Nat := 4983230072969 + 3 ^ 40 * 1335107 * 2
def baseEnd_1335107 : Nat := 685551616182413121422461

theorem tailTrace_1335107 : CollatzResearch.WordTrace tailWord_1335107 prefixEnd_1335107 685551616182413121422461 := by
  unfold tailWord_1335107
  simp only [CollatzResearch.WordTrace]
  refine ⟨48695352774142831967259575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32463568516095221311506383 48695352774142831967259575)
  ·
    refine ⟨73043029161214247950889363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48695352774142831967259575 73043029161214247950889363)
    ·
      refine ⟨109564543741821371926334045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73043029161214247950889363 109564543741821371926334045)
      ·
        refine ⟨41086703903183014472375267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109564543741821371926334045 41086703903183014472375267)
        ·
          refine ⟨61630055854774521708562901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41086703903183014472375267 61630055854774521708562901)
          ·
            refine ⟨1444454434096277852544443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 61630055854774521708562901 1444454434096277852544443)
            ·
              refine ⟨2166681651144416778816665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1444454434096277852544443 2166681651144416778816665)
              ·
                refine ⟨1625011238358312584112499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2166681651144416778816665 1625011238358312584112499)
                ·
                  refine ⟨2437516857537468876168749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625011238358312584112499 2437516857537468876168749)
                  ·
                    refine ⟨914068821576550828563281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2437516857537468876168749 914068821576550828563281)
                    ·
                      refine ⟨685551616182413121422461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 914068821576550828563281 685551616182413121422461)
                      ·
                        rfl

theorem cell23_1335107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 3, 2].length) (baseStart_1335107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335107 prefixEnd_1335107 := by exact prefixLift 1335107
  have htrace : WordTrace (prefixWord ++ tailWord_1335107) baseStart_1335107 baseEnd_1335107 := by
    simpa [prefixWord, tailWord_1335107, baseEnd_1335107] using wordTrace_append hprefix tailTrace_1335107
  have hstable : (prefixWord ++ tailWord_1335107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335107).length < 2 ^ (prefixWord ++ tailWord_1335107).sum := by decide
  have hdescent : baseEnd_1335107 < baseStart_1335107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335124 : List Nat := [2, 4, 1, 1, 3, 2, 3, 1, 1, 3, 2]
def baseStart_1335124 : Nat := 118140960795 + 1335124 * 2 ^ 59
def prefixEnd_1335124 : Nat := 4983230072969 + 3 ^ 40 * 1335124 * 2
def baseEnd_1335124 : Nat := 685560345353539554909883

theorem tailTrace_1335124 : CollatzResearch.WordTrace tailWord_1335124 prefixEnd_1335124 685560345353539554909883 := by
  unfold tailWord_1335124
  simp only [CollatzResearch.WordTrace]
  refine ⟨24347986407540621935314213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32463981876720829247085617 24347986407540621935314213)
  ·
    refine ⟨4565247451413866612871415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24347986407540621935314213 4565247451413866612871415)
    ·
      refine ⟨6847871177120799919307123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4565247451413866612871415 6847871177120799919307123)
      ·
        refine ⟨10271806765681199878960685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6847871177120799919307123 10271806765681199878960685)
        ·
          refine ⟨3851927537130449954610257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10271806765681199878960685 3851927537130449954610257)
          ·
            refine ⟨2888945652847837465957693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3851927537130449954610257 2888945652847837465957693)
            ·
              refine ⟨1083354619817939049734135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2888945652847837465957693 1083354619817939049734135)
              ·
                refine ⟨1625031929726908574601203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083354619817939049734135 1625031929726908574601203)
                ·
                  refine ⟨2437547894590362861901805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625031929726908574601203 2437547894590362861901805)
                  ·
                    refine ⟨914080460471386073213177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2437547894590362861901805 914080460471386073213177)
                    ·
                      refine ⟨685560345353539554909883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 914080460471386073213177 685560345353539554909883)
                      ·
                        rfl

theorem cell23_1335124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_1335124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335124 prefixEnd_1335124 := by exact prefixLift 1335124
  have htrace : WordTrace (prefixWord ++ tailWord_1335124) baseStart_1335124 baseEnd_1335124 := by
    simpa [prefixWord, tailWord_1335124, baseEnd_1335124] using wordTrace_append hprefix tailTrace_1335124
  have hstable : (prefixWord ++ tailWord_1335124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335124).length < 2 ^ (prefixWord ++ tailWord_1335124).sum := by decide
  have hdescent : baseEnd_1335124 < baseStart_1335124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335137 : List Nat := [1, 2, 3, 1, 1, 1, 6, 2, 2, 2, 2]
def baseStart_1335137 : Nat := 118140960795 + 1335137 * 2 ^ 59
def prefixEnd_1335137 : Nat := 4983230072969 + 3 ^ 40 * 1335137 * 2
def baseEnd_1335137 : Nat := 685567020602048004047323

theorem tailTrace_1335137 : CollatzResearch.WordTrace tailWord_1335137 prefixEnd_1335137 685567020602048004047323 := by
  unfold tailWord_1335137
  simp only [CollatzResearch.WordTrace]
  refine ⟨48696446964034147090851665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32464297976022764727234443 48696446964034147090851665)
  ·
    refine ⟨36522335223025610318138749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48696446964034147090851665 36522335223025610318138749)
    ·
      refine ⟨13695875708634603869302031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36522335223025610318138749 13695875708634603869302031)
      ·
        refine ⟨20543813562951905803953047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13695875708634603869302031 20543813562951905803953047)
        ·
          refine ⟨30815720344427858705929571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20543813562951905803953047 30815720344427858705929571)
          ·
            refine ⟨46223580516641788058894357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30815720344427858705929571 46223580516641788058894357)
            ·
              refine ⟨2166730336717583815260673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46223580516641788058894357 2166730336717583815260673)
              ·
                refine ⟨1625047752538187861445505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2166730336717583815260673 1625047752538187861445505)
                ·
                  refine ⟨1218785814403640896084129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1625047752538187861445505 1218785814403640896084129)
                  ·
                    refine ⟨914089360802730672063097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1218785814403640896084129 914089360802730672063097)
                    ·
                      refine ⟨685567020602048004047323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 914089360802730672063097 685567020602048004047323)
                      ·
                        rfl

theorem cell23_1335137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_1335137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335137 prefixEnd_1335137 := by exact prefixLift 1335137
  have htrace : WordTrace (prefixWord ++ tailWord_1335137) baseStart_1335137 baseEnd_1335137 := by
    simpa [prefixWord, tailWord_1335137, baseEnd_1335137] using wordTrace_append hprefix tailTrace_1335137
  have hstable : (prefixWord ++ tailWord_1335137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335137).length < 2 ^ (prefixWord ++ tailWord_1335137).sum := by decide
  have hdescent : baseEnd_1335137 < baseStart_1335137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335150 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1335150 : Nat := 118140960795 + 1335150 * 2 ^ 59
def prefixEnd_1335150 : Nat := 4983230072969 + 3 ^ 40 * 1335150 * 2
def baseEnd_1335150 : Nat := 685573695850556453184763

theorem tailTrace_1335150 : CollatzResearch.WordTrace tailWord_1335150 prefixEnd_1335150 685573695850556453184763 := by
  unfold tailWord_1335150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6087115139123381288884363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32464614075324700207383269 6087115139123381288884363)
  ·
    refine ⟨9130672708685071933326545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6087115139123381288884363 9130672708685071933326545)
    ·
      refine ⟨6848004531513803949994909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9130672708685071933326545 6848004531513803949994909)
      ·
        refine ⟨2568001699317676481248091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6848004531513803949994909 2568001699317676481248091)
        ·
          refine ⟨3852002548976514721872137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2568001699317676481248091 3852002548976514721872137)
          ·
            refine ⟨2889001911732386041404103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3852002548976514721872137 2889001911732386041404103)
            ·
              refine ⟨4333502867598579062106155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2889001911732386041404103 4333502867598579062106155)
              ·
                refine ⟨6500254301397868593159233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4333502867598579062106155 6500254301397868593159233)
                ·
                  refine ⟨4875190726048401444869425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6500254301397868593159233 4875190726048401444869425)
                  ·
                    refine ⟨3656393044536301083652069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4875190726048401444869425 3656393044536301083652069)
                    ·
                      refine ⟨685573695850556453184763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3656393044536301083652069 685573695850556453184763)
                      ·
                        rfl

theorem cell23_1335150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1335150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335150 prefixEnd_1335150 := by exact prefixLift 1335150
  have htrace : WordTrace (prefixWord ++ tailWord_1335150) baseStart_1335150 baseEnd_1335150 := by
    simpa [prefixWord, tailWord_1335150, baseEnd_1335150] using wordTrace_append hprefix tailTrace_1335150
  have hstable : (prefixWord ++ tailWord_1335150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335150).length < 2 ^ (prefixWord ++ tailWord_1335150).sum := by decide
  have hdescent : baseEnd_1335150 < baseStart_1335150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335153 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 2, 3, 3]
def baseStart_1335153 : Nat := 118140960795 + 1335153 * 2 ^ 59
def prefixEnd_1335153 : Nat := 4983230072969 + 3 ^ 40 * 1335153 * 2
def baseEnd_1335153 : Nat := 685575236292519941447249

theorem tailTrace_1335153 : CollatzResearch.WordTrace tailWord_1335153 prefixEnd_1335153 685575236292519941447249 := by
  unfold tailWord_1335153
  simp only [CollatzResearch.WordTrace]
  refine ⟨48697030531976181823434113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32464687021317454548956075 48697030531976181823434113)
  ·
    refine ⟨36522772898982136367575585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48697030531976181823434113 36522772898982136367575585)
    ·
      refine ⟨27392079674236602275681689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36522772898982136367575585 27392079674236602275681689)
      ·
        refine ⟨20544059755677451706761267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27392079674236602275681689 20544059755677451706761267)
        ·
          refine ⟨30816089633516177560141901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20544059755677451706761267 30816089633516177560141901)
          ·
            refine ⟨11556033612568566585053213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30816089633516177560141901 11556033612568566585053213)
            ·
              refine ⟨4333512604713212469394955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11556033612568566585053213 4333512604713212469394955)
              ·
                refine ⟨6500268907069818704092433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4333512604713212469394955 6500268907069818704092433)
                ·
                  refine ⟨4875201680302364028069325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6500268907069818704092433 4875201680302364028069325)
                  ·
                    refine ⟨1828200630113386510525997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4875201680302364028069325 1828200630113386510525997)
                    ·
                      refine ⟨685575236292519941447249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1828200630113386510525997 685575236292519941447249)
                      ·
                        rfl

theorem cell23_1335153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_1335153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335153 prefixEnd_1335153 := by exact prefixLift 1335153
  have htrace : WordTrace (prefixWord ++ tailWord_1335153) baseStart_1335153 baseEnd_1335153 := by
    simpa [prefixWord, tailWord_1335153, baseEnd_1335153] using wordTrace_append hprefix tailTrace_1335153
  have hstable : (prefixWord ++ tailWord_1335153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335153).length < 2 ^ (prefixWord ++ tailWord_1335153).sum := by decide
  have hdescent : baseEnd_1335153 < baseStart_1335153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335163 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 4, 5, 2]
def baseStart_1335163 : Nat := 118140960795 + 1335163 * 2 ^ 59
def prefixEnd_1335163 : Nat := 4983230072969 + 3 ^ 40 * 1335163 * 2
def baseEnd_1335163 : Nat := 685580371099064902322203

theorem tailTrace_1335163 : CollatzResearch.WordTrace tailWord_1335163 prefixEnd_1335163 685580371099064902322203 := by
  unfold tailWord_1335163
  simp only [CollatzResearch.WordTrace]
  refine ⟨48697395261939953531298143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32464930174626635687532095 48697395261939953531298143)
  ·
    refine ⟨73046092892909930296947215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48697395261939953531298143 73046092892909930296947215)
    ·
      refine ⟨109569139339364895445420823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73046092892909930296947215 109569139339364895445420823)
      ·
        refine ⟨164353709009047343168131235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109569139339364895445420823 164353709009047343168131235)
        ·
          refine ⟨246530563513571014752196853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164353709009047343168131235 246530563513571014752196853)
          ·
            refine ⟨23112240329397282633018455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 246530563513571014752196853 23112240329397282633018455)
            ·
              refine ⟨34668360494095923949527683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23112240329397282633018455 34668360494095923949527683)
              ·
                refine ⟨52002540741143885924291525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34668360494095923949527683 52002540741143885924291525)
                ·
                  refine ⟨9750476388964478610804661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52002540741143885924291525 9750476388964478610804661)
                  ·
                    refine ⟨914107161465419869762937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9750476388964478610804661 914107161465419869762937)
                    ·
                      refine ⟨685580371099064902322203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 914107161465419869762937 685580371099064902322203)
                      ·
                        rfl

theorem cell23_1335163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 5, 2].length) (baseStart_1335163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335163 prefixEnd_1335163 := by exact prefixLift 1335163
  have htrace : WordTrace (prefixWord ++ tailWord_1335163) baseStart_1335163 baseEnd_1335163 := by
    simpa [prefixWord, tailWord_1335163, baseEnd_1335163] using wordTrace_append hprefix tailTrace_1335163
  have hstable : (prefixWord ++ tailWord_1335163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335163).length < 2 ^ (prefixWord ++ tailWord_1335163).sum := by decide
  have hdescent : baseEnd_1335163 < baseStart_1335163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335193 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 2, 1, 4]
def baseStart_1335193 : Nat := 118140960795 + 1335193 * 2 ^ 59
def prefixEnd_1335193 : Nat := 4983230072969 + 3 ^ 40 * 1335193 * 2
def baseEnd_1335193 : Nat := 685595775518699784947065

theorem tailTrace_1335193 : CollatzResearch.WordTrace tailWord_1335193 prefixEnd_1335193 685595775518699784947065 := by
  unfold tailWord_1335193
  simp only [CollatzResearch.WordTrace]
  refine ⟨48698489451831268654890233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32465659634554179103260155 48698489451831268654890233)
  ·
    refine ⟨36523867088873451491167675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48698489451831268654890233 36523867088873451491167675)
    ·
      refine ⟨54785800633310177236751513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36523867088873451491167675 54785800633310177236751513)
      ·
        refine ⟨41089350474982632927563635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54785800633310177236751513 41089350474982632927563635)
        ·
          refine ⟨61634025712473949391345453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41089350474982632927563635 61634025712473949391345453)
          ·
            refine ⟨23112759642177731021754545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61634025712473949391345453 23112759642177731021754545)
            ·
              refine ⟨17334569731633298266315909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23112759642177731021754545 17334569731633298266315909)
              ·
                refine ⟨3250231824681243424934233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17334569731633298266315909 3250231824681243424934233)
                ·
                  refine ⟨2437673868510932568700675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3250231824681243424934233 2437673868510932568700675)
                  ·
                    refine ⟨3656510802766398853051013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2437673868510932568700675 3656510802766398853051013)
                    ·
                      refine ⟨685595775518699784947065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3656510802766398853051013 685595775518699784947065)
                      ·
                        rfl

theorem cell23_1335193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_1335193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335193 prefixEnd_1335193 := by exact prefixLift 1335193
  have htrace : WordTrace (prefixWord ++ tailWord_1335193) baseStart_1335193 baseEnd_1335193 := by
    simpa [prefixWord, tailWord_1335193, baseEnd_1335193] using wordTrace_append hprefix tailTrace_1335193
  have hstable : (prefixWord ++ tailWord_1335193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335193).length < 2 ^ (prefixWord ++ tailWord_1335193).sum := by decide
  have hdescent : baseEnd_1335193 < baseStart_1335193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335230 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_1335230 : Nat := 118140960795 + 1335230 * 2 ^ 59
def prefixEnd_1335230 : Nat := 4983230072969 + 3 ^ 40 * 1335230 * 2
def baseEnd_1335230 : Nat := 685614774302916140184395

theorem tailTrace_1335230 : CollatzResearch.WordTrace tailWord_1335230 prefixEnd_1335230 685614774302916140184395 := by
  unfold tailWord_1335230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6087479869087152996748393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32466559301798149315991429 6087479869087152996748393)
  ·
    refine ⟨4565609901815364747561295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6087479869087152996748393 4565609901815364747561295)
    ·
      refine ⟨6848414852723047121341943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4565609901815364747561295 6848414852723047121341943)
      ·
        refine ⟨10272622279084570682012915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6848414852723047121341943 10272622279084570682012915)
        ·
          refine ⟨15408933418626856023019373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10272622279084570682012915 15408933418626856023019373)
          ·
            refine ⟨5778350031985071008632265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15408933418626856023019373 5778350031985071008632265)
            ·
              refine ⟨4333762523988803256474199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5778350031985071008632265 4333762523988803256474199)
              ·
                refine ⟨6500643785983204884711299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4333762523988803256474199 6500643785983204884711299)
                ·
                  refine ⟨9750965678974807327066949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6500643785983204884711299 9750965678974807327066949)
                  ·
                    refine ⟨1828306064807776373825053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9750965678974807327066949 1828306064807776373825053)
                    ·
                      refine ⟨685614774302916140184395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1828306064807776373825053 685614774302916140184395)
                      ·
                        rfl

theorem cell23_1335230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_1335230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335230 prefixEnd_1335230 := by exact prefixLift 1335230
  have htrace : WordTrace (prefixWord ++ tailWord_1335230) baseStart_1335230 baseEnd_1335230 := by
    simpa [prefixWord, tailWord_1335230, baseEnd_1335230] using wordTrace_append hprefix tailTrace_1335230
  have hstable : (prefixWord ++ tailWord_1335230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335230).length < 2 ^ (prefixWord ++ tailWord_1335230).sum := by decide
  have hdescent : baseEnd_1335230 < baseStart_1335230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335267 : List Nat := [1, 1, 1, 6, 1, 4, 2, 1, 6]
def baseStart_1335267 : Nat := 118140960795 + 1335267 * 2 ^ 59
def prefixEnd_1335267 : Nat := 4983230072969 + 3 ^ 40 * 1335267 * 2
def baseEnd_1335267 : Nat := 76181530343014721713525

theorem tailTrace_1335267 : CollatzResearch.WordTrace tailWord_1335267 prefixEnd_1335267 76181530343014721713525 := by
  unfold tailWord_1335267
  simp only [CollatzResearch.WordTrace]
  refine ⟨48701188453563179293084055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32467458969042119528722703 48701188453563179293084055)
  ·
    refine ⟨73051782680344768939626083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48701188453563179293084055 73051782680344768939626083)
    ·
      refine ⟨109577674020517153409439125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73051782680344768939626083 109577674020517153409439125)
      ·
        refine ⟨5136453469711741566067459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 109577674020517153409439125 5136453469711741566067459)
        ·
          refine ⟨7704680204567612349101189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5136453469711741566067459 7704680204567612349101189)
          ·
            refine ⟨1444627538356427315456473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7704680204567612349101189 1444627538356427315456473)
            ·
              refine ⟨1083470653767320486592355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1444627538356427315456473 1083470653767320486592355)
              ·
                refine ⟨1625205980650980729888533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083470653767320486592355 1625205980650980729888533)
                ·
                  refine ⟨76181530343014721713525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1625205980650980729888533 76181530343014721713525)
                  ·
                    rfl

theorem cell23_1335267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 6].length) (baseStart_1335267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335267 prefixEnd_1335267 := by exact prefixLift 1335267
  have htrace : WordTrace (prefixWord ++ tailWord_1335267) baseStart_1335267 baseEnd_1335267 := by
    simpa [prefixWord, tailWord_1335267, baseEnd_1335267] using wordTrace_append hprefix tailTrace_1335267
  have hstable : (prefixWord ++ tailWord_1335267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335267).length < 2 ^ (prefixWord ++ tailWord_1335267).sum := by decide
  have hdescent : baseEnd_1335267 < baseStart_1335267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335280 : List Nat := [2, 1, 1, 1, 3, 2, 5, 2, 1, 5]
def baseStart_1335280 : Nat := 118140960795 + 1335280 * 2 ^ 59
def prefixEnd_1335280 : Nat := 4983230072969 + 3 ^ 40 * 1335280 * 2
def baseEnd_1335280 : Nat := 228546816111880314853055

theorem tailTrace_1335280 : CollatzResearch.WordTrace tailWord_1335280 prefixEnd_1335280 228546816111880314853055 := by
  unfold tailWord_1335280
  simp only [CollatzResearch.WordTrace]
  refine ⟨24350831301258041256653647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32467775068344055008871529 24350831301258041256653647)
  ·
    refine ⟨36526246951887061884980471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24350831301258041256653647 36526246951887061884980471)
    ·
      refine ⟨54789370427830592827470707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36526246951887061884980471 54789370427830592827470707)
      ·
        refine ⟨82184055641745889241206061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54789370427830592827470707 82184055641745889241206061)
        ·
          refine ⟨30819020865654708465452273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82184055641745889241206061 30819020865654708465452273)
          ·
            refine ⟨23114265649241031349089205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30819020865654708465452273 23114265649241031349089205)
            ·
              refine ⟨2166962404616346688977113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23114265649241031349089205 2166962404616346688977113)
              ·
                refine ⟨1625221803462260016732835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2166962404616346688977113 1625221803462260016732835)
                ·
                  refine ⟨2437832705193390025099253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625221803462260016732835 2437832705193390025099253)
                  ·
                    refine ⟨228546816111880314853055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2437832705193390025099253 228546816111880314853055)
                    ·
                      rfl

theorem cell23_1335280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 1, 5].length) (baseStart_1335280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335280 prefixEnd_1335280 := by exact prefixLift 1335280
  have htrace : WordTrace (prefixWord ++ tailWord_1335280) baseStart_1335280 baseEnd_1335280 := by
    simpa [prefixWord, tailWord_1335280, baseEnd_1335280] using wordTrace_append hprefix tailTrace_1335280
  have hstable : (prefixWord ++ tailWord_1335280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335280).length < 2 ^ (prefixWord ++ tailWord_1335280).sum := by decide
  have hdescent : baseEnd_1335280 < baseStart_1335280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335293 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 3, 6]
def baseStart_1335293 : Nat := 118140960795 + 1335293 * 2 ^ 59
def prefixEnd_1335293 : Nat := 4983230072969 + 3 ^ 40 * 1335293 * 2
def baseEnd_1335293 : Nat := 228549041194716464565535

theorem tailTrace_1335293 : CollatzResearch.WordTrace tailWord_1335293 prefixEnd_1335293 228549041194716464565535 := by
  unfold tailWord_1335293
  simp only [CollatzResearch.WordTrace]
  refine ⟨48702136751468985733530533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32468091167645990489020355 48702136751468985733530533)
  ·
    refine ⟨9131650640900434825036975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48702136751468985733530533 9131650640900434825036975)
    ·
      refine ⟨13697475961350652237555463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9131650640900434825036975 13697475961350652237555463)
      ·
        refine ⟨20546213942025978356333195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13697475961350652237555463 20546213942025978356333195)
        ·
          refine ⟨30819320913038967534499793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20546213942025978356333195 30819320913038967534499793)
          ·
            refine ⟨23114490684779225650874845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30819320913038967534499793 23114490684779225650874845)
            ·
              refine ⟨8667934006792209619078067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23114490684779225650874845 8667934006792209619078067)
              ·
                refine ⟨13001901010188314428617101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8667934006792209619078067 13001901010188314428617101)
                ·
                  refine ⟨4875712878820617910731413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13001901010188314428617101 4875712878820617910731413)
                  ·
                    refine ⟨228549041194716464565535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4875712878820617910731413 228549041194716464565535)
                    ·
                      rfl

theorem cell23_1335293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_1335293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335293 prefixEnd_1335293 := by exact prefixLift 1335293
  have htrace : WordTrace (prefixWord ++ tailWord_1335293) baseStart_1335293 baseEnd_1335293 := by
    simpa [prefixWord, tailWord_1335293, baseEnd_1335293] using wordTrace_append hprefix tailTrace_1335293
  have hstable : (prefixWord ++ tailWord_1335293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335293).length < 2 ^ (prefixWord ++ tailWord_1335293).sum := by decide
  have hdescent : baseEnd_1335293 < baseStart_1335293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335297 : List Nat := [1, 2, 4, 1, 2, 1, 5, 1, 1, 5]
def baseStart_1335297 : Nat := 118140960795 + 1335297 * 2 ^ 59
def prefixEnd_1335297 : Nat := 4983230072969 + 3 ^ 40 * 1335297 * 2
def baseEnd_1335297 : Nat := 228549725835589126015529

theorem tailTrace_1335297 : CollatzResearch.WordTrace tailWord_1335297 prefixEnd_1335297 228549725835589126015529 := by
  unfold tailWord_1335297
  simp only [CollatzResearch.WordTrace]
  refine ⟨48702282643454494416676145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32468188428969662944450763 48702282643454494416676145)
  ·
    refine ⟨36526711982590870812507109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48702282643454494416676145 36526711982590870812507109)
    ·
      refine ⟨6848758496735788277345083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36526711982590870812507109 6848758496735788277345083)
      ·
        refine ⟨10273137745103682416017625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6848758496735788277345083 10273137745103682416017625)
        ·
          refine ⟨7704853308827761812013219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10273137745103682416017625 7704853308827761812013219)
          ·
            refine ⟨11557279963241642718019829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7704853308827761812013219 11557279963241642718019829)
            ·
              refine ⟨1083494996553904004814359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11557279963241642718019829 1083494996553904004814359)
              ·
                refine ⟨1625242494830856007221539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083494996553904004814359 1625242494830856007221539)
                ·
                  refine ⟨2437863742246284010832309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625242494830856007221539 2437863742246284010832309)
                  ·
                    refine ⟨228549725835589126015529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2437863742246284010832309 228549725835589126015529)
                    ·
                      rfl

theorem cell23_1335297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_1335297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335297 prefixEnd_1335297 := by exact prefixLift 1335297
  have htrace : WordTrace (prefixWord ++ tailWord_1335297) baseStart_1335297 baseEnd_1335297 := by
    simpa [prefixWord, tailWord_1335297, baseEnd_1335297] using wordTrace_append hprefix tailTrace_1335297
  have hstable : (prefixWord ++ tailWord_1335297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335297).length < 2 ^ (prefixWord ++ tailWord_1335297).sum := by decide
  have hdescent : baseEnd_1335297 < baseStart_1335297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335320 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 5, 2, 3]
def baseStart_1335320 : Nat := 118140960795 + 1335320 * 2 ^ 59
def prefixEnd_1335320 : Nat := 4983230072969 + 3 ^ 40 * 1335320 * 2
def baseEnd_1335320 : Nat := 685660987561820788058981

theorem tailTrace_1335320 : CollatzResearch.WordTrace tailWord_1335320 prefixEnd_1335320 685660987561820788058981 := by
  unfold tailWord_1335320
  simp only [CollatzResearch.WordTrace]
  refine ⟨24351560761185584672381707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32468747681580779563175609 24351560761185584672381707)
  ·
    refine ⟨36527341141778377008572561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24351560761185584672381707 36527341141778377008572561)
    ·
      refine ⟨27395505856333782756429421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36527341141778377008572561 27395505856333782756429421)
      ·
        refine ⟨10273314696125168533661033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27395505856333782756429421 10273314696125168533661033)
        ·
          refine ⟨7704986022093876400245775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10273314696125168533661033 7704986022093876400245775)
          ·
            refine ⟨11557479033140814600368663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7704986022093876400245775 11557479033140814600368663)
            ·
              refine ⟨17336218549711221900552995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11557479033140814600368663 17336218549711221900552995)
              ·
                refine ⟨26004327824566832850829493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17336218549711221900552995 26004327824566832850829493)
                ·
                  refine ⟨2437905733553140579765265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26004327824566832850829493 2437905733553140579765265)
                  ·
                    refine ⟨1828429300164855434823949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2437905733553140579765265 1828429300164855434823949)
                    ·
                      refine ⟨685660987561820788058981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1828429300164855434823949 685660987561820788058981)
                      ·
                        rfl

theorem cell23_1335320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_1335320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335320 prefixEnd_1335320 := by exact prefixLift 1335320
  have htrace : WordTrace (prefixWord ++ tailWord_1335320) baseStart_1335320 baseEnd_1335320 := by
    simpa [prefixWord, tailWord_1335320, baseEnd_1335320] using wordTrace_append hprefix tailTrace_1335320
  have hstable : (prefixWord ++ tailWord_1335320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335320).length < 2 ^ (prefixWord ++ tailWord_1335320).sum := by decide
  have hdescent : baseEnd_1335320 < baseStart_1335320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335348 : List Nat := [2, 5, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_1335348 : Nat := 118140960795 + 1335348 * 2 ^ 59
def prefixEnd_1335348 : Nat := 4983230072969 + 3 ^ 40 * 1335348 * 2
def baseEnd_1335348 : Nat := 228558455006715559502951

theorem tailTrace_1335348 : CollatzResearch.WordTrace tailWord_1335348 prefixEnd_1335348 228558455006715559502951 := by
  unfold tailWord_1335348
  simp only [CollatzResearch.WordTrace]
  refine ⟨24352071383134865063391349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32469428510846486751188465 24352071383134865063391349)
  ·
    refine ⟨2283006692168893599692939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24352071383134865063391349 2283006692168893599692939)
    ·
      refine ⟨3424510038253340399539409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2283006692168893599692939 3424510038253340399539409)
      ·
        refine ⟨2568382528690005299654557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3424510038253340399539409 2568382528690005299654557)
        ·
          refine ⟨963143448258751987370459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2568382528690005299654557 963143448258751987370459)
          ·
            refine ⟨1444715172388127981055689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963143448258751987370459 1444715172388127981055689)
            ·
              refine ⟨1083536379291095985791767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1444715172388127981055689 1083536379291095985791767)
              ·
                refine ⟨1625304568936643978687651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083536379291095985791767 1625304568936643978687651)
                ·
                  refine ⟨2437956853404965968031477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625304568936643978687651 2437956853404965968031477)
                  ·
                    refine ⟨228558455006715559502951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2437956853404965968031477 228558455006715559502951)
                    ·
                      rfl

theorem cell23_1335348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_1335348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335348 prefixEnd_1335348 := by exact prefixLift 1335348
  have htrace : WordTrace (prefixWord ++ tailWord_1335348) baseStart_1335348 baseEnd_1335348 := by
    simpa [prefixWord, tailWord_1335348, baseEnd_1335348] using wordTrace_append hprefix tailTrace_1335348
  have hstable : (prefixWord ++ tailWord_1335348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335348).length < 2 ^ (prefixWord ++ tailWord_1335348).sum := by decide
  have hdescent : baseEnd_1335348 < baseStart_1335348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335363 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 5]
def baseStart_1335363 : Nat := 118140960795 + 1335363 * 2 ^ 59
def prefixEnd_1335363 : Nat := 4983230072969 + 3 ^ 40 * 1335363 * 2
def baseEnd_1335363 : Nat := 685683067229964119821283

theorem tailTrace_1335363 : CollatzResearch.WordTrace tailWord_1335363 prefixEnd_1335363 685683067229964119821283 := by
  unfold tailWord_1335363
  simp only [CollatzResearch.WordTrace]
  refine ⟨48704689861215387688578743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32469793240810258459052495 48704689861215387688578743)
  ·
    refine ⟨73057034791823081532868115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48704689861215387688578743 73057034791823081532868115)
    ·
      refine ⟨109585552187734622299302173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73057034791823081532868115 109585552187734622299302173)
      ·
        refine ⟨41094582070400483362238315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109585552187734622299302173 41094582070400483362238315)
        ·
          refine ⟨61641873105600725043357473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41094582070400483362238315 61641873105600725043357473)
          ·
            refine ⟨46231404829200543782518105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61641873105600725043357473 46231404829200543782518105)
            ·
              refine ⟨34673553621900407836888579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46231404829200543782518105 34673553621900407836888579)
              ·
                refine ⟨52010330432850611755332869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34673553621900407836888579 52010330432850611755332869)
                ·
                  refine ⟨9751936956159489704124913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52010330432850611755332869 9751936956159489704124913)
                  ·
                    refine ⟨7313952717119617278093685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9751936956159489704124913 7313952717119617278093685)
                    ·
                      refine ⟨685683067229964119821283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7313952717119617278093685 685683067229964119821283)
                      ·
                        rfl

theorem cell23_1335363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_1335363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335363 prefixEnd_1335363 := by exact prefixLift 1335363
  have htrace : WordTrace (prefixWord ++ tailWord_1335363) baseStart_1335363 baseEnd_1335363 := by
    simpa [prefixWord, tailWord_1335363, baseEnd_1335363] using wordTrace_append hprefix tailTrace_1335363
  have hstable : (prefixWord ++ tailWord_1335363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335363).length < 2 ^ (prefixWord ++ tailWord_1335363).sum := by decide
  have hdescent : baseEnd_1335363 < baseStart_1335363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335367 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 4, 1, 3]
def baseStart_1335367 : Nat := 118140960795 + 1335367 * 2 ^ 59
def prefixEnd_1335367 : Nat := 4983230072969 + 3 ^ 40 * 1335367 * 2
def baseEnd_1335367 : Nat := 685685121152582104171265

theorem tailTrace_1335367 : CollatzResearch.WordTrace tailWord_1335367 prefixEnd_1335367 685685121152582104171265 := by
  unfold tailWord_1335367
  simp only [CollatzResearch.WordTrace]
  refine ⟨48704835753200896371724355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32469890502133930914482903 48704835753200896371724355)
  ·
    refine ⟨73057253629801344557586533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48704835753200896371724355 73057253629801344557586533)
    ·
      refine ⟨13698235055587752104547475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73057253629801344557586533 13698235055587752104547475)
      ·
        refine ⟨20547352583381628156821213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13698235055587752104547475 20547352583381628156821213)
        ·
          refine ⟨7705257218768110558807955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20547352583381628156821213 7705257218768110558807955)
          ·
            refine ⟨11557885828152165838211933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7705257218768110558807955 11557885828152165838211933)
            ·
              refine ⟨4334207185557062189329475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11557885828152165838211933 4334207185557062189329475)
              ·
                refine ⟨6501310778335593283994213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4334207185557062189329475 6501310778335593283994213)
                ·
                  refine ⟨1218995770937923740748915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6501310778335593283994213 1218995770937923740748915)
                  ·
                    refine ⟨1828493656406885611123373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1218995770937923740748915 1828493656406885611123373)
                    ·
                      refine ⟨685685121152582104171265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1828493656406885611123373 685685121152582104171265)
                      ·
                        rfl

theorem cell23_1335367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_1335367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335367 prefixEnd_1335367 := by exact prefixLift 1335367
  have htrace : WordTrace (prefixWord ++ tailWord_1335367) baseStart_1335367 baseEnd_1335367 := by
    simpa [prefixWord, tailWord_1335367, baseEnd_1335367] using wordTrace_append hprefix tailTrace_1335367
  have hstable : (prefixWord ++ tailWord_1335367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335367).length < 2 ^ (prefixWord ++ tailWord_1335367).sum := by decide
  have hdescent : baseEnd_1335367 < baseStart_1335367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335410 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1335410 : Nat := 118140960795 + 1335410 * 2 ^ 59
def prefixEnd_1335410 : Nat := 4983230072969 + 3 ^ 40 * 1335410 * 2
def baseEnd_1335410 : Nat := 685707200820725435933567

theorem tailTrace_1335410 : CollatzResearch.WordTrace tailWord_1335410 prefixEnd_1335410 685707200820725435933567 := by
  unfold tailWord_1335410
  simp only [CollatzResearch.WordTrace]
  refine ⟨12176601023011278678884921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32470936061363409810359789 12176601023011278678884921)
  ·
    refine ⟨9132450767258459009163691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12176601023011278678884921 9132450767258459009163691)
    ·
      refine ⟨13698676150887688513745537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9132450767258459009163691 13698676150887688513745537)
      ·
        refine ⟨10274007113165766385309153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13698676150887688513745537 10274007113165766385309153)
        ·
          refine ⟨7705505334874324788981865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10274007113165766385309153 7705505334874324788981865)
          ·
            refine ⟨5779129001155743591736399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7705505334874324788981865 5779129001155743591736399)
            ·
              refine ⟨8668693501733615387604599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5779129001155743591736399 8668693501733615387604599)
              ·
                refine ⟨13003040252600423081406899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8668693501733615387604599 13003040252600423081406899)
                ·
                  refine ⟨19504560378900634622110349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13003040252600423081406899 19504560378900634622110349)
                  ·
                    refine ⟨7314210142087737983291381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19504560378900634622110349 7314210142087737983291381)
                    ·
                      refine ⟨685707200820725435933567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7314210142087737983291381 685707200820725435933567)
                      ·
                        rfl

theorem cell23_1335410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1335410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335410 prefixEnd_1335410 := by exact prefixLift 1335410
  have htrace : WordTrace (prefixWord ++ tailWord_1335410) baseStart_1335410 baseEnd_1335410 := by
    simpa [prefixWord, tailWord_1335410, baseEnd_1335410] using wordTrace_append hprefix tailTrace_1335410
  have hstable : (prefixWord ++ tailWord_1335410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335410).length < 2 ^ (prefixWord ++ tailWord_1335410).sum := by decide
  have hdescent : baseEnd_1335410 < baseStart_1335410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335424 : List Nat := [2, 1, 1, 2, 1, 3, 1, 6, 2, 2, 2]
def baseStart_1335424 : Nat := 118140960795 + 1335424 * 2 ^ 59
def prefixEnd_1335424 : Nat := 4983230072969 + 3 ^ 40 * 1335424 * 2
def baseEnd_1335424 : Nat := 685714389549888381158503

theorem tailTrace_1335424 : CollatzResearch.WordTrace tailWord_1335424 prefixEnd_1335424 685714389549888381158503 := by
  unfold tailWord_1335424
  simp only [CollatzResearch.WordTrace]
  refine ⟨24353457356997197553274663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32471276475996263404366217 24353457356997197553274663)
  ·
    refine ⟨36530186035495796329911995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24353457356997197553274663 36530186035495796329911995)
    ·
      refine ⟨54795279053243694494867993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36530186035495796329911995 54795279053243694494867993)
      ·
        refine ⟨41096459289932770871150995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54795279053243694494867993 41096459289932770871150995)
        ·
          refine ⟨61644688934899156306726493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41096459289932770871150995 61644688934899156306726493)
          ·
            refine ⟨23116758350587183615022435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61644688934899156306726493 23116758350587183615022435)
            ·
              refine ⟨34675137525880775422533653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23116758350587183615022435 34675137525880775422533653)
              ·
                refine ⟨1625397071525661347931265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34675137525880775422533653 1625397071525661347931265)
                ·
                  refine ⟨1219047803644246010948449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1625397071525661347931265 1219047803644246010948449)
                  ·
                    refine ⟨914285852733184508211337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1219047803644246010948449 914285852733184508211337)
                    ·
                      refine ⟨685714389549888381158503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 914285852733184508211337 685714389549888381158503)
                      ·
                        rfl

theorem cell23_1335424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 2, 2, 2].length) (baseStart_1335424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335424 prefixEnd_1335424 := by exact prefixLift 1335424
  have htrace : WordTrace (prefixWord ++ tailWord_1335424) baseStart_1335424 baseEnd_1335424 := by
    simpa [prefixWord, tailWord_1335424, baseEnd_1335424] using wordTrace_append hprefix tailTrace_1335424
  have hstable : (prefixWord ++ tailWord_1335424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335424).length < 2 ^ (prefixWord ++ tailWord_1335424).sum := by decide
  have hdescent : baseEnd_1335424 < baseStart_1335424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335440 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 3]
def baseStart_1335440 : Nat := 118140960795 + 1335440 * 2 ^ 59
def prefixEnd_1335440 : Nat := 4983230072969 + 3 ^ 40 * 1335440 * 2
def baseEnd_1335440 : Nat := 685722605240360318558429

theorem tailTrace_1335440 : CollatzResearch.WordTrace tailWord_1335440 prefixEnd_1335440 685722605240360318558429 := by
  unfold tailWord_1335440
  simp only [CollatzResearch.WordTrace]
  refine ⟨24353749140968214919565887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32471665521290953226087849 24353749140968214919565887)
  ·
    refine ⟨36530623711452322379348831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24353749140968214919565887 36530623711452322379348831)
    ·
      refine ⟨54795935567178483569023247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36530623711452322379348831 54795935567178483569023247)
      ·
        refine ⟨82193903350767725353534871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54795935567178483569023247 82193903350767725353534871)
        ·
          refine ⟨123290855026151588030302307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82193903350767725353534871 123290855026151588030302307)
          ·
            refine ⟨184936282539227382045453461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123290855026151588030302307 184936282539227382045453461)
            ·
              refine ⟨8668888244026283533380631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 184936282539227382045453461 8668888244026283533380631)
              ·
                refine ⟨13003332366039425300070947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8668888244026283533380631 13003332366039425300070947)
                ·
                  refine ⟨19504998549059137950106421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13003332366039425300070947 19504998549059137950106421)
                  ·
                    refine ⟨1828593613974294182822477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19504998549059137950106421 1828593613974294182822477)
                    ·
                      refine ⟨685722605240360318558429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1828593613974294182822477 685722605240360318558429)
                      ·
                        rfl

theorem cell23_1335440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 3].length) (baseStart_1335440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335440 prefixEnd_1335440 := by exact prefixLift 1335440
  have htrace : WordTrace (prefixWord ++ tailWord_1335440) baseStart_1335440 baseEnd_1335440 := by
    simpa [prefixWord, tailWord_1335440, baseEnd_1335440] using wordTrace_append hprefix tailTrace_1335440
  have hstable : (prefixWord ++ tailWord_1335440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335440).length < 2 ^ (prefixWord ++ tailWord_1335440).sum := by decide
  have hdescent : baseEnd_1335440 < baseStart_1335440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335520 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 8]
def baseStart_1335520 : Nat := 118140960795 + 1335520 * 2 ^ 59
def prefixEnd_1335520 : Nat := 4983230072969 + 3 ^ 40 * 1335520 * 2
def baseEnd_1335520 : Nat := 76195964854746667284229

theorem tailTrace_1335520 : CollatzResearch.WordTrace tailWord_1335520 prefixEnd_1335520 76195964854746667284229 := by
  unfold tailWord_1335520
  simp only [CollatzResearch.WordTrace]
  refine ⟨24355208060823301751022007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32473610747764402334696009 24355208060823301751022007)
  ·
    refine ⟨36532812091234952626533011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24355208060823301751022007 36532812091234952626533011)
    ·
      refine ⟨54799218136852428939799517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36532812091234952626533011 54799218136852428939799517)
      ·
        refine ⟨20549706801319660852424819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54799218136852428939799517 20549706801319660852424819)
        ·
          refine ⟨30824560201979491278637229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20549706801319660852424819 30824560201979491278637229)
          ·
            refine ⟨11559210075742309229488961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30824560201979491278637229 11559210075742309229488961)
            ·
              refine ⟨8669407556806731922116721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11559210075742309229488961 8669407556806731922116721)
              ·
                refine ⟨6502055667605048941587541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8669407556806731922116721 6502055667605048941587541)
                ·
                  refine ⟨76195964854746667284229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6502055667605048941587541 76195964854746667284229)
                  ·
                    rfl

theorem cell23_1335520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 8].length) (baseStart_1335520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335520 prefixEnd_1335520 := by exact prefixLift 1335520
  have htrace : WordTrace (prefixWord ++ tailWord_1335520) baseStart_1335520 baseEnd_1335520 := by
    simpa [prefixWord, tailWord_1335520, baseEnd_1335520] using wordTrace_append hprefix tailTrace_1335520
  have hstable : (prefixWord ++ tailWord_1335520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335520).length < 2 ^ (prefixWord ++ tailWord_1335520).sum := by decide
  have hdescent : baseEnd_1335520 < baseStart_1335520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335527 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1335527 : Nat := 118140960795 + 1335527 * 2 ^ 59
def prefixEnd_1335527 : Nat := 4983230072969 + 3 ^ 40 * 1335527 * 2
def baseEnd_1335527 : Nat := 685767278057301478170529

theorem tailTrace_1335527 : CollatzResearch.WordTrace tailWord_1335527 prefixEnd_1335527 685767278057301478170529 := by
  unfold tailWord_1335527
  simp only [CollatzResearch.WordTrace]
  refine ⟨48710671432621243697548835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32473780955080829131699223 48710671432621243697548835)
  ·
    refine ⟨73066007148931865546323253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48710671432621243697548835 73066007148931865546323253)
    ·
      refine ⟨6849938170212362394967805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73066007148931865546323253 6849938170212362394967805)
      ·
        refine ⟨2568726813829635898112927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6849938170212362394967805 2568726813829635898112927)
        ·
          refine ⟨3853090220744453847169391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2568726813829635898112927 3853090220744453847169391)
          ·
            refine ⟨5779635331116680770754087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3853090220744453847169391 5779635331116680770754087)
            ·
              refine ⟨8669452996675021156131131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5779635331116680770754087 8669452996675021156131131)
              ·
                refine ⟨13004179495012531734196697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8669452996675021156131131 13004179495012531734196697)
                ·
                  refine ⟨9753134621259398800647523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13004179495012531734196697 9753134621259398800647523)
                  ·
                    refine ⟨14629701931889098200971285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9753134621259398800647523 14629701931889098200971285)
                    ·
                      refine ⟨685767278057301478170529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14629701931889098200971285 685767278057301478170529)
                      ·
                        rfl

theorem cell23_1335527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1335527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335527 prefixEnd_1335527 := by exact prefixLift 1335527
  have htrace : WordTrace (prefixWord ++ tailWord_1335527) baseStart_1335527 baseEnd_1335527 := by
    simpa [prefixWord, tailWord_1335527, baseEnd_1335527] using wordTrace_append hprefix tailTrace_1335527
  have hstable : (prefixWord ++ tailWord_1335527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335527).length < 2 ^ (prefixWord ++ tailWord_1335527).sum := by decide
  have hdescent : baseEnd_1335527 < baseStart_1335527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335537 : List Nat := [1, 2, 2, 2, 2, 1, 5, 2, 6]
def baseStart_1335537 : Nat := 118140960795 + 1335537 * 2 ^ 59
def prefixEnd_1335537 : Nat := 4983230072969 + 3 ^ 40 * 1335537 * 2
def baseEnd_1335537 : Nat := 76196934762649604338387

theorem tailTrace_1335537 : CollatzResearch.WordTrace tailWord_1335537 prefixEnd_1335537 76196934762649604338387 := by
  unfold tailWord_1335537
  simp only [CollatzResearch.WordTrace]
  refine ⟨48711036162585015405412865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32474024108390010270275243 48711036162585015405412865)
  ·
    refine ⟨36533277121938761554059649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48711036162585015405412865 36533277121938761554059649)
    ·
      refine ⟨27399957841454071165544737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36533277121938761554059649 27399957841454071165544737)
      ·
        refine ⟨20549968381090553374158553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27399957841454071165544737 20549968381090553374158553)
        ·
          refine ⟨15412476285817915030618915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20549968381090553374158553 15412476285817915030618915)
          ·
            refine ⟨23118714428726872545928373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15412476285817915030618915 23118714428726872545928373)
            ·
              refine ⟨2167379477693144301180785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23118714428726872545928373 2167379477693144301180785)
              ·
                refine ⟨1625534608269858225885589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2167379477693144301180785 1625534608269858225885589)
                ·
                  refine ⟨76196934762649604338387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1625534608269858225885589 76196934762649604338387)
                  ·
                    rfl

theorem cell23_1335537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 6].length) (baseStart_1335537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335537 prefixEnd_1335537 := by exact prefixLift 1335537
  have htrace : WordTrace (prefixWord ++ tailWord_1335537) baseStart_1335537 baseEnd_1335537 := by
    simpa [prefixWord, tailWord_1335537, baseEnd_1335537] using wordTrace_append hprefix tailTrace_1335537
  have hstable : (prefixWord ++ tailWord_1335537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335537).length < 2 ^ (prefixWord ++ tailWord_1335537).sum := by decide
  have hdescent : baseEnd_1335537 < baseStart_1335537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335564 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 3, 1, 3]
def baseStart_1335564 : Nat := 118140960795 + 1335564 * 2 ^ 59
def prefixEnd_1335564 : Nat := 4983230072969 + 3 ^ 40 * 1335564 * 2
def baseEnd_1335564 : Nat := 685786276841517833407859

theorem tailTrace_1335564 : CollatzResearch.WordTrace tailWord_1335564 prefixEnd_1335564 685786276841517833407859 := by
  unfold tailWord_1335564
  simp only [CollatzResearch.WordTrace]
  refine ⟨24356010466743599508322873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32474680622324799344430497 24356010466743599508322873)
  ·
    refine ⟨18267007850057699631242155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24356010466743599508322873 18267007850057699631242155)
    ·
      refine ⟨27400511775086549446863233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18267007850057699631242155 27400511775086549446863233)
      ·
        refine ⟨20550383831314912085147425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27400511775086549446863233 20550383831314912085147425)
        ·
          refine ⟨15412787873486184063860569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20550383831314912085147425 15412787873486184063860569)
          ·
            refine ⟨11559590905114638047895427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15412787873486184063860569 11559590905114638047895427)
            ·
              refine ⟨17339386357671957071843141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11559590905114638047895427 17339386357671957071843141)
              ·
                refine ⟨3251134942063491950970589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17339386357671957071843141 3251134942063491950970589)
                ·
                  refine ⟨1219175603273809481613971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3251134942063491950970589 1219175603273809481613971)
                  ·
                    refine ⟨1828763404910714222420957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1219175603273809481613971 1828763404910714222420957)
                    ·
                      refine ⟨685786276841517833407859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1828763404910714222420957 685786276841517833407859)
                      ·
                        rfl

theorem cell23_1335564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_1335564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335564 prefixEnd_1335564 := by exact prefixLift 1335564
  have htrace : WordTrace (prefixWord ++ tailWord_1335564) baseStart_1335564 baseEnd_1335564 := by
    simpa [prefixWord, tailWord_1335564, baseEnd_1335564] using wordTrace_append hprefix tailTrace_1335564
  have hstable : (prefixWord ++ tailWord_1335564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335564).length < 2 ^ (prefixWord ++ tailWord_1335564).sum := by decide
  have hdescent : baseEnd_1335564 < baseStart_1335564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335584 : List Nat := [2, 1, 1, 5, 2, 1, 2, 3, 1, 5]
def baseStart_1335584 : Nat := 118140960795 + 1335584 * 2 ^ 59
def prefixEnd_1335584 : Nat := 4983230072969 + 3 ^ 40 * 1335584 * 2
def baseEnd_1335584 : Nat := 228598848818202585052589

theorem tailTrace_1335584 : CollatzResearch.WordTrace tailWord_1335584 prefixEnd_1335584 228598848818202585052589 := by
  unfold tailWord_1335584
  simp only [CollatzResearch.WordTrace]
  refine ⟨24356375196707371216186903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32475166928943161621582537 24356375196707371216186903)
  ·
    refine ⟨36534562795061056824280355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24356375196707371216186903 36534562795061056824280355)
    ·
      refine ⟨54801844192591585236420533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36534562795061056824280355 54801844192591585236420533)
      ·
        refine ⟨5137672893055461115914425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54801844192591585236420533 5137672893055461115914425)
        ·
          refine ⟨3853254669791595836935819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5137672893055461115914425 3853254669791595836935819)
          ·
            refine ⟨5779882004687393755403729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3853254669791595836935819 5779882004687393755403729)
            ·
              refine ⟨4334911503515545316552797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5779882004687393755403729 4334911503515545316552797)
              ·
                refine ⟨1625591813818329493707299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4334911503515545316552797 1625591813818329493707299)
                ·
                  refine ⟨2438387720727494240560949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625591813818329493707299 2438387720727494240560949)
                  ·
                    refine ⟨228598848818202585052589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2438387720727494240560949 228598848818202585052589)
                    ·
                      rfl

theorem cell23_1335584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 1, 5].length) (baseStart_1335584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335584 prefixEnd_1335584 := by exact prefixLift 1335584
  have htrace : WordTrace (prefixWord ++ tailWord_1335584) baseStart_1335584 baseEnd_1335584 := by
    simpa [prefixWord, tailWord_1335584, baseEnd_1335584] using wordTrace_append hprefix tailTrace_1335584
  have hstable : (prefixWord ++ tailWord_1335584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335584).length < 2 ^ (prefixWord ++ tailWord_1335584).sum := by decide
  have hdescent : baseEnd_1335584 < baseStart_1335584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335644 : List Nat := [2, 2, 4, 3, 1, 11]
def baseStart_1335644 : Nat := 118140960795 + 1335644 * 2 ^ 59
def prefixEnd_1335644 : Nat := 4983230072969 + 3 ^ 40 * 1335644 * 2
def baseEnd_1335644 : Nat := 2822334795448055639537

theorem tailTrace_1335644 : CollatzResearch.WordTrace tailWord_1335644 prefixEnd_1335644 2822334795448055639537 := by
  unfold tailWord_1335644
  simp only [CollatzResearch.WordTrace]
  refine ⟨24357469386598686339778993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32476625848798248453038657 24357469386598686339778993)
  ·
    refine ⟨18268102039949014754834245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24357469386598686339778993 18268102039949014754834245)
    ·
      refine ⟨3425269132490440266531421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18268102039949014754834245 3425269132490440266531421)
      ·
        refine ⟨1284475924683915099949283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3425269132490440266531421 1284475924683915099949283)
        ·
          refine ⟨1926713887025872649923925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1284475924683915099949283 1926713887025872649923925)
          ·
            refine ⟨2822334795448055639537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1926713887025872649923925 2822334795448055639537)
            ·
              rfl

theorem cell23_1335644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 11].length) (baseStart_1335644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335644 prefixEnd_1335644 := by exact prefixLift 1335644
  have htrace : WordTrace (prefixWord ++ tailWord_1335644) baseStart_1335644 baseEnd_1335644 := by
    simpa [prefixWord, tailWord_1335644, baseEnd_1335644] using wordTrace_append hprefix tailTrace_1335644
  have hstable : (prefixWord ++ tailWord_1335644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335644).length < 2 ^ (prefixWord ++ tailWord_1335644).sum := by decide
  have hdescent : baseEnd_1335644 < baseStart_1335644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335655 : List Nat := [1, 1, 5, 1, 3, 2, 1, 4, 1, 2, 2]
def baseStart_1335655 : Nat := 118140960795 + 1335655 * 2 ^ 59
def prefixEnd_1335655 : Nat := 4983230072969 + 3 ^ 40 * 1335655 * 2
def baseEnd_1335655 : Nat := 685833003581076977369941

theorem tailTrace_1335655 : CollatzResearch.WordTrace tailWord_1335655 prefixEnd_1335655 685833003581076977369941 := by
  unfold tailWord_1335655
  simp only [CollatzResearch.WordTrace]
  refine ⟨48715339976157521558208419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32476893317438347705472279 48715339976157521558208419)
  ·
    refine ⟨73073009964236282337312629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48715339976157521558208419 73073009964236282337312629)
    ·
      refine ⟨6850594684147151469123059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73073009964236282337312629 6850594684147151469123059)
      ·
        refine ⟨10275892026220727203684589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6850594684147151469123059 10275892026220727203684589)
        ·
          refine ⟨3853459509832772701381721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10275892026220727203684589 3853459509832772701381721)
          ·
            refine ⟨2890094632374579526036291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3853459509832772701381721 2890094632374579526036291)
            ·
              refine ⟨4335141948561869289054437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2890094632374579526036291 4335141948561869289054437)
              ·
                refine ⟨812839115355350491697707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4335141948561869289054437 812839115355350491697707)
                ·
                  refine ⟨1219258673033025737546561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 812839115355350491697707 1219258673033025737546561)
                  ·
                    refine ⟨914444004774769303159921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1219258673033025737546561 914444004774769303159921)
                    ·
                      refine ⟨685833003581076977369941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 914444004774769303159921 685833003581076977369941)
                      ·
                        rfl

theorem cell23_1335655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_1335655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335655 prefixEnd_1335655 := by exact prefixLift 1335655
  have htrace : WordTrace (prefixWord ++ tailWord_1335655) baseStart_1335655 baseEnd_1335655 := by
    simpa [prefixWord, tailWord_1335655, baseEnd_1335655] using wordTrace_append hprefix tailTrace_1335655
  have hstable : (prefixWord ++ tailWord_1335655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335655).length < 2 ^ (prefixWord ++ tailWord_1335655).sum := by decide
  have hdescent : baseEnd_1335655 < baseStart_1335655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335687 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 1, 8]
def baseStart_1335687 : Nat := 118140960795 + 1335687 * 2 ^ 59
def prefixEnd_1335687 : Nat := 4983230072969 + 3 ^ 40 * 1335687 * 2
def baseEnd_1335687 : Nat := 228616478320673617389931

theorem tailTrace_1335687 : CollatzResearch.WordTrace tailWord_1335687 prefixEnd_1335687 228616478320673617389931 := by
  unfold tailWord_1335687
  simp only [CollatzResearch.WordTrace]
  refine ⟨48716507112041591023373315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32477671408027727348915543 48716507112041591023373315)
  ·
    refine ⟨73074760668062386535059973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48716507112041591023373315 73074760668062386535059973)
    ·
      refine ⟨13701517625261697475323745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73074760668062386535059973 13701517625261697475323745)
      ·
        refine ⟨10276138218946273106492809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13701517625261697475323745 10276138218946273106492809)
        ·
          refine ⟨7707103664209704829869607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10276138218946273106492809 7707103664209704829869607)
          ·
            refine ⟨11560655496314557244804411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7707103664209704829869607 11560655496314557244804411)
            ·
              refine ⟨17340983244471835867206617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11560655496314557244804411 17340983244471835867206617)
              ·
                refine ⟨13005737433353876900404963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17340983244471835867206617 13005737433353876900404963)
                ·
                  refine ⟨19508606150030815350607445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13005737433353876900404963 19508606150030815350607445)
                  ·
                    refine ⟨228616478320673617389931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19508606150030815350607445 228616478320673617389931)
                    ·
                      rfl

theorem cell23_1335687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_1335687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335687 prefixEnd_1335687 := by exact prefixLift 1335687
  have htrace : WordTrace (prefixWord ++ tailWord_1335687) baseStart_1335687 baseEnd_1335687 := by
    simpa [prefixWord, tailWord_1335687, baseEnd_1335687] using wordTrace_append hprefix tailTrace_1335687
  have hstable : (prefixWord ++ tailWord_1335687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335687).length < 2 ^ (prefixWord ++ tailWord_1335687).sum := by decide
  have hdescent : baseEnd_1335687 < baseStart_1335687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335704 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 2, 6]
def baseStart_1335704 : Nat := 118140960795 + 1335704 * 2 ^ 59
def prefixEnd_1335704 : Nat := 4983230072969 + 3 ^ 40 * 1335704 * 2
def baseEnd_1335704 : Nat := 228619388044382428552405

theorem tailTrace_1335704 : CollatzResearch.WordTrace tailWord_1335704 prefixEnd_1335704 228619388044382428552405 := by
  unfold tailWord_1335704
  simp only [CollatzResearch.WordTrace]
  refine ⟨24358563576490001463371083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32478084768653335284494777 24358563576490001463371083)
  ·
    refine ⟨36537845364735002195056625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24358563576490001463371083 36537845364735002195056625)
    ·
      refine ⟨27403384023551251646292469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36537845364735002195056625 27403384023551251646292469)
      ·
        refine ⟨2569067252207929841839919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27403384023551251646292469 2569067252207929841839919)
        ·
          refine ⟨3853600878311894762759879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2569067252207929841839919 3853600878311894762759879)
          ·
            refine ⟨5780401317467842144139819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3853600878311894762759879 5780401317467842144139819)
            ·
              refine ⟨8670601976201763216209729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5780401317467842144139819 8670601976201763216209729)
              ·
                refine ⟨6502951482151322412157297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8670601976201763216209729 6502951482151322412157297)
                ·
                  refine ⟨4877213611613491809117973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6502951482151322412157297 4877213611613491809117973)
                  ·
                    refine ⟨228619388044382428552405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4877213611613491809117973 228619388044382428552405)
                    ·
                      rfl

theorem cell23_1335704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_1335704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335704 prefixEnd_1335704 := by exact prefixLift 1335704
  have htrace : WordTrace (prefixWord ++ tailWord_1335704) baseStart_1335704 baseEnd_1335704 := by
    simpa [prefixWord, tailWord_1335704, baseEnd_1335704] using wordTrace_append hprefix tailTrace_1335704
  have hstable : (prefixWord ++ tailWord_1335704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335704).length < 2 ^ (prefixWord ++ tailWord_1335704).sum := by decide
  have hdescent : baseEnd_1335704 < baseStart_1335704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335722 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1335722 : Nat := 118140960795 + 1335722 * 2 ^ 59
def prefixEnd_1335722 : Nat := 4983230072969 + 3 ^ 40 * 1335722 * 2
def baseEnd_1335722 : Nat := 685867406784928215232133

theorem tailTrace_1335722 : CollatzResearch.WordTrace tailWord_1335722 prefixEnd_1335722 685867406784928215232133 := by
  unfold tailWord_1335722
  simp only [CollatzResearch.WordTrace]
  refine ⟨12179445916728698000224355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32478522444609861333931613 12179445916728698000224355)
  ·
    refine ⟨18269168875093047000336533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12179445916728698000224355 18269168875093047000336533)
    ·
      refine ⟨856367291019986578140775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18269168875093047000336533 856367291019986578140775)
      ·
        refine ⟨1284550936529979867211163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 856367291019986578140775 1284550936529979867211163)
        ·
          refine ⟨1926826404794969800816745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1284550936529979867211163 1926826404794969800816745)
          ·
            refine ⟨1445119803596227350612559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1926826404794969800816745 1445119803596227350612559)
            ·
              refine ⟨2167679705394341025918839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1445119803596227350612559 2167679705394341025918839)
              ·
                refine ⟨3251519558091511538878259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2167679705394341025918839 3251519558091511538878259)
                ·
                  refine ⟨4877279337137267308317389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3251519558091511538878259 4877279337137267308317389)
                  ·
                    refine ⟨1828979751426475240619021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4877279337137267308317389 1828979751426475240619021)
                    ·
                      refine ⟨685867406784928215232133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1828979751426475240619021 685867406784928215232133)
                      ·
                        rfl

theorem cell23_1335722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1335722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335722 prefixEnd_1335722 := by exact prefixLift 1335722
  have htrace : WordTrace (prefixWord ++ tailWord_1335722) baseStart_1335722 baseEnd_1335722 := by
    simpa [prefixWord, tailWord_1335722, baseEnd_1335722] using wordTrace_append hprefix tailTrace_1335722
  have hstable : (prefixWord ++ tailWord_1335722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335722).length < 2 ^ (prefixWord ++ tailWord_1335722).sum := by decide
  have hdescent : baseEnd_1335722 < baseStart_1335722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335751 : List Nat := [1, 1, 4, 1, 1, 4, 3, 3, 5]
def baseStart_1335751 : Nat := 118140960795 + 1335751 * 2 ^ 59
def prefixEnd_1335751 : Nat := 4983230072969 + 3 ^ 40 * 1335751 * 2
def baseEnd_1335751 : Nat := 76209144191545400196611

theorem tailTrace_1335751 : CollatzResearch.WordTrace tailWord_1335751 prefixEnd_1335751 76209144191545400196611 := by
  unfold tailWord_1335751
  simp only [CollatzResearch.WordTrace]
  refine ⟨48718841383809729953703107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32479227589206486635802071 48718841383809729953703107)
  ·
    refine ⟨73078262075714594930554661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48718841383809729953703107 73078262075714594930554661)
    ·
      refine ⟨13702174139196486549478999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73078262075714594930554661 13702174139196486549478999)
      ·
        refine ⟨20553261208794729824218499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13702174139196486549478999 20553261208794729824218499)
        ·
          refine ⟨30829891813192094736327749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20553261208794729824218499 30829891813192094736327749)
          ·
            refine ⟨5780604714973517763061453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30829891813192094736327749 5780604714973517763061453)
            ·
              refine ⟨2167726768115069161148045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5780604714973517763061453 2167726768115069161148045)
              ·
                refine ⟨812897538043150935430517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2167726768115069161148045 812897538043150935430517)
                ·
                  refine ⟨76209144191545400196611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 812897538043150935430517 76209144191545400196611)
                  ·
                    rfl

theorem cell23_1335751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 5].length) (baseStart_1335751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335751 prefixEnd_1335751 := by exact prefixLift 1335751
  have htrace : WordTrace (prefixWord ++ tailWord_1335751) baseStart_1335751 baseEnd_1335751 := by
    simpa [prefixWord, tailWord_1335751, baseEnd_1335751] using wordTrace_append hprefix tailTrace_1335751
  have hstable : (prefixWord ++ tailWord_1335751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335751).length < 2 ^ (prefixWord ++ tailWord_1335751).sum := by decide
  have hdescent : baseEnd_1335751 < baseStart_1335751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335767 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 8]
def baseStart_1335767 : Nat := 118140960795 + 1335767 * 2 ^ 59
def prefixEnd_1335767 : Nat := 4983230072969 + 3 ^ 40 * 1335767 * 2
def baseEnd_1335767 : Nat := 685890513414380539169425

theorem tailTrace_1335767 : CollatzResearch.WordTrace tailWord_1335767 prefixEnd_1335767 685890513414380539169425 := by
  unfold tailWord_1335767
  simp only [CollatzResearch.WordTrace]
  refine ⟨48719424951751764686285555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32479616634501176457523703 48719424951751764686285555)
  ·
    refine ⟨73079137427627647029428333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48719424951751764686285555 73079137427627647029428333)
    ·
      refine ⟨27404676535360367636035625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73079137427627647029428333 27404676535360367636035625)
      ·
        refine ⟨20553507401520275727026719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27404676535360367636035625 20553507401520275727026719)
        ·
          refine ⟨30830261102280413590540079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20553507401520275727026719 30830261102280413590540079)
          ·
            refine ⟨46245391653420620385810119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30830261102280413590540079 46245391653420620385810119)
            ·
              refine ⟨69368087480130930578715179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46245391653420620385810119 69368087480130930578715179)
              ·
                refine ⟨104052131220196395868072769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69368087480130930578715179 104052131220196395868072769)
                ·
                  refine ⟨78039098415147296901054577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104052131220196395868072769 78039098415147296901054577)
                  ·
                    refine ⟨58529323811360472675790933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78039098415147296901054577 58529323811360472675790933)
                    ·
                      refine ⟨685890513414380539169425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 58529323811360472675790933 685890513414380539169425)
                      ·
                        rfl

theorem cell23_1335767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_1335767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335767 prefixEnd_1335767 := by exact prefixLift 1335767
  have htrace : WordTrace (prefixWord ++ tailWord_1335767) baseStart_1335767 baseEnd_1335767 := by
    simpa [prefixWord, tailWord_1335767, baseEnd_1335767] using wordTrace_append hprefix tailTrace_1335767
  have hstable : (prefixWord ++ tailWord_1335767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335767).length < 2 ^ (prefixWord ++ tailWord_1335767).sum := by decide
  have hdescent : baseEnd_1335767 < baseStart_1335767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335779 : List Nat := [1, 1, 1, 6, 4, 1, 2, 1, 2, 2, 2]
def baseStart_1335779 : Nat := 118140960795 + 1335779 * 2 ^ 59
def prefixEnd_1335779 : Nat := 4983230072969 + 3 ^ 40 * 1335779 * 2
def baseEnd_1335779 : Nat := 685896675182234492219371

theorem tailTrace_1335779 : CollatzResearch.WordTrace tailWord_1335779 prefixEnd_1335779 685896675182234492219371 := by
  unfold tailWord_1335779
  simp only [CollatzResearch.WordTrace]
  refine ⟨48719862627708290735722391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32479908418472193823814927 48719862627708290735722391)
  ·
    refine ⟨73079793941562436103583587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48719862627708290735722391 73079793941562436103583587)
    ·
      refine ⟨109619690912343654155375381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73079793941562436103583587 109619690912343654155375381)
      ·
        refine ⟨5138423011516108788533221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 109619690912343654155375381 5138423011516108788533221)
        ·
          refine ⟨963454314659270397849979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5138423011516108788533221 963454314659270397849979)
          ·
            refine ⟨1445181471988905596774969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963454314659270397849979 1445181471988905596774969)
            ·
              refine ⟨1083886103991679197581227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1445181471988905596774969 1083886103991679197581227)
              ·
                refine ⟨1625829155987518796371841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083886103991679197581227 1625829155987518796371841)
                ·
                  refine ⟨1219371866990639097278881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1625829155987518796371841 1219371866990639097278881)
                  ·
                    refine ⟨914528900242979322959161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1219371866990639097278881 914528900242979322959161)
                    ·
                      refine ⟨685896675182234492219371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 914528900242979322959161 685896675182234492219371)
                      ·
                        rfl

theorem cell23_1335779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_1335779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335779 prefixEnd_1335779 := by exact prefixLift 1335779
  have htrace : WordTrace (prefixWord ++ tailWord_1335779) baseStart_1335779 baseEnd_1335779 := by
    simpa [prefixWord, tailWord_1335779, baseEnd_1335779] using wordTrace_append hprefix tailTrace_1335779
  have hstable : (prefixWord ++ tailWord_1335779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335779).length < 2 ^ (prefixWord ++ tailWord_1335779).sum := by decide
  have hdescent : baseEnd_1335779 < baseStart_1335779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335862 : List Nat := [5, 1, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_1335862 : Nat := 118140960795 + 1335862 * 2 ^ 59
def prefixEnd_1335862 : Nat := 4983230072969 + 3 ^ 40 * 1335862 * 2
def baseEnd_1335862 : Nat := 228646431358852555827163

theorem tailTrace_1335862 : CollatzResearch.WordTrace tailWord_1335862 prefixEnd_1335862 228646431358852555827163 := by
  unfold tailWord_1335862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3045180617900474744437115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32481926590938397273995893 3045180617900474744437115)
  ·
    refine ⟨4567770926850712116655673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3045180617900474744437115 4567770926850712116655673)
    ·
      refine ⟨3425828195138034087491755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4567770926850712116655673 3425828195138034087491755)
      ·
        refine ⟨5138742292707051131237633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3425828195138034087491755 5138742292707051131237633)
        ·
          refine ⟨3854056719530288348428225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5138742292707051131237633 3854056719530288348428225)
          ·
            refine ⟨2890542539647716261321169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3854056719530288348428225 2890542539647716261321169)
            ·
              refine ⟨2167906904735787195990877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2890542539647716261321169 2167906904735787195990877)
              ·
                refine ⟨812965089275920198496579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2167906904735787195990877 812965089275920198496579)
                ·
                  refine ⟨1219447633913880297744869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 812965089275920198496579 1219447633913880297744869)
                  ·
                    refine ⟨228646431358852555827163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1219447633913880297744869 228646431358852555827163)
                    ·
                      rfl

theorem cell23_1335862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_1335862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335862 prefixEnd_1335862 := by exact prefixLift 1335862
  have htrace : WordTrace (prefixWord ++ tailWord_1335862) baseStart_1335862 baseEnd_1335862 := by
    simpa [prefixWord, tailWord_1335862, baseEnd_1335862] using wordTrace_append hprefix tailTrace_1335862
  have hstable : (prefixWord ++ tailWord_1335862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335862).length < 2 ^ (prefixWord ++ tailWord_1335862).sum := by decide
  have hdescent : baseEnd_1335862 < baseStart_1335862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335871 : List Nat := [1, 1, 2, 2, 3, 2, 3, 3, 1, 5]
def baseStart_1335871 : Nat := 118140960795 + 1335871 * 2 ^ 59
def prefixEnd_1335871 : Nat := 4983230072969 + 3 ^ 40 * 1335871 * 2
def baseEnd_1335871 : Nat := 228647971800816044089649

theorem tailTrace_1335871 : CollatzResearch.WordTrace tailWord_1335871 prefixEnd_1335871 228647971800816044089649 := by
  unfold tailWord_1335871
  simp only [CollatzResearch.WordTrace]
  refine ⟨48723218143374990448071467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32482145428916660298714311 48723218143374990448071467)
  ·
    refine ⟨73084827215062485672107201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48723218143374990448071467 73084827215062485672107201)
    ·
      refine ⟨54813620411296864254080401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73084827215062485672107201 54813620411296864254080401)
      ·
        refine ⟨41110215308472648190560301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54813620411296864254080401 41110215308472648190560301)
        ·
          refine ⟨15416330740677243071460113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41110215308472648190560301 15416330740677243071460113)
          ·
            refine ⟨11562248055507932303595085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15416330740677243071460113 11562248055507932303595085)
            ·
              refine ⟨4335843020815474613848157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11562248055507932303595085 4335843020815474613848157)
              ·
                refine ⟨1625941132805802980193059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4335843020815474613848157 1625941132805802980193059)
                ·
                  refine ⟨2438911699208704470289589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625941132805802980193059 2438911699208704470289589)
                  ·
                    refine ⟨228647971800816044089649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2438911699208704470289589 228647971800816044089649)
                    ·
                      rfl

theorem cell23_1335871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 5].length) (baseStart_1335871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335871 prefixEnd_1335871 := by exact prefixLift 1335871
  have htrace : WordTrace (prefixWord ++ tailWord_1335871) baseStart_1335871 baseEnd_1335871 := by
    simpa [prefixWord, tailWord_1335871, baseEnd_1335871] using wordTrace_append hprefix tailTrace_1335871
  have hstable : (prefixWord ++ tailWord_1335871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335871).length < 2 ^ (prefixWord ++ tailWord_1335871).sum := by decide
  have hdescent : baseEnd_1335871 < baseStart_1335871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335878 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1335878 : Nat := 118140960795 + 1335878 * 2 ^ 59
def prefixEnd_1335878 : Nat := 4983230072969 + 3 ^ 40 * 1335878 * 2
def baseEnd_1335878 : Nat := 685947509767029604881415

theorem tailTrace_1335878 : CollatzResearch.WordTrace tailWord_1335878 prefixEnd_1335878 685947509767029604881415 := by
  unfold tailWord_1335878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1522608545448425957611759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32482315636233087095717525 1522608545448425957611759)
  ·
    refine ⟨2283912818172638936417639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1522608545448425957611759 2283912818172638936417639)
    ·
      refine ⟨3425869227258958404626459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2283912818172638936417639 3425869227258958404626459)
      ·
        refine ⟨5138803840888437606939689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3425869227258958404626459 5138803840888437606939689)
        ·
          refine ⟨3854102880666328205204767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5138803840888437606939689 3854102880666328205204767)
          ·
            refine ⟨5781154320999492307807151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854102880666328205204767 5781154320999492307807151)
            ·
              refine ⟨8671731481499238461710727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5781154320999492307807151 8671731481499238461710727)
              ·
                refine ⟨13007597222248857692566091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8671731481499238461710727 13007597222248857692566091)
                ·
                  refine ⟨19511395833373286538849137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13007597222248857692566091 19511395833373286538849137)
                  ·
                    refine ⟨14633546875029964904136853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19511395833373286538849137 14633546875029964904136853)
                    ·
                      refine ⟨685947509767029604881415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14633546875029964904136853 685947509767029604881415)
                      ·
                        rfl

theorem cell23_1335878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1335878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335878 prefixEnd_1335878 := by exact prefixLift 1335878
  have htrace : WordTrace (prefixWord ++ tailWord_1335878) baseStart_1335878 baseEnd_1335878 := by
    simpa [prefixWord, tailWord_1335878, baseEnd_1335878] using wordTrace_append hprefix tailTrace_1335878
  have hstable : (prefixWord ++ tailWord_1335878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335878).length < 2 ^ (prefixWord ++ tailWord_1335878).sum := by decide
  have hdescent : baseEnd_1335878 < baseStart_1335878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335885 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_1335885 : Nat := 118140960795 + 1335885 * 2 ^ 59
def prefixEnd_1335885 : Nat := 4983230072969 + 3 ^ 40 * 1335885 * 2
def baseEnd_1335885 : Nat := 685951104131611077493883

theorem tailTrace_1335885 : CollatzResearch.WordTrace tailWord_1335885 prefixEnd_1335885 685951104131611077493883 := by
  unfold tailWord_1335885
  simp only [CollatzResearch.WordTrace]
  refine ⟨48723728765324270839081109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32482485843549513892720739 48723728765324270839081109)
  ·
    refine ⟨2283924785874575195581927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48723728765324270839081109 2283924785874575195581927)
    ·
      refine ⟨3425887178811862793372891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2283924785874575195581927 3425887178811862793372891)
      ·
        refine ⟨5138830768217794190059337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3425887178811862793372891 5138830768217794190059337)
        ·
          refine ⟨3854123076163345642544503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5138830768217794190059337 3854123076163345642544503)
          ·
            refine ⟨5781184614245018463816755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854123076163345642544503 5781184614245018463816755)
            ·
              refine ⟨8671776921367527695725133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5781184614245018463816755 8671776921367527695725133)
              ·
                refine ⟨3251916345512822885896925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8671776921367527695725133 3251916345512822885896925)
                ·
                  refine ⟨1219468629567308582211347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3251916345512822885896925 1219468629567308582211347)
                  ·
                    refine ⟨1829202944350962873317021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1219468629567308582211347 1829202944350962873317021)
                    ·
                      refine ⟨685951104131611077493883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1829202944350962873317021 685951104131611077493883)
                      ·
                        rfl

theorem cell23_1335885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_1335885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335885 prefixEnd_1335885 := by exact prefixLift 1335885
  have htrace : WordTrace (prefixWord ++ tailWord_1335885) baseStart_1335885 baseEnd_1335885 := by
    simpa [prefixWord, tailWord_1335885, baseEnd_1335885] using wordTrace_append hprefix tailTrace_1335885
  have hstable : (prefixWord ++ tailWord_1335885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335885).length < 2 ^ (prefixWord ++ tailWord_1335885).sum := by decide
  have hdescent : baseEnd_1335885 < baseStart_1335885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335908 : List Nat := [2, 3, 1, 1, 2, 2, 4, 2, 1, 1, 4]
def baseStart_1335908 : Nat := 118140960795 + 1335908 * 2 ^ 59
def prefixEnd_1335908 : Nat := 4983230072969 + 3 ^ 40 * 1335908 * 2
def baseEnd_1335908 : Nat := 685962914186664487506277

theorem tailTrace_1335908 : CollatzResearch.WordTrace tailWord_1335908 prefixEnd_1335908 685962914186664487506277 := by
  unfold tailWord_1335908
  simp only [CollatzResearch.WordTrace]
  refine ⟨24362283822120472883584189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32483045096160630511445585 24362283822120472883584189)
  ·
    refine ⟨9135856433295177331344071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24362283822120472883584189 9135856433295177331344071)
    ·
      refine ⟨13703784649942765997016107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9135856433295177331344071 13703784649942765997016107)
      ·
        refine ⟨20555676974914148995524161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13703784649942765997016107 20555676974914148995524161)
        ·
          refine ⟨15416757731185611746643121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20555676974914148995524161 15416757731185611746643121)
          ·
            refine ⟨11562568298389208809982341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15416757731185611746643121 11562568298389208809982341)
            ·
              refine ⟨2167981555947976651871689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11562568298389208809982341 2167981555947976651871689)
              ·
                refine ⟨1625986166960982488903767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2167981555947976651871689 1625986166960982488903767)
                ·
                  refine ⟨2438979250441473733355651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625986166960982488903767 2438979250441473733355651)
                  ·
                    refine ⟨3658468875662210600033477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2438979250441473733355651 3658468875662210600033477)
                    ·
                      refine ⟨685962914186664487506277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3658468875662210600033477 685962914186664487506277)
                      ·
                        rfl

theorem cell23_1335908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_1335908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335908 prefixEnd_1335908 := by exact prefixLift 1335908
  have htrace : WordTrace (prefixWord ++ tailWord_1335908) baseStart_1335908 baseEnd_1335908 := by
    simpa [prefixWord, tailWord_1335908, baseEnd_1335908] using wordTrace_append hprefix tailTrace_1335908
  have hstable : (prefixWord ++ tailWord_1335908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335908).length < 2 ^ (prefixWord ++ tailWord_1335908).sum := by decide
  have hdescent : baseEnd_1335908 < baseStart_1335908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335918 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 4, 4]
def baseStart_1335918 : Nat := 118140960795 + 1335918 * 2 ^ 59
def prefixEnd_1335918 : Nat := 4983230072969 + 3 ^ 40 * 1335918 * 2
def baseEnd_1335918 : Nat := 228656016331069816127077

theorem tailTrace_1335918 : CollatzResearch.WordTrace tailWord_1335918 prefixEnd_1335918 228656016331069816127077 := by
  unfold tailWord_1335918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6090616546775589684379051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32483288249469811650021605 6090616546775589684379051)
  ·
    refine ⟨9135924820163384526568577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6090616546775589684379051 9135924820163384526568577)
    ·
      refine ⟨6851943615122538394926433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9135924820163384526568577 6851943615122538394926433)
      ·
        refine ⟨5138957711341903796194825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6851943615122538394926433 5138957711341903796194825)
        ·
          refine ⟨3854218283506427847146119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5138957711341903796194825 3854218283506427847146119)
          ·
            refine ⟨5781327425259641770719179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854218283506427847146119 5781327425259641770719179)
            ·
              refine ⟨8671991137889462656078769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5781327425259641770719179 8671991137889462656078769)
              ·
                refine ⟨6503993353417096992059077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8671991137889462656078769 6503993353417096992059077)
                ·
                  refine ⟨1219498753765705686011077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6503993353417096992059077 1219498753765705686011077)
                  ·
                    refine ⟨228656016331069816127077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1219498753765705686011077 228656016331069816127077)
                    ·
                      rfl

theorem cell23_1335918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_1335918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1335918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1335918 prefixEnd_1335918 := by exact prefixLift 1335918
  have htrace : WordTrace (prefixWord ++ tailWord_1335918) baseStart_1335918 baseEnd_1335918 := by
    simpa [prefixWord, tailWord_1335918, baseEnd_1335918] using wordTrace_append hprefix tailTrace_1335918
  have hstable : (prefixWord ++ tailWord_1335918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335918).length < 2 ^ (prefixWord ++ tailWord_1335918).sum := by decide
  have hdescent : baseEnd_1335918 < baseStart_1335918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336051 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 4, 5]
def baseStart_1336051 : Nat := 118140960795 + 1336051 * 2 ^ 59
def prefixEnd_1336051 : Nat := 4983230072969 + 3 ^ 40 * 1336051 * 2
def baseEnd_1336051 : Nat := 228678780640085809339373

theorem tailTrace_1336051 : CollatzResearch.WordTrace tailWord_1336051 prefixEnd_1336051 228678780640085809339373 := by
  unfold tailWord_1336051
  simp only [CollatzResearch.WordTrace]
  refine ⟨48729783282722881189624007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32486522188481920793082671 48729783282722881189624007)
  ·
    refine ⟨73094674924084321784436011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48729783282722881189624007 73094674924084321784436011)
    ·
      refine ⟨109642012386126482676654017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73094674924084321784436011 109642012386126482676654017)
      ·
        refine ⟨82231509289594862007490513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109642012386126482676654017 82231509289594862007490513)
        ·
          refine ⟨61673631967196146505617885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82231509289594862007490513 61673631967196146505617885)
          ·
            refine ⟨23127611987698554939606707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61673631967196146505617885 23127611987698554939606707)
            ·
              refine ⟨34691417981547832409410061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23127611987698554939606707 34691417981547832409410061)
              ·
                refine ⟨13009281743080437153528773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34691417981547832409410061 13009281743080437153528773)
                ·
                  refine ⟨2439240326827581966286645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13009281743080437153528773 2439240326827581966286645)
                  ·
                    refine ⟨228678780640085809339373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2439240326827581966286645 228678780640085809339373)
                    ·
                      rfl

theorem cell23_1336051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 5].length) (baseStart_1336051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336051 prefixEnd_1336051 := by exact prefixLift 1336051
  have htrace : WordTrace (prefixWord ++ tailWord_1336051) baseStart_1336051 baseEnd_1336051 := by
    simpa [prefixWord, tailWord_1336051, baseEnd_1336051] using wordTrace_append hprefix tailTrace_1336051
  have hstable : (prefixWord ++ tailWord_1336051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336051).length < 2 ^ (prefixWord ++ tailWord_1336051).sum := by decide
  have hdescent : baseEnd_1336051 < baseStart_1336051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336058 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2]
def baseStart_1336058 : Nat := 118140960795 + 1336058 * 2 ^ 59
def prefixEnd_1336058 : Nat := 4983230072969 + 3 ^ 40 * 1336058 * 2
def baseEnd_1336058 : Nat := 686039936284838900630587

theorem tailTrace_1336058 : CollatzResearch.WordTrace tailWord_1336058 prefixEnd_1336058 686039936284838900630587 := by
  unfold tailWord_1336058
  simp only [CollatzResearch.WordTrace]
  refine ⟨12182509648424380346282207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32486692395798347590085885 12182509648424380346282207)
  ·
    refine ⟨18273764472636570519423311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12182509648424380346282207 18273764472636570519423311)
    ·
      refine ⟨27410646708954855779134967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18273764472636570519423311 27410646708954855779134967)
      ·
        refine ⟨41115970063432283668702451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27410646708954855779134967 41115970063432283668702451)
        ·
          refine ⟨61673955095148425503053677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41115970063432283668702451 61673955095148425503053677)
          ·
            refine ⟨23127733160680659563645129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61673955095148425503053677 23127733160680659563645129)
            ·
              refine ⟨17345799870510494672733847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23127733160680659563645129 17345799870510494672733847)
              ·
                refine ⟨26018699805765742009100771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17345799870510494672733847 26018699805765742009100771)
                ·
                  refine ⟨39028049708648613013651157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26018699805765742009100771 39028049708648613013651157)
                  ·
                    refine ⟨914719915046451867507449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39028049708648613013651157 914719915046451867507449)
                    ·
                      refine ⟨686039936284838900630587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 914719915046451867507449 686039936284838900630587)
                      ·
                        rfl

theorem cell23_1336058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2].length) (baseStart_1336058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336058 prefixEnd_1336058 := by exact prefixLift 1336058
  have htrace : WordTrace (prefixWord ++ tailWord_1336058) baseStart_1336058 baseEnd_1336058 := by
    simpa [prefixWord, tailWord_1336058, baseEnd_1336058] using wordTrace_append hprefix tailTrace_1336058
  have hstable : (prefixWord ++ tailWord_1336058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336058).length < 2 ^ (prefixWord ++ tailWord_1336058).sum := by decide
  have hdescent : baseEnd_1336058 < baseStart_1336058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336061 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_1336061 : Nat := 118140960795 + 1336061 * 2 ^ 59
def prefixEnd_1336061 : Nat := 4983230072969 + 3 ^ 40 * 1336061 * 2
def baseEnd_1336061 : Nat := 686041476726802388893073

theorem tailTrace_1336061 : CollatzResearch.WordTrace tailWord_1336061 prefixEnd_1336061 686041476726802388893073 := by
  unfold tailWord_1336061
  simp only [CollatzResearch.WordTrace]
  refine ⟨48730148012686652897488037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32486765341791101931658691 48730148012686652897488037)
  ·
    refine ⟨9136902752378747418279007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48730148012686652897488037 9136902752378747418279007)
    ·
      refine ⟨13705354128568121127418511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9136902752378747418279007 13705354128568121127418511)
      ·
        refine ⟨20558031192852181691127767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13705354128568121127418511 20558031192852181691127767)
        ·
          refine ⟨30837046789278272536691651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20558031192852181691127767 30837046789278272536691651)
          ·
            refine ⟨46255570183917408805037477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30837046789278272536691651 46255570183917408805037477)
            ·
              refine ⟨8672919409484514150944527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46255570183917408805037477 8672919409484514150944527)
              ·
                refine ⟨13009379114226771226416791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8672919409484514150944527 13009379114226771226416791)
                ·
                  refine ⟨19514068671340156839625187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13009379114226771226416791 19514068671340156839625187)
                  ·
                    refine ⟨29271103007010235259437781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19514068671340156839625187 29271103007010235259437781)
                    ·
                      refine ⟨686041476726802388893073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29271103007010235259437781 686041476726802388893073)
                      ·
                        rfl

theorem cell23_1336061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_1336061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336061 prefixEnd_1336061 := by exact prefixLift 1336061
  have htrace : WordTrace (prefixWord ++ tailWord_1336061) baseStart_1336061 baseEnd_1336061 := by
    simpa [prefixWord, tailWord_1336061, baseEnd_1336061] using wordTrace_append hprefix tailTrace_1336061
  have hstable : (prefixWord ++ tailWord_1336061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336061).length < 2 ^ (prefixWord ++ tailWord_1336061).sum := by decide
  have hdescent : baseEnd_1336061 < baseStart_1336061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336066 : List Nat := [3, 4, 1, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_1336066 : Nat := 118140960795 + 1336066 * 2 ^ 59
def prefixEnd_1336066 : Nat := 4983230072969 + 3 ^ 40 * 1336066 * 2
def baseEnd_1336066 : Nat := 686044044130074869330551

theorem tailTrace_1336066 : CollatzResearch.WordTrace tailWord_1336066 prefixEnd_1336066 686044044130074869330551 := by
  unfold tailWord_1336066
  simp only [CollatzResearch.WordTrace]
  refine ⟨12182582594417134687855013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32486886918445692500946701 12182582594417134687855013)
  ·
    refine ⟨2284234236453212753972815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12182582594417134687855013 2284234236453212753972815)
    ·
      refine ⟨3426351354679819130959223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2284234236453212753972815 3426351354679819130959223)
      ·
        refine ⟨5139527032019728696438835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3426351354679819130959223 5139527032019728696438835)
        ·
          refine ⟨7709290548029593044658253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5139527032019728696438835 7709290548029593044658253)
          ·
            refine ⟨2890983955511097391746845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7709290548029593044658253 2890983955511097391746845)
            ·
              refine ⟨1084118983316661521905067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2890983955511097391746845 1084118983316661521905067)
              ·
                refine ⟨1626178474974992282857601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1084118983316661521905067 1626178474974992282857601)
                ·
                  refine ⟨1219633856231244212143201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1626178474974992282857601 1219633856231244212143201)
                  ·
                    refine ⟨914725392173433159107401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1219633856231244212143201 914725392173433159107401)
                    ·
                      refine ⟨686044044130074869330551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 914725392173433159107401 686044044130074869330551)
                      ·
                        rfl

theorem cell23_1336066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_1336066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336066 prefixEnd_1336066 := by exact prefixLift 1336066
  have htrace : WordTrace (prefixWord ++ tailWord_1336066) baseStart_1336066 baseEnd_1336066 := by
    simpa [prefixWord, tailWord_1336066, baseEnd_1336066] using wordTrace_append hprefix tailTrace_1336066
  have hstable : (prefixWord ++ tailWord_1336066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336066).length < 2 ^ (prefixWord ++ tailWord_1336066).sum := by decide
  have hdescent : baseEnd_1336066 < baseStart_1336066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336088 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 2, 1, 4]
def baseStart_1336088 : Nat := 118140960795 + 1336088 * 2 ^ 59
def prefixEnd_1336088 : Nat := 4983230072969 + 3 ^ 40 * 1336088 * 2
def baseEnd_1336088 : Nat := 686055340704473783255449

theorem tailTrace_1336088 : CollatzResearch.WordTrace tailWord_1336088 prefixEnd_1336088 686055340704473783255449 := by
  unfold tailWord_1336088
  simp only [CollatzResearch.WordTrace]
  refine ⟨24365566391794418254360459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32487421855725891005813945 24365566391794418254360459)
  ·
    refine ⟨36548349587691627381540689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24365566391794418254360459 36548349587691627381540689)
    ·
      refine ⟨27411262190768720536155517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36548349587691627381540689 27411262190768720536155517)
      ·
        refine ⟨10279223321538270201058319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27411262190768720536155517 10279223321538270201058319)
        ·
          refine ⟨15418834982307405301587479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10279223321538270201058319 15418834982307405301587479)
          ·
            refine ⟨23128252473461107952381219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15418834982307405301587479 23128252473461107952381219)
            ·
              refine ⟨34692378710191661928571829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23128252473461107952381219 34692378710191661928571829)
              ·
                refine ⟨3252410504080468305803609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34692378710191661928571829 3252410504080468305803609)
                ·
                  refine ⟨2439307878060351229352707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3252410504080468305803609 2439307878060351229352707)
                  ·
                    refine ⟨3658961817090526844029061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2439307878060351229352707 3658961817090526844029061)
                    ·
                      refine ⟨686055340704473783255449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3658961817090526844029061 686055340704473783255449)
                      ·
                        rfl

theorem cell23_1336088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_1336088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336088 prefixEnd_1336088 := by exact prefixLift 1336088
  have htrace : WordTrace (prefixWord ++ tailWord_1336088) baseStart_1336088 baseEnd_1336088 := by
    simpa [prefixWord, tailWord_1336088, baseEnd_1336088] using wordTrace_append hprefix tailTrace_1336088
  have hstable : (prefixWord ++ tailWord_1336088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336088).length < 2 ^ (prefixWord ++ tailWord_1336088).sum := by decide
  have hdescent : baseEnd_1336088 < baseStart_1336088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336115 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 3, 4]
def baseStart_1336115 : Nat := 118140960795 + 1336115 * 2 ^ 59
def prefixEnd_1336115 : Nat := 4983230072969 + 3 ^ 40 * 1336115 * 2
def baseEnd_1336115 : Nat := 228689734894048392539275

theorem tailTrace_1336115 : CollatzResearch.WordTrace tailWord_1336115 prefixEnd_1336115 228689734894048392539275 := by
  unfold tailWord_1336115
  simp only [CollatzResearch.WordTrace]
  refine ⟨48732117554491020119953799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32488078369660680079969199 48732117554491020119953799)
  ·
    refine ⟨73098176331736530179930699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48732117554491020119953799 73098176331736530179930699)
    ·
      refine ⟨109647264497604795269896049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73098176331736530179930699 109647264497604795269896049)
      ·
        refine ⟨82235448373203596452422037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109647264497604795269896049 82235448373203596452422037)
        ·
          refine ⟨3854786642493918583707283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82235448373203596452422037 3854786642493918583707283)
          ·
            refine ⟨5782179963740877875560925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854786642493918583707283 5782179963740877875560925)
            ·
              refine ⟨2168317486402829203335347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5782179963740877875560925 2168317486402829203335347)
              ·
                refine ⟨3252476229604243805003021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2168317486402829203335347 3252476229604243805003021)
                ·
                  refine ⟨1219678586101591426876133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3252476229604243805003021 1219678586101591426876133)
                  ·
                    refine ⟨228689734894048392539275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1219678586101591426876133 228689734894048392539275)
                    ·
                      rfl

theorem cell23_1336115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 4].length) (baseStart_1336115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336115 prefixEnd_1336115 := by exact prefixLift 1336115
  have htrace : WordTrace (prefixWord ++ tailWord_1336115) baseStart_1336115 baseEnd_1336115 := by
    simpa [prefixWord, tailWord_1336115, baseEnd_1336115] using wordTrace_append hprefix tailTrace_1336115
  have hstable : (prefixWord ++ tailWord_1336115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336115).length < 2 ^ (prefixWord ++ tailWord_1336115).sum := by decide
  have hdescent : baseEnd_1336115 < baseStart_1336115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336162 : List Nat := [3, 3, 2, 1, 3, 1, 2, 2, 6]
def baseStart_1336162 : Nat := 118140960795 + 1336162 * 2 ^ 59
def prefixEnd_1336162 : Nat := 4983230072969 + 3 ^ 40 * 1336162 * 2
def baseEnd_1336162 : Nat := 76232593141434054858901

theorem tailTrace_1336162 : CollatzResearch.WordTrace tailWord_1336162 prefixEnd_1336162 76232593141434054858901 := by
  unfold tailWord_1336162
  simp only [CollatzResearch.WordTrace]
  refine ⟨12183457946330186786728685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32489221190213831431276493 12183457946330186786728685)
  ·
    refine ⟨4568796729873820045023257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12183457946330186786728685 4568796729873820045023257)
    ·
      refine ⟨3426597547405365033767443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4568796729873820045023257 3426597547405365033767443)
      ·
        refine ⟨5139896321108047550651165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3426597547405365033767443 5139896321108047550651165)
        ·
          refine ⟨1927461120415517831494187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5139896321108047550651165 1927461120415517831494187)
          ·
            refine ⟨2891191680623276747241281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1927461120415517831494187 2891191680623276747241281)
            ·
              refine ⟨2168393760467457560430961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2891191680623276747241281 2168393760467457560430961)
              ·
                refine ⟨1626295320350593170323221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2168393760467457560430961 1626295320350593170323221)
                ·
                  refine ⟨76232593141434054858901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1626295320350593170323221 76232593141434054858901)
                  ·
                    rfl

theorem cell23_1336162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_1336162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336162 prefixEnd_1336162 := by exact prefixLift 1336162
  have htrace : WordTrace (prefixWord ++ tailWord_1336162) baseStart_1336162 baseEnd_1336162 := by
    simpa [prefixWord, tailWord_1336162, baseEnd_1336162] using wordTrace_append hprefix tailTrace_1336162
  have hstable : (prefixWord ++ tailWord_1336162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336162).length < 2 ^ (prefixWord ++ tailWord_1336162).sum := by decide
  have hdescent : baseEnd_1336162 < baseStart_1336162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336195 : List Nat := [1, 1, 1, 3, 4, 1, 2, 4, 1, 1, 4]
def baseStart_1336195 : Nat := 118140960795 + 1336195 * 2 ^ 59
def prefixEnd_1336195 : Nat := 4983230072969 + 3 ^ 40 * 1336195 * 2
def baseEnd_1336195 : Nat := 686110283134504864617457

theorem tailTrace_1336195 : CollatzResearch.WordTrace tailWord_1336195 prefixEnd_1336195 686110283134504864617457 := by
  unfold tailWord_1336195
  simp only [CollatzResearch.WordTrace]
  refine ⟨48735035394201193782866039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32490023596134129188577359 48735035394201193782866039)
  ·
    refine ⟨73102553091301790674299059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48735035394201193782866039 73102553091301790674299059)
    ·
      refine ⟨109653829636952686011448589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73102553091301790674299059 109653829636952686011448589)
      ·
        refine ⟨41120186113857257254293221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109653829636952686011448589 41120186113857257254293221)
        ·
          refine ⟨7710034896348235735179979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41120186113857257254293221 7710034896348235735179979)
          ·
            refine ⟨11565052344522353602769969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7710034896348235735179979 11565052344522353602769969)
            ·
              refine ⟨8673789258391765202077477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11565052344522353602769969 8673789258391765202077477)
              ·
                refine ⟨1626335485948455975389527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8673789258391765202077477 1626335485948455975389527)
                ·
                  refine ⟨2439503228922683963084291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626335485948455975389527 2439503228922683963084291)
                  ·
                    refine ⟨3659254843384025944626437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2439503228922683963084291 3659254843384025944626437)
                    ·
                      refine ⟨686110283134504864617457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3659254843384025944626437 686110283134504864617457)
                      ·
                        rfl

theorem cell23_1336195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_1336195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336195 prefixEnd_1336195 := by exact prefixLift 1336195
  have htrace : WordTrace (prefixWord ++ tailWord_1336195) baseStart_1336195 baseEnd_1336195 := by
    simpa [prefixWord, tailWord_1336195, baseEnd_1336195] using wordTrace_append hprefix tailTrace_1336195
  have hstable : (prefixWord ++ tailWord_1336195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336195).length < 2 ^ (prefixWord ++ tailWord_1336195).sum := by decide
  have hdescent : baseEnd_1336195 < baseStart_1336195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336199 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 2, 3, 2]
def baseStart_1336199 : Nat := 118140960795 + 1336199 * 2 ^ 59
def prefixEnd_1336199 : Nat := 4983230072969 + 3 ^ 40 * 1336199 * 2
def baseEnd_1336199 : Nat := 686112337057122848967439

theorem tailTrace_1336199 : CollatzResearch.WordTrace tailWord_1336199 prefixEnd_1336199 686112337057122848967439 := by
  unfold tailWord_1336199
  simp only [CollatzResearch.WordTrace]
  refine ⟨48735181286186702466011651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32490120857457801644007767 48735181286186702466011651)
  ·
    refine ⟨73102771929280053699017477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48735181286186702466011651 73102771929280053699017477)
    ·
      refine ⟨13706769736740010068565777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73102771929280053699017477 13706769736740010068565777)
      ·
        refine ⟨10280077302555007551424333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13706769736740010068565777 10280077302555007551424333)
        ·
          refine ⟨3855028988458127831784125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10280077302555007551424333 3855028988458127831784125)
          ·
            refine ⟨1445635870671797936919047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3855028988458127831784125 1445635870671797936919047)
            ·
              refine ⟨2168453806007696905378571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1445635870671797936919047 2168453806007696905378571)
              ·
                refine ⟨3252680709011545358067857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2168453806007696905378571 3252680709011545358067857)
                ·
                  refine ⟨2439510531758659018550893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3252680709011545358067857 2439510531758659018550893)
                  ·
                    refine ⟨914816449409497131956585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2439510531758659018550893 914816449409497131956585)
                    ·
                      refine ⟨686112337057122848967439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 914816449409497131956585 686112337057122848967439)
                      ·
                        rfl

theorem cell23_1336199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_1336199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336199 prefixEnd_1336199 := by exact prefixLift 1336199
  have htrace : WordTrace (prefixWord ++ tailWord_1336199) baseStart_1336199 baseEnd_1336199 := by
    simpa [prefixWord, tailWord_1336199, baseEnd_1336199] using wordTrace_append hprefix tailTrace_1336199
  have hstable : (prefixWord ++ tailWord_1336199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336199).length < 2 ^ (prefixWord ++ tailWord_1336199).sum := by decide
  have hdescent : baseEnd_1336199 < baseStart_1336199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336212 : List Nat := [2, 4, 2, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_1336212 : Nat := 118140960795 + 1336212 * 2 ^ 59
def prefixEnd_1336212 : Nat := 4983230072969 + 3 ^ 40 * 1336212 * 2
def baseEnd_1336212 : Nat := 686119012305631298104879

theorem tailTrace_1336212 : CollatzResearch.WordTrace tailWord_1336212 prefixEnd_1336212 686119012305631298104879 := by
  unfold tailWord_1336212
  simp only [CollatzResearch.WordTrace]
  refine ⟨24367827717569802843117445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32490436956759737124156593 24367827717569802843117445)
  ·
    refine ⟨4568967697044338033084521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24367827717569802843117445 4568967697044338033084521)
    ·
      refine ⟨3426725772783253524813391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4568967697044338033084521 3426725772783253524813391)
      ·
        refine ⟨5140088659174880287220087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3426725772783253524813391 5140088659174880287220087)
        ·
          refine ⟨7710132988762320430830131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5140088659174880287220087 7710132988762320430830131)
          ·
            refine ⟨11565199483143480646245197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7710132988762320430830131 11565199483143480646245197)
            ·
              refine ⟨4336949806178805242341949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11565199483143480646245197 4336949806178805242341949)
              ·
                refine ⟨1626356177317051965878231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4336949806178805242341949 1626356177317051965878231)
                ·
                  refine ⟨2439534265975577948817347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626356177317051965878231 2439534265975577948817347)
                  ·
                    refine ⟨3659301398963366923226021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2439534265975577948817347 3659301398963366923226021)
                    ·
                      refine ⟨686119012305631298104879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3659301398963366923226021 686119012305631298104879)
                      ·
                        rfl

theorem cell23_1336212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_1336212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336212 prefixEnd_1336212 := by exact prefixLift 1336212
  have htrace : WordTrace (prefixWord ++ tailWord_1336212) baseStart_1336212 baseEnd_1336212 := by
    simpa [prefixWord, tailWord_1336212, baseEnd_1336212] using wordTrace_append hprefix tailTrace_1336212
  have hstable : (prefixWord ++ tailWord_1336212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336212).length < 2 ^ (prefixWord ++ tailWord_1336212).sum := by decide
  have hdescent : baseEnd_1336212 < baseStart_1336212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336305 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 2, 1, 5]
def baseStart_1336305 : Nat := 118140960795 + 1336305 * 2 ^ 59
def prefixEnd_1336305 : Nat := 4983230072969 + 3 ^ 40 * 1336305 * 2
def baseEnd_1336305 : Nat := 686166766006499434241951

theorem tailTrace_1336305 : CollatzResearch.WordTrace tailWord_1336305 prefixEnd_1336305 686166766006499434241951 := by
  unfold tailWord_1336305
  simp only [CollatzResearch.WordTrace]
  refine ⟨48739047423802682569370369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32492698282535121712913579 48739047423802682569370369)
  ·
    refine ⟨36554285567852011927027777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48739047423802682569370369 36554285567852011927027777)
    ·
      refine ⟨27415714175889008945270833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36554285567852011927027777 27415714175889008945270833)
      ·
        refine ⟨20561785631916756708953125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27415714175889008945270833 20561785631916756708953125)
        ·
          refine ⟨3855334805984391882928711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20561785631916756708953125 3855334805984391882928711)
          ·
            refine ⟨5783002208976587824393067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3855334805984391882928711 5783002208976587824393067)
            ·
              refine ⟨8674503313464881736589601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5783002208976587824393067 8674503313464881736589601)
              ·
                refine ⟨6505877485098661302442201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8674503313464881736589601 6505877485098661302442201)
                ·
                  refine ⟨4879408113823995976831651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6505877485098661302442201 4879408113823995976831651)
                  ·
                    refine ⟨7319112170735993965247477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4879408113823995976831651 7319112170735993965247477)
                    ·
                      refine ⟨686166766006499434241951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7319112170735993965247477 686166766006499434241951)
                      ·
                        rfl

theorem cell23_1336305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_1336305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336305 prefixEnd_1336305 := by exact prefixLift 1336305
  have htrace : WordTrace (prefixWord ++ tailWord_1336305) baseStart_1336305 baseEnd_1336305 := by
    simpa [prefixWord, tailWord_1336305, baseEnd_1336305] using wordTrace_append hprefix tailTrace_1336305
  have hstable : (prefixWord ++ tailWord_1336305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336305).length < 2 ^ (prefixWord ++ tailWord_1336305).sum := by decide
  have hdescent : baseEnd_1336305 < baseStart_1336305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336306 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 3, 3, 2]
def baseStart_1336306 : Nat := 118140960795 + 1336306 * 2 ^ 59
def prefixEnd_1336306 : Nat := 4983230072969 + 3 ^ 40 * 1336306 * 2
def baseEnd_1336306 : Nat := 686167279487153930329447

theorem tailTrace_1336306 : CollatzResearch.WordTrace tailWord_1336306 prefixEnd_1336306 686167279487153930329447 := by
  unfold tailWord_1336306
  simp only [CollatzResearch.WordTrace]
  refine ⟨12184770974199764935039193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32492722597866039826771181 12184770974199764935039193)
  ·
    refine ⟨9138578230649823701279395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12184770974199764935039193 9138578230649823701279395)
    ·
      refine ⟨13707867345974735551919093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9138578230649823701279395 13707867345974735551919093)
      ·
        refine ⟨1285112563685131457992415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13707867345974735551919093 1285112563685131457992415)
        ·
          refine ⟨1927668845527697186988623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1285112563685131457992415 1927668845527697186988623)
          ·
            refine ⟨2891503268291545780482935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1927668845527697186988623 2891503268291545780482935)
            ·
              refine ⟨4337254902437318670724403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2891503268291545780482935 4337254902437318670724403)
              ·
                refine ⟨6505882353655978006086605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4337254902437318670724403 6505882353655978006086605)
                ·
                  refine ⟨2439705882620991752282477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6505882353655978006086605 2439705882620991752282477)
                  ·
                    refine ⟨914889705982871907105929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2439705882620991752282477 914889705982871907105929)
                    ·
                      refine ⟨686167279487153930329447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 914889705982871907105929 686167279487153930329447)
                      ·
                        rfl

theorem cell23_1336306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_1336306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336306 prefixEnd_1336306 := by exact prefixLift 1336306
  have htrace : WordTrace (prefixWord ++ tailWord_1336306) baseStart_1336306 baseEnd_1336306 := by
    simpa [prefixWord, tailWord_1336306, baseEnd_1336306] using wordTrace_append hprefix tailTrace_1336306
  have hstable : (prefixWord ++ tailWord_1336306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336306).length < 2 ^ (prefixWord ++ tailWord_1336306).sum := by decide
  have hdescent : baseEnd_1336306 < baseStart_1336306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336392 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 4, 4, 2]
def baseStart_1336392 : Nat := 118140960795 + 1336392 * 2 ^ 59
def prefixEnd_1336392 : Nat := 4983230072969 + 3 ^ 40 * 1336392 * 2
def baseEnd_1336392 : Nat := 686211438823440593854051

theorem tailTrace_1336392 : CollatzResearch.WordTrace tailWord_1336392 prefixEnd_1336392 686211438823440593854051 := by
  unfold tailWord_1336392
  simp only [CollatzResearch.WordTrace]
  refine ⟨24371110287243748213893715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32494813716324997618524953 24371110287243748213893715)
  ·
    refine ⟨36556665430865622320840573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24371110287243748213893715 36556665430865622320840573)
    ·
      refine ⟨13708749536574608370315215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36556665430865622320840573 13708749536574608370315215)
      ·
        refine ⟨20563124304861912555472823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13708749536574608370315215 20563124304861912555472823)
        ·
          refine ⟨30844686457292868833209235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20563124304861912555472823 30844686457292868833209235)
          ·
            refine ⟨46267029685939303249813853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30844686457292868833209235 46267029685939303249813853)
            ·
              refine ⟨17350136132227238718680195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46267029685939303249813853 17350136132227238718680195)
              ·
                refine ⟨26025204198340858078020293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17350136132227238718680195 26025204198340858078020293)
                ·
                  refine ⟨4879725787188910889628805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26025204198340858078020293 4879725787188910889628805)
                  ·
                    refine ⟨914948585097920791805401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4879725787188910889628805 914948585097920791805401)
                    ·
                      refine ⟨686211438823440593854051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 914948585097920791805401 686211438823440593854051)
                      ·
                        rfl

theorem cell23_1336392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_1336392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336392 prefixEnd_1336392 := by exact prefixLift 1336392
  have htrace : WordTrace (prefixWord ++ tailWord_1336392) baseStart_1336392 baseEnd_1336392 := by
    simpa [prefixWord, tailWord_1336392, baseEnd_1336392] using wordTrace_append hprefix tailTrace_1336392
  have hstable : (prefixWord ++ tailWord_1336392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336392).length < 2 ^ (prefixWord ++ tailWord_1336392).sum := by decide
  have hdescent : baseEnd_1336392 < baseStart_1336392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336395 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 3]
def baseStart_1336395 : Nat := 118140960795 + 1336395 * 2 ^ 59
def prefixEnd_1336395 : Nat := 4983230072969 + 3 ^ 40 * 1336395 * 2
def baseEnd_1336395 : Nat := 686212979265404082116537

theorem tailTrace_1336395 : CollatzResearch.WordTrace tailWord_1336395 prefixEnd_1336395 686212979265404082116537 := by
  unfold tailWord_1336395
  simp only [CollatzResearch.WordTrace]
  refine ⟨48742329993476627940146639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32494886662317751960097759 48742329993476627940146639)
  ·
    refine ⟨73113494990214941910219959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48742329993476627940146639 73113494990214941910219959)
    ·
      refine ⟨109670242485322412865329939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73113494990214941910219959 109670242485322412865329939)
      ·
        refine ⟨164505363727983619297994909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109670242485322412865329939 164505363727983619297994909)
        ·
          refine ⟨61689511397993857236748091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164505363727983619297994909 61689511397993857236748091)
          ·
            refine ⟨92534267096990785855122137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61689511397993857236748091 92534267096990785855122137)
            ·
              refine ⟨69400700322743089391341603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92534267096990785855122137 69400700322743089391341603)
              ·
                refine ⟨104101050484114634087012405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69400700322743089391341603 104101050484114634087012405)
                ·
                  refine ⟨9759473482885746945657413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104101050484114634087012405 9759473482885746945657413)
                  ·
                    refine ⟨1829901278041077552310765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9759473482885746945657413 1829901278041077552310765)
                    ·
                      refine ⟨686212979265404082116537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1829901278041077552310765 686212979265404082116537)
                      ·
                        rfl

theorem cell23_1336395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 3].length) (baseStart_1336395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336395 prefixEnd_1336395 := by exact prefixLift 1336395
  have htrace : WordTrace (prefixWord ++ tailWord_1336395) baseStart_1336395 baseEnd_1336395 := by
    simpa [prefixWord, tailWord_1336395, baseEnd_1336395] using wordTrace_append hprefix tailTrace_1336395
  have hstable : (prefixWord ++ tailWord_1336395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336395).length < 2 ^ (prefixWord ++ tailWord_1336395).sum := by decide
  have hdescent : baseEnd_1336395 < baseStart_1336395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336405 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_1336405 : Nat := 118140960795 + 1336405 * 2 ^ 59
def prefixEnd_1336405 : Nat := 4983230072969 + 3 ^ 40 * 1336405 * 2
def baseEnd_1336405 : Nat := 686218114071949042991491

theorem tailTrace_1336405 : CollatzResearch.WordTrace tailWord_1336405 prefixEnd_1336405 686218114071949042991491 := by
  unfold tailWord_1336405
  simp only [CollatzResearch.WordTrace]
  refine ⟨48742694723440399648010669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32495129815626933098673779 48742694723440399648010669)
  ·
    refine ⟨18278510521290149868004001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48742694723440399648010669 18278510521290149868004001)
    ·
      refine ⟨13708882890967612401003001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18278510521290149868004001 13708882890967612401003001)
      ·
        refine ⟨10281662168225709300752251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13708882890967612401003001 10281662168225709300752251)
        ·
          refine ⟨15422493252338563951128377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10281662168225709300752251 15422493252338563951128377)
          ·
            refine ⟨11566869939253922963346283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15422493252338563951128377 11566869939253922963346283)
            ·
              refine ⟨17350304908880884445019425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11566869939253922963346283 17350304908880884445019425)
              ·
                refine ⟨13012728681660663333764569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17350304908880884445019425 13012728681660663333764569)
                ·
                  refine ⟨9759546511245497500323427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13012728681660663333764569 9759546511245497500323427)
                  ·
                    refine ⟨14639319766868246250485141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9759546511245497500323427 14639319766868246250485141)
                    ·
                      refine ⟨686218114071949042991491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14639319766868246250485141 686218114071949042991491)
                      ·
                        rfl

theorem cell23_1336405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_1336405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336405 prefixEnd_1336405 := by exact prefixLift 1336405
  have htrace : WordTrace (prefixWord ++ tailWord_1336405) baseStart_1336405 baseEnd_1336405 := by
    simpa [prefixWord, tailWord_1336405, baseEnd_1336405] using wordTrace_append hprefix tailTrace_1336405
  have hstable : (prefixWord ++ tailWord_1336405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336405).length < 2 ^ (prefixWord ++ tailWord_1336405).sum := by decide
  have hdescent : baseEnd_1336405 < baseStart_1336405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336412 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1336412 : Nat := 118140960795 + 1336412 * 2 ^ 59
def prefixEnd_1336412 : Nat := 4983230072969 + 3 ^ 40 * 1336412 * 2
def baseEnd_1336412 : Nat := 686221708436530515603959

theorem tailTrace_1336412 : CollatzResearch.WordTrace tailWord_1336412 prefixEnd_1336412 686221708436530515603959 := by
  unfold tailWord_1336412
  simp only [CollatzResearch.WordTrace]
  refine ⟨24371475017207519921757745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32495300022943359895676993 24371475017207519921757745)
  ·
    refine ⟨18278606262905639941318309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24371475017207519921757745 18278606262905639941318309)
    ·
      refine ⟨3427238674294807488997183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18278606262905639941318309 3427238674294807488997183)
      ·
        refine ⟨5140858011442211233495775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3427238674294807488997183 5140858011442211233495775)
        ·
          refine ⟨7711287017163316850243663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5140858011442211233495775 7711287017163316850243663)
          ·
            refine ⟨11566930525744975275365495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7711287017163316850243663 11566930525744975275365495)
            ·
              refine ⟨17350395788617462913048243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11566930525744975275365495 17350395788617462913048243)
              ·
                refine ⟨26025593682926194369572365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17350395788617462913048243 26025593682926194369572365)
                ·
                  refine ⟨9759597631097322888589637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26025593682926194369572365 9759597631097322888589637)
                  ·
                    refine ⟨1829924555830748041610557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9759597631097322888589637 1829924555830748041610557)
                    ·
                      refine ⟨686221708436530515603959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1829924555830748041610557 686221708436530515603959)
                      ·
                        rfl

theorem cell23_1336412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1336412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336412 prefixEnd_1336412 := by exact prefixLift 1336412
  have htrace : WordTrace (prefixWord ++ tailWord_1336412) baseStart_1336412 baseEnd_1336412 := by
    simpa [prefixWord, tailWord_1336412, baseEnd_1336412] using wordTrace_append hprefix tailTrace_1336412
  have hstable : (prefixWord ++ tailWord_1336412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336412).length < 2 ^ (prefixWord ++ tailWord_1336412).sum := by decide
  have hdescent : baseEnd_1336412 < baseStart_1336412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
