import V185TrunkScan23Chunk1309

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7758772 : List Nat := [2, 5, 2, 1, 1, 12]
def baseStart_7758772 : Nat := 118140960795 + 7758772 * 2 ^ 59
def prefixEnd_7758772 : Nat := 4983230072969 + 3 ^ 40 * 7758772 * 2
def baseEnd_7758772 : Nat := 16394976644633839516741

theorem tailTrace_7758772 : CollatzResearch.WordTrace tailWord_7758772 prefixEnd_7758772 16394976644633839516741 := by
  unfold tailWord_7758772
  simp only [CollatzResearch.WordTrace]
  refine ⟨141492831523650805803343285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188657108698201074404457713 141492831523650805803343285)
  ·
    refine ⟨13264952955342263044063433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141492831523650805803343285 13264952955342263044063433)
    ·
      refine ⟨9948714716506697283047575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13264952955342263044063433 9948714716506697283047575)
      ·
        refine ⟨14923072074760045924571363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9948714716506697283047575 14923072074760045924571363)
        ·
          refine ⟨22384608112140068886857045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14923072074760045924571363 22384608112140068886857045)
          ·
            refine ⟨16394976644633839516741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 22384608112140068886857045 16394976644633839516741)
            ·
              rfl

theorem cell23_7758772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 12].length) (baseStart_7758772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758772 prefixEnd_7758772 := by exact prefixLift 7758772
  have htrace : WordTrace (prefixWord ++ tailWord_7758772) baseStart_7758772 baseEnd_7758772 := by
    simpa [prefixWord, tailWord_7758772, baseEnd_7758772] using wordTrace_append hprefix tailTrace_7758772
  have hstable : (prefixWord ++ tailWord_7758772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758772).length < 2 ^ (prefixWord ++ tailWord_7758772).sum := by decide
  have hdescent : baseEnd_7758772 < baseStart_7758772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758782 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_7758782 : Nat := 118140960795 + 7758782 * 2 ^ 59
def prefixEnd_7758782 : Nat := 4983230072969 + 3 ^ 40 * 7758782 * 2
def baseEnd_7758782 : Nat := 3983984459452567963443017

theorem tailTrace_7758782 : CollatzResearch.WordTrace tailWord_7758782 prefixEnd_7758782 3983984459452567963443017 := by
  unfold tailWord_7758782
  simp only [CollatzResearch.WordTrace]
  refine ⟨35373253472158172914318825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188657351851510255543033733 35373253472158172914318825)
  ·
    refine ⟨26529940104118629685739119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35373253472158172914318825 26529940104118629685739119)
    ·
      refine ⟨39794910156177944528608679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26529940104118629685739119 39794910156177944528608679)
      ·
        refine ⟨59692365234266916792913019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39794910156177944528608679 59692365234266916792913019)
        ·
          refine ⟨89538547851400375189369529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59692365234266916792913019 89538547851400375189369529)
          ·
            refine ⟨67153910888550281392027147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89538547851400375189369529 67153910888550281392027147)
            ·
              refine ⟨100730866332825422088040721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67153910888550281392027147 100730866332825422088040721)
              ·
                refine ⟨75548149749619066566030541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100730866332825422088040721 75548149749619066566030541)
                ·
                  refine ⟨28330556156107149962261453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75548149749619066566030541 28330556156107149962261453)
                  ·
                    refine ⟨10623958558540181235848045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28330556156107149962261453 10623958558540181235848045)
                    ·
                      refine ⟨3983984459452567963443017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10623958558540181235848045 3983984459452567963443017)
                      ·
                        rfl

theorem cell23_7758782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_7758782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758782 prefixEnd_7758782 := by exact prefixLift 7758782
  have htrace : WordTrace (prefixWord ++ tailWord_7758782) baseStart_7758782 baseEnd_7758782 := by
    simpa [prefixWord, tailWord_7758782, baseEnd_7758782] using wordTrace_append hprefix tailTrace_7758782
  have hstable : (prefixWord ++ tailWord_7758782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758782).length < 2 ^ (prefixWord ++ tailWord_7758782).sum := by decide
  have hdescent : baseEnd_7758782 < baseStart_7758782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758799 : List Nat := [1, 1, 2, 1, 1, 6, 2, 3, 2, 1, 3]
def baseStart_7758799 : Nat := 118140960795 + 7758799 * 2 ^ 59
def prefixEnd_7758799 : Nat := 4983230072969 + 3 ^ 40 * 7758799 * 2
def baseEnd_7758799 : Nat := 3983993188623694396930439

theorem tailTrace_7758799 : CollatzResearch.WordTrace tailWord_7758799 prefixEnd_7758799 3983993188623694396930439 := by
  unfold tailWord_7758799
  simp only [CollatzResearch.WordTrace]
  refine ⟨282986647818203795217919451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188657765212135863478612967 282986647818203795217919451)
  ·
    refine ⟨424479971727305692826879177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282986647818203795217919451 424479971727305692826879177)
    ·
      refine ⟨318359978795479269620159383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424479971727305692826879177 318359978795479269620159383)
      ·
        refine ⟨477539968193218904430239075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318359978795479269620159383 477539968193218904430239075)
        ·
          refine ⟨716309952289828356645358613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477539968193218904430239075 716309952289828356645358613)
          ·
            refine ⟨33577029013585704217751185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 716309952289828356645358613 33577029013585704217751185)
            ·
              refine ⟨25182771760189278163313389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33577029013585704217751185 25182771760189278163313389)
              ·
                refine ⟨9443539410070979311242521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25182771760189278163313389 9443539410070979311242521)
                ·
                  refine ⟨7082654557553234483431891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9443539410070979311242521 7082654557553234483431891)
                  ·
                    refine ⟨10623981836329851725147837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7082654557553234483431891 10623981836329851725147837)
                    ·
                      refine ⟨3983993188623694396930439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10623981836329851725147837 3983993188623694396930439)
                      ·
                        rfl

theorem cell23_7758799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 1, 3].length) (baseStart_7758799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758799 prefixEnd_7758799 := by exact prefixLift 7758799
  have htrace : WordTrace (prefixWord ++ tailWord_7758799) baseStart_7758799 baseEnd_7758799 := by
    simpa [prefixWord, tailWord_7758799, baseEnd_7758799] using wordTrace_append hprefix tailTrace_7758799
  have hstable : (prefixWord ++ tailWord_7758799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758799).length < 2 ^ (prefixWord ++ tailWord_7758799).sum := by decide
  have hdescent : baseEnd_7758799 < baseStart_7758799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758809 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 3, 3, 2]
def baseStart_7758809 : Nat := 118140960795 + 7758809 * 2 ^ 59
def prefixEnd_7758809 : Nat := 4983230072969 + 3 ^ 40 * 7758809 * 2
def baseEnd_7758809 : Nat := 3983998323430239357805393

theorem tailTrace_7758809 : CollatzResearch.WordTrace tailWord_7758809 prefixEnd_7758809 3983998323430239357805393 := by
  unfold tailWord_7758809
  simp only [CollatzResearch.WordTrace]
  refine ⟨282987012548167566925783481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188658008365445044617188987 282987012548167566925783481)
  ·
    refine ⟨212240259411125675194337611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282987012548167566925783481 212240259411125675194337611)
    ·
      refine ⟨318360389116688512791506417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212240259411125675194337611 318360389116688512791506417)
      ·
        refine ⟨238770291837516384593629813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318360389116688512791506417 238770291837516384593629813)
        ·
          refine ⟨22384714859767161055652795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238770291837516384593629813 22384714859767161055652795)
          ·
            refine ⟨33577072289650741583479193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22384714859767161055652795 33577072289650741583479193)
            ·
              refine ⟨25182804217238056187609395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33577072289650741583479193 25182804217238056187609395)
              ·
                refine ⟨37774206325857084281414093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25182804217238056187609395 37774206325857084281414093)
                ·
                  refine ⟨14165327372196406605530285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37774206325857084281414093 14165327372196406605530285)
                  ·
                    refine ⟨5311997764573652477073857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14165327372196406605530285 5311997764573652477073857)
                    ·
                      refine ⟨3983998323430239357805393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5311997764573652477073857 3983998323430239357805393)
                      ·
                        rfl

theorem cell23_7758809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 3, 2].length) (baseStart_7758809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758809 prefixEnd_7758809 := by exact prefixLift 7758809
  have htrace : WordTrace (prefixWord ++ tailWord_7758809) baseStart_7758809 baseEnd_7758809 := by
    simpa [prefixWord, tailWord_7758809, baseEnd_7758809] using wordTrace_append hprefix tailTrace_7758809
  have hstable : (prefixWord ++ tailWord_7758809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758809).length < 2 ^ (prefixWord ++ tailWord_7758809).sum := by decide
  have hdescent : baseEnd_7758809 < baseStart_7758809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758826 : List Nat := [3, 1, 3, 1, 2, 3, 1, 3, 1, 3, 2]
def baseStart_7758826 : Nat := 118140960795 + 7758826 * 2 ^ 59
def prefixEnd_7758826 : Nat := 4983230072969 + 3 ^ 40 * 7758826 * 2
def baseEnd_7758826 : Nat := 3984007052601365791292815

theorem tailTrace_7758826 : CollatzResearch.WordTrace tailWord_7758826 prefixEnd_7758826 3984007052601365791292815 := by
  unfold tailWord_7758826
  simp only [CollatzResearch.WordTrace]
  refine ⟨70746908147276494707288083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188658421726070652552768221 70746908147276494707288083)
  ·
    refine ⟨106120362220914742060932125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70746908147276494707288083 106120362220914742060932125)
    ·
      refine ⟨39795135832843028272849547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106120362220914742060932125 39795135832843028272849547)
      ·
        refine ⟨59692703749264542409274321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39795135832843028272849547 59692703749264542409274321)
        ·
          refine ⟨44769527811948406806955741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59692703749264542409274321 44769527811948406806955741)
          ·
            refine ⟨16788572929480652552608403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44769527811948406806955741 16788572929480652552608403)
            ·
              refine ⟨25182859394220978828912605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16788572929480652552608403 25182859394220978828912605)
              ·
                refine ⟨9443572272832867060842227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25182859394220978828912605 9443572272832867060842227)
                ·
                  refine ⟨14165358409249300591263341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9443572272832867060842227 14165358409249300591263341)
                  ·
                    refine ⟨5312009403468487721723753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14165358409249300591263341 5312009403468487721723753)
                    ·
                      refine ⟨3984007052601365791292815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5312009403468487721723753 3984007052601365791292815)
                      ·
                        rfl

theorem cell23_7758826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_7758826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758826 prefixEnd_7758826 := by exact prefixLift 7758826
  have htrace : WordTrace (prefixWord ++ tailWord_7758826) baseStart_7758826 baseEnd_7758826 := by
    simpa [prefixWord, tailWord_7758826, baseEnd_7758826] using wordTrace_append hprefix tailTrace_7758826
  have hstable : (prefixWord ++ tailWord_7758826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758826).length < 2 ^ (prefixWord ++ tailWord_7758826).sum := by decide
  have hdescent : baseEnd_7758826 < baseStart_7758826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758850 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_7758850 : Nat := 118140960795 + 7758850 * 2 ^ 59
def prefixEnd_7758850 : Nat := 4983230072969 + 3 ^ 40 * 7758850 * 2
def baseEnd_7758850 : Nat := 3984019376137073697392705

theorem tailTrace_7758850 : CollatzResearch.WordTrace tailWord_7758850 prefixEnd_7758850 3984019376137073697392705 := by
  unfold tailWord_7758850
  simp only [CollatzResearch.WordTrace]
  refine ⟨70747126985254757732006501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188659005294012687285350669 70747126985254757732006501)
  ·
    refine ⟨13265086309735267074751219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70747126985254757732006501 13265086309735267074751219)
    ·
      refine ⟨19897629464602900612126829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13265086309735267074751219 19897629464602900612126829)
      ·
        refine ⟨7461611049226087729547561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19897629464602900612126829 7461611049226087729547561)
        ·
          refine ⟨5596208286919565797160671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7461611049226087729547561 5596208286919565797160671)
          ·
            refine ⟨8394312430379348695741007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5596208286919565797160671 8394312430379348695741007)
            ·
              refine ⟨12591468645569023043611511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8394312430379348695741007 12591468645569023043611511)
              ·
                refine ⟨18887202968353534565417267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12591468645569023043611511 18887202968353534565417267)
                ·
                  refine ⟨28330804452530301848125901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18887202968353534565417267 28330804452530301848125901)
                  ·
                    refine ⟨10624051669698863193047213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28330804452530301848125901 10624051669698863193047213)
                    ·
                      refine ⟨3984019376137073697392705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10624051669698863193047213 3984019376137073697392705)
                      ·
                        rfl

theorem cell23_7758850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_7758850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758850 prefixEnd_7758850 := by exact prefixLift 7758850
  have htrace : WordTrace (prefixWord ++ tailWord_7758850) baseStart_7758850 baseEnd_7758850 := by
    simpa [prefixWord, tailWord_7758850, baseEnd_7758850] using wordTrace_append hprefix tailTrace_7758850
  have hstable : (prefixWord ++ tailWord_7758850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758850).length < 2 ^ (prefixWord ++ tailWord_7758850).sum := by decide
  have hdescent : baseEnd_7758850 < baseStart_7758850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758856 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 1, 4, 2]
def baseStart_7758856 : Nat := 118140960795 + 7758856 * 2 ^ 59
def prefixEnd_7758856 : Nat := 4983230072969 + 3 ^ 40 * 7758856 * 2
def baseEnd_7758856 : Nat := 3984022457021000673917677

theorem tailTrace_7758856 : CollatzResearch.WordTrace tailWord_7758856 prefixEnd_7758856 3984022457021000673917677 := by
  unfold tailWord_7758856
  simp only [CollatzResearch.WordTrace]
  refine ⟨141494363389498646976372211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188659151185998195968496281 141494363389498646976372211)
  ·
    refine ⟨212241545084247970464558317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141494363389498646976372211 212241545084247970464558317)
    ·
      refine ⟨79590579406592988924209369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212241545084247970464558317 79590579406592988924209369)
      ·
        refine ⟨59692934554944741693157027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79590579406592988924209369 59692934554944741693157027)
        ·
          refine ⟨89539401832417112539735541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59692934554944741693157027 89539401832417112539735541)
          ·
            refine ⟨8394318921789104300600207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89539401832417112539735541 8394318921789104300600207)
            ·
              refine ⟨12591478382683656450900311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8394318921789104300600207 12591478382683656450900311)
              ·
                refine ⟨18887217574025484676350467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12591478382683656450900311 18887217574025484676350467)
                ·
                  refine ⟨28330826361038227014525701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18887217574025484676350467 28330826361038227014525701)
                  ·
                    refine ⟨5312029942694667565223569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28330826361038227014525701 5312029942694667565223569)
                    ·
                      refine ⟨3984022457021000673917677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5312029942694667565223569 3984022457021000673917677)
                      ·
                        rfl

theorem cell23_7758856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_7758856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758856 prefixEnd_7758856 := by exact prefixLift 7758856
  have htrace : WordTrace (prefixWord ++ tailWord_7758856) baseStart_7758856 baseEnd_7758856 := by
    simpa [prefixWord, tailWord_7758856, baseEnd_7758856] using wordTrace_append hprefix tailTrace_7758856
  have hstable : (prefixWord ++ tailWord_7758856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758856).length < 2 ^ (prefixWord ++ tailWord_7758856).sum := by decide
  have hdescent : baseEnd_7758856 < baseStart_7758856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758862 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 7]
def baseStart_7758862 : Nat := 118140960795 + 7758862 * 2 ^ 59
def prefixEnd_7758862 : Nat := 4983230072969 + 3 ^ 40 * 7758862 * 2
def baseEnd_7758862 : Nat := 442669504211658627826961

theorem tailTrace_7758862 : CollatzResearch.WordTrace tailWord_7758862 prefixEnd_7758862 442669504211658627826961 := by
  unfold tailWord_7758862
  simp only [CollatzResearch.WordTrace]
  refine ⟨35373618202121944622182855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188659297077983704651641893 35373618202121944622182855)
  ·
    refine ⟨53060427303182916933274283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35373618202121944622182855 53060427303182916933274283)
    ·
      refine ⟨79590640954774375399911425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53060427303182916933274283 79590640954774375399911425)
      ·
        refine ⟨59692980716080781549933569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79590640954774375399911425 59692980716080781549933569)
        ·
          refine ⟨44769735537060586162450177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59692980716080781549933569 44769735537060586162450177)
          ·
            refine ⟨33577301652795439621837633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44769735537060586162450177 33577301652795439621837633)
            ·
              refine ⟨25182976239596579716378225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33577301652795439621837633 25182976239596579716378225)
              ·
                refine ⟨18887232179697434787283669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25182976239596579716378225 18887232179697434787283669)
                ·
                  refine ⟨442669504211658627826961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18887232179697434787283669 442669504211658627826961)
                  ·
                    rfl

theorem cell23_7758862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_7758862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758862 prefixEnd_7758862 := by exact prefixLift 7758862
  have htrace : WordTrace (prefixWord ++ tailWord_7758862) baseStart_7758862 baseEnd_7758862 := by
    simpa [prefixWord, tailWord_7758862, baseEnd_7758862] using wordTrace_append hprefix tailTrace_7758862
  have hstable : (prefixWord ++ tailWord_7758862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758862).length < 2 ^ (prefixWord ++ tailWord_7758862).sum := by decide
  have hdescent : baseEnd_7758862 < baseStart_7758862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758879 : List Nat := [1, 1, 2, 4, 1, 3, 3, 3, 5]
def baseStart_7758879 : Nat := 118140960795 + 7758879 * 2 ^ 59
def prefixEnd_7758879 : Nat := 4983230072969 + 3 ^ 40 * 7758879 * 2
def baseEnd_7758879 : Nat := 442670474119561564881119

theorem tailTrace_7758879 : CollatzResearch.WordTrace tailWord_7758879 prefixEnd_7758879 442670474119561564881119 := by
  unfold tailWord_7758879
  simp only [CollatzResearch.WordTrace]
  refine ⟨282989565657913968880831691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188659710438609312587221127 282989565657913968880831691)
  ·
    refine ⟨424484348486870953321247537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282989565657913968880831691 424484348486870953321247537)
    ·
      refine ⟨318363261365153214990935653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424484348486870953321247537 318363261365153214990935653)
      ·
        refine ⟨59693111505966227810800435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318363261365153214990935653 59693111505966227810800435)
        ·
          refine ⟨89539667258949341716200653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59693111505966227810800435 89539667258949341716200653)
          ·
            refine ⟨33577375222106003143575245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89539667258949341716200653 33577375222106003143575245)
            ·
              refine ⟨12591515708289751178840717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33577375222106003143575245 12591515708289751178840717)
              ·
                refine ⟨4721818390608656692065269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12591515708289751178840717 4721818390608656692065269)
                ·
                  refine ⟨442670474119561564881119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4721818390608656692065269 442670474119561564881119)
                  ·
                    rfl

theorem cell23_7758879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 5].length) (baseStart_7758879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758879 prefixEnd_7758879 := by exact prefixLift 7758879
  have htrace : WordTrace (prefixWord ++ tailWord_7758879) baseStart_7758879 baseEnd_7758879 := by
    simpa [prefixWord, tailWord_7758879, baseEnd_7758879] using wordTrace_append hprefix tailTrace_7758879
  have hstable : (prefixWord ++ tailWord_7758879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758879).length < 2 ^ (prefixWord ++ tailWord_7758879).sum := by decide
  have hdescent : baseEnd_7758879 < baseStart_7758879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758892 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 2, 5]
def baseStart_7758892 : Nat := 118140960795 + 7758892 * 2 ^ 59
def prefixEnd_7758892 : Nat := 4983230072969 + 3 ^ 40 * 7758892 * 2
def baseEnd_7758892 : Nat := 1328013647441520844355837

theorem tailTrace_7758892 : CollatzResearch.WordTrace tailWord_7758892 prefixEnd_7758892 1328013647441520844355837 := by
  unfold tailWord_7758892
  simp only [CollatzResearch.WordTrace]
  refine ⟨141495019903433436050527465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188660026537911248067369953 141495019903433436050527465)
  ·
    refine ⟨106121264927575077037895599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141495019903433436050527465 106121264927575077037895599)
    ·
      refine ⟨159181897391362615556843399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106121264927575077037895599 159181897391362615556843399)
      ·
        refine ⟨238772846087043923335265099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159181897391362615556843399 238772846087043923335265099)
        ·
          refine ⟨358159269130565885002897649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238772846087043923335265099 358159269130565885002897649)
          ·
            refine ⟨268619451847924413752173237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358159269130565885002897649 268619451847924413752173237)
            ·
              refine ⟨25183073610742913789266241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 268619451847924413752173237 25183073610742913789266241)
              ·
                refine ⟨18887305208057185341949681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25183073610742913789266241 18887305208057185341949681)
                ·
                  refine ⟨14165478906042889006462261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18887305208057185341949681 14165478906042889006462261)
                  ·
                    refine ⟨1328013647441520844355837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14165478906042889006462261 1328013647441520844355837)
                    ·
                      rfl

theorem cell23_7758892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_7758892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758892 prefixEnd_7758892 := by exact prefixLift 7758892
  have htrace : WordTrace (prefixWord ++ tailWord_7758892) baseStart_7758892 baseEnd_7758892 := by
    simpa [prefixWord, tailWord_7758892, baseEnd_7758892] using wordTrace_append hprefix tailTrace_7758892
  have hstable : (prefixWord ++ tailWord_7758892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758892).length < 2 ^ (prefixWord ++ tailWord_7758892).sum := by decide
  have hdescent : baseEnd_7758892 < baseStart_7758892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758912 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 4]
def baseStart_7758912 : Nat := 118140960795 + 7758912 * 2 ^ 59
def prefixEnd_7758912 : Nat := 4983230072969 + 3 ^ 40 * 7758912 * 2
def baseEnd_7758912 : Nat := 3984051211937652454817419

theorem tailTrace_7758912 : CollatzResearch.WordTrace tailWord_7758912 prefixEnd_7758912 3984051211937652454817419 := by
  unfold tailWord_7758912
  simp only [CollatzResearch.WordTrace]
  refine ⟨141495384633397207758391495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188660512844529610344521993 141495384633397207758391495)
  ·
    refine ⟨212243076950095811637587243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141495384633397207758391495 212243076950095811637587243)
    ·
      refine ⟨318364615425143717456380865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212243076950095811637587243 318364615425143717456380865)
      ·
        refine ⟨238773461568857788092285649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318364615425143717456380865 238773461568857788092285649)
        ·
          refine ⟨179080096176643341069214237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238773461568857788092285649 179080096176643341069214237)
          ·
            refine ⟨67155036066241252900955339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179080096176643341069214237 67155036066241252900955339)
            ·
              refine ⟨100732554099361879351433009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67155036066241252900955339 100732554099361879351433009)
              ·
                refine ⟨75549415574521409513574757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100732554099361879351433009 75549415574521409513574757)
                ·
                  refine ⟨14165515420222764283795267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75549415574521409513574757 14165515420222764283795267)
                  ·
                    refine ⟨21248273130334146425692901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14165515420222764283795267 21248273130334146425692901)
                    ·
                      refine ⟨3984051211937652454817419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21248273130334146425692901 3984051211937652454817419)
                      ·
                        rfl

theorem cell23_7758912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_7758912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758912 prefixEnd_7758912 := by exact prefixLift 7758912
  have htrace : WordTrace (prefixWord ++ tailWord_7758912) baseStart_7758912 baseEnd_7758912 := by
    simpa [prefixWord, tailWord_7758912, baseEnd_7758912] using wordTrace_append hprefix tailTrace_7758912
  have hstable : (prefixWord ++ tailWord_7758912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758912).length < 2 ^ (prefixWord ++ tailWord_7758912).sum := by decide
  have hdescent : baseEnd_7758912 < baseStart_7758912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758946 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_7758946 : Nat := 118140960795 + 7758946 * 2 ^ 59
def prefixEnd_7758946 : Nat := 4983230072969 + 3 ^ 40 * 7758946 * 2
def baseEnd_7758946 : Nat := 3984068670279905321792263

theorem tailTrace_7758946 : CollatzResearch.WordTrace tailWord_7758946 prefixEnd_7758946 3984068670279905321792263 := by
  unfold tailWord_7758946
  simp only [CollatzResearch.WordTrace]
  refine ⟨70748002337167809830880173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188661339565780826215680461 70748002337167809830880173)
  ·
    refine ⟨26530500876437928686580065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70748002337167809830880173 26530500876437928686580065)
    ·
      refine ⟨19897875657328446514935049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26530500876437928686580065 19897875657328446514935049)
      ·
        refine ⟨14923406742996334886201287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19897875657328446514935049 14923406742996334886201287)
        ·
          refine ⟨22385110114494502329301931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14923406742996334886201287 22385110114494502329301931)
          ·
            refine ⟨33577665171741753493952897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22385110114494502329301931 33577665171741753493952897)
            ·
              refine ⟨25183248878806315120464673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33577665171741753493952897 25183248878806315120464673)
              ·
                refine ⟨18887436659104736340348505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25183248878806315120464673 18887436659104736340348505)
                ·
                  refine ⟨14165577494328552255261379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18887436659104736340348505 14165577494328552255261379)
                  ·
                    refine ⟨21248366241492828382892069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14165577494328552255261379 21248366241492828382892069)
                    ·
                      refine ⟨3984068670279905321792263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21248366241492828382892069 3984068670279905321792263)
                      ·
                        rfl

theorem cell23_7758946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_7758946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758946 prefixEnd_7758946 := by exact prefixLift 7758946
  have htrace : WordTrace (prefixWord ++ tailWord_7758946) baseStart_7758946 baseEnd_7758946 := by
    simpa [prefixWord, tailWord_7758946, baseEnd_7758946] using wordTrace_append hprefix tailTrace_7758946
  have hstable : (prefixWord ++ tailWord_7758946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758946).length < 2 ^ (prefixWord ++ tailWord_7758946).sum := by decide
  have hdescent : baseEnd_7758946 < baseStart_7758946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758949 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 2, 2, 3]
def baseStart_7758949 : Nat := 118140960795 + 7758949 * 2 ^ 59
def prefixEnd_7758949 : Nat := 4983230072969 + 3 ^ 40 * 7758949 * 2
def baseEnd_7758949 : Nat := 3984070210721868810054749

theorem tailTrace_7758949 : CollatzResearch.WordTrace tailWord_7758949 prefixEnd_7758949 3984070210721868810054749 := by
  unfold tailWord_7758949
  simp only [CollatzResearch.WordTrace]
  refine ⟨282992118767660370835879901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188661412511773580557253267 282992118767660370835879901)
  ·
    refine ⟨106122044537872639063454963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282992118767660370835879901 106122044537872639063454963)
    ·
      refine ⟨159183066806808958595182445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106122044537872639063454963 159183066806808958595182445)
      ·
        refine ⟨59693650052553359473193417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159183066806808958595182445 59693650052553359473193417)
        ·
          refine ⟨44770237539415019604895063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59693650052553359473193417 44770237539415019604895063)
          ·
            refine ⟨67155356309122529407342595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44770237539415019604895063 67155356309122529407342595)
            ·
              refine ⟨100733034463683794111013893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67155356309122529407342595 100733034463683794111013893)
              ·
                refine ⟨18887443961940711395815105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100733034463683794111013893 18887443961940711395815105)
                ·
                  refine ⟨14165582971455533546861329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18887443961940711395815105 14165582971455533546861329)
                  ·
                    refine ⟨10624187228591650160145997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14165582971455533546861329 10624187228591650160145997)
                    ·
                      refine ⟨3984070210721868810054749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10624187228591650160145997 3984070210721868810054749)
                      ·
                        rfl

theorem cell23_7758949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_7758949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758949 prefixEnd_7758949 := by exact prefixLift 7758949
  have htrace : WordTrace (prefixWord ++ tailWord_7758949) baseStart_7758949 baseEnd_7758949 := by
    simpa [prefixWord, tailWord_7758949, baseEnd_7758949] using wordTrace_append hprefix tailTrace_7758949
  have hstable : (prefixWord ++ tailWord_7758949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758949).length < 2 ^ (prefixWord ++ tailWord_7758949).sum := by decide
  have hdescent : baseEnd_7758949 < baseStart_7758949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758956 : List Nat := [2, 2, 1, 1, 3, 2, 3, 4, 1, 4]
def baseStart_7758956 : Nat := 118140960795 + 7758956 * 2 ^ 59
def prefixEnd_7758956 : Nat := 4983230072969 + 3 ^ 40 * 7758956 * 2
def baseEnd_7758956 : Nat := 1328024601695483427555739

theorem tailTrace_7758956 : CollatzResearch.WordTrace tailWord_7758956 prefixEnd_7758956 1328024601695483427555739 := by
  unfold tailWord_7758956
  simp only [CollatzResearch.WordTrace]
  refine ⟨141496187039317505515692361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188661582719090007354256481 141496187039317505515692361)
  ·
    refine ⟨106122140279488129136769271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141496187039317505515692361 106122140279488129136769271)
    ·
      refine ⟨159183210419232193705153907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106122140279488129136769271 159183210419232193705153907)
      ·
        refine ⟨238774815628848290557730861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159183210419232193705153907 238774815628848290557730861)
        ·
          refine ⟨89540555860818108959149073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238774815628848290557730861 89540555860818108959149073)
          ·
            refine ⟨67155416895613581719361805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89540555860818108959149073 67155416895613581719361805)
            ·
              refine ⟨25183281335855093144760677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67155416895613581719361805 25183281335855093144760677)
              ·
                refine ⟨4721865250472829964642627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25183281335855093144760677 4721865250472829964642627)
                ·
                  refine ⟨7082797875709244946963941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4721865250472829964642627 7082797875709244946963941)
                  ·
                    refine ⟨1328024601695483427555739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7082797875709244946963941 1328024601695483427555739)
                    ·
                      rfl

theorem cell23_7758956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 1, 4].length) (baseStart_7758956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758956 prefixEnd_7758956 := by exact prefixLift 7758956
  have htrace : WordTrace (prefixWord ++ tailWord_7758956) baseStart_7758956 baseEnd_7758956 := by
    simpa [prefixWord, tailWord_7758956, baseEnd_7758956] using wordTrace_append hprefix tailTrace_7758956
  have hstable : (prefixWord ++ tailWord_7758956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758956).length < 2 ^ (prefixWord ++ tailWord_7758956).sum := by decide
  have hdescent : baseEnd_7758956 < baseStart_7758956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759013 : List Nat := [1, 3, 1, 2, 1, 4, 2, 4, 1, 1, 3]
def baseStart_7759013 : Nat := 118140960795 + 7759013 * 2 ^ 59
def prefixEnd_7759013 : Nat := 4983230072969 + 3 ^ 40 * 7759013 * 2
def baseEnd_7759013 : Nat := 3984103073483756559654455

theorem tailTrace_7759013 : CollatzResearch.WordTrace tailWord_7759013 prefixEnd_7759013 3984103073483756559654455 := by
  unfold tailWord_7759013
  simp only [CollatzResearch.WordTrace]
  refine ⟨282994453039428509766209693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188662968692952339844139795 282994453039428509766209693)
  ·
    refine ⟨106122919889785691162328635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282994453039428509766209693 106122919889785691162328635)
    ·
      refine ⟨159184379834678536743492953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106122919889785691162328635 159184379834678536743492953)
      ·
        refine ⟨119388284876008902557619715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159184379834678536743492953 119388284876008902557619715)
        ·
          refine ⟨179082427314013353836429573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119388284876008902557619715 179082427314013353836429573)
          ·
            refine ⟨33577955121377503844330545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179082427314013353836429573 33577955121377503844330545)
            ·
              refine ⟨25183466341033127883247909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33577955121377503844330545 25183466341033127883247909)
              ·
                refine ⟨4721899938943711478108983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25183466341033127883247909 4721899938943711478108983)
                ·
                  refine ⟨7082849908415567217163475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4721899938943711478108983 7082849908415567217163475)
                  ·
                    refine ⟨10624274862623350825745213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7082849908415567217163475 10624274862623350825745213)
                    ·
                      refine ⟨3984103073483756559654455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10624274862623350825745213 3984103073483756559654455)
                      ·
                        rfl

theorem cell23_7759013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_7759013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759013 prefixEnd_7759013 := by exact prefixLift 7759013
  have htrace : WordTrace (prefixWord ++ tailWord_7759013) baseStart_7759013 baseEnd_7759013 := by
    simpa [prefixWord, tailWord_7759013, baseEnd_7759013] using wordTrace_append hprefix tailTrace_7759013
  have hstable : (prefixWord ++ tailWord_7759013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759013).length < 2 ^ (prefixWord ++ tailWord_7759013).sum := by decide
  have hdescent : baseEnd_7759013 < baseStart_7759013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759036 : List Nat := [2, 2, 2, 3, 2, 1, 1, 4, 1, 1, 4]
def baseStart_7759036 : Nat := 118140960795 + 7759036 * 2 ^ 59
def prefixEnd_7759036 : Nat := 4983230072969 + 3 ^ 40 * 7759036 * 2
def baseEnd_7759036 : Nat := 3984114883538809969666849

theorem tailTrace_7759036 : CollatzResearch.WordTrace tailWord_7759036 prefixEnd_7759036 3984114883538809969666849 := by
  unfold tailWord_7759036
  simp only [CollatzResearch.WordTrace]
  refine ⟨141497645959172592347148481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188663527945563456462864641 141497645959172592347148481)
  ·
    refine ⟨106123234469379444260361361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141497645959172592347148481 106123234469379444260361361)
    ·
      refine ⟨79592425852034583195271021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106123234469379444260361361 79592425852034583195271021)
      ·
        refine ⟨29847159694512968698226633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79592425852034583195271021 29847159694512968698226633)
        ·
          refine ⟨22385369770884726523669975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29847159694512968698226633 22385369770884726523669975)
          ·
            refine ⟨33578054656327089785504963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22385369770884726523669975 33578054656327089785504963)
            ·
              refine ⟨50367081984490634678257445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33578054656327089785504963 50367081984490634678257445)
              ·
                refine ⟨9443827872091994002173271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50367081984490634678257445 9443827872091994002173271)
                ·
                  refine ⟨14165741808137991003259907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9443827872091994002173271 14165741808137991003259907)
                  ·
                    refine ⟨21248612712206986504889861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14165741808137991003259907 21248612712206986504889861)
                    ·
                      refine ⟨3984114883538809969666849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21248612712206986504889861 3984114883538809969666849)
                      ·
                        rfl

theorem cell23_7759036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_7759036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759036 prefixEnd_7759036 := by exact prefixLift 7759036
  have htrace : WordTrace (prefixWord ++ tailWord_7759036) baseStart_7759036 baseEnd_7759036 := by
    simpa [prefixWord, tailWord_7759036, baseEnd_7759036] using wordTrace_append hprefix tailTrace_7759036
  have hstable : (prefixWord ++ tailWord_7759036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759036).length < 2 ^ (prefixWord ++ tailWord_7759036).sum := by decide
  have hdescent : baseEnd_7759036 < baseStart_7759036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759039 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 3]
def baseStart_7759039 : Nat := 118140960795 + 7759039 * 2 ^ 59
def prefixEnd_7759039 : Nat := 4983230072969 + 3 ^ 40 * 7759039 * 2
def baseEnd_7759039 : Nat := 3984116423980773457929335

theorem tailTrace_7759039 : CollatzResearch.WordTrace tailWord_7759039 prefixEnd_7759039 3984116423980773457929335 := by
  unfold tailWord_7759039
  simp only [CollatzResearch.WordTrace]
  refine ⟨282995401337334316206656171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188663600891556210804437447 282995401337334316206656171)
  ·
    refine ⟨424493102006001474309984257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282995401337334316206656171 424493102006001474309984257)
    ·
      refine ⟨318369826504501105732488193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424493102006001474309984257 318369826504501105732488193)
      ·
        refine ⟨238777369878375829299366145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318369826504501105732488193 238777369878375829299366145)
        ·
          refine ⟨179083027408781871974524609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238777369878375829299366145 179083027408781871974524609)
          ·
            refine ⟨134312270556586403980893457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179083027408781871974524609 134312270556586403980893457)
            ·
              refine ⟨100734202917439802985670093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134312270556586403980893457 100734202917439802985670093)
              ·
                refine ⟨37775326094039926119626285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100734202917439802985670093 37775326094039926119626285)
                ·
                  refine ⟨14165747285264972294859857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37775326094039926119626285 14165747285264972294859857)
                  ·
                    refine ⟨10624310463948729221144893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14165747285264972294859857 10624310463948729221144893)
                    ·
                      refine ⟨3984116423980773457929335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10624310463948729221144893 3984116423980773457929335)
                      ·
                        rfl

theorem cell23_7759039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_7759039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759039 prefixEnd_7759039 := by exact prefixLift 7759039
  have htrace : WordTrace (prefixWord ++ tailWord_7759039) baseStart_7759039 baseEnd_7759039 := by
    simpa [prefixWord, tailWord_7759039, baseEnd_7759039] using wordTrace_append hprefix tailTrace_7759039
  have hstable : (prefixWord ++ tailWord_7759039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759039).length < 2 ^ (prefixWord ++ tailWord_7759039).sum := by decide
  have hdescent : baseEnd_7759039 < baseStart_7759039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759090 : List Nat := [3, 2, 1, 3, 3, 2, 1, 2, 1, 2, 3]
def baseStart_7759090 : Nat := 118140960795 + 7759090 * 2 ^ 59
def prefixEnd_7759090 : Nat := 4983230072969 + 3 ^ 40 * 7759090 * 2
def baseEnd_7759090 : Nat := 3984142611494152758391601

theorem tailTrace_7759090 : CollatzResearch.WordTrace tailWord_7759090 prefixEnd_7759090 3984142611494152758391601 := by
  unfold tailWord_7759090
  simp only [CollatzResearch.WordTrace]
  refine ⟨70749315365037387979190681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188664840973433034611175149 70749315365037387979190681)
  ·
    refine ⟨53061986523778040984393011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70749315365037387979190681 53061986523778040984393011)
    ·
      refine ⟨79592979785667061476589517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53061986523778040984393011 79592979785667061476589517)
      ·
        refine ⟨29847367419625148053721069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79592979785667061476589517 29847367419625148053721069)
        ·
          refine ⟨11192762782359430520145401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29847367419625148053721069 11192762782359430520145401)
          ·
            refine ⟨8394572086769572890109051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11192762782359430520145401 8394572086769572890109051)
            ·
              refine ⟨12591858130154359335163577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8394572086769572890109051 12591858130154359335163577)
              ·
                refine ⟨9443893597615769501372683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12591858130154359335163577 9443893597615769501372683)
                ·
                  refine ⟨14165840396423654252059025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9443893597615769501372683 14165840396423654252059025)
                  ·
                    refine ⟨10624380297317740689044269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14165840396423654252059025 10624380297317740689044269)
                    ·
                      refine ⟨3984142611494152758391601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10624380297317740689044269 3984142611494152758391601)
                      ·
                        rfl

theorem cell23_7759090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_7759090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759090 prefixEnd_7759090 := by exact prefixLift 7759090
  have htrace : WordTrace (prefixWord ++ tailWord_7759090) baseStart_7759090 baseEnd_7759090 := by
    simpa [prefixWord, tailWord_7759090, baseEnd_7759090] using wordTrace_append hprefix tailTrace_7759090
  have hstable : (prefixWord ++ tailWord_7759090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759090).length < 2 ^ (prefixWord ++ tailWord_7759090).sum := by decide
  have hdescent : baseEnd_7759090 < baseStart_7759090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759136 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 2, 6]
def baseStart_7759136 : Nat := 118140960795 + 7759136 * 2 ^ 59
def prefixEnd_7759136 : Nat := 4983230072969 + 3 ^ 40 * 7759136 * 2
def baseEnd_7759136 : Nat := 1328055410534753192805463

theorem tailTrace_7759136 : CollatzResearch.WordTrace tailWord_7759136 prefixEnd_7759136 1328055410534753192805463 := by
  unfold tailWord_7759136
  simp only [CollatzResearch.WordTrace]
  refine ⟨141499469608991450886468631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188665959478655267848624841 141499469608991450886468631)
  ·
    refine ⟨212249204413487176329702947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141499469608991450886468631 212249204413487176329702947)
    ·
      refine ⟨318373806620230764494554421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212249204413487176329702947 318373806620230764494554421)
      ·
        refine ⟨29847544370646634171364477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 318373806620230764494554421 29847544370646634171364477)
        ·
          refine ⟨11192829138992487814261679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29847544370646634171364477 11192829138992487814261679)
          ·
            refine ⟨16789243708488731721392519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11192829138992487814261679 16789243708488731721392519)
            ·
              refine ⟨25183865562733097582088779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16789243708488731721392519 25183865562733097582088779)
              ·
                refine ⟨37775798344099646373133169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25183865562733097582088779 37775798344099646373133169)
                ·
                  refine ⟨28331848758074734779849877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37775798344099646373133169 28331848758074734779849877)
                  ·
                    refine ⟨1328055410534753192805463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28331848758074734779849877 1328055410534753192805463)
                    ·
                      rfl

theorem cell23_7759136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 2, 6].length) (baseStart_7759136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759136 prefixEnd_7759136 := by exact prefixLift 7759136
  have htrace : WordTrace (prefixWord ++ tailWord_7759136) baseStart_7759136 baseEnd_7759136 := by
    simpa [prefixWord, tailWord_7759136, baseEnd_7759136] using wordTrace_append hprefix tailTrace_7759136
  have hstable : (prefixWord ++ tailWord_7759136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759136).length < 2 ^ (prefixWord ++ tailWord_7759136).sum := by decide
  have hdescent : baseEnd_7759136 < baseStart_7759136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759139 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 4]
def baseStart_7759139 : Nat := 118140960795 + 7759139 * 2 ^ 59
def prefixEnd_7759139 : Nat := 4983230072969 + 3 ^ 40 * 7759139 * 2
def baseEnd_7759139 : Nat := 3984167772046223066678875

theorem tailTrace_7759139 : CollatzResearch.WordTrace tailWord_7759139 prefixEnd_7759139 3984167772046223066678875 := by
  unfold tailWord_7759139
  simp only [CollatzResearch.WordTrace]
  refine ⟨282999048636972033285296471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188666032424648022190197647 282999048636972033285296471)
  ·
    refine ⟨424498572955458049927944707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282999048636972033285296471 424498572955458049927944707)
    ·
      refine ⟨636747859433187074891917061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424498572955458049927944707 636747859433187074891917061)
      ·
        refine ⟨119390223643722576542234449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 636747859433187074891917061 119390223643722576542234449)
        ·
          refine ⟨89542667732791932406675837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119390223643722576542234449 89542667732791932406675837)
          ·
            refine ⟨33578500399796974652503439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89542667732791932406675837 33578500399796974652503439)
            ·
              refine ⟨50367750599695461978755159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33578500399796974652503439 50367750599695461978755159)
              ·
                refine ⟨75551625899543192968132739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50367750599695461978755159 75551625899543192968132739)
                ·
                  refine ⟨113327438849314789452199109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75551625899543192968132739 113327438849314789452199109)
                  ·
                    refine ⟨21248894784246523022287333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113327438849314789452199109 21248894784246523022287333)
                    ·
                      refine ⟨3984167772046223066678875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21248894784246523022287333 3984167772046223066678875)
                      ·
                        rfl

theorem cell23_7759139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_7759139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759139 prefixEnd_7759139 := by exact prefixLift 7759139
  have htrace : WordTrace (prefixWord ++ tailWord_7759139) baseStart_7759139 baseEnd_7759139 := by
    simpa [prefixWord, tailWord_7759139, baseEnd_7759139] using wordTrace_append hprefix tailTrace_7759139
  have hstable : (prefixWord ++ tailWord_7759139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759139).length < 2 ^ (prefixWord ++ tailWord_7759139).sum := by decide
  have hdescent : baseEnd_7759139 < baseStart_7759139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759156 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_7759156 : Nat := 118140960795 + 7759156 * 2 ^ 59
def prefixEnd_7759156 : Nat := 4983230072969 + 3 ^ 40 * 7759156 * 2
def baseEnd_7759156 : Nat := 3984176501217349500166297

theorem tailTrace_7759156 : CollatzResearch.WordTrace tailWord_7759156 prefixEnd_7759156 3984176501217349500166297 := by
  unfold tailWord_7759156
  simp only [CollatzResearch.WordTrace]
  refine ⟨141499834338955222594332661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188666445785273630125776881 141499834338955222594332661)
  ·
    refine ⟨13265609469277052118218687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141499834338955222594332661 13265609469277052118218687)
    ·
      refine ⟨19898414203915578177328031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13265609469277052118218687 19898414203915578177328031)
      ·
        refine ⟨29847621305873367265992047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19898414203915578177328031 29847621305873367265992047)
        ·
          refine ⟨44771431958810050898988071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29847621305873367265992047 44771431958810050898988071)
          ·
            refine ⟨67157147938215076348482107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44771431958810050898988071 67157147938215076348482107)
            ·
              refine ⟨100735721907322614522723161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67157147938215076348482107 100735721907322614522723161)
              ·
                refine ⟨75551791430491960892042371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100735721907322614522723161 75551791430491960892042371)
                ·
                  refine ⟨113327687145737941338063557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75551791430491960892042371 113327687145737941338063557)
                  ·
                    refine ⟨21248941339825864000886917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113327687145737941338063557 21248941339825864000886917)
                    ·
                      refine ⟨3984176501217349500166297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21248941339825864000886917 3984176501217349500166297)
                      ·
                        rfl

theorem cell23_7759156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_7759156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759156 prefixEnd_7759156 := by exact prefixLift 7759156
  have htrace : WordTrace (prefixWord ++ tailWord_7759156) baseStart_7759156 baseEnd_7759156 := by
    simpa [prefixWord, tailWord_7759156, baseEnd_7759156] using wordTrace_append hprefix tailTrace_7759156
  have hstable : (prefixWord ++ tailWord_7759156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759156).length < 2 ^ (prefixWord ++ tailWord_7759156).sum := by decide
  have hdescent : baseEnd_7759156 < baseStart_7759156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759216 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 4]
def baseStart_7759216 : Nat := 118140960795 + 7759216 * 2 ^ 59
def prefixEnd_7759216 : Nat := 4983230072969 + 3 ^ 40 * 7759216 * 2
def baseEnd_7759216 : Nat := 3984207310056619265416021

theorem tailTrace_7759216 : CollatzResearch.WordTrace tailWord_7759216 prefixEnd_7759216 3984207310056619265416021 := by
  unfold tailWord_7759216
  simp only [CollatzResearch.WordTrace]
  refine ⟨141500928528846537717924751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188667904705128716957233001 141500928528846537717924751)
  ·
    refine ⟨212251392793269806576887127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141500928528846537717924751 212251392793269806576887127)
    ·
      refine ⟨318377089189904709865330691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212251392793269806576887127 318377089189904709865330691)
      ·
        refine ⟨477565633784857064797996037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318377089189904709865330691 477565633784857064797996037)
        ·
          refine ⟨89543556334660699649624257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 477565633784857064797996037 89543556334660699649624257)
          ·
            refine ⟨67157667250995524737218193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89543556334660699649624257 67157667250995524737218193)
            ·
              refine ⟨50368250438246643552913645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67157667250995524737218193 50368250438246643552913645)
              ·
                refine ⟨18888093914342491332342617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50368250438246643552913645 18888093914342491332342617)
                ·
                  refine ⟨14166070435756868499256963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18888093914342491332342617 14166070435756868499256963)
                  ·
                    refine ⟨21249105653635302748885445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14166070435756868499256963 21249105653635302748885445)
                    ·
                      refine ⟨3984207310056619265416021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21249105653635302748885445 3984207310056619265416021)
                      ·
                        rfl

theorem cell23_7759216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 4].length) (baseStart_7759216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759216 prefixEnd_7759216 := by exact prefixLift 7759216
  have htrace : WordTrace (prefixWord ++ tailWord_7759216) baseStart_7759216 baseEnd_7759216 := by
    simpa [prefixWord, tailWord_7759216, baseEnd_7759216] using wordTrace_append hprefix tailTrace_7759216
  have hstable : (prefixWord ++ tailWord_7759216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759216).length < 2 ^ (prefixWord ++ tailWord_7759216).sum := by decide
  have hdescent : baseEnd_7759216 < baseStart_7759216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759279 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 7]
def baseStart_7759279 : Nat := 118140960795 + 7759279 * 2 ^ 59
def prefixEnd_7759279 : Nat := 4983230072969 + 3 ^ 40 * 7759279 * 2
def baseEnd_7759279 : Nat := 3984239659337852518928231

theorem tailTrace_7759279 : CollatzResearch.WordTrace tailWord_7759279 prefixEnd_7759279 3984239659337852518928231 := by
  unfold tailWord_7759279
  simp only [CollatzResearch.WordTrace]
  refine ⟨283004154856464837195392891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188669436570976558130261927 283004154856464837195392891)
  ·
    refine ⟨424506232284697255793089337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283004154856464837195392891 424506232284697255793089337)
    ·
      refine ⟨318379674213522941844817003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424506232284697255793089337 318379674213522941844817003)
      ·
        refine ⟨477569511320284412767225505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318379674213522941844817003 477569511320284412767225505)
        ·
          refine ⟨358177133490213309575419129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477569511320284412767225505 358177133490213309575419129)
          ·
            refine ⟨268632850117659982181564347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358177133490213309575419129 268632850117659982181564347)
            ·
              refine ⟨402949275176489973272346521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268632850117659982181564347 402949275176489973272346521)
              ·
                refine ⟨302211956382367479954259891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402949275176489973272346521 302211956382367479954259891)
                ·
                  refine ⟨453317934573551219931389837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302211956382367479954259891 453317934573551219931389837)
                  ·
                    refine ⟨169994225465081707474271189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 453317934573551219931389837 169994225465081707474271189)
                    ·
                      refine ⟨3984239659337852518928231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169994225465081707474271189 3984239659337852518928231)
                      ·
                        rfl

theorem cell23_7759279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_7759279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759279 prefixEnd_7759279 := by exact prefixLift 7759279
  have htrace : WordTrace (prefixWord ++ tailWord_7759279) baseStart_7759279 baseEnd_7759279 := by
    simpa [prefixWord, tailWord_7759279, baseEnd_7759279] using wordTrace_append hprefix tailTrace_7759279
  have hstable : (prefixWord ++ tailWord_7759279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759279).length < 2 ^ (prefixWord ++ tailWord_7759279).sum := by decide
  have hdescent : baseEnd_7759279 < baseStart_7759279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759333 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 1, 6]
def baseStart_7759333 : Nat := 118140960795 + 7759333 * 2 ^ 59
def prefixEnd_7759333 : Nat := 4983230072969 + 3 ^ 40 * 7759333 * 2
def baseEnd_7759333 : Nat := 1328089129097731769217661

theorem tailTrace_7759333 : CollatzResearch.WordTrace tailWord_7759333 prefixEnd_7759333 1328089129097731769217661 := by
  unfold tailWord_7759333
  simp only [CollatzResearch.WordTrace]
  refine ⟨283006124398269204417858653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188670749598846136278572435 283006124398269204417858653)
  ·
    refine ⟨106127296649350951656696995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283006124398269204417858653 106127296649350951656696995)
    ·
      refine ⟨159190944974026427485045493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106127296649350951656696995 159190944974026427485045493)
      ·
        refine ⟨14924151091314977576723015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159190944974026427485045493 14924151091314977576723015)
        ·
          refine ⟨22386226636972466365084523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14924151091314977576723015 22386226636972466365084523)
          ·
            refine ⟨33579339955458699547626785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22386226636972466365084523 33579339955458699547626785)
            ·
              refine ⟨25184504966594024660720089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33579339955458699547626785 25184504966594024660720089)
              ·
                refine ⟨18888378724945518495540067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25184504966594024660720089 18888378724945518495540067)
                ·
                  refine ⟨28332568087418277743310101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18888378724945518495540067 28332568087418277743310101)
                  ·
                    refine ⟨1328089129097731769217661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28332568087418277743310101 1328089129097731769217661)
                    ·
                      rfl

theorem cell23_7759333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_7759333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759333 prefixEnd_7759333 := by exact prefixLift 7759333
  have htrace : WordTrace (prefixWord ++ tailWord_7759333) baseStart_7759333 baseEnd_7759333 := by
    simpa [prefixWord, tailWord_7759333, baseEnd_7759333] using wordTrace_append hprefix tailTrace_7759333
  have hstable : (prefixWord ++ tailWord_7759333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759333).length < 2 ^ (prefixWord ++ tailWord_7759333).sum := by decide
  have hdescent : baseEnd_7759333 < baseStart_7759333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759350 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_7759350 : Nat := 118140960795 + 7759350 * 2 ^ 59
def prefixEnd_7759350 : Nat := 4983230072969 + 3 ^ 40 * 7759350 * 2
def baseEnd_7759350 : Nat := 1328092038821440580380135

theorem tailTrace_7759350 : CollatzResearch.WordTrace tailWord_7759350 prefixEnd_7759350 1328092038821440580380135 := by
  unfold tailWord_7759350
  simp only [CollatzResearch.WordTrace]
  refine ⟨17687921527450476020076719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188671162959471744214151669 17687921527450476020076719)
  ·
    refine ⟨26531882291175714030115079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17687921527450476020076719 26531882291175714030115079)
    ·
      refine ⟨39797823436763571045172619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26531882291175714030115079 39797823436763571045172619)
      ·
        refine ⟨59696735155145356567758929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39797823436763571045172619 59696735155145356567758929)
        ·
          refine ⟨44772551366359017425819197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59696735155145356567758929 44772551366359017425819197)
          ·
            refine ⟨16789706762384631534682199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44772551366359017425819197 16789706762384631534682199)
            ·
              refine ⟨25184560143576947302023299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16789706762384631534682199 25184560143576947302023299)
              ·
                refine ⟨37776840215365420953034949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25184560143576947302023299 37776840215365420953034949)
                ·
                  refine ⟨7083157540381016428694053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37776840215365420953034949 7083157540381016428694053)
                  ·
                    refine ⟨1328092038821440580380135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7083157540381016428694053 1328092038821440580380135)
                    ·
                      rfl

theorem cell23_7759350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_7759350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759350 prefixEnd_7759350 := by exact prefixLift 7759350
  have htrace : WordTrace (prefixWord ++ tailWord_7759350) baseStart_7759350 baseEnd_7759350 := by
    simpa [prefixWord, tailWord_7759350, baseEnd_7759350] using wordTrace_append hprefix tailTrace_7759350
  have hstable : (prefixWord ++ tailWord_7759350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759350).length < 2 ^ (prefixWord ++ tailWord_7759350).sum := by decide
  have hdescent : baseEnd_7759350 < baseStart_7759350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759357 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 3, 2, 2]
def baseStart_7759357 : Nat := 118140960795 + 7759357 * 2 ^ 59
def prefixEnd_7759357 : Nat := 4983230072969 + 3 ^ 40 * 7759357 * 2
def baseEnd_7759357 : Nat := 3984279710828903213752873

theorem tailTrace_7759357 : CollatzResearch.WordTrace tailWord_7759357 prefixEnd_7759357 3984279710828903213752873 := by
  unfold tailWord_7759357
  simp only [CollatzResearch.WordTrace]
  refine ⟨283006999750182256516732325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188671333166788171011154883 283006999750182256516732325)
  ·
    refine ⟨53063812453159173096887311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283006999750182256516732325 53063812453159173096887311)
    ·
      refine ⟨79595718679738759645330967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53063812453159173096887311 79595718679738759645330967)
      ·
        refine ⟨119393578019608139467996451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79595718679738759645330967 119393578019608139467996451)
        ·
          refine ⟨179090367029412209201994677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119393578019608139467996451 179090367029412209201994677)
          ·
            refine ⟨16789721909007394612687001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179090367029412209201994677 16789721909007394612687001)
            ·
              refine ⟨12592291431755545959515251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16789721909007394612687001 12592291431755545959515251)
              ·
                refine ⟨18888437147633318939272877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12592291431755545959515251 18888437147633318939272877)
                ·
                  refine ⟨7083163930362494602227329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18888437147633318939272877 7083163930362494602227329)
                  ·
                    refine ⟨5312372947771870951670497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7083163930362494602227329 5312372947771870951670497)
                    ·
                      refine ⟨3984279710828903213752873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5312372947771870951670497 3984279710828903213752873)
                      ·
                        rfl

theorem cell23_7759357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_7759357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759357 prefixEnd_7759357 := by exact prefixLift 7759357
  have htrace : WordTrace (prefixWord ++ tailWord_7759357) baseStart_7759357 baseEnd_7759357 := by
    simpa [prefixWord, tailWord_7759357, baseEnd_7759357] using wordTrace_append hprefix tailTrace_7759357
  have hstable : (prefixWord ++ tailWord_7759357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759357).length < 2 ^ (prefixWord ++ tailWord_7759357).sum := by decide
  have hdescent : baseEnd_7759357 < baseStart_7759357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759367 : List Nat := [1, 1, 4, 3, 2, 2, 3, 1, 2, 4]
def baseStart_7759367 : Nat := 118140960795 + 7759367 * 2 ^ 59
def prefixEnd_7759367 : Nat := 4983230072969 + 3 ^ 40 * 7759367 * 2
def baseEnd_7759367 : Nat := 1328094948545149391542609

theorem tailTrace_7759367 : CollatzResearch.WordTrace tailWord_7759367 prefixEnd_7759367 1328094948545149391542609 := by
  unfold tailWord_7759367
  simp only [CollatzResearch.WordTrace]
  refine ⟨283007364480146028224596355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188671576320097352149730903 283007364480146028224596355)
  ·
    refine ⟨424511046720219042336894533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283007364480146028224596355 424511046720219042336894533)
    ·
      refine ⟨79595821260041070438167725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 424511046720219042336894533 79595821260041070438167725)
      ·
        refine ⟨29848432972515401414312897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79595821260041070438167725 29848432972515401414312897)
        ·
          refine ⟨22386324729386551060734673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29848432972515401414312897 22386324729386551060734673)
          ·
            refine ⟨16789743547039913295551005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22386324729386551060734673 16789743547039913295551005)
            ·
              refine ⟨6296153830139967485831627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16789743547039913295551005 6296153830139967485831627)
              ·
                refine ⟨9444230745209951228747441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6296153830139967485831627 9444230745209951228747441)
                ·
                  refine ⟨7083173058907463421560581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9444230745209951228747441 7083173058907463421560581)
                  ·
                    refine ⟨1328094948545149391542609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7083173058907463421560581 1328094948545149391542609)
                    ·
                      rfl

theorem cell23_7759367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_7759367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759367 prefixEnd_7759367 := by exact prefixLift 7759367
  have htrace : WordTrace (prefixWord ++ tailWord_7759367) baseStart_7759367 baseEnd_7759367 := by
    simpa [prefixWord, tailWord_7759367, baseEnd_7759367] using wordTrace_append hprefix tailTrace_7759367
  have hstable : (prefixWord ++ tailWord_7759367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759367).length < 2 ^ (prefixWord ++ tailWord_7759367).sum := by decide
  have hdescent : baseEnd_7759367 < baseStart_7759367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759370 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 1, 2, 4]
def baseStart_7759370 : Nat := 118140960795 + 7759370 * 2 ^ 59
def prefixEnd_7759370 : Nat := 4983230072969 + 3 ^ 40 * 7759370 * 2
def baseEnd_7759370 : Nat := 3984286386077411662890313

theorem tailTrace_7759370 : CollatzResearch.WordTrace tailWord_7759370 prefixEnd_7759370 3984286386077411662890313 := by
  unfold tailWord_7759370
  simp only [CollatzResearch.WordTrace]
  refine ⟨70751868474783789934238891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188671649266090106491303709 70751868474783789934238891)
  ·
    refine ⟨106127802712175684901358337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70751868474783789934238891 106127802712175684901358337)
    ·
      refine ⟨79595852034131763676018753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106127802712175684901358337 79595852034131763676018753)
      ·
        refine ⟨59696889025598822757014065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79595852034131763676018753 59696889025598822757014065)
        ·
          refine ⟨44772666769199117067760549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59696889025598822757014065 44772666769199117067760549)
          ·
            refine ⟨8394875019224834450205103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44772666769199117067760549 8394875019224834450205103)
            ·
              refine ⟨12592312528837251675307655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8394875019224834450205103 12592312528837251675307655)
              ·
                refine ⟨18888468793255877512961483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12592312528837251675307655 18888468793255877512961483)
                ·
                  refine ⟨28332703189883816269442225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18888468793255877512961483 28332703189883816269442225)
                  ·
                    refine ⟨21249527392412862202081669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28332703189883816269442225 21249527392412862202081669)
                    ·
                      refine ⟨3984286386077411662890313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21249527392412862202081669 3984286386077411662890313)
                      ·
                        rfl

theorem cell23_7759370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_7759370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759370 prefixEnd_7759370 := by exact prefixLift 7759370
  have htrace : WordTrace (prefixWord ++ tailWord_7759370) baseStart_7759370 baseEnd_7759370 := by
    simpa [prefixWord, tailWord_7759370, baseEnd_7759370] using wordTrace_append hprefix tailTrace_7759370
  have hstable : (prefixWord ++ tailWord_7759370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759370).length < 2 ^ (prefixWord ++ tailWord_7759370).sum := by decide
  have hdescent : baseEnd_7759370 < baseStart_7759370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759380 : List Nat := [2, 4, 3, 1, 2, 1, 1, 9]
def baseStart_7759380 : Nat := 118140960795 + 7759380 * 2 ^ 59
def prefixEnd_7759380 : Nat := 4983230072969 + 3 ^ 40 * 7759380 * 2
def baseEnd_7759380 : Nat := 147566352625331726806121

theorem tailTrace_7759380 : CollatzResearch.WordTrace tailWord_7759380 prefixEnd_7759380 147566352625331726806121 := by
  unfold tailWord_7759380
  simp only [CollatzResearch.WordTrace]
  refine ⟨141503919314549465722409797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188671892419399287629879729 141503919314549465722409797)
  ·
    refine ⟨26531984871478024822951837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141503919314549465722409797 26531984871478024822951837)
    ·
      refine ⟨9949494326804259308606939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26531984871478024822951837 9949494326804259308606939)
      ·
        refine ⟨14924241490206388962910409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9949494326804259308606939 14924241490206388962910409)
        ·
          refine ⟨11193181117654791722182807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14924241490206388962910409 11193181117654791722182807)
          ·
            refine ⟨16789771676482187583274211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11193181117654791722182807 16789771676482187583274211)
            ·
              refine ⟨25184657514723281374911317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16789771676482187583274211 25184657514723281374911317)
              ·
                refine ⟨147566352625331726806121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25184657514723281374911317 147566352625331726806121)
                ·
                  rfl

theorem cell23_7759380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 9].length) (baseStart_7759380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759380 prefixEnd_7759380 := by exact prefixLift 7759380
  have htrace : WordTrace (prefixWord ++ tailWord_7759380) baseStart_7759380 baseEnd_7759380 := by
    simpa [prefixWord, tailWord_7759380, baseEnd_7759380] using wordTrace_append hprefix tailTrace_7759380
  have hstable : (prefixWord ++ tailWord_7759380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759380).length < 2 ^ (prefixWord ++ tailWord_7759380).sum := by decide
  have hdescent : baseEnd_7759380 < baseStart_7759380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759464 : List Nat := [2, 1, 4, 3, 1, 1, 1, 4, 2, 2, 2]
def baseStart_7759464 : Nat := 118140960795 + 7759464 * 2 ^ 59
def prefixEnd_7759464 : Nat := 4983230072969 + 3 ^ 40 * 7759464 * 2
def baseEnd_7759464 : Nat := 3984334653258934295114881

theorem tailTrace_7759464 : CollatzResearch.WordTrace tailWord_7759464 prefixEnd_7759464 3984334653258934295114881 := by
  unfold tailWord_7759464
  simp only [CollatzResearch.WordTrace]
  refine ⟨141505451180397306895438723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188673934907196409193918297 141505451180397306895438723)
  ·
    refine ⟨212258176770595960343158085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141505451180397306895438723 212258176770595960343158085)
    ·
      refine ⟨39798408144486742564342141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212258176770595960343158085 39798408144486742564342141)
      ·
        refine ⟨14924403054182528461628303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39798408144486742564342141 14924403054182528461628303)
        ·
          refine ⟨22386604581273792692442455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14924403054182528461628303 22386604581273792692442455)
          ·
            refine ⟨33579906871910689038663683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22386604581273792692442455 33579906871910689038663683)
            ·
              refine ⟨50369860307866033557995525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33579906871910689038663683 50369860307866033557995525)
              ·
                refine ⟨9444348807724881292124161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50369860307866033557995525 9444348807724881292124161)
                ·
                  refine ⟨7083261605793660969093121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9444348807724881292124161 7083261605793660969093121)
                  ·
                    refine ⟨5312446204345245726819841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7083261605793660969093121 5312446204345245726819841)
                    ·
                      refine ⟨3984334653258934295114881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5312446204345245726819841 3984334653258934295114881)
                      ·
                        rfl

theorem cell23_7759464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_7759464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759464 prefixEnd_7759464 := by exact prefixLift 7759464
  have htrace : WordTrace (prefixWord ++ tailWord_7759464) baseStart_7759464 baseEnd_7759464 := by
    simpa [prefixWord, tailWord_7759464, baseEnd_7759464] using wordTrace_append hprefix tailTrace_7759464
  have hstable : (prefixWord ++ tailWord_7759464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759464).length < 2 ^ (prefixWord ++ tailWord_7759464).sum := by decide
  have hdescent : baseEnd_7759464 < baseStart_7759464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759581 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 3, 4]
def baseStart_7759581 : Nat := 118140960795 + 7759581 * 2 ^ 59
def prefixEnd_7759581 : Nat := 4983230072969 + 3 ^ 40 * 7759581 * 2
def baseEnd_7759581 : Nat := 1328131576831836779117281

theorem tailTrace_7759581 : CollatzResearch.WordTrace tailWord_7759581 prefixEnd_7759581 1328131576831836779117281 := by
  unfold tailWord_7759581
  simp only [CollatzResearch.WordTrace]
  refine ⟨283015169701370742772886597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188676779800913828515257731 283015169701370742772886597)
  ·
    refine ⟨53065344319007014269916237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283015169701370742772886597 53065344319007014269916237)
    ·
      refine ⟨19899504119627630351218589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53065344319007014269916237 19899504119627630351218589)
      ·
        refine ⟨7462314044860361381706971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19899504119627630351218589 7462314044860361381706971)
        ·
          refine ⟨11193471067290542072560457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7462314044860361381706971 11193471067290542072560457)
          ·
            refine ⟨8395103300467906554420343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11193471067290542072560457 8395103300467906554420343)
            ·
              refine ⟨12592654950701859831630515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8395103300467906554420343 12592654950701859831630515)
              ·
                refine ⟨18888982426052789747445773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12592654950701859831630515 18888982426052789747445773)
                ·
                  refine ⟨7083368409769796155292165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18888982426052789747445773 7083368409769796155292165)
                  ·
                    refine ⟨1328131576831836779117281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7083368409769796155292165 1328131576831836779117281)
                    ·
                      rfl

theorem cell23_7759581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_7759581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759581 prefixEnd_7759581 := by exact prefixLift 7759581
  have htrace : WordTrace (prefixWord ++ tailWord_7759581) baseStart_7759581 baseEnd_7759581 := by
    simpa [prefixWord, tailWord_7759581, baseEnd_7759581] using wordTrace_append hprefix tailTrace_7759581
  have hstable : (prefixWord ++ tailWord_7759581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759581).length < 2 ^ (prefixWord ++ tailWord_7759581).sum := by decide
  have hdescent : baseEnd_7759581 < baseStart_7759581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759593 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 2, 5, 4]
def baseStart_7759593 : Nat := 118140960795 + 7759593 * 2 ^ 59
def prefixEnd_7759593 : Nat := 4983230072969 + 3 ^ 40 * 7759593 * 2
def baseEnd_7759593 : Nat := 3984400892263364290401787

theorem tailTrace_7759593 : CollatzResearch.WordTrace tailWord_7759593 prefixEnd_7759593 3984400892263364290401787 := by
  unfold tailWord_7759593
  simp only [CollatzResearch.WordTrace]
  refine ⟨283015607377327268822323433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188677071584884845881548955 283015607377327268822323433)
  ·
    refine ⟨212261705532995451616742575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283015607377327268822323433 212261705532995451616742575)
    ·
      refine ⟨318392558299493177425113863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212261705532995451616742575 318392558299493177425113863)
      ·
        refine ⟨477588837449239766137670795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318392558299493177425113863 477588837449239766137670795)
        ·
          refine ⟨716383256173859649206506193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477588837449239766137670795 716383256173859649206506193)
          ·
            refine ⟨537287442130394736904879645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716383256173859649206506193 537287442130394736904879645)
            ·
              refine ⟨201482790798898026339329867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 537287442130394736904879645 201482790798898026339329867)
              ·
                refine ⟨302224186198347039508994801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201482790798898026339329867 302224186198347039508994801)
                ·
                  refine ⟨226668139648760279631746101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302224186198347039508994801 226668139648760279631746101)
                  ·
                    refine ⟨21250138092071276215476197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 226668139648760279631746101 21250138092071276215476197)
                    ·
                      refine ⟨3984400892263364290401787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21250138092071276215476197 3984400892263364290401787)
                      ·
                        rfl

theorem cell23_7759593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_7759593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759593 prefixEnd_7759593 := by exact prefixLift 7759593
  have htrace : WordTrace (prefixWord ++ tailWord_7759593) baseStart_7759593 baseEnd_7759593 := by
    simpa [prefixWord, tailWord_7759593, baseEnd_7759593] using wordTrace_append hprefix tailTrace_7759593
  have hstable : (prefixWord ++ tailWord_7759593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759593).length < 2 ^ (prefixWord ++ tailWord_7759593).sum := by decide
  have hdescent : baseEnd_7759593 < baseStart_7759593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759620 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 3, 6]
def baseStart_7759620 : Nat := 118140960795 + 7759620 * 2 ^ 59
def prefixEnd_7759620 : Nat := 4983230072969 + 3 ^ 40 * 7759620 * 2
def baseEnd_7759620 : Nat := 1328138252080345228254721

theorem tailTrace_7759620 : CollatzResearch.WordTrace tailWord_7759620 prefixEnd_7759620 1328138252080345228254721 := by
  unfold tailWord_7759620
  simp only [CollatzResearch.WordTrace]
  refine ⟨141508296074114726216778157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188677728098819634955704209 141508296074114726216778157)
  ·
    refine ⟨53065611027793022331291809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141508296074114726216778157 53065611027793022331291809)
    ·
      refine ⟨39799208270844766748468857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53065611027793022331291809 39799208270844766748468857)
      ·
        refine ⟨29849406203133575061351643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39799208270844766748468857 29849406203133575061351643)
        ·
          refine ⟨44774109304700362592027465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29849406203133575061351643 44774109304700362592027465)
          ·
            refine ⟨33580581978525271944020599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44774109304700362592027465 33580581978525271944020599)
            ·
              refine ⟨50370872967787907916030899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33580581978525271944020599 50370872967787907916030899)
              ·
                refine ⟨75556309451681861874046349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50370872967787907916030899 75556309451681861874046349)
                ·
                  refine ⟨28333616044380698202767381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75556309451681861874046349 28333616044380698202767381)
                  ·
                    refine ⟨1328138252080345228254721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28333616044380698202767381 1328138252080345228254721)
                    ·
                      rfl

theorem cell23_7759620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_7759620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759620 prefixEnd_7759620 := by exact prefixLift 7759620
  have htrace : WordTrace (prefixWord ++ tailWord_7759620) baseStart_7759620 baseEnd_7759620 := by
    simpa [prefixWord, tailWord_7759620, baseEnd_7759620] using wordTrace_append hprefix tailTrace_7759620
  have hstable : (prefixWord ++ tailWord_7759620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759620).length < 2 ^ (prefixWord ++ tailWord_7759620).sum := by decide
  have hdescent : baseEnd_7759620 < baseStart_7759620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759637 : List Nat := [1, 3, 2, 1, 2, 3, 1, 4, 2, 4]
def baseStart_7759637 : Nat := 118140960795 + 7759637 * 2 ^ 59
def prefixEnd_7759637 : Nat := 4983230072969 + 3 ^ 40 * 7759637 * 2
def baseEnd_7759637 : Nat := 1328141161804054039417195

theorem tailTrace_7759637 : CollatzResearch.WordTrace tailWord_7759637 prefixEnd_7759637 1328141161804054039417195 := by
  unfold tailWord_7759637
  simp only [CollatzResearch.WordTrace]
  refine ⟨283017212189167864336925165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188678141459445242891283443 283017212189167864336925165)
  ·
    refine ⟨106131454570937949126346937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283017212189167864336925165 106131454570937949126346937)
    ·
      refine ⟨79598590928203461844760203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106131454570937949126346937 79598590928203461844760203)
      ·
        refine ⟨119397886392305192767140305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79598590928203461844760203 119397886392305192767140305)
        ·
          refine ⟨89548414794228894575355229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119397886392305192767140305 89548414794228894575355229)
          ·
            refine ⟨33580655547835835465758211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89548414794228894575355229 33580655547835835465758211)
            ·
              refine ⟨50370983321753753198637317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33580655547835835465758211 50370983321753753198637317)
              ·
                refine ⟨9444559372828828724744497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50370983321753753198637317 9444559372828828724744497)
                ·
                  refine ⟨7083419529621621543558373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9444559372828828724744497 7083419529621621543558373)
                  ·
                    refine ⟨1328141161804054039417195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7083419529621621543558373 1328141161804054039417195)
                    ·
                      rfl

theorem cell23_7759637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_7759637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759637 prefixEnd_7759637 := by exact prefixLift 7759637
  have htrace : WordTrace (prefixWord ++ tailWord_7759637) baseStart_7759637 baseEnd_7759637 := by
    simpa [prefixWord, tailWord_7759637, baseEnd_7759637] using wordTrace_append hprefix tailTrace_7759637
  have hstable : (prefixWord ++ tailWord_7759637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759637).length < 2 ^ (prefixWord ++ tailWord_7759637).sum := by decide
  have hdescent : baseEnd_7759637 < baseStart_7759637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759644 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 3, 2, 2]
def baseStart_7759644 : Nat := 118140960795 + 7759644 * 2 ^ 59
def prefixEnd_7759644 : Nat := 4983230072969 + 3 ^ 40 * 7759644 * 2
def baseEnd_7759644 : Nat := 3984427079776743590864053

theorem tailTrace_7759644 : CollatzResearch.WordTrace tailWord_7759644 prefixEnd_7759644 3984427079776743590864053 := by
  unfold tailWord_7759644
  simp only [CollatzResearch.WordTrace]
  refine ⟨141508733750071252266214993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188678311666761669688286657 141508733750071252266214993)
  ·
    refine ⟨106131550312553439199661245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141508733750071252266214993 106131550312553439199661245)
    ·
      refine ⟨39799331367207539699872967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106131550312553439199661245 39799331367207539699872967)
      ·
        refine ⟨59698997050811309549809451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39799331367207539699872967 59698997050811309549809451)
        ·
          refine ⟨89548495576216964324714177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59698997050811309549809451 89548495576216964324714177)
          ·
            refine ⟨67161371682162723243535633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89548495576216964324714177 67161371682162723243535633)
            ·
              refine ⟨50371028761622042432651725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67161371682162723243535633 50371028761622042432651725)
              ·
                refine ⟨18889135785608265912244397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50371028761622042432651725 18889135785608265912244397)
                ·
                  refine ⟨7083425919603099717091649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18889135785608265912244397 7083425919603099717091649)
                  ·
                    refine ⟨5312569439702324787818737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7083425919603099717091649 5312569439702324787818737)
                    ·
                      refine ⟨3984427079776743590864053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5312569439702324787818737 3984427079776743590864053)
                      ·
                        rfl

theorem cell23_7759644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_7759644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759644 prefixEnd_7759644 := by exact prefixLift 7759644
  have htrace : WordTrace (prefixWord ++ tailWord_7759644) baseStart_7759644 baseEnd_7759644 := by
    simpa [prefixWord, tailWord_7759644, baseEnd_7759644] using wordTrace_append hprefix tailTrace_7759644
  have hstable : (prefixWord ++ tailWord_7759644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759644).length < 2 ^ (prefixWord ++ tailWord_7759644).sum := by decide
  have hdescent : baseEnd_7759644 < baseStart_7759644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759667 : List Nat := [1, 1, 1, 2, 7, 1, 3, 7]
def baseStart_7759667 : Nat := 118140960795 + 7759667 * 2 ^ 59
def prefixEnd_7759667 : Nat := 4983230072969 + 3 ^ 40 * 7759667 * 2
def baseEnd_7759667 : Nat := 147571810734511000032461

theorem tailTrace_7759667 : CollatzResearch.WordTrace tailWord_7759667 prefixEnd_7759667 147571810734511000032461 := by
  unfold tailWord_7759667
  simp only [CollatzResearch.WordTrace]
  refine ⟨283018306379059179460517255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188678870919372786307011503 283018306379059179460517255)
  ·
    refine ⟨424527459568588769190775883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283018306379059179460517255 424527459568588769190775883)
    ·
      refine ⟨636791189352883153786163825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424527459568588769190775883 636791189352883153786163825)
      ·
        refine ⟨477593392014662365339622869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 636791189352883153786163825 477593392014662365339622869)
        ·
          refine ⟨11193595125343649187647411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 477593392014662365339622869 11193595125343649187647411)
          ·
            refine ⟨16790392688015473781471117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11193595125343649187647411 16790392688015473781471117)
            ·
              refine ⟨6296397258005802668051669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16790392688015473781471117 6296397258005802668051669)
              ·
                refine ⟨147571810734511000032461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6296397258005802668051669 147571810734511000032461)
                ·
                  rfl

theorem cell23_7759667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 7].length) (baseStart_7759667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759667 prefixEnd_7759667 := by exact prefixLift 7759667
  have htrace : WordTrace (prefixWord ++ tailWord_7759667) baseStart_7759667 baseEnd_7759667 := by
    simpa [prefixWord, tailWord_7759667, baseEnd_7759667] using wordTrace_append hprefix tailTrace_7759667
  have hstable : (prefixWord ++ tailWord_7759667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759667).length < 2 ^ (prefixWord ++ tailWord_7759667).sum := by decide
  have hdescent : baseEnd_7759667 < baseStart_7759667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759678 : List Nat := [4, 2, 1, 2, 2, 1, 1, 5, 1, 2, 2]
def baseStart_7759678 : Nat := 118140960795 + 7759678 * 2 ^ 59
def prefixEnd_7759678 : Nat := 4983230072969 + 3 ^ 40 * 7759678 * 2
def baseEnd_7759678 : Nat := 3984444538118996457838897

theorem tailTrace_7759678 : CollatzResearch.WordTrace tailWord_7759678 prefixEnd_7759678 3984444538118996457838897 := by
  unfold tailWord_7759678
  simp only [CollatzResearch.WordTrace]
  refine ⟨35377338447752416042395961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188679138388012885559445125 35377338447752416042395961)
  ·
    refine ⟨26533003835814312031796971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35377338447752416042395961 26533003835814312031796971)
    ·
      refine ⟨39799505753721468047695457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26533003835814312031796971 39799505753721468047695457)
      ·
        refine ⟨29849629315291101035771593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39799505753721468047695457 29849629315291101035771593)
        ·
          refine ⟨22387221986468325776828695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29849629315291101035771593 22387221986468325776828695)
          ·
            refine ⟨33580832979702488665243043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22387221986468325776828695 33580832979702488665243043)
            ·
              refine ⟨50371249469553732997864565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33580832979702488665243043 50371249469553732997864565)
              ·
                refine ⟨4722304637770662468549803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50371249469553732997864565 4722304637770662468549803)
                ·
                  refine ⟨7083456956655993702824705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4722304637770662468549803 7083456956655993702824705)
                  ·
                    refine ⟨5312592717491995277118529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7083456956655993702824705 5312592717491995277118529)
                    ·
                      refine ⟨3984444538118996457838897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5312592717491995277118529 3984444538118996457838897)
                      ·
                        rfl

theorem cell23_7759678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_7759678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759678 prefixEnd_7759678 := by exact prefixLift 7759678
  have htrace : WordTrace (prefixWord ++ tailWord_7759678) baseStart_7759678 baseEnd_7759678 := by
    simpa [prefixWord, tailWord_7759678, baseEnd_7759678] using wordTrace_append hprefix tailTrace_7759678
  have hstable : (prefixWord ++ tailWord_7759678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759678).length < 2 ^ (prefixWord ++ tailWord_7759678).sum := by decide
  have hdescent : baseEnd_7759678 < baseStart_7759678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759711 : List Nat := [1, 1, 2, 3, 1, 5, 3, 1, 2, 1, 3]
def baseStart_7759711 : Nat := 118140960795 + 7759711 * 2 ^ 59
def prefixEnd_7759711 : Nat := 4983230072969 + 3 ^ 40 * 7759711 * 2
def baseEnd_7759711 : Nat := 3984461482980594828726245

theorem tailTrace_7759711 : CollatzResearch.WordTrace tailWord_7759711 prefixEnd_7759711 3984461482980594828726245 := by
  unfold tailWord_7759711
  simp only [CollatzResearch.WordTrace]
  refine ⟨283019911190899774975118987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188679940793933183316745991 283019911190899774975118987)
  ·
    refine ⟨424529866786349662462678481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283019911190899774975118987 424529866786349662462678481)
    ·
      refine ⟨318397400089762246847008861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424529866786349662462678481 318397400089762246847008861)
      ·
        refine ⟨119399025033660842567628323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318397400089762246847008861 119399025033660842567628323)
        ·
          refine ⟨179098537550491263851442485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119399025033660842567628323 179098537550491263851442485)
          ·
            refine ⟨16790487895358555986072733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179098537550491263851442485 16790487895358555986072733)
            ·
              refine ⟨6296432960759458494777275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16790487895358555986072733 6296432960759458494777275)
              ·
                refine ⟨9444649441139187742165913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6296432960759458494777275 9444649441139187742165913)
                ·
                  refine ⟨7083487080854390806624435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9444649441139187742165913 7083487080854390806624435)
                  ·
                    refine ⟨10625230621281586209936653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7083487080854390806624435 10625230621281586209936653)
                    ·
                      refine ⟨3984461482980594828726245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10625230621281586209936653 3984461482980594828726245)
                      ·
                        rfl

theorem cell23_7759711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_7759711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759711 prefixEnd_7759711 := by exact prefixLift 7759711
  have htrace : WordTrace (prefixWord ++ tailWord_7759711) baseStart_7759711 baseEnd_7759711 := by
    simpa [prefixWord, tailWord_7759711, baseEnd_7759711] using wordTrace_append hprefix tailTrace_7759711
  have hstable : (prefixWord ++ tailWord_7759711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759711).length < 2 ^ (prefixWord ++ tailWord_7759711).sum := by decide
  have hdescent : baseEnd_7759711 < baseStart_7759711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759797 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_7759797 : Nat := 118140960795 + 7759797 * 2 ^ 59
def prefixEnd_7759797 : Nat := 4983230072969 + 3 ^ 40 * 7759797 * 2
def baseEnd_7759797 : Nat := 3984505642316881492250849

theorem tailTrace_7759797 : CollatzResearch.WordTrace tailWord_7759797 prefixEnd_7759797 3984505642316881492250849 := by
  unfold tailWord_7759797
  simp only [CollatzResearch.WordTrace]
  refine ⟨283023047868588211662749645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188682031912392141108499763 283023047868588211662749645)
  ·
    refine ⟨106133642950720579373531117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283023047868588211662749645 106133642950720579373531117)
    ·
      refine ⟨39800116106520217265074169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106133642950720579373531117 39800116106520217265074169)
      ·
        refine ⟨29850087079890162948805627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39800116106520217265074169 29850087079890162948805627)
        ·
          refine ⟨44775130619835244423208441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29850087079890162948805627 44775130619835244423208441)
          ·
            refine ⟨33581347964876433317406331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44775130619835244423208441 33581347964876433317406331)
            ·
              refine ⟨50372021947314649976109497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33581347964876433317406331 50372021947314649976109497)
              ·
                refine ⟨37779016460485987482082123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50372021947314649976109497 37779016460485987482082123)
                ·
                  refine ⟨56668524690728981223123185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37779016460485987482082123 56668524690728981223123185)
                  ·
                    refine ⟨42501393518046735917342389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56668524690728981223123185 42501393518046735917342389)
                    ·
                      refine ⟨3984505642316881492250849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42501393518046735917342389 3984505642316881492250849)
                      ·
                        rfl

theorem cell23_7759797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_7759797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759797 prefixEnd_7759797 := by exact prefixLift 7759797
  have htrace : WordTrace (prefixWord ++ tailWord_7759797) baseStart_7759797 baseEnd_7759797 := by
    simpa [prefixWord, tailWord_7759797, baseEnd_7759797] using wordTrace_append hprefix tailTrace_7759797
  have hstable : (prefixWord ++ tailWord_7759797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759797).length < 2 ^ (prefixWord ++ tailWord_7759797).sum := by decide
  have hdescent : baseEnd_7759797 < baseStart_7759797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759807 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 4]
def baseStart_7759807 : Nat := 118140960795 + 7759807 * 2 ^ 59
def prefixEnd_7759807 : Nat := 4983230072969 + 3 ^ 40 * 7759807 * 2
def baseEnd_7759807 : Nat := 3984510777123426453125803

theorem tailTrace_7759807 : CollatzResearch.WordTrace tailWord_7759807 prefixEnd_7759807 3984510777123426453125803 := by
  unfold tailWord_7759807
  simp only [CollatzResearch.WordTrace]
  refine ⟨283023412598551983370613675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188682275065701322247075783 283023412598551983370613675)
  ·
    refine ⟨424535118897827975055920513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283023412598551983370613675 424535118897827975055920513)
    ·
      refine ⟨318401339173370981291940385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424535118897827975055920513 318401339173370981291940385)
      ·
        refine ⟨238801004380028235968955289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318401339173370981291940385 238801004380028235968955289)
        ·
          refine ⟨179100753285021176976716467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238801004380028235968955289 179100753285021176976716467)
          ·
            refine ⟨268651129927531765465074701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179100753285021176976716467 268651129927531765465074701)
            ·
              refine ⟨100744173722824412049403013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268651129927531765465074701 100744173722824412049403013)
              ·
                refine ⟨18889532573029577259263065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100744173722824412049403013 18889532573029577259263065)
                ·
                  refine ⟨14167149429772182944447299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18889532573029577259263065 14167149429772182944447299)
                  ·
                    refine ⟨21250724144658274416670949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14167149429772182944447299 21250724144658274416670949)
                    ·
                      refine ⟨3984510777123426453125803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21250724144658274416670949 3984510777123426453125803)
                      ·
                        rfl

theorem cell23_7759807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_7759807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759807 prefixEnd_7759807 := by exact prefixLift 7759807
  have htrace : WordTrace (prefixWord ++ tailWord_7759807) baseStart_7759807 baseEnd_7759807 := by
    simpa [prefixWord, tailWord_7759807, baseEnd_7759807] using wordTrace_append hprefix tailTrace_7759807
  have hstable : (prefixWord ++ tailWord_7759807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759807).length < 2 ^ (prefixWord ++ tailWord_7759807).sum := by decide
  have hdescent : baseEnd_7759807 < baseStart_7759807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759884 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 3, 5, 2]
def baseStart_7759884 : Nat := 118140960795 + 7759884 * 2 ^ 59
def prefixEnd_7759884 : Nat := 4983230072969 + 3 ^ 40 * 7759884 * 2
def baseEnd_7759884 : Nat := 3984550315133822651862949

theorem tailTrace_7759884 : CollatzResearch.WordTrace tailWord_7759884 prefixEnd_7759884 3984550315133822651862949 := by
  unfold tailWord_7759884
  simp only [CollatzResearch.WordTrace]
  refine ⟨141513110509636512760583353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188684147346182017014111137 141513110509636512760583353)
  ·
    refine ⟨106134832882227384570437515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141513110509636512760583353 106134832882227384570437515)
    ·
      refine ⟨159202249323341076855656273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106134832882227384570437515 159202249323341076855656273)
      ·
        refine ⟨119401686992505807641742205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159202249323341076855656273 119401686992505807641742205)
        ·
          refine ⟨44775632622189677865653327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119401686992505807641742205 44775632622189677865653327)
          ·
            refine ⟨67163448933284516798479991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44775632622189677865653327 67163448933284516798479991)
            ·
              refine ⟨100745173399926775197719987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67163448933284516798479991 100745173399926775197719987)
              ·
                refine ⟨151117760099890162796579981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100745173399926775197719987 151117760099890162796579981)
                ·
                  refine ⟨56669160037458811048717493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151117760099890162796579981 56669160037458811048717493)
                  ·
                    refine ⟨5312733753511763535817265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56669160037458811048717493 5312733753511763535817265)
                    ·
                      refine ⟨3984550315133822651862949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5312733753511763535817265 3984550315133822651862949)
                      ·
                        rfl

theorem cell23_7759884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_7759884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759884 prefixEnd_7759884 := by exact prefixLift 7759884
  have htrace : WordTrace (prefixWord ++ tailWord_7759884) baseStart_7759884 baseEnd_7759884 := by
    simpa [prefixWord, tailWord_7759884, baseEnd_7759884] using wordTrace_append hprefix tailTrace_7759884
  have hstable : (prefixWord ++ tailWord_7759884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759884).length < 2 ^ (prefixWord ++ tailWord_7759884).sum := by decide
  have hdescent : baseEnd_7759884 < baseStart_7759884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759901 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 1, 5, 2]
def baseStart_7759901 : Nat := 118140960795 + 7759901 * 2 ^ 59
def prefixEnd_7759901 : Nat := 4983230072969 + 3 ^ 40 * 7759901 * 2
def baseEnd_7759901 : Nat := 3984559044304949085350371

theorem tailTrace_7759901 : CollatzResearch.WordTrace tailWord_7759901 prefixEnd_7759901 3984559044304949085350371 := by
  unfold tailWord_7759901
  simp only [CollatzResearch.WordTrace]
  refine ⟨283026841060211437424535557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188684560706807624949690371 283026841060211437424535557)
  ·
    refine ⟨53067532698789644517100417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283026841060211437424535557 53067532698789644517100417)
    ·
      refine ⟨39800649524092233387825313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53067532698789644517100417 39800649524092233387825313)
      ·
        refine ⟨29850487143069175040868985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39800649524092233387825313 29850487143069175040868985)
        ·
          refine ⟨22387865357301881280651739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29850487143069175040868985 22387865357301881280651739)
          ·
            refine ⟨33581798035952821920977609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22387865357301881280651739 33581798035952821920977609)
            ·
              refine ⟨25186348526964616440733207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33581798035952821920977609 25186348526964616440733207)
              ·
                refine ⟨37779522790446924661099811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25186348526964616440733207 37779522790446924661099811)
                ·
                  refine ⟨56669284185670386991649717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37779522790446924661099811 56669284185670386991649717)
                  ·
                    refine ⟨5312745392406598780467161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56669284185670386991649717 5312745392406598780467161)
                    ·
                      refine ⟨3984559044304949085350371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5312745392406598780467161 3984559044304949085350371)
                      ·
                        rfl

theorem cell23_7759901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_7759901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759901 prefixEnd_7759901 := by exact prefixLift 7759901
  have htrace : WordTrace (prefixWord ++ tailWord_7759901) baseStart_7759901 baseEnd_7759901 := by
    simpa [prefixWord, tailWord_7759901, baseEnd_7759901] using wordTrace_append hprefix tailTrace_7759901
  have hstable : (prefixWord ++ tailWord_7759901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759901).length < 2 ^ (prefixWord ++ tailWord_7759901).sum := by decide
  have hdescent : baseEnd_7759901 < baseStart_7759901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759907 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 3, 6]
def baseStart_7759907 : Nat := 118140960795 + 7759907 * 2 ^ 59
def prefixEnd_7759907 : Nat := 4983230072969 + 3 ^ 40 * 7759907 * 2
def baseEnd_7759907 : Nat := 1328187375062958687291781

theorem tailTrace_7759907 : CollatzResearch.WordTrace tailWord_7759907 prefixEnd_7759907 1328187375062958687291781 := by
  unfold tailWord_7759907
  simp only [CollatzResearch.WordTrace]
  refine ⟨283027059898189700449253975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188684706598793133632835983 283027059898189700449253975)
  ·
    refine ⟨424540589847284550673880963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283027059898189700449253975 424540589847284550673880963)
    ·
      refine ⟨636810884770926826010821445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424540589847284550673880963 636810884770926826010821445)
      ·
        refine ⟨119402040894548779877029021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 636810884770926826010821445 119402040894548779877029021)
        ·
          refine ⟨44775765335455792453885883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119402040894548779877029021 44775765335455792453885883)
          ·
            refine ⟨67163648003183688680828825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44775765335455792453885883 67163648003183688680828825)
            ·
              refine ⟨50372736002387766510621619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67163648003183688680828825 50372736002387766510621619)
              ·
                refine ⟨75559104003581649765932429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50372736002387766510621619 75559104003581649765932429)
                ·
                  refine ⟨28334664001343118662224661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75559104003581649765932429 28334664001343118662224661)
                  ·
                    refine ⟨1328187375062958687291781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28334664001343118662224661 1328187375062958687291781)
                    ·
                      rfl

theorem cell23_7759907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 6].length) (baseStart_7759907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759907 prefixEnd_7759907 := by exact prefixLift 7759907
  have htrace : WordTrace (prefixWord ++ tailWord_7759907) baseStart_7759907 baseEnd_7759907 := by
    simpa [prefixWord, tailWord_7759907, baseEnd_7759907] using wordTrace_append hprefix tailTrace_7759907
  have hstable : (prefixWord ++ tailWord_7759907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759907).length < 2 ^ (prefixWord ++ tailWord_7759907).sum := by decide
  have hdescent : baseEnd_7759907 < baseStart_7759907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759918 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_7759918 : Nat := 118140960795 + 7759918 * 2 ^ 59
def prefixEnd_7759918 : Nat := 4983230072969 + 3 ^ 40 * 7759918 * 2
def baseEnd_7759918 : Nat := 3984567773476075518837793

theorem tailTrace_7759918 : CollatzResearch.WordTrace tailWord_7759918 prefixEnd_7759918 3984567773476075518837793 := by
  unfold tailWord_7759918
  simp only [CollatzResearch.WordTrace]
  refine ⟨35378432637643731165988051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188684974067433232885269605 35378432637643731165988051)
  ·
    refine ⟨53067648956465596748982077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35378432637643731165988051 53067648956465596748982077)
    ·
      refine ⟨19900368358674598780868279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53067648956465596748982077 19900368358674598780868279)
      ·
        refine ⟨29850552538011898171302419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19900368358674598780868279 29850552538011898171302419)
        ·
          refine ⟨44775828807017847256953629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29850552538011898171302419 44775828807017847256953629)
          ·
            refine ⟨16790935802631692721357611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44775828807017847256953629 16790935802631692721357611)
            ·
              refine ⟨25186403703947539082036417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16790935802631692721357611 25186403703947539082036417)
              ·
                refine ⟨18889802777960654311527313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25186403703947539082036417 18889802777960654311527313)
                ·
                  refine ⟨14167352083470490733645485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18889802777960654311527313 14167352083470490733645485)
                  ·
                    refine ⟨5312757031301434025117057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14167352083470490733645485 5312757031301434025117057)
                    ·
                      refine ⟨3984567773476075518837793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5312757031301434025117057 3984567773476075518837793)
                      ·
                        rfl

theorem cell23_7759918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_7759918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759918 prefixEnd_7759918 := by exact prefixLift 7759918
  have htrace : WordTrace (prefixWord ++ tailWord_7759918) baseStart_7759918 baseEnd_7759918 := by
    simpa [prefixWord, tailWord_7759918, baseEnd_7759918] using wordTrace_append hprefix tailTrace_7759918
  have hstable : (prefixWord ++ tailWord_7759918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759918).length < 2 ^ (prefixWord ++ tailWord_7759918).sum := by decide
  have hdescent : baseEnd_7759918 < baseStart_7759918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759927 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 6]
def baseStart_7759927 : Nat := 118140960795 + 7759927 * 2 ^ 59
def prefixEnd_7759927 : Nat := 4983230072969 + 3 ^ 40 * 7759927 * 2
def baseEnd_7759927 : Nat := 3984572394801965983625251

theorem tailTrace_7759927 : CollatzResearch.WordTrace tailWord_7759927 prefixEnd_7759927 3984572394801965983625251 := by
  unfold tailWord_7759927
  simp only [CollatzResearch.WordTrace]
  refine ⟨283027789358117243864982035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188685192905411495909988023 283027789358117243864982035)
  ·
    refine ⟨424541684037175865797473053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283027789358117243864982035 424541684037175865797473053)
    ·
      refine ⟨159203131513940949674052395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424541684037175865797473053 159203131513940949674052395)
      ·
        refine ⟨238804697270911424511078593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159203131513940949674052395 238804697270911424511078593)
        ·
          refine ⟨179103522953183568383308945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238804697270911424511078593 179103522953183568383308945)
          ·
            refine ⟨134327642214887676287481709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179103522953183568383308945 134327642214887676287481709)
            ·
              refine ⟨50372865830582878607805641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134327642214887676287481709 50372865830582878607805641)
              ·
                refine ⟨37779649372937158955854231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50372865830582878607805641 37779649372937158955854231)
                ·
                  refine ⟨56669474059405738433781347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37779649372937158955854231 56669474059405738433781347)
                  ·
                    refine ⟨85004211089108607650672021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56669474059405738433781347 85004211089108607650672021)
                    ·
                      refine ⟨3984572394801965983625251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85004211089108607650672021 3984572394801965983625251)
                      ·
                        rfl

theorem cell23_7759927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_7759927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759927 prefixEnd_7759927 := by exact prefixLift 7759927
  have htrace : WordTrace (prefixWord ++ tailWord_7759927) baseStart_7759927 baseEnd_7759927 := by
    simpa [prefixWord, tailWord_7759927, baseEnd_7759927] using wordTrace_append hprefix tailTrace_7759927
  have hstable : (prefixWord ++ tailWord_7759927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759927).length < 2 ^ (prefixWord ++ tailWord_7759927).sum := by decide
  have hdescent : baseEnd_7759927 < baseStart_7759927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759958 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_7759958 : Nat := 118140960795 + 7759958 * 2 ^ 59
def prefixEnd_7759958 : Nat := 4983230072969 + 3 ^ 40 * 7759958 * 2
def baseEnd_7759958 : Nat := 1328196104234085120779203

theorem tailTrace_7759958 : CollatzResearch.WordTrace tailWord_7759958 prefixEnd_7759958 1328196104234085120779203 := by
  unfold tailWord_7759958
  simp only [CollatzResearch.WordTrace]
  refine ⟨17689307501312808509960033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188685946680669957439573685 17689307501312808509960033)
  ·
    refine ⟨13266980625984606382470025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17689307501312808509960033 13266980625984606382470025)
    ·
      refine ⟨9950235469488454786852519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13266980625984606382470025 9950235469488454786852519)
      ·
        refine ⟨14925353204232682180278779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9950235469488454786852519 14925353204232682180278779)
        ·
          refine ⟨22388029806349023270418169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14925353204232682180278779 22388029806349023270418169)
          ·
            refine ⟨16791022354761767452813627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22388029806349023270418169 16791022354761767452813627)
            ·
              refine ⟨25186533532142651179220441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16791022354761767452813627 25186533532142651179220441)
              ·
                refine ⟨18889900149106988384415331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25186533532142651179220441 18889900149106988384415331)
                ·
                  refine ⟨28334850223660482576622997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18889900149106988384415331 28334850223660482576622997)
                  ·
                    refine ⟨1328196104234085120779203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28334850223660482576622997 1328196104234085120779203)
                    ·
                      rfl

theorem cell23_7759958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_7759958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759958 prefixEnd_7759958 := by exact prefixLift 7759958
  have htrace : WordTrace (prefixWord ++ tailWord_7759958) baseStart_7759958 baseEnd_7759958 := by
    simpa [prefixWord, tailWord_7759958, baseEnd_7759958] using wordTrace_append hprefix tailTrace_7759958
  have hstable : (prefixWord ++ tailWord_7759958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759958).length < 2 ^ (prefixWord ++ tailWord_7759958).sum := by decide
  have hdescent : baseEnd_7759958 < baseStart_7759958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759965 : List Nat := [1, 4, 4, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_7759965 : Nat := 118140960795 + 7759965 * 2 ^ 59
def prefixEnd_7759965 : Nat := 4983230072969 + 3 ^ 40 * 7759965 * 2
def baseEnd_7759965 : Nat := 3984591907066836834950077

theorem tailTrace_7759965 : CollatzResearch.WordTrace tailWord_7759965 prefixEnd_7759965 3984591907066836834950077 := by
  unfold tailWord_7759965
  simp only [CollatzResearch.WordTrace]
  refine ⟨283029175331979576354865349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188686116887986384236576899 283029175331979576354865349)
  ·
    refine ⟨53067970374746170566537253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283029175331979576354865349 53067970374746170566537253)
    ·
      refine ⟨9950244445264906981225735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53067970374746170566537253 9950244445264906981225735)
      ·
        refine ⟨14925366667897360471838603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9950244445264906981225735 14925366667897360471838603)
        ·
          refine ⟨22388050001846040707757905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14925366667897360471838603 22388050001846040707757905)
          ·
            refine ⟨16791037501384530530818429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22388050001846040707757905 16791037501384530530818429)
            ·
              refine ⟨6296639063019198949056911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16791037501384530530818429 6296639063019198949056911)
              ·
                refine ⟨9444958594528798423585367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6296639063019198949056911 9444958594528798423585367)
                ·
                  refine ⟨14167437891793197635378051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9444958594528798423585367 14167437891793197635378051)
                  ·
                    refine ⟨21251156837689796453067077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14167437891793197635378051 21251156837689796453067077)
                    ·
                      refine ⟨3984591907066836834950077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21251156837689796453067077 3984591907066836834950077)
                      ·
                        rfl

theorem cell23_7759965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_7759965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759965 prefixEnd_7759965 := by exact prefixLift 7759965
  have htrace : WordTrace (prefixWord ++ tailWord_7759965) baseStart_7759965 baseEnd_7759965 := by
    simpa [prefixWord, tailWord_7759965, baseEnd_7759965] using wordTrace_append hprefix tailTrace_7759965
  have hstable : (prefixWord ++ tailWord_7759965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759965).length < 2 ^ (prefixWord ++ tailWord_7759965).sum := by decide
  have hdescent : baseEnd_7759965 < baseStart_7759965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759968 : List Nat := [2, 1, 1, 3, 2, 4, 3, 1, 1, 2, 3]
def baseStart_7759968 : Nat := 118140960795 + 7759968 * 2 ^ 59
def prefixEnd_7759968 : Nat := 4983230072969 + 3 ^ 40 * 7759968 * 2
def baseEnd_7759968 : Nat := 3984593447508800323212563

theorem tailTrace_7759968 : CollatzResearch.WordTrace tailWord_7759968 prefixEnd_7759968 3984593447508800323212563 := by
  unfold tailWord_7759968
  simp only [CollatzResearch.WordTrace]
  refine ⟨141514642375484353933612279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188686189833979138578149705 141514642375484353933612279)
  ·
    refine ⟨212271963563226530900418419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141514642375484353933612279 212271963563226530900418419)
    ·
      refine ⟨318407945344839796350627629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212271963563226530900418419 318407945344839796350627629)
      ·
        refine ⟨119402979504314923631485361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318407945344839796350627629 119402979504314923631485361)
        ·
          refine ⟨89552234628236192723614021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119402979504314923631485361 89552234628236192723614021)
          ·
            refine ⟨16791043992794286135677629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89552234628236192723614021 16791043992794286135677629)
            ·
              refine ⟨6296641497297857300879111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16791043992794286135677629 6296641497297857300879111)
              ·
                refine ⟨9444962245946785951318667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6296641497297857300879111 9444962245946785951318667)
                ·
                  refine ⟨14167443368920178926978001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9444962245946785951318667 14167443368920178926978001)
                  ·
                    refine ⟨10625582526690134195233501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14167443368920178926978001 10625582526690134195233501)
                    ·
                      refine ⟨3984593447508800323212563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10625582526690134195233501 3984593447508800323212563)
                      ·
                        rfl

theorem cell23_7759968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_7759968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759968 prefixEnd_7759968 := by exact prefixLift 7759968
  have htrace : WordTrace (prefixWord ++ tailWord_7759968) baseStart_7759968 baseEnd_7759968 := by
    simpa [prefixWord, tailWord_7759968, baseEnd_7759968] using wordTrace_append hprefix tailTrace_7759968
  have hstable : (prefixWord ++ tailWord_7759968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759968).length < 2 ^ (prefixWord ++ tailWord_7759968).sum := by decide
  have hdescent : baseEnd_7759968 < baseStart_7759968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7759991 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 3, 3, 2]
def baseStart_7759991 : Nat := 118140960795 + 7759991 * 2 ^ 59
def prefixEnd_7759991 : Nat := 4983230072969 + 3 ^ 40 * 7759991 * 2
def baseEnd_7759991 : Nat := 3984605257563853733224957

theorem tailTrace_7759991 : CollatzResearch.WordTrace tailWord_7759991 prefixEnd_7759991 3984605257563853733224957 := by
  unfold tailWord_7759991
  simp only [CollatzResearch.WordTrace]
  refine ⟨283030123629885382795311827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188686749086590255196874551 283030123629885382795311827)
  ·
    refine ⟨424545185444828074192967741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283030123629885382795311827 424545185444828074192967741)
    ·
      refine ⟨159204444541810527822362903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424545185444828074192967741 159204444541810527822362903)
      ·
        refine ⟨238806666812715791733544355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159204444541810527822362903 238806666812715791733544355)
        ·
          refine ⟨358210000219073687600316533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238806666812715791733544355 358210000219073687600316533)
          ·
            refine ⟨33582187520538158212529675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 358210000219073687600316533 33582187520538158212529675)
            ·
              refine ⟨50373281280807237318794513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33582187520538158212529675 50373281280807237318794513)
              ·
                refine ⟨37779960960605427989095885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50373281280807237318794513 37779960960605427989095885)
                ·
                  refine ⟨14167485360227035495910957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37779960960605427989095885 14167485360227035495910957)
                  ·
                    refine ⟨5312807010085138310966609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14167485360227035495910957 5312807010085138310966609)
                    ·
                      refine ⟨3984605257563853733224957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5312807010085138310966609 3984605257563853733224957)
                      ·
                        rfl

theorem cell23_7759991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 3, 2].length) (baseStart_7759991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7759991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7759991 prefixEnd_7759991 := by exact prefixLift 7759991
  have htrace : WordTrace (prefixWord ++ tailWord_7759991) baseStart_7759991 baseEnd_7759991 := by
    simpa [prefixWord, tailWord_7759991, baseEnd_7759991] using wordTrace_append hprefix tailTrace_7759991
  have hstable : (prefixWord ++ tailWord_7759991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7759991).length < 2 ^ (prefixWord ++ tailWord_7759991).sum := by decide
  have hdescent : baseEnd_7759991 < baseStart_7759991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7759991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760004 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_7760004 : Nat := 118140960795 + 7760004 * 2 ^ 59
def prefixEnd_7760004 : Nat := 4983230072969 + 3 ^ 40 * 7760004 * 2
def baseEnd_7760004 : Nat := 3984611932812362182362397

theorem tailTrace_7760004 : CollatzResearch.WordTrace tailWord_7760004 prefixEnd_7760004 3984611932812362182362397 := by
  unfold tailWord_7760004
  simp only [CollatzResearch.WordTrace]
  refine ⟨141515298889419143007767533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188687065185892190677023377 141515298889419143007767533)
  ·
    refine ⟨53068237083532178627912825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141515298889419143007767533 53068237083532178627912825)
    ·
      refine ⟨39801177812649133970934619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53068237083532178627912825 39801177812649133970934619)
      ·
        refine ⟨59701766718973700956401929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39801177812649133970934619 59701766718973700956401929)
        ·
          refine ⟨44776325039230275717301447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59701766718973700956401929 44776325039230275717301447)
          ·
            refine ⟨67164487558845413575952171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44776325039230275717301447 67164487558845413575952171)
            ·
              refine ⟨100746731338268120363928257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67164487558845413575952171 100746731338268120363928257)
              ·
                refine ⟨75560048503701090272946193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100746731338268120363928257 75560048503701090272946193)
                ·
                  refine ⟨56670036377775817704709645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75560048503701090272946193 56670036377775817704709645)
                  ·
                    refine ⟨21251263641665931639266117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56670036377775817704709645 21251263641665931639266117)
                    ·
                      refine ⟨3984611932812362182362397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21251263641665931639266117 3984611932812362182362397)
                      ·
                        rfl

theorem cell23_7760004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_7760004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760004 prefixEnd_7760004 := by exact prefixLift 7760004
  have htrace : WordTrace (prefixWord ++ tailWord_7760004) baseStart_7760004 baseEnd_7760004 := by
    simpa [prefixWord, tailWord_7760004, baseEnd_7760004] using wordTrace_append hprefix tailTrace_7760004
  have hstable : (prefixWord ++ tailWord_7760004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760004).length < 2 ^ (prefixWord ++ tailWord_7760004).sum := by decide
  have hdescent : baseEnd_7760004 < baseStart_7760004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760008 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 3, 3, 2]
def baseStart_7760008 : Nat := 118140960795 + 7760008 * 2 ^ 59
def prefixEnd_7760008 : Nat := 4983230072969 + 3 ^ 40 * 7760008 * 2
def baseEnd_7760008 : Nat := 3984613986734980166712379

theorem tailTrace_7760008 : CollatzResearch.WordTrace tailWord_7760008 prefixEnd_7760008 3984613986734980166712379 := by
  unfold tailWord_7760008
  simp only [CollatzResearch.WordTrace]
  refine ⟨141515371835411897349340339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188687162447215863132453785 141515371835411897349340339)
  ·
    refine ⟨212273057753117846024010509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141515371835411897349340339 212273057753117846024010509)
    ·
      refine ⟨79602396657419192259003941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212273057753117846024010509 79602396657419192259003941)
      ·
        refine ⟨14925449373266098548563239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79602396657419192259003941 14925449373266098548563239)
        ·
          refine ⟨22388174059899147822844859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14925449373266098548563239 22388174059899147822844859)
          ·
            refine ⟨33582261089848721734267289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22388174059899147822844859 33582261089848721734267289)
            ·
              refine ⟨25186695817386541300700467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33582261089848721734267289 25186695817386541300700467)
              ·
                refine ⟨37780043726079811951050701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25186695817386541300700467 37780043726079811951050701)
                ·
                  refine ⟨14167516397279929481644013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37780043726079811951050701 14167516397279929481644013)
                  ·
                    refine ⟨5312818648979973555616505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14167516397279929481644013 5312818648979973555616505)
                    ·
                      refine ⟨3984613986734980166712379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5312818648979973555616505 3984613986734980166712379)
                      ·
                        rfl

theorem cell23_7760008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_7760008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760008 prefixEnd_7760008 := by exact prefixLift 7760008
  have htrace : WordTrace (prefixWord ++ tailWord_7760008) baseStart_7760008 baseEnd_7760008 := by
    simpa [prefixWord, tailWord_7760008, baseEnd_7760008] using wordTrace_append hprefix tailTrace_7760008
  have hstable : (prefixWord ++ tailWord_7760008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760008).length < 2 ^ (prefixWord ++ tailWord_7760008).sum := by decide
  have hdescent : baseEnd_7760008 < baseStart_7760008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760021 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 1, 4, 2]
def baseStart_7760021 : Nat := 118140960795 + 7760021 * 2 ^ 59
def prefixEnd_7760021 : Nat := 4983230072969 + 3 ^ 40 * 7760021 * 2
def baseEnd_7760021 : Nat := 3984620661983488615849819

theorem tailTrace_7760021 : CollatzResearch.WordTrace tailWord_7760021 prefixEnd_7760021 3984620661983488615849819 := by
  unfold tailWord_7760021
  simp only [CollatzResearch.WordTrace]
  refine ⟨283031217819776697918903917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188687478546517798612602611 283031217819776697918903917)
  ·
    refine ⟨106136706682416261719588969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283031217819776697918903917 106136706682416261719588969)
    ·
      refine ⟨79602530011812196289691727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106136706682416261719588969 79602530011812196289691727)
      ·
        refine ⟨119403795017718294434537591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79602530011812196289691727 119403795017718294434537591)
        ·
          refine ⟨179105692526577441651806387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119403795017718294434537591 179105692526577441651806387)
          ·
            refine ⟨268658538789866162477709581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179105692526577441651806387 268658538789866162477709581)
            ·
              refine ⟨100746952046199810929141093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268658538789866162477709581 100746952046199810929141093)
              ·
                refine ⟨18890053508662464549213955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100746952046199810929141093 18890053508662464549213955)
                ·
                  refine ⟨28335080262993696823820933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18890053508662464549213955 28335080262993696823820933)
                  ·
                    refine ⟨5312827549311318154466425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28335080262993696823820933 5312827549311318154466425)
                    ·
                      refine ⟨3984620661983488615849819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5312827549311318154466425 3984620661983488615849819)
                      ·
                        rfl

theorem cell23_7760021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_7760021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760021 prefixEnd_7760021 := by exact prefixLift 7760021
  have htrace : WordTrace (prefixWord ++ tailWord_7760021) baseStart_7760021 baseEnd_7760021 := by
    simpa [prefixWord, tailWord_7760021, baseEnd_7760021] using wordTrace_append hprefix tailTrace_7760021
  have hstable : (prefixWord ++ tailWord_7760021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760021).length < 2 ^ (prefixWord ++ tailWord_7760021).sum := by decide
  have hdescent : baseEnd_7760021 < baseStart_7760021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760027 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 9]
def baseStart_7760027 : Nat := 118140960795 + 7760027 * 2 ^ 59
def prefixEnd_7760027 : Nat := 4983230072969 + 3 ^ 40 * 7760027 * 2
def baseEnd_7760027 : Nat := 442735971429712843597199

theorem tailTrace_7760027 : CollatzResearch.WordTrace tailWord_7760027 prefixEnd_7760027 442735971429712843597199 := by
  unfold tailWord_7760027
  simp only [CollatzResearch.WordTrace]
  refine ⟨283031436657754960943622335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188687624438503307295748223 283031436657754960943622335)
  ·
    refine ⟨424547154986632441415433503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283031436657754960943622335 424547154986632441415433503)
    ·
      refine ⟨636820732479948662123150255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424547154986632441415433503 636820732479948662123150255)
      ·
        refine ⟨955231098719922993184725383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636820732479948662123150255 955231098719922993184725383)
        ·
          refine ⟨1432846648079884489777088075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955231098719922993184725383 1432846648079884489777088075)
          ·
            refine ⟨2149269972119826734665632113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432846648079884489777088075 2149269972119826734665632113)
            ·
              refine ⟨1611952479089870050999224085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2149269972119826734665632113 1611952479089870050999224085)
              ·
                refine ⟨75560272457337658640588629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1611952479089870050999224085 75560272457337658640588629)
                ·
                  refine ⟨442735971429712843597199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75560272457337658640588629 442735971429712843597199)
                  ·
                    rfl

theorem cell23_7760027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 9].length) (baseStart_7760027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760027 prefixEnd_7760027 := by exact prefixLift 7760027
  have htrace : WordTrace (prefixWord ++ tailWord_7760027) baseStart_7760027 baseEnd_7760027 := by
    simpa [prefixWord, tailWord_7760027, baseEnd_7760027] using wordTrace_append hprefix tailTrace_7760027
  have hstable : (prefixWord ++ tailWord_7760027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760027).length < 2 ^ (prefixWord ++ tailWord_7760027).sum := by decide
  have hdescent : baseEnd_7760027 < baseStart_7760027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760074 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 1, 7]
def baseStart_7760074 : Nat := 118140960795 + 7760074 * 2 ^ 59
def prefixEnd_7760074 : Nat := 4983230072969 + 3 ^ 40 * 7760074 * 2
def baseEnd_7760074 : Nat := 1328215958819392302829025

theorem tailTrace_7760074 : CollatzResearch.WordTrace tailWord_7760074 prefixEnd_7760074 1328215958819392302829025 := by
  unfold tailWord_7760074
  simp only [CollatzResearch.WordTrace]
  refine ⟨70758287722146171992645819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188688767259056458647055517 70758287722146171992645819)
  ·
    refine ⟨106137431583219257988968729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70758287722146171992645819 106137431583219257988968729)
    ·
      refine ⟨79603073687414443491726547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106137431583219257988968729 79603073687414443491726547)
      ·
        refine ⟨119404610531121665237589821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79603073687414443491726547 119404610531121665237589821)
        ·
          refine ⟨44776728949170624464096183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119404610531121665237589821 44776728949170624464096183)
          ·
            refine ⟨67165093423755936696144275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44776728949170624464096183 67165093423755936696144275)
            ·
              refine ⟨100747640135633905044216413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67165093423755936696144275 100747640135633905044216413)
              ·
                refine ⟨37780365050862714391581155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100747640135633905044216413 37780365050862714391581155)
                ·
                  refine ⟨56670547576294071587371733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37780365050862714391581155 56670547576294071587371733)
                  ·
                    refine ⟨1328215958819392302829025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56670547576294071587371733 1328215958819392302829025)
                    ·
                      rfl

theorem cell23_7760074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_7760074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760074 prefixEnd_7760074 := by exact prefixLift 7760074
  have htrace : WordTrace (prefixWord ++ tailWord_7760074) baseStart_7760074 baseEnd_7760074 := by
    simpa [prefixWord, tailWord_7760074, baseEnd_7760074] using wordTrace_append hprefix tailTrace_7760074
  have hstable : (prefixWord ++ tailWord_7760074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760074).length < 2 ^ (prefixWord ++ tailWord_7760074).sum := by decide
  have hdescent : baseEnd_7760074 < baseStart_7760074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760078 : List Nat := [4, 1, 1, 1, 4, 1, 3, 3, 5]
def baseStart_7760078 : Nat := 118140960795 + 7760078 * 2 ^ 59
def prefixEnd_7760078 : Nat := 4983230072969 + 3 ^ 40 * 7760078 * 2
def baseEnd_7760078 : Nat := 442738881153421654759673

theorem tailTrace_7760078 : CollatzResearch.WordTrace tailWord_7760078 prefixEnd_7760078 442738881153421654759673 := by
  unfold tailWord_7760078
  simp only [CollatzResearch.WordTrace]
  refine ⟨35379162097571274581716111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188688864520380131102485925 35379162097571274581716111)
  ·
    refine ⟨53068743146356911872574167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35379162097571274581716111 53068743146356911872574167)
    ·
      refine ⟨79603114719535367808861251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53068743146356911872574167 79603114719535367808861251)
      ·
        refine ⟨119404672079303051713291877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79603114719535367808861251 119404672079303051713291877)
        ·
          refine ⟨22388376014869322196242227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119404672079303051713291877 22388376014869322196242227)
          ·
            refine ⟨33582564022303983294363341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22388376014869322196242227 33582564022303983294363341)
            ·
              refine ⟨12593461508363993735386253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33582564022303983294363341 12593461508363993735386253)
              ·
                refine ⟨4722548065636497650769845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12593461508363993735386253 4722548065636497650769845)
                ·
                  refine ⟨442738881153421654759673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4722548065636497650769845 442738881153421654759673)
                  ·
                    rfl

theorem cell23_7760078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_7760078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760078 prefixEnd_7760078 := by exact prefixLift 7760078
  have htrace : WordTrace (prefixWord ++ tailWord_7760078) baseStart_7760078 baseEnd_7760078 := by
    simpa [prefixWord, tailWord_7760078, baseEnd_7760078] using wordTrace_append hprefix tailTrace_7760078
  have hstable : (prefixWord ++ tailWord_7760078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760078).length < 2 ^ (prefixWord ++ tailWord_7760078).sum := by decide
  have hdescent : baseEnd_7760078 < baseStart_7760078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760101 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 1, 2, 5]
def baseStart_7760101 : Nat := 118140960795 + 7760101 * 2 ^ 59
def prefixEnd_7760101 : Nat := 4983230072969 + 3 ^ 40 * 7760101 * 2
def baseEnd_7760101 : Nat := 3984661740435848302849451

theorem tailTrace_7760101 : CollatzResearch.WordTrace tailWord_7760101 prefixEnd_7760101 3984661740435848302849451 := by
  unfold tailWord_7760101
  simp only [CollatzResearch.WordTrace]
  refine ⟨283034135659486871581816157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188689423772991247721210771 283034135659486871581816157)
  ·
    refine ⟨106137800872307576843181059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283034135659486871581816157 106137800872307576843181059)
    ·
      refine ⟨159206701308461365264771589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106137800872307576843181059 159206701308461365264771589)
      ·
        refine ⟨29851256495336505987144673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159206701308461365264771589 29851256495336505987144673)
        ·
          refine ⟨22388442371502379490358505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29851256495336505987144673 22388442371502379490358505)
          ·
            refine ⟨16791331778626784617768879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22388442371502379490358505 16791331778626784617768879)
            ·
              refine ⟨25186997667940176926653319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16791331778626784617768879 25186997667940176926653319)
              ·
                refine ⟨37780496501910265389979979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25186997667940176926653319 37780496501910265389979979)
                ·
                  refine ⟨56670744752865398084969969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37780496501910265389979979 56670744752865398084969969)
                  ·
                    refine ⟨42503058564649048563727477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56670744752865398084969969 42503058564649048563727477)
                    ·
                      refine ⟨3984661740435848302849451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42503058564649048563727477 3984661740435848302849451)
                      ·
                        rfl

theorem cell23_7760101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_7760101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760101 prefixEnd_7760101 := by exact prefixLift 7760101
  have htrace : WordTrace (prefixWord ++ tailWord_7760101) baseStart_7760101 baseEnd_7760101 := by
    simpa [prefixWord, tailWord_7760101, baseEnd_7760101] using wordTrace_append hprefix tailTrace_7760101
  have hstable : (prefixWord ++ tailWord_7760101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760101).length < 2 ^ (prefixWord ++ tailWord_7760101).sum := by decide
  have hdescent : baseEnd_7760101 < baseStart_7760101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760151 : List Nat := [1, 1, 3, 4, 1, 2, 1, 4, 6]
def baseStart_7760151 : Nat := 118140960795 + 7760151 * 2 ^ 59
def prefixEnd_7760151 : Nat := 4983230072969 + 3 ^ 40 * 7760151 * 2
def baseEnd_7760151 : Nat := 442743046052063678580469

theorem tailTrace_7760151 : CollatzResearch.WordTrace tailWord_7760151 prefixEnd_7760151 442743046052063678580469 := by
  unfold tailWord_7760151
  simp only [CollatzResearch.WordTrace]
  refine ⟨283035959309305730121136307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188690639539537153414090871 283035959309305730121136307)
  ·
    refine ⟨424553938963958595181704461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283035959309305730121136307 424553938963958595181704461)
    ·
      refine ⟨159207727111484473193139173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424553938963958595181704461 159207727111484473193139173)
      ·
        refine ⟨29851448833403338723713595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159207727111484473193139173 29851448833403338723713595)
        ·
          refine ⟨44777173250105008085570393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29851448833403338723713595 44777173250105008085570393)
          ·
            refine ⟨33582879937578756064177795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44777173250105008085570393 33582879937578756064177795)
            ·
              refine ⟨50374319906368134096266693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33582879937578756064177795 50374319906368134096266693)
              ·
                refine ⟨9445184982444025143050005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50374319906368134096266693 9445184982444025143050005)
                ·
                  refine ⟨442743046052063678580469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9445184982444025143050005 442743046052063678580469)
                  ·
                    rfl

theorem cell23_7760151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 6].length) (baseStart_7760151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760151 prefixEnd_7760151 := by exact prefixLift 7760151
  have htrace : WordTrace (prefixWord ++ tailWord_7760151) baseStart_7760151 baseEnd_7760151 := by
    simpa [prefixWord, tailWord_7760151, baseEnd_7760151] using wordTrace_append hprefix tailTrace_7760151
  have hstable : (prefixWord ++ tailWord_7760151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760151).length < 2 ^ (prefixWord ++ tailWord_7760151).sum := by decide
  have hdescent : baseEnd_7760151 < baseStart_7760151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760155 : List Nat := [1, 1, 1, 1, 1, 1, 10, 2, 1, 4]
def baseStart_7760155 : Nat := 118140960795 + 7760155 * 2 ^ 59
def prefixEnd_7760155 : Nat := 4983230072969 + 3 ^ 40 * 7760155 * 2
def baseEnd_7760155 : Nat := 1328229822797063697191401

theorem tailTrace_7760155 : CollatzResearch.WordTrace tailWord_7760155 prefixEnd_7760155 1328229822797063697191401 := by
  unfold tailWord_7760155
  simp only [CollatzResearch.WordTrace]
  refine ⟨283036105201291238804281919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188690736800860825869521279 283036105201291238804281919)
  ·
    refine ⟨424554157801936858206422879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283036105201291238804281919 424554157801936858206422879)
    ·
      refine ⟨636831236702905287309634319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424554157801936858206422879 636831236702905287309634319)
      ·
        refine ⟨955246855054357930964451479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636831236702905287309634319 955246855054357930964451479)
        ·
          refine ⟨1432870282581536896446677219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955246855054357930964451479 1432870282581536896446677219)
          ·
            refine ⟨2149305423872305344670015829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432870282581536896446677219 2149305423872305344670015829)
            ·
              refine ⟨6296793234000894564462937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2149305423872305344670015829 6296793234000894564462937)
              ·
                refine ⟨4722594925500670923347203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6296793234000894564462937 4722594925500670923347203)
                ·
                  refine ⟨7083892388251006385020805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4722594925500670923347203 7083892388251006385020805)
                  ·
                    refine ⟨1328229822797063697191401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7083892388251006385020805 1328229822797063697191401)
                    ·
                      rfl

theorem cell23_7760155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 1, 4].length) (baseStart_7760155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760155 prefixEnd_7760155 := by exact prefixLift 7760155
  have htrace : WordTrace (prefixWord ++ tailWord_7760155) baseStart_7760155 baseEnd_7760155 := by
    simpa [prefixWord, tailWord_7760155, baseEnd_7760155] using wordTrace_append hprefix tailTrace_7760155
  have hstable : (prefixWord ++ tailWord_7760155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760155).length < 2 ^ (prefixWord ++ tailWord_7760155).sum := by decide
  have hdescent : baseEnd_7760155 < baseStart_7760155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760181 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 3, 5]
def baseStart_7760181 : Nat := 118140960795 + 7760181 * 2 ^ 59
def prefixEnd_7760181 : Nat := 4983230072969 + 3 ^ 40 * 7760181 * 2
def baseEnd_7760181 : Nat := 1328234272962735996616361

theorem tailTrace_7760181 : CollatzResearch.WordTrace tailWord_7760181 prefixEnd_7760181 1328234272962735996616361 := by
  unfold tailWord_7760181
  simp only [CollatzResearch.WordTrace]
  refine ⟨283037053499197045244728397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188691368999464696829818931 283037053499197045244728397)
  ·
    refine ⟨106138895062198891966773149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283037053499197045244728397 106138895062198891966773149)
    ·
      refine ⟨39802085648324584487539931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106138895062198891966773149 39802085648324584487539931)
      ·
        refine ⟨59703128472486876731309897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39802085648324584487539931 59703128472486876731309897)
        ·
          refine ⟨44777346354365157548482423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59703128472486876731309897 44777346354365157548482423)
          ·
            refine ⟨67166019531547736322723635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44777346354365157548482423 67166019531547736322723635)
            ·
              refine ⟨100749029297321604484085453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67166019531547736322723635 100749029297321604484085453)
              ·
                refine ⟨37780885986495601681532045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100749029297321604484085453 37780885986495601681532045)
                ·
                  refine ⟨14167832244935850630574517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37780885986495601681532045 14167832244935850630574517)
                  ·
                    refine ⟨1328234272962735996616361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14167832244935850630574517 1328234272962735996616361)
                    ·
                      rfl

theorem cell23_7760181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_7760181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760181 prefixEnd_7760181 := by exact prefixLift 7760181
  have htrace : WordTrace (prefixWord ++ tailWord_7760181) baseStart_7760181 baseEnd_7760181 := by
    simpa [prefixWord, tailWord_7760181, baseEnd_7760181] using wordTrace_append hprefix tailTrace_7760181
  have hstable : (prefixWord ++ tailWord_7760181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760181).length < 2 ^ (prefixWord ++ tailWord_7760181).sum := by decide
  have hdescent : baseEnd_7760181 < baseStart_7760181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760188 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 1, 5, 2]
def baseStart_7760188 : Nat := 118140960795 + 7760188 * 2 ^ 59
def prefixEnd_7760188 : Nat := 4983230072969 + 3 ^ 40 * 7760188 * 2
def baseEnd_7760188 : Nat := 3984706413252789462461551

theorem tailTrace_7760188 : CollatzResearch.WordTrace tailWord_7760188 prefixEnd_7760188 3984706413252789462461551 := by
  unfold tailWord_7760188
  simp only [CollatzResearch.WordTrace]
  refine ⟨141518654405085842720116609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188691539206781123626822145 141518654405085842720116609)
  ·
    refine ⟨106138990803814382040087457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141518654405085842720116609 106138990803814382040087457)
    ·
      refine ⟨79604243102860786530065593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106138990803814382040087457 79604243102860786530065593)
      ·
        refine ⟨59703182327145589897549195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79604243102860786530065593 59703182327145589897549195)
        ·
          refine ⟨89554773490718384846323793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59703182327145589897549195 89554773490718384846323793)
          ·
            refine ⟨67166080118038788634742845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89554773490718384846323793 67166080118038788634742845)
            ·
              refine ⟨25187280044264545738028567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67166080118038788634742845 25187280044264545738028567)
              ·
                refine ⟨37780920066396818607042851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25187280044264545738028567 37780920066396818607042851)
                ·
                  refine ⟨56671380099595227910564277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37780920066396818607042851 56671380099595227910564277)
                  ·
                    refine ⟨5312941884337052616615401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56671380099595227910564277 5312941884337052616615401)
                    ·
                      refine ⟨3984706413252789462461551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5312941884337052616615401 3984706413252789462461551)
                      ·
                        rfl

theorem cell23_7760188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_7760188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760188 prefixEnd_7760188 := by exact prefixLift 7760188
  have htrace : WordTrace (prefixWord ++ tailWord_7760188) baseStart_7760188 baseEnd_7760188 := by
    simpa [prefixWord, tailWord_7760188, baseEnd_7760188] using wordTrace_append hprefix tailTrace_7760188
  have hstable : (prefixWord ++ tailWord_7760188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760188).length < 2 ^ (prefixWord ++ tailWord_7760188).sum := by decide
  have hdescent : baseEnd_7760188 < baseStart_7760188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760195 : List Nat := [1, 1, 1, 3, 1, 3, 3, 5, 1, 1, 3]
def baseStart_7760195 : Nat := 118140960795 + 7760195 * 2 ^ 59
def prefixEnd_7760195 : Nat := 4983230072969 + 3 ^ 40 * 7760195 * 2
def baseEnd_7760195 : Nat := 3984710007617370935074019

theorem tailTrace_7760195 : CollatzResearch.WordTrace tailWord_7760195 prefixEnd_7760195 3984710007617370935074019 := by
  unfold tailWord_7760195
  simp only [CollatzResearch.WordTrace]
  refine ⟨283037564121146325635738039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188691709414097550423825359 283037564121146325635738039)
  ·
    refine ⟨424556346181719488453607059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283037564121146325635738039 424556346181719488453607059)
    ·
      refine ⟨636834519272579232680410589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424556346181719488453607059 636834519272579232680410589)
      ·
        refine ⟨238812944727217212255153971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 636834519272579232680410589 238812944727217212255153971)
        ·
          refine ⟨358219417090825818382730957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238812944727217212255153971 358219417090825818382730957)
          ·
            refine ⟨134332281409059681893524109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358219417090825818382730957 134332281409059681893524109)
            ·
              refine ⟨50374605528397380710071541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134332281409059681893524109 50374605528397380710071541)
              ·
                refine ⟨4722619268287254441569207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50374605528397380710071541 4722619268287254441569207)
                ·
                  refine ⟨7083928902430881662353811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4722619268287254441569207 7083928902430881662353811)
                  ·
                    refine ⟨10625893353646322493530717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7083928902430881662353811 10625893353646322493530717)
                    ·
                      refine ⟨3984710007617370935074019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10625893353646322493530717 3984710007617370935074019)
                      ·
                        rfl

theorem cell23_7760195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 1, 1, 3].length) (baseStart_7760195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760195 prefixEnd_7760195 := by exact prefixLift 7760195
  have htrace : WordTrace (prefixWord ++ tailWord_7760195) baseStart_7760195 baseEnd_7760195 := by
    simpa [prefixWord, tailWord_7760195, baseEnd_7760195] using wordTrace_append hprefix tailTrace_7760195
  have hstable : (prefixWord ++ tailWord_7760195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760195).length < 2 ^ (prefixWord ++ tailWord_7760195).sum := by decide
  have hdescent : baseEnd_7760195 < baseStart_7760195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760212 : List Nat := [2, 4, 1, 1, 2, 2, 2, 4, 1, 1, 3]
def baseStart_7760212 : Nat := 118140960795 + 7760212 * 2 ^ 59
def prefixEnd_7760212 : Nat := 4983230072969 + 3 ^ 40 * 7760212 * 2
def baseEnd_7760212 : Nat := 3984718736788497368561441

theorem tailTrace_7760212 : CollatzResearch.WordTrace tailWord_7760212 prefixEnd_7760212 3984718736788497368561441 := by
  unfold tailWord_7760212
  simp only [CollatzResearch.WordTrace]
  refine ⟨141519092081042368769553445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188692122774723158359404593 141519092081042368769553445)
  ·
    refine ⟨26534829765195444144291271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141519092081042368769553445 26534829765195444144291271)
    ·
      refine ⟨39802244647793166216436907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26534829765195444144291271 39802244647793166216436907)
      ·
        refine ⟨59703366971689749324655361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39802244647793166216436907 59703366971689749324655361)
        ·
          refine ⟨44777525228767311993491521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59703366971689749324655361 44777525228767311993491521)
          ·
            refine ⟨33583143921575483995118641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44777525228767311993491521 33583143921575483995118641)
            ·
              refine ⟨25187357941181612996338981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33583143921575483995118641 25187357941181612996338981)
              ·
                refine ⟨4722629613971552436813559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25187357941181612996338981 4722629613971552436813559)
                ·
                  refine ⟨7083944420957328655220339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4722629613971552436813559 7083944420957328655220339)
                  ·
                    refine ⟨10625916631435992982830509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7083944420957328655220339 10625916631435992982830509)
                    ·
                      refine ⟨3984718736788497368561441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10625916631435992982830509 3984718736788497368561441)
                      ·
                        rfl

theorem cell23_7760212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_7760212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760212 prefixEnd_7760212 := by exact prefixLift 7760212
  have htrace : WordTrace (prefixWord ++ tailWord_7760212) baseStart_7760212 baseEnd_7760212 := by
    simpa [prefixWord, tailWord_7760212, baseEnd_7760212] using wordTrace_append hprefix tailTrace_7760212
  have hstable : (prefixWord ++ tailWord_7760212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760212).length < 2 ^ (prefixWord ++ tailWord_7760212).sum := by decide
  have hdescent : baseEnd_7760212 < baseStart_7760212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760252 : List Nat := [2, 2, 2, 1, 1, 1, 2, 7, 1, 2, 2]
def baseStart_7760252 : Nat := 118140960795 + 7760252 * 2 ^ 59
def prefixEnd_7760252 : Nat := 4983230072969 + 3 ^ 40 * 7760252 * 2
def baseEnd_7760252 : Nat := 3984739276014677212061257

theorem tailTrace_7760252 : CollatzResearch.WordTrace tailWord_7760252 prefixEnd_7760252 3984739276014677212061257 := by
  unfold tailWord_7760252
  simp only [CollatzResearch.WordTrace]
  refine ⟨141519821540969912185281505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188693095387959882913708673 141519821540969912185281505)
  ·
    refine ⟨106139866155727434138961129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141519821540969912185281505 106139866155727434138961129)
    ·
      refine ⟨79604899616795575604220847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106139866155727434138961129 79604899616795575604220847)
      ·
        refine ⟨119407349425193363406331271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79604899616795575604220847 119407349425193363406331271)
        ·
          refine ⟨179111024137790045109496907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119407349425193363406331271 179111024137790045109496907)
          ·
            refine ⟨268666536206685067664245361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179111024137790045109496907 268666536206685067664245361)
            ·
              refine ⟨201499902155013800748184021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268666536206685067664245361 201499902155013800748184021)
              ·
                refine ⟨4722653956758135955035563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 201499902155013800748184021 4722653956758135955035563)
                ·
                  refine ⟨7083980935137203932553345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4722653956758135955035563 7083980935137203932553345)
                  ·
                    refine ⟨5312985701352902949415009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7083980935137203932553345 5312985701352902949415009)
                    ·
                      refine ⟨3984739276014677212061257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5312985701352902949415009 3984739276014677212061257)
                      ·
                        rfl

theorem cell23_7760252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_7760252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760252 prefixEnd_7760252 := by exact prefixLift 7760252
  have htrace : WordTrace (prefixWord ++ tailWord_7760252) baseStart_7760252 baseEnd_7760252 := by
    simpa [prefixWord, tailWord_7760252, baseEnd_7760252] using wordTrace_append hprefix tailTrace_7760252
  have hstable : (prefixWord ++ tailWord_7760252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760252).length < 2 ^ (prefixWord ++ tailWord_7760252).sum := by decide
  have hdescent : baseEnd_7760252 < baseStart_7760252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760289 : List Nat := [1, 2, 3, 5, 1, 2, 1, 2, 1, 2, 3]
def baseStart_7760289 : Nat := 118140960795 + 7760289 * 2 ^ 59
def prefixEnd_7760289 : Nat := 4983230072969 + 3 ^ 40 * 7760289 * 2
def baseEnd_7760289 : Nat := 3984758274798893567298587

theorem tailTrace_7760289 : CollatzResearch.WordTrace tailWord_7760289 prefixEnd_7760289 3984758274798893567298587 := by
  unfold tailWord_7760289
  simp only [CollatzResearch.WordTrace]
  refine ⟨283040992582805779689659921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188693995055203853126439947 283040992582805779689659921)
  ·
    refine ⟨212280744437104334767244941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283040992582805779689659921 212280744437104334767244941)
    ·
      refine ⟨79605279163914125537716853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212280744437104334767244941 79605279163914125537716853)
      ·
        refine ⟨7462994921616949269160955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79605279163914125537716853 7462994921616949269160955)
        ·
          refine ⟨11194492382425423903741433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7462994921616949269160955 11194492382425423903741433)
          ·
            refine ⟨8395869286819067927806075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11194492382425423903741433 8395869286819067927806075)
            ·
              refine ⟨12593803930228601891709113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8395869286819067927806075 12593803930228601891709113)
              ·
                refine ⟨9445352947671451418781835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12593803930228601891709113 9445352947671451418781835)
                ·
                  refine ⟨14168029421507177128172753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9445352947671451418781835 14168029421507177128172753)
                  ·
                    refine ⟨10626022066130382846129565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14168029421507177128172753 10626022066130382846129565)
                    ·
                      refine ⟨3984758274798893567298587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10626022066130382846129565 3984758274798893567298587)
                      ·
                        rfl

theorem cell23_7760289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_7760289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760289 prefixEnd_7760289 := by exact prefixLift 7760289
  have htrace : WordTrace (prefixWord ++ tailWord_7760289) baseStart_7760289 baseEnd_7760289 := by
    simpa [prefixWord, tailWord_7760289, baseEnd_7760289] using wordTrace_append hprefix tailTrace_7760289
  have hstable : (prefixWord ++ tailWord_7760289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760289).length < 2 ^ (prefixWord ++ tailWord_7760289).sum := by decide
  have hdescent : baseEnd_7760289 < baseStart_7760289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760328 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 2, 4, 3]
def baseStart_7760328 : Nat := 118140960795 + 7760328 * 2 ^ 59
def prefixEnd_7760328 : Nat := 4983230072969 + 3 ^ 40 * 7760328 * 2
def baseEnd_7760328 : Nat := 3984778300544418914710907

theorem tailTrace_7760328 : CollatzResearch.WordTrace tailWord_7760328 prefixEnd_7760328 3984778300544418914710907 := by
  unfold tailWord_7760328
  simp only [CollatzResearch.WordTrace]
  refine ⟨141521207514832244675164819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188694943353109659566886425 141521207514832244675164819)
  ·
    refine ⟨212281811272248367012747229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141521207514832244675164819 212281811272248367012747229)
    ·
      refine ⟨79605679227093137629780211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212281811272248367012747229 79605679227093137629780211)
      ·
        refine ⟨119408518840639706444670317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79605679227093137629780211 119408518840639706444670317)
        ·
          refine ⟨44778194565239889916751369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119408518840639706444670317 44778194565239889916751369)
          ·
            refine ⟨33583645923929917437563527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44778194565239889916751369 33583645923929917437563527)
            ·
              refine ⟨50375468885894876156345291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33583645923929917437563527 50375468885894876156345291)
              ·
                refine ⟨75563203328842314234517937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50375468885894876156345291 75563203328842314234517937)
                ·
                  refine ⟨56672402496631735675888453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75563203328842314234517937 56672402496631735675888453)
                  ·
                    refine ⟨10626075468118450439229085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56672402496631735675888453 10626075468118450439229085)
                    ·
                      refine ⟨3984778300544418914710907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10626075468118450439229085 3984778300544418914710907)
                      ·
                        rfl

theorem cell23_7760328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_7760328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760328 prefixEnd_7760328 := by exact prefixLift 7760328
  have htrace : WordTrace (prefixWord ++ tailWord_7760328) baseStart_7760328 baseEnd_7760328 := by
    simpa [prefixWord, tailWord_7760328, baseEnd_7760328] using wordTrace_append hprefix tailTrace_7760328
  have hstable : (prefixWord ++ tailWord_7760328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760328).length < 2 ^ (prefixWord ++ tailWord_7760328).sum := by decide
  have hdescent : baseEnd_7760328 < baseStart_7760328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760331 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 7]
def baseStart_7760331 : Nat := 118140960795 + 7760331 * 2 ^ 59
def prefixEnd_7760331 : Nat := 4983230072969 + 3 ^ 40 * 7760331 * 2
def baseEnd_7760331 : Nat := 442753315665153600330377

theorem tailTrace_7760331 : CollatzResearch.WordTrace tailWord_7760331 prefixEnd_7760331 442753315665153600330377 := by
  unfold tailWord_7760331
  simp only [CollatzResearch.WordTrace]
  refine ⟨283042524448653620862688847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188695016299102413908459231 283042524448653620862688847)
  ·
    refine ⟨424563786672980431294033271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283042524448653620862688847 424563786672980431294033271)
    ·
      refine ⟨636845680009470646941049907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424563786672980431294033271 636845680009470646941049907)
      ·
        refine ⟨955268520014205970411574861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636845680009470646941049907 955268520014205970411574861)
        ·
          refine ⟨358225695005327238904340573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 955268520014205970411574861 358225695005327238904340573)
          ·
            refine ⟨134334635626997714589127715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358225695005327238904340573 134334635626997714589127715)
            ·
              refine ⟨201501953440496571883691573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134334635626997714589127715 201501953440496571883691573)
              ·
                refine ⟨18890808135046553614096085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201501953440496571883691573 18890808135046553614096085)
                ·
                  refine ⟨442753315665153600330377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18890808135046553614096085 442753315665153600330377)
                  ·
                    rfl

theorem cell23_7760331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 7].length) (baseStart_7760331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760331 prefixEnd_7760331 := by exact prefixLift 7760331
  have htrace : WordTrace (prefixWord ++ tailWord_7760331) baseStart_7760331 baseEnd_7760331 := by
    simpa [prefixWord, tailWord_7760331, baseEnd_7760331] using wordTrace_append hprefix tailTrace_7760331
  have hstable : (prefixWord ++ tailWord_7760331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760331).length < 2 ^ (prefixWord ++ tailWord_7760331).sum := by decide
  have hdescent : baseEnd_7760331 < baseStart_7760331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760418 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_7760418 : Nat := 118140960795 + 7760418 * 2 ^ 59
def prefixEnd_7760418 : Nat := 4983230072969 + 3 ^ 40 * 7760418 * 2
def baseEnd_7760418 : Nat := 3984824513803323562585493

theorem tailTrace_7760418 : CollatzResearch.WordTrace tailWord_7760418 prefixEnd_7760418 3984824513803323562585493 := by
  unfold tailWord_7760418
  simp only [CollatzResearch.WordTrace]
  refine ⟨70761424399834608680276477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188697131732892289814070605 70761424399834608680276477)
  ·
    refine ⟨26535534149937978255103679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70761424399834608680276477 26535534149937978255103679)
    ·
      refine ⟨39803301224906967382655519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26535534149937978255103679 39803301224906967382655519)
      ·
        refine ⟨59704951837360451073983279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39803301224906967382655519 59704951837360451073983279)
        ·
          refine ⟨89557427756040676610974919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59704951837360451073983279 89557427756040676610974919)
          ·
            refine ⟨134336141634061014916462379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89557427756040676610974919 134336141634061014916462379)
            ·
              refine ⟨201504212451091522374693569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134336141634061014916462379 201504212451091522374693569)
              ·
                refine ⟨151128159338318641781020177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201504212451091522374693569 151128159338318641781020177)
                ·
                  refine ⟨113346119503738981335765133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151128159338318641781020177 113346119503738981335765133)
                  ·
                    refine ⟨42504794813902118000911925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113346119503738981335765133 42504794813902118000911925)
                    ·
                      refine ⟨3984824513803323562585493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42504794813902118000911925 3984824513803323562585493)
                      ·
                        rfl

theorem cell23_7760418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_7760418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760418 prefixEnd_7760418 := by exact prefixLift 7760418
  have htrace : WordTrace (prefixWord ++ tailWord_7760418) baseStart_7760418 baseEnd_7760418 := by
    simpa [prefixWord, tailWord_7760418, baseEnd_7760418] using wordTrace_append hprefix tailTrace_7760418
  have hstable : (prefixWord ++ tailWord_7760418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760418).length < 2 ^ (prefixWord ++ tailWord_7760418).sum := by decide
  have hdescent : baseEnd_7760418 < baseStart_7760418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760435 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 3]
def baseStart_7760435 : Nat := 118140960795 + 7760435 * 2 ^ 59
def prefixEnd_7760435 : Nat := 4983230072969 + 3 ^ 40 * 7760435 * 2
def baseEnd_7760435 : Nat := 3984833242974449996072915

theorem tailTrace_7760435 : CollatzResearch.WordTrace tailWord_7760435 prefixEnd_7760435 3984833242974449996072915 := by
  unfold tailWord_7760435
  simp only [CollatzResearch.WordTrace]
  refine ⟨283046317640276846624474759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188697545093517897749649839 283046317640276846624474759)
  ·
    refine ⟨424569476460415269936712139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283046317640276846624474759 424569476460415269936712139)
    ·
      refine ⟨636854214690622904905068209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424569476460415269936712139 636854214690622904905068209)
      ·
        refine ⟨477640661017967178678801157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 636854214690622904905068209 477640661017967178678801157)
        ·
          refine ⟨89557623940868846002275217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 477640661017967178678801157 89557623940868846002275217)
          ·
            refine ⟨67168217955651634501706413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89557623940868846002275217 67168217955651634501706413)
            ·
              refine ⟨25188081733369362938139905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67168217955651634501706413 25188081733369362938139905)
              ·
                refine ⟨18891061300027022203604929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25188081733369362938139905 18891061300027022203604929)
                ·
                  refine ⟨14168295975020266652703697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18891061300027022203604929 14168295975020266652703697)
                  ·
                    refine ⟨10626221981265199989527773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14168295975020266652703697 10626221981265199989527773)
                    ·
                      refine ⟨3984833242974449996072915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10626221981265199989527773 3984833242974449996072915)
                      ·
                        rfl

theorem cell23_7760435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 3].length) (baseStart_7760435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760435 prefixEnd_7760435 := by exact prefixLift 7760435
  have htrace : WordTrace (prefixWord ++ tailWord_7760435) baseStart_7760435 baseEnd_7760435 := by
    simpa [prefixWord, tailWord_7760435, baseEnd_7760435] using wordTrace_append hprefix tailTrace_7760435
  have hstable : (prefixWord ++ tailWord_7760435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760435).length < 2 ^ (prefixWord ++ tailWord_7760435).sum := by decide
  have hdescent : baseEnd_7760435 < baseStart_7760435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760442 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 3, 4]
def baseStart_7760442 : Nat := 118140960795 + 7760442 * 2 ^ 59
def prefixEnd_7760442 : Nat := 4983230072969 + 3 ^ 40 * 7760442 * 2
def baseEnd_7760442 : Nat := 1328278945779677156228461

theorem tailTrace_7760442 : CollatzResearch.WordTrace tailWord_7760442 prefixEnd_7760442 1328278945779677156228461 := by
  unfold tailWord_7760442
  simp only [CollatzResearch.WordTrace]
  refine ⟨70761643237812871704994895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188697715300834324546653053 70761643237812871704994895)
  ·
    refine ⟨106142464856719307557492343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70761643237812871704994895 106142464856719307557492343)
    ·
      refine ⟨159213697285078961336238515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106142464856719307557492343 159213697285078961336238515)
      ·
        refine ⟨238820545927618442004357773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159213697285078961336238515 238820545927618442004357773)
        ·
          refine ⟨89557704722856915751634165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238820545927618442004357773 89557704722856915751634165)
          ·
            refine ⟨8396034817767835851715703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89557704722856915751634165 8396034817767835851715703)
            ·
              refine ⟨12594052226651753777573555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8396034817767835851715703 12594052226651753777573555)
              ·
                refine ⟨18891078339977630666360333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12594052226651753777573555 18891078339977630666360333)
                ·
                  refine ⟨7084154377491611499885125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18891078339977630666360333 7084154377491611499885125)
                  ·
                    refine ⟨1328278945779677156228461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7084154377491611499885125 1328278945779677156228461)
                    ·
                      rfl

theorem cell23_7760442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_7760442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760442 prefixEnd_7760442 := by exact prefixLift 7760442
  have htrace : WordTrace (prefixWord ++ tailWord_7760442) baseStart_7760442 baseEnd_7760442 := by
    simpa [prefixWord, tailWord_7760442, baseEnd_7760442] using wordTrace_append hprefix tailTrace_7760442
  have hstable : (prefixWord ++ tailWord_7760442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760442).length < 2 ^ (prefixWord ++ tailWord_7760442).sum := by decide
  have hdescent : baseEnd_7760442 < baseStart_7760442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760455 : List Nat := [1, 1, 4, 1, 4, 2, 1, 3, 6]
def baseStart_7760455 : Nat := 118140960795 + 7760455 * 2 ^ 59
def prefixEnd_7760455 : Nat := 4983230072969 + 3 ^ 40 * 7760455 * 2
def baseEnd_7760455 : Nat := 442760390287504435313647

theorem tailTrace_7760455 : CollatzResearch.WordTrace tailWord_7760455 prefixEnd_7760455 442760390287504435313647 := by
  unfold tailWord_7760455
  simp only [CollatzResearch.WordTrace]
  refine ⟨283047047100204390040202819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188698031400136260026801879 283047047100204390040202819)
  ·
    refine ⟨424570570650306585060304229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283047047100204390040202819 424570570650306585060304229)
    ·
      refine ⟨79606981996932484698807043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 424570570650306585060304229 79606981996932484698807043)
      ·
        refine ⟨119410472995398727048210565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79606981996932484698807043 119410472995398727048210565)
        ·
          refine ⟨22389463686637261321539481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119410472995398727048210565 22389463686637261321539481)
          ·
            refine ⟨16792097764977945991154611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22389463686637261321539481 16792097764977945991154611)
            ·
              refine ⟨25188146647466918986731917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16792097764977945991154611 25188146647466918986731917)
              ·
                refine ⟨9445554992800094620024469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25188146647466918986731917 9445554992800094620024469)
                ·
                  refine ⟨442760390287504435313647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9445554992800094620024469 442760390287504435313647)
                  ·
                    rfl

theorem cell23_7760455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 6].length) (baseStart_7760455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760455 prefixEnd_7760455 := by exact prefixLift 7760455
  have htrace : WordTrace (prefixWord ++ tailWord_7760455) baseStart_7760455 baseEnd_7760455 := by
    simpa [prefixWord, tailWord_7760455, baseEnd_7760455] using wordTrace_append hprefix tailTrace_7760455
  have hstable : (prefixWord ++ tailWord_7760455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760455).length < 2 ^ (prefixWord ++ tailWord_7760455).sum := by decide
  have hdescent : baseEnd_7760455 < baseStart_7760455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760492 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 2, 3, 2]
def baseStart_7760492 : Nat := 118140960795 + 7760492 * 2 ^ 59
def prefixEnd_7760492 : Nat := 4983230072969 + 3 ^ 40 * 7760492 * 2
def baseEnd_7760492 : Nat := 3984862511371756273060153

theorem tailTrace_7760492 : CollatzResearch.WordTrace tailWord_7760492 prefixEnd_7760492 3984862511371756273060153 := by
  unfold tailWord_7760492
  simp only [CollatzResearch.WordTrace]
  refine ⟨141524198300535172679649865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188698931067380230239533153 141524198300535172679649865)
  ·
    refine ⟨106143148725401379509737399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141524198300535172679649865 106143148725401379509737399)
    ·
      refine ⟨159214723088102069264606099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106143148725401379509737399 159214723088102069264606099)
      ·
        refine ⟨238822084632153103896909149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159214723088102069264606099 238822084632153103896909149)
        ·
          refine ⟨89558281737057413961340931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238822084632153103896909149 89558281737057413961340931)
          ·
            refine ⟨134337422605586120942011397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89558281737057413961340931 134337422605586120942011397)
            ·
              refine ⟨25188266738547397676627137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134337422605586120942011397 25188266738547397676627137)
              ·
                refine ⟨18891200053910548257470353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25188266738547397676627137 18891200053910548257470353)
                ·
                  refine ⟨14168400040432911193102765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18891200053910548257470353 14168400040432911193102765)
                  ·
                    refine ⟨5313150015162341697413537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14168400040432911193102765 5313150015162341697413537)
                    ·
                      refine ⟨3984862511371756273060153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5313150015162341697413537 3984862511371756273060153)
                      ·
                        rfl

theorem cell23_7760492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 3, 2].length) (baseStart_7760492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760492 prefixEnd_7760492 := by exact prefixLift 7760492
  have htrace : WordTrace (prefixWord ++ tailWord_7760492) baseStart_7760492 baseEnd_7760492 := by
    simpa [prefixWord, tailWord_7760492, baseEnd_7760492] using wordTrace_append hprefix tailTrace_7760492
  have hstable : (prefixWord ++ tailWord_7760492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760492).length < 2 ^ (prefixWord ++ tailWord_7760492).sum := by decide
  have hdescent : baseEnd_7760492 < baseStart_7760492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760505 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 3, 1, 4]
def baseStart_7760505 : Nat := 118140960795 + 7760505 * 2 ^ 59
def prefixEnd_7760505 : Nat := 4983230072969 + 3 ^ 40 * 7760505 * 2
def baseEnd_7760505 : Nat := 3984869186620264722197593

theorem tailTrace_7760505 : CollatzResearch.WordTrace tailWord_7760505 prefixEnd_7760505 3984869186620264722197593 := by
  unfold tailWord_7760505
  simp only [CollatzResearch.WordTrace]
  refine ⟨283048870750023248579522969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188699247166682165719681979 283048870750023248579522969)
  ·
    refine ⟨212286653062517436434642227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283048870750023248579522969 212286653062517436434642227)
    ·
      refine ⟨318429979593776154651963341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212286653062517436434642227 318429979593776154651963341)
      ·
        refine ⟨119411242347666057994486253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318429979593776154651963341 119411242347666057994486253)
        ·
          refine ⟨44779215880374771747932345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119411242347666057994486253 44779215880374771747932345)
          ·
            refine ⟨33584411910281078810949259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44779215880374771747932345 33584411910281078810949259)
            ·
              refine ⟨50376617865421618216423889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33584411910281078810949259 50376617865421618216423889)
              ·
                refine ⟨37782463399066213662317917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50376617865421618216423889 37782463399066213662317917)
                ·
                  refine ⟨14168423774649830123369219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37782463399066213662317917 14168423774649830123369219)
                  ·
                    refine ⟨21252635661974745185053829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14168423774649830123369219 21252635661974745185053829)
                    ·
                      refine ⟨3984869186620264722197593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21252635661974745185053829 3984869186620264722197593)
                      ·
                        rfl

theorem cell23_7760505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_7760505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760505 prefixEnd_7760505 := by exact prefixLift 7760505
  have htrace : WordTrace (prefixWord ++ tailWord_7760505) baseStart_7760505 baseEnd_7760505 := by
    simpa [prefixWord, tailWord_7760505, baseEnd_7760505] using wordTrace_append hprefix tailTrace_7760505
  have hstable : (prefixWord ++ tailWord_7760505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760505).length < 2 ^ (prefixWord ++ tailWord_7760505).sum := by decide
  have hdescent : baseEnd_7760505 < baseStart_7760505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760532 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_7760532 : Nat := 118140960795 + 7760532 * 2 ^ 59
def prefixEnd_7760532 : Nat := 4983230072969 + 3 ^ 40 * 7760532 * 2
def baseEnd_7760532 : Nat := 1328294350199312038853323

theorem tailTrace_7760532 : CollatzResearch.WordTrace tailWord_7760532 prefixEnd_7760532 1328294350199312038853323 := by
  unfold tailWord_7760532
  simp only [CollatzResearch.WordTrace]
  refine ⟨141524927760462716095377925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188699903680616954793837233 141524927760462716095377925)
  ·
    refine ⟨26535923955086759267883361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141524927760462716095377925 26535923955086759267883361)
    ·
      refine ⟨19901942966315069450912521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26535923955086759267883361 19901942966315069450912521)
      ·
        refine ⟨14926457224736302088184391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19901942966315069450912521 14926457224736302088184391)
        ·
          refine ⟨22389685837104453132276587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14926457224736302088184391 22389685837104453132276587)
          ·
            refine ⟨33584528755656679698414881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22389685837104453132276587 33584528755656679698414881)
            ·
              refine ⟨25188396566742509773811161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33584528755656679698414881 25188396566742509773811161)
              ·
                refine ⟨18891297425056882330358371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25188396566742509773811161 18891297425056882330358371)
                ·
                  refine ⟨28336946137585323495537557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18891297425056882330358371 28336946137585323495537557)
                  ·
                    refine ⟨1328294350199312038853323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28336946137585323495537557 1328294350199312038853323)
                    ·
                      rfl

theorem cell23_7760532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_7760532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760532 prefixEnd_7760532 := by exact prefixLift 7760532
  have htrace : WordTrace (prefixWord ++ tailWord_7760532) baseStart_7760532 baseEnd_7760532 := by
    simpa [prefixWord, tailWord_7760532, baseEnd_7760532] using wordTrace_append hprefix tailTrace_7760532
  have hstable : (prefixWord ++ tailWord_7760532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760532).length < 2 ^ (prefixWord ++ tailWord_7760532).sum := by decide
  have hdescent : baseEnd_7760532 < baseStart_7760532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760535 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 4]
def baseStart_7760535 : Nat := 118140960795 + 7760535 * 2 ^ 59
def prefixEnd_7760535 : Nat := 4983230072969 + 3 ^ 40 * 7760535 * 2
def baseEnd_7760535 : Nat := 3984884591039899604822455

theorem tailTrace_7760535 : CollatzResearch.WordTrace tailWord_7760535 prefixEnd_7760535 3984884591039899604822455 := by
  unfold tailWord_7760535
  simp only [CollatzResearch.WordTrace]
  refine ⟨283049964939914563703115059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188699976626609709135410039 283049964939914563703115059)
  ·
    refine ⟨424574947409871845554672589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283049964939914563703115059 424574947409871845554672589)
    ·
      refine ⟨159215605278701942083002221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424574947409871845554672589 159215605278701942083002221)
      ·
        refine ⟨59705851979513228281125833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159215605278701942083002221 59705851979513228281125833)
        ·
          refine ⟨44779388984634921210844375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59705851979513228281125833 44779388984634921210844375)
          ·
            refine ⟨67169083476952381816266563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44779388984634921210844375 67169083476952381816266563)
            ·
              refine ⟨100753625215428572724399845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67169083476952381816266563 100753625215428572724399845)
              ·
                refine ⟨18891304727892857385824971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100753625215428572724399845 18891304727892857385824971)
                ·
                  refine ⟨28336957091839286078737457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18891304727892857385824971 28336957091839286078737457)
                  ·
                    refine ⟨21252717818879464559053093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28336957091839286078737457 21252717818879464559053093)
                    ·
                      refine ⟨3984884591039899604822455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21252717818879464559053093 3984884591039899604822455)
                      ·
                        rfl

theorem cell23_7760535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_7760535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760535 prefixEnd_7760535 := by exact prefixLift 7760535
  have htrace : WordTrace (prefixWord ++ tailWord_7760535) baseStart_7760535 baseEnd_7760535 := by
    simpa [prefixWord, tailWord_7760535, baseEnd_7760535] using wordTrace_append hprefix tailTrace_7760535
  have hstable : (prefixWord ++ tailWord_7760535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760535).length < 2 ^ (prefixWord ++ tailWord_7760535).sum := by decide
  have hdescent : baseEnd_7760535 < baseStart_7760535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760542 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_7760542 : Nat := 118140960795 + 7760542 * 2 ^ 59
def prefixEnd_7760542 : Nat := 4983230072969 + 3 ^ 40 * 7760542 * 2
def baseEnd_7760542 : Nat := 3984888185404481077434923

theorem tailTrace_7760542 : CollatzResearch.WordTrace tailWord_7760542 prefixEnd_7760542 3984888185404481077434923 := by
  unfold tailWord_7760542
  simp only [CollatzResearch.WordTrace]
  refine ⟨35381277531361150487327485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188700146833926135932413253 35381277531361150487327485)
  ·
    refine ⟨13267979074260431432747807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35381277531361150487327485 13267979074260431432747807)
    ·
      refine ⟨19901968611390647149121711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13267979074260431432747807 19901968611390647149121711)
      ·
        refine ⟨29852952917085970723682567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19901968611390647149121711 29852952917085970723682567)
        ·
          refine ⟨44779429375628956085523851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29852952917085970723682567 44779429375628956085523851)
          ·
            refine ⟨67169144063443434128285777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44779429375628956085523851 67169144063443434128285777)
            ·
              refine ⟨50376858047582575596214333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67169144063443434128285777 50376858047582575596214333)
              ·
                refine ⟨18891321767843465848580375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50376858047582575596214333 18891321767843465848580375)
                ·
                  refine ⟨28336982651765198772870563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18891321767843465848580375 28336982651765198772870563)
                  ·
                    refine ⟨42505473977647798159305845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28336982651765198772870563 42505473977647798159305845)
                    ·
                      refine ⟨3984888185404481077434923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42505473977647798159305845 3984888185404481077434923)
                      ·
                        rfl

theorem cell23_7760542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_7760542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760542 prefixEnd_7760542 := by exact prefixLift 7760542
  have htrace : WordTrace (prefixWord ++ tailWord_7760542) baseStart_7760542 baseEnd_7760542 := by
    simpa [prefixWord, tailWord_7760542, baseEnd_7760542] using wordTrace_append hprefix tailTrace_7760542
  have hstable : (prefixWord ++ tailWord_7760542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760542).length < 2 ^ (prefixWord ++ tailWord_7760542).sum := by decide
  have hdescent : baseEnd_7760542 < baseStart_7760542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760545 : List Nat := [1, 2, 3, 3, 3, 1, 10]
def baseStart_7760545 : Nat := 118140960795 + 7760545 * 2 ^ 59
def prefixEnd_7760545 : Nat := 4983230072969 + 3 ^ 40 * 7760545 * 2
def baseEnd_7760545 : Nat := 49196169454894377354289

theorem tailTrace_7760545 : CollatzResearch.WordTrace tailWord_7760545 prefixEnd_7760545 49196169454894377354289 := by
  unfold tailWord_7760545
  simp only [CollatzResearch.WordTrace]
  refine ⟨283050329669878335410979089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188700219779918890273986059 283050329669878335410979089)
  ·
    refine ⟨212287747252408751558234317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283050329669878335410979089 212287747252408751558234317)
    ·
      refine ⟨79607905219653281834337869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212287747252408751558234317 79607905219653281834337869)
      ·
        refine ⟨29852964457369980687876701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79607905219653281834337869 29852964457369980687876701)
        ·
          refine ⟨11194861671513742757953763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29852964457369980687876701 11194861671513742757953763)
          ·
            refine ⟨16792292507270614136930645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11194861671513742757953763 16792292507270614136930645)
            ·
              refine ⟨49196169454894377354289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16792292507270614136930645 49196169454894377354289)
              ·
                rfl

theorem cell23_7760545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 10].length) (baseStart_7760545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760545 prefixEnd_7760545 := by exact prefixLift 7760545
  have htrace : WordTrace (prefixWord ++ tailWord_7760545) baseStart_7760545 baseEnd_7760545 := by
    simpa [prefixWord, tailWord_7760545, baseEnd_7760545] using wordTrace_append hprefix tailTrace_7760545
  have hstable : (prefixWord ++ tailWord_7760545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760545).length < 2 ^ (prefixWord ++ tailWord_7760545).sum := by decide
  have hdescent : baseEnd_7760545 < baseStart_7760545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760566 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_7760566 : Nat := 118140960795 + 7760566 * 2 ^ 59
def prefixEnd_7760566 : Nat := 4983230072969 + 3 ^ 40 * 7760566 * 2
def baseEnd_7760566 : Nat := 1328300169646729661178271

theorem tailTrace_7760566 : CollatzResearch.WordTrace tailWord_7760566 prefixEnd_7760566 1328300169646729661178271 := by
  unfold tailWord_7760566
  simp only [CollatzResearch.WordTrace]
  refine ⟨17690693475175140999843347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188700730401868170664995701 17690693475175140999843347)
  ·
    refine ⟨26536040212762711499765021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17690693475175140999843347 26536040212762711499765021)
    ·
      refine ⟨9951015079786016812411883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26536040212762711499765021 9951015079786016812411883)
      ·
        refine ⟨14926522619679025218617825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9951015079786016812411883 14926522619679025218617825)
        ·
          refine ⟨11194891964759268913963369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14926522619679025218617825 11194891964759268913963369)
          ·
            refine ⟨8396168973569451685472527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11194891964759268913963369 8396168973569451685472527)
            ·
              refine ⟨12594253460354177528208791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8396168973569451685472527 12594253460354177528208791)
              ·
                refine ⟨18891380190531266292313187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12594253460354177528208791 18891380190531266292313187)
                ·
                  refine ⟨28337070285796899438469781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18891380190531266292313187 28337070285796899438469781)
                  ·
                    refine ⟨1328300169646729661178271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28337070285796899438469781 1328300169646729661178271)
                    ·
                      rfl

theorem cell23_7760566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_7760566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760566 prefixEnd_7760566 := by exact prefixLift 7760566
  have htrace : WordTrace (prefixWord ++ tailWord_7760566) baseStart_7760566 baseEnd_7760566 := by
    simpa [prefixWord, tailWord_7760566, baseEnd_7760566] using wordTrace_append hprefix tailTrace_7760566
  have hstable : (prefixWord ++ tailWord_7760566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760566).length < 2 ^ (prefixWord ++ tailWord_7760566).sum := by decide
  have hdescent : baseEnd_7760566 < baseStart_7760566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760599 : List Nat := [1, 1, 3, 2, 1, 4, 2, 3, 1, 3, 2]
def baseStart_7760599 : Nat := 118140960795 + 7760599 * 2 ^ 59
def prefixEnd_7760599 : Nat := 4983230072969 + 3 ^ 40 * 7760599 * 2
def baseEnd_7760599 : Nat := 3984917453801787354422161

theorem tailTrace_7760599 : CollatzResearch.WordTrace tailWord_7760599 prefixEnd_7760599 3984917453801787354422161 := by
  unfold tailWord_7760599
  simp only [CollatzResearch.WordTrace]
  refine ⟨283052299211682702633444851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188701532807788468422296567 283052299211682702633444851)
  ·
    refine ⟨424578448817524053950167277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283052299211682702633444851 424578448817524053950167277)
    ·
      refine ⟨159216918306571520231312729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424578448817524053950167277 159216918306571520231312729)
      ·
        refine ⟨119412688729928640173484547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159216918306571520231312729 119412688729928640173484547)
        ·
          refine ⟨179119033094892960260226821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119412688729928640173484547 179119033094892960260226821)
          ·
            refine ⟨33584818705292430048792529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179119033094892960260226821 33584818705292430048792529)
            ·
              refine ⟨25188614028969322536594397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33584818705292430048792529 25188614028969322536594397)
              ·
                refine ⟨9445730260863495951222899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25188614028969322536594397 9445730260863495951222899)
                ·
                  refine ⟨14168595391295243926834349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9445730260863495951222899 14168595391295243926834349)
                  ·
                    refine ⟨5313223271735716472562881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14168595391295243926834349 5313223271735716472562881)
                    ·
                      refine ⟨3984917453801787354422161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5313223271735716472562881 3984917453801787354422161)
                      ·
                        rfl

theorem cell23_7760599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_7760599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760599 prefixEnd_7760599 := by exact prefixLift 7760599
  have htrace : WordTrace (prefixWord ++ tailWord_7760599) baseStart_7760599 baseEnd_7760599 := by
    simpa [prefixWord, tailWord_7760599, baseEnd_7760599] using wordTrace_append hprefix tailTrace_7760599
  have hstable : (prefixWord ++ tailWord_7760599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760599).length < 2 ^ (prefixWord ++ tailWord_7760599).sum := by decide
  have hdescent : baseEnd_7760599 < baseStart_7760599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760625 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 1, 4, 4]
def baseStart_7760625 : Nat := 118140960795 + 7760625 * 2 ^ 59
def prefixEnd_7760625 : Nat := 4983230072969 + 3 ^ 40 * 7760625 * 2
def baseEnd_7760625 : Nat := 3984930804298804252697041

theorem tailTrace_7760625 : CollatzResearch.WordTrace tailWord_7760625 prefixEnd_7760625 3984930804298804252697041 := by
  unfold tailWord_7760625
  simp only [CollatzResearch.WordTrace]
  refine ⟨283053247509588509073891329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188702165006392339382594219 283053247509588509073891329)
  ·
    refine ⟨212289935632191381805418497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283053247509588509073891329 212289935632191381805418497)
    ·
      refine ⟨159217451724143536354063873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212289935632191381805418497 159217451724143536354063873)
      ·
        refine ⟨119413088793107652265547905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159217451724143536354063873 119413088793107652265547905)
        ·
          refine ⟨89559816594830739199160929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119413088793107652265547905 89559816594830739199160929)
          ·
            refine ⟨67169862446123054399370697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89559816594830739199160929 67169862446123054399370697)
            ·
              refine ⟨50377396834592290799528023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67169862446123054399370697 50377396834592290799528023)
              ·
                refine ⟨75566095251888436199292035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50377396834592290799528023 75566095251888436199292035)
                ·
                  refine ⟨113349142877832654298938053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75566095251888436199292035 113349142877832654298938053)
                  ·
                    refine ⟨21252964289593622681050885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113349142877832654298938053 21252964289593622681050885)
                    ·
                      refine ⟨3984930804298804252697041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21252964289593622681050885 3984930804298804252697041)
                      ·
                        rfl

theorem cell23_7760625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_7760625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760625 prefixEnd_7760625 := by exact prefixLift 7760625
  have htrace : WordTrace (prefixWord ++ tailWord_7760625) baseStart_7760625 baseEnd_7760625 := by
    simpa [prefixWord, tailWord_7760625, baseEnd_7760625] using wordTrace_append hprefix tailTrace_7760625
  have hstable : (prefixWord ++ tailWord_7760625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760625).length < 2 ^ (prefixWord ++ tailWord_7760625).sum := by decide
  have hdescent : baseEnd_7760625 < baseStart_7760625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760652 : List Nat := [2, 2, 1, 2, 2, 1, 1, 7, 5]
def baseStart_7760652 : Nat := 118140960795 + 7760652 * 2 ^ 59
def prefixEnd_7760652 : Nat := 4983230072969 + 3 ^ 40 * 7760652 * 2
def baseEnd_7760652 : Nat := 442771629808497294117713

theorem tailTrace_7760652 : CollatzResearch.WordTrace tailWord_7760652 prefixEnd_7760652 442771629808497294117713 := by
  unfold tailWord_7760652
  simp only [CollatzResearch.WordTrace]
  refine ⟨141527116140245346342562105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188702821520327128456749473 141527116140245346342562105)
  ·
    refine ⟨106145337105184009756921579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141527116140245346342562105 106145337105184009756921579)
    ·
      refine ⟨159218005657776014635382369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106145337105184009756921579 159218005657776014635382369)
      ·
        refine ⟨119413504243332010976536777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159218005657776014635382369 119413504243332010976536777)
        ·
          refine ⟨89560128182499008232402583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119413504243332010976536777 89560128182499008232402583)
          ·
            refine ⟨134340192273748512348603875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89560128182499008232402583 134340192273748512348603875)
            ·
              refine ⟨201510288410622768522905813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134340192273748512348603875 201510288410622768522905813)
              ·
                refine ⟨4722897384623971137255605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 201510288410622768522905813 4722897384623971137255605)
                ·
                  refine ⟨442771629808497294117713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4722897384623971137255605 442771629808497294117713)
                  ·
                    rfl

theorem cell23_7760652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 5].length) (baseStart_7760652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760652 prefixEnd_7760652 := by exact prefixLift 7760652
  have htrace : WordTrace (prefixWord ++ tailWord_7760652) baseStart_7760652 baseEnd_7760652 := by
    simpa [prefixWord, tailWord_7760652, baseEnd_7760652] using wordTrace_append hprefix tailTrace_7760652
  have hstable : (prefixWord ++ tailWord_7760652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760652).length < 2 ^ (prefixWord ++ tailWord_7760652).sum := by decide
  have hdescent : baseEnd_7760652 < baseStart_7760652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760663 : List Nat := [1, 1, 3, 4, 3, 1, 2, 2, 2, 2, 2]
def baseStart_7760663 : Nat := 118140960795 + 7760663 * 2 ^ 59
def prefixEnd_7760663 : Nat := 4983230072969 + 3 ^ 40 * 7760663 * 2
def baseEnd_7760663 : Nat := 3984950316563675104021867

theorem tailTrace_7760663 : CollatzResearch.WordTrace tailWord_7760663 prefixEnd_7760663 3984950316563675104021867 := by
  unfold tailWord_7760663
  simp only [CollatzResearch.WordTrace]
  refine ⟨283054633483450841563774643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188703088988967227709183095 283054633483450841563774643)
  ·
    refine ⟨424581950225176262345661965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283054633483450841563774643 424581950225176262345661965)
    ·
      refine ⟨159218231334441098379623237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424581950225176262345661965 159218231334441098379623237)
      ·
        refine ⟨29853418375207705946179357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159218231334441098379623237 29853418375207705946179357)
        ·
          refine ⟨11195031890702889729817259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29853418375207705946179357 11195031890702889729817259)
          ·
            refine ⟨16792547836054334594725889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11195031890702889729817259 16792547836054334594725889)
            ·
              refine ⟨12594410877040750946044417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16792547836054334594725889 12594410877040750946044417)
              ·
                refine ⟨9445808157780563209533313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12594410877040750946044417 9445808157780563209533313)
                ·
                  refine ⟨7084356118335422407149985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9445808157780563209533313 7084356118335422407149985)
                  ·
                    refine ⟨5313267088751566805362489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7084356118335422407149985 5313267088751566805362489)
                    ·
                      refine ⟨3984950316563675104021867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5313267088751566805362489 3984950316563675104021867)
                      ·
                        rfl

theorem cell23_7760663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_7760663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760663 prefixEnd_7760663 := by exact prefixLift 7760663
  have htrace : WordTrace (prefixWord ++ tailWord_7760663) baseStart_7760663 baseEnd_7760663 := by
    simpa [prefixWord, tailWord_7760663, baseEnd_7760663] using wordTrace_append hprefix tailTrace_7760663
  have hstable : (prefixWord ++ tailWord_7760663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760663).length < 2 ^ (prefixWord ++ tailWord_7760663).sum := by decide
  have hdescent : baseEnd_7760663 < baseStart_7760663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760665 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 4, 5]
def baseStart_7760665 : Nat := 118140960795 + 7760665 * 2 ^ 59
def prefixEnd_7760665 : Nat := 4983230072969 + 3 ^ 40 * 7760665 * 2
def baseEnd_7760665 : Nat := 1328317114508328032065619

theorem tailTrace_7760665 : CollatzResearch.WordTrace tailWord_7760665 prefixEnd_7760665 1328317114508328032065619 := by
  unfold tailWord_7760665
  simp only [CollatzResearch.WordTrace]
  refine ⟨283054706429443595905347449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188703137619629063936898299 283054706429443595905347449)
  ·
    refine ⟨212291029822082696929010587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283054706429443595905347449 212291029822082696929010587)
    ·
      refine ⟨318436544733124045393515881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212291029822082696929010587 318436544733124045393515881)
      ·
        refine ⟨238827408549843034045136911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318436544733124045393515881 238827408549843034045136911)
        ·
          refine ⟨358241112824764551067705367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238827408549843034045136911 358241112824764551067705367)
          ·
            refine ⟨537361669237146826601558051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358241112824764551067705367 537361669237146826601558051)
            ·
              refine ⟨806042503855720239902337077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537361669237146826601558051 806042503855720239902337077)
              ·
                refine ⟨75566484736473772490844101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 806042503855720239902337077 75566484736473772490844101)
                ·
                  refine ⟨14168715888088832342033269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75566484736473772490844101 14168715888088832342033269)
                  ·
                    refine ⟨1328317114508328032065619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14168715888088832342033269 1328317114508328032065619)
                    ·
                      rfl

theorem cell23_7760665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 5].length) (baseStart_7760665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760665 prefixEnd_7760665 := by exact prefixLift 7760665
  have htrace : WordTrace (prefixWord ++ tailWord_7760665) baseStart_7760665 baseEnd_7760665 := by
    simpa [prefixWord, tailWord_7760665, baseEnd_7760665] using wordTrace_append hprefix tailTrace_7760665
  have hstable : (prefixWord ++ tailWord_7760665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760665).length < 2 ^ (prefixWord ++ tailWord_7760665).sum := by decide
  have hdescent : baseEnd_7760665 < baseStart_7760665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760712 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 5, 4]
def baseStart_7760712 : Nat := 118140960795 + 7760712 * 2 ^ 59
def prefixEnd_7760712 : Nat := 4983230072969 + 3 ^ 40 * 7760712 * 2
def baseEnd_7760712 : Nat := 1328325159038581804103047

theorem tailTrace_7760712 : CollatzResearch.WordTrace tailWord_7760712 prefixEnd_7760712 1328325159038581804103047 := by
  unfold tailWord_7760712
  simp only [CollatzResearch.WordTrace]
  refine ⟨141528210330136661466154195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188704280440182215288205593 141528210330136661466154195)
  ·
    refine ⟨212292315495204992199231293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141528210330136661466154195 212292315495204992199231293)
    ·
      refine ⟨79609618310701872074711735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212292315495204992199231293 79609618310701872074711735)
      ·
        refine ⟨119414427466052808112067603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79609618310701872074711735 119414427466052808112067603)
        ·
          refine ⟨179121641199079212168101405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119414427466052808112067603 179121641199079212168101405)
          ·
            refine ⟨67170615449654704563038027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179121641199079212168101405 67170615449654704563038027)
            ·
              refine ⟨100755923174482056844557041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67170615449654704563038027 100755923174482056844557041)
              ·
                refine ⟨75566942380861542633417781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100755923174482056844557041 75566942380861542633417781)
                ·
                  refine ⟨7084400848205769621882917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75566942380861542633417781 7084400848205769621882917)
                  ·
                    refine ⟨1328325159038581804103047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7084400848205769621882917 1328325159038581804103047)
                    ·
                      rfl

theorem cell23_7760712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_7760712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760712 prefixEnd_7760712 := by exact prefixLift 7760712
  have htrace : WordTrace (prefixWord ++ tailWord_7760712) baseStart_7760712 baseEnd_7760712 := by
    simpa [prefixWord, tailWord_7760712, baseEnd_7760712] using wordTrace_append hprefix tailTrace_7760712
  have hstable : (prefixWord ++ tailWord_7760712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760712).length < 2 ^ (prefixWord ++ tailWord_7760712).sum := by decide
  have hdescent : baseEnd_7760712 < baseStart_7760712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760715 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 4]
def baseStart_7760715 : Nat := 118140960795 + 7760715 * 2 ^ 59
def prefixEnd_7760715 : Nat := 4983230072969 + 3 ^ 40 * 7760715 * 2
def baseEnd_7760715 : Nat := 3984977017557708900571627

theorem tailTrace_7760715 : CollatzResearch.WordTrace tailWord_7760715 prefixEnd_7760715 3984977017557708900571627 := by
  unfold tailWord_7760715
  simp only [CollatzResearch.WordTrace]
  refine ⟨283056530079262454444667599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188704353386174969629778399 283056530079262454444667599)
  ·
    refine ⟨424584795118893681667001399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283056530079262454444667599 424584795118893681667001399)
    ·
      refine ⟨636877192678340522500502099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424584795118893681667001399 636877192678340522500502099)
      ·
        refine ⟨955315789017510783750753149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636877192678340522500502099 955315789017510783750753149)
        ·
          refine ⟨358243420881566543906532431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 955315789017510783750753149 358243420881566543906532431)
          ·
            refine ⟨537365131322349815859798647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358243420881566543906532431 537365131322349815859798647)
            ·
              refine ⟨806047696983524723789697971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537365131322349815859798647 806047696983524723789697971)
              ·
                refine ⟨1209071545475287085684546957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806047696983524723789697971 1209071545475287085684546957)
                ·
                  refine ⟨453401829553232657131705109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1209071545475287085684546957 453401829553232657131705109)
                  ·
                    refine ⟨21253210760307780803048677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 453401829553232657131705109 21253210760307780803048677)
                    ·
                      refine ⟨3984977017557708900571627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21253210760307780803048677 3984977017557708900571627)
                      ·
                        rfl

theorem cell23_7760715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 4].length) (baseStart_7760715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760715 prefixEnd_7760715 := by exact prefixLift 7760715
  have htrace : WordTrace (prefixWord ++ tailWord_7760715) baseStart_7760715 baseEnd_7760715 := by
    simpa [prefixWord, tailWord_7760715, baseEnd_7760715] using wordTrace_append hprefix tailTrace_7760715
  have hstable : (prefixWord ++ tailWord_7760715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760715).length < 2 ^ (prefixWord ++ tailWord_7760715).sum := by decide
  have hdescent : baseEnd_7760715 < baseStart_7760715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760729 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 3, 4]
def baseStart_7760729 : Nat := 118140960795 + 7760729 * 2 ^ 59
def prefixEnd_7760729 : Nat := 4983230072969 + 3 ^ 40 * 7760729 * 2
def baseEnd_7760729 : Nat := 1328328068762290615265521

theorem tailTrace_7760729 : CollatzResearch.WordTrace tailWord_7760729 prefixEnd_7760729 1328328068762290615265521 := by
  unfold tailWord_7760729
  simp only [CollatzResearch.WordTrace]
  refine ⟨283057040701211734835677241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188704693800807823223784827 283057040701211734835677241)
  ·
    refine ⟨212292780525908801126757931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283057040701211734835677241 212292780525908801126757931)
    ·
      refine ⟨318439170788863201690136897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212292780525908801126757931 318439170788863201690136897)
      ·
        refine ⟨238829378091647401267602673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318439170788863201690136897 238829378091647401267602673)
        ·
          refine ⟨179122033568735550950702005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238829378091647401267602673 179122033568735550950702005)
          ·
            refine ⟨16792690647068957901628313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179122033568735550950702005 16792690647068957901628313)
            ·
              refine ⟨12594517985301718426221235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16792690647068957901628313 12594517985301718426221235)
              ·
                refine ⟨18891776977952577639331853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12594517985301718426221235 18891776977952577639331853)
                ·
                  refine ⟨7084416366732216614749445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18891776977952577639331853 7084416366732216614749445)
                  ·
                    refine ⟨1328328068762290615265521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7084416366732216614749445 1328328068762290615265521)
                    ·
                      rfl

theorem cell23_7760729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 4].length) (baseStart_7760729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760729 prefixEnd_7760729 := by exact prefixLift 7760729
  have htrace : WordTrace (prefixWord ++ tailWord_7760729) baseStart_7760729 baseEnd_7760729 := by
    simpa [prefixWord, tailWord_7760729, baseEnd_7760729] using wordTrace_append hprefix tailTrace_7760729
  have hstable : (prefixWord ++ tailWord_7760729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760729).length < 2 ^ (prefixWord ++ tailWord_7760729).sum := by decide
  have hdescent : baseEnd_7760729 < baseStart_7760729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760772 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 5, 5]
def baseStart_7760772 : Nat := 118140960795 + 7760772 * 2 ^ 59
def prefixEnd_7760772 : Nat := 4983230072969 + 3 ^ 40 * 7760772 * 2
def baseEnd_7760772 : Nat := 1328335428651671725852955

theorem tailTrace_7760772 : CollatzResearch.WordTrace tailWord_7760772 prefixEnd_7760772 1328335428651671725852955 := by
  unfold tailWord_7760772
  simp only [CollatzResearch.WordTrace]
  refine ⟨141529304520027976589746285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188705739360037302119661713 141529304520027976589746285)
  ·
    refine ⟨53073489195010491221154857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141529304520027976589746285 53073489195010491221154857)
    ·
      refine ⟨39805116896257868415866143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53073489195010491221154857 39805116896257868415866143)
      ·
        refine ⟨59707675344386802623799215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39805116896257868415866143 59707675344386802623799215)
        ·
          refine ⟨89561513016580203935698823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59707675344386802623799215 89561513016580203935698823)
          ·
            refine ⟨134342269524870305903548235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89561513016580203935698823 134342269524870305903548235)
            ·
              refine ⟨201513404287305458855322353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134342269524870305903548235 201513404287305458855322353)
              ·
                refine ⟨151135053215479094141491765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201513404287305458855322353 151135053215479094141491765)
                ·
                  refine ⟨14168911238951165075764853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151135053215479094141491765 14168911238951165075764853)
                  ·
                    refine ⟨1328335428651671725852955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14168911238951165075764853 1328335428651671725852955)
                    ·
                      rfl

theorem cell23_7760772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_7760772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760772 prefixEnd_7760772 := by exact prefixLift 7760772
  have htrace : WordTrace (prefixWord ++ tailWord_7760772) baseStart_7760772 baseEnd_7760772 := by
    simpa [prefixWord, tailWord_7760772, baseEnd_7760772] using wordTrace_append hprefix tailTrace_7760772
  have hstable : (prefixWord ++ tailWord_7760772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760772).length < 2 ^ (prefixWord ++ tailWord_7760772).sum := by decide
  have hdescent : baseEnd_7760772 < baseStart_7760772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760779 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 4, 3, 2]
def baseStart_7760779 : Nat := 118140960795 + 7760779 * 2 ^ 59
def prefixEnd_7760779 : Nat := 4983230072969 + 3 ^ 40 * 7760779 * 2
def baseEnd_7760779 : Nat := 3985009880319596650171333

theorem tailTrace_7760779 : CollatzResearch.WordTrace tailWord_7760779 prefixEnd_7760779 3985009880319596650171333 := by
  unfold tailWord_7760779
  simp only [CollatzResearch.WordTrace]
  refine ⟨283058864351030593374997391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188705909567353728916664927 283058864351030593374997391)
  ·
    refine ⟨424588296526545890062496087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283058864351030593374997391 424588296526545890062496087)
    ·
      refine ⟨636882444789818835093744131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424588296526545890062496087 636882444789818835093744131)
      ·
        refine ⟨955323667184728252640616197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636882444789818835093744131 955323667184728252640616197)
        ·
          refine ⟨179123187597136547370115537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 955323667184728252640616197 179123187597136547370115537)
          ·
            refine ⟨134342390697852410527586653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179123187597136547370115537 134342390697852410527586653)
            ·
              refine ⟨50378396511694653947844995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134342390697852410527586653 50378396511694653947844995)
              ·
                refine ⟨75567594767541980921767493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50378396511694653947844995 75567594767541980921767493)
                ·
                  refine ⟨14168924018914121422831405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75567594767541980921767493 14168924018914121422831405)
                  ·
                    refine ⟨5313346507092795533561777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14168924018914121422831405 5313346507092795533561777)
                    ·
                      refine ⟨3985009880319596650171333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5313346507092795533561777 3985009880319596650171333)
                      ·
                        rfl

theorem cell23_7760779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 3, 2].length) (baseStart_7760779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760779 prefixEnd_7760779 := by exact prefixLift 7760779
  have htrace : WordTrace (prefixWord ++ tailWord_7760779) baseStart_7760779 baseEnd_7760779 := by
    simpa [prefixWord, tailWord_7760779, baseEnd_7760779] using wordTrace_append hprefix tailTrace_7760779
  have hstable : (prefixWord ++ tailWord_7760779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760779).length < 2 ^ (prefixWord ++ tailWord_7760779).sum := by decide
  have hdescent : baseEnd_7760779 < baseStart_7760779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760812 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 3]
def baseStart_7760812 : Nat := 118140960795 + 7760812 * 2 ^ 59
def prefixEnd_7760812 : Nat := 4983230072969 + 3 ^ 40 * 7760812 * 2
def baseEnd_7760812 : Nat := 3985026825181195021058681

theorem tailTrace_7760812 : CollatzResearch.WordTrace tailWord_7760812 prefixEnd_7760812 3985026825181195021058681 := by
  unfold tailWord_7760812
  simp only [CollatzResearch.WordTrace]
  refine ⟨141530033979955520005474345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188706711973274026673965793 141530033979955520005474345)
  ·
    refine ⟨106147525484966640004105759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141530033979955520005474345 106147525484966640004105759)
    ·
      refine ⟨159221288227449960006158639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106147525484966640004105759 159221288227449960006158639)
      ·
        refine ⟨238831932341174940009237959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159221288227449960006158639 238831932341174940009237959)
        ·
          refine ⟨358247898511762410013856939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238831932341174940009237959 358247898511762410013856939)
          ·
            refine ⟨537371847767643615020785409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358247898511762410013856939 537371847767643615020785409)
            ·
              refine ⟨403028885825732711265589057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537371847767643615020785409 403028885825732711265589057)
              ·
                refine ⟨302271664369299533449191793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403028885825732711265589057 302271664369299533449191793)
                ·
                  refine ⟨226703748276974650086893845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302271664369299533449191793 226703748276974650086893845)
                  ·
                    refine ⟨10626738200483186722823149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 226703748276974650086893845 10626738200483186722823149)
                    ·
                      refine ⟨3985026825181195021058681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10626738200483186722823149 3985026825181195021058681)
                      ·
                        rfl

theorem cell23_7760812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_7760812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760812 prefixEnd_7760812 := by exact prefixLift 7760812
  have htrace : WordTrace (prefixWord ++ tailWord_7760812) baseStart_7760812 baseEnd_7760812 := by
    simpa [prefixWord, tailWord_7760812, baseEnd_7760812] using wordTrace_append hprefix tailTrace_7760812
  have hstable : (prefixWord ++ tailWord_7760812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760812).length < 2 ^ (prefixWord ++ tailWord_7760812).sum := by decide
  have hdescent : baseEnd_7760812 < baseStart_7760812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760826 : List Nat := [3, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4]
def baseStart_7760826 : Nat := 118140960795 + 7760826 * 2 ^ 59
def prefixEnd_7760826 : Nat := 4983230072969 + 3 ^ 40 * 7760826 * 2
def baseEnd_7760826 : Nat := 3985034013910357966283617

theorem tailTrace_7760826 : CollatzResearch.WordTrace tailWord_7760826 prefixEnd_7760826 3985034013910357966283617 := by
  unfold tailWord_7760826
  simp only [CollatzResearch.WordTrace]
  refine ⟨70765144645465080100489583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188707052387906880267972221 70765144645465080100489583)
  ·
    refine ⟨106147716968197620150734375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70765144645465080100489583 106147716968197620150734375)
    ·
      refine ⟨159221575452296430226101563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106147716968197620150734375 159221575452296430226101563)
      ·
        refine ⟨238832363178444645339152345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159221575452296430226101563 238832363178444645339152345)
        ·
          refine ⟨179124272383833484004364259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238832363178444645339152345 179124272383833484004364259)
          ·
            refine ⟨268686408575750226006546389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179124272383833484004364259 268686408575750226006546389)
            ·
              refine ⟨6297337700994145922028431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 268686408575750226006546389 6297337700994145922028431)
              ·
                refine ⟨9446006551491218883042647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6297337700994145922028431 9446006551491218883042647)
                ·
                  refine ⟨14169009827236828324563971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9446006551491218883042647 14169009827236828324563971)
                  ·
                    refine ⟨21253514740855242486845957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14169009827236828324563971 21253514740855242486845957)
                    ·
                      refine ⟨3985034013910357966283617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21253514740855242486845957 3985034013910357966283617)
                      ·
                        rfl

theorem cell23_7760826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4].length) (baseStart_7760826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760826 prefixEnd_7760826 := by exact prefixLift 7760826
  have htrace : WordTrace (prefixWord ++ tailWord_7760826) baseStart_7760826 baseEnd_7760826 := by
    simpa [prefixWord, tailWord_7760826, baseEnd_7760826] using wordTrace_append hprefix tailTrace_7760826
  have hstable : (prefixWord ++ tailWord_7760826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760826).length < 2 ^ (prefixWord ++ tailWord_7760826).sum := by decide
  have hdescent : baseEnd_7760826 < baseStart_7760826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760899 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 2, 8, 2]
def baseStart_7760899 : Nat := 118140960795 + 7760899 * 2 ^ 59
def prefixEnd_7760899 : Nat := 4983230072969 + 3 ^ 40 * 7760899 * 2
def baseEnd_7760899 : Nat := 3985071497998136180670781

theorem tailTrace_7760899 : CollatzResearch.WordTrace tailWord_7760899 prefixEnd_7760899 3985071497998136180670781 := by
  unfold tailWord_7760899
  simp only [CollatzResearch.WordTrace]
  refine ⟨283063241110595853869365751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188708827407063902579577167 283063241110595853869365751)
  ·
    refine ⟨424594861665893780804048627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283063241110595853869365751 424594861665893780804048627)
    ·
      refine ⟨636892292498840671206072941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424594861665893780804048627 636892292498840671206072941)
      ·
        refine ⟨238834609687065251702277353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 636892292498840671206072941 238834609687065251702277353)
        ·
          refine ⟨179125957265298938776708015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238834609687065251702277353 179125957265298938776708015)
          ·
            refine ⟨268688935897948408165062023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179125957265298938776708015 268688935897948408165062023)
            ·
              refine ⟨403033403846922612247593035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268688935897948408165062023 403033403846922612247593035)
              ·
                refine ⟨604550105770383918371389553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403033403846922612247593035 604550105770383918371389553)
                ·
                  refine ⟨453412579327787938778542165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604550105770383918371389553 453412579327787938778542165)
                  ·
                    refine ⟨5313428663997514907561041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 453412579327787938778542165 5313428663997514907561041)
                    ·
                      refine ⟨3985071497998136180670781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5313428663997514907561041 3985071497998136180670781)
                      ·
                        rfl

theorem cell23_7760899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 8, 2].length) (baseStart_7760899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760899 prefixEnd_7760899 := by exact prefixLift 7760899
  have htrace : WordTrace (prefixWord ++ tailWord_7760899) baseStart_7760899 baseEnd_7760899 := by
    simpa [prefixWord, tailWord_7760899, baseEnd_7760899] using wordTrace_append hprefix tailTrace_7760899
  have hstable : (prefixWord ++ tailWord_7760899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760899).length < 2 ^ (prefixWord ++ tailWord_7760899).sum := by decide
  have hdescent : baseEnd_7760899 < baseStart_7760899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760910 : List Nat := [4, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3]
def baseStart_7760910 : Nat := 118140960795 + 7760910 * 2 ^ 59
def prefixEnd_7760910 : Nat := 4983230072969 + 3 ^ 40 * 7760910 * 2
def baseEnd_7760910 : Nat := 3985077146285335637633231

theorem tailTrace_7760910 : CollatzResearch.WordTrace tailWord_7760910 prefixEnd_7760910 3985077146285335637633231 := by
  unfold tailWord_7760910
  simp only [CollatzResearch.WordTrace]
  refine ⟨35382955289194500343502023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188709094875704001832010789 35382955289194500343502023)
  ·
    refine ⟨53074432933791750515253035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35382955289194500343502023 53074432933791750515253035)
    ·
      refine ⟨79611649400687625772879553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53074432933791750515253035 79611649400687625772879553)
      ·
        refine ⟨59708737050515719329659665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79611649400687625772879553 59708737050515719329659665)
        ·
          refine ⟨44781552787886789497244749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59708737050515719329659665 44781552787886789497244749)
          ·
            refine ⟨16793082295457546061466781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44781552787886789497244749 16793082295457546061466781)
            ·
              refine ⟨6297405860796579773050043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16793082295457546061466781 6297405860796579773050043)
              ·
                refine ⟨9446108791194869659575065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6297405860796579773050043 9446108791194869659575065)
                ·
                  refine ⟨7084581593396152244681299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9446108791194869659575065 7084581593396152244681299)
                  ·
                    refine ⟨10626872390094228367021949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7084581593396152244681299 10626872390094228367021949)
                    ·
                      refine ⟨3985077146285335637633231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10626872390094228367021949 3985077146285335637633231)
                      ·
                        rfl

theorem cell23_7760910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_7760910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760910 prefixEnd_7760910 := by exact prefixLift 7760910
  have htrace : WordTrace (prefixWord ++ tailWord_7760910) baseStart_7760910 baseEnd_7760910 := by
    simpa [prefixWord, tailWord_7760910, baseEnd_7760910] using wordTrace_append hprefix tailTrace_7760910
  have hstable : (prefixWord ++ tailWord_7760910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760910).length < 2 ^ (prefixWord ++ tailWord_7760910).sum := by decide
  have hdescent : baseEnd_7760910 < baseStart_7760910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760950 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_7760950 : Nat := 118140960795 + 7760950 * 2 ^ 59
def prefixEnd_7760950 : Nat := 4983230072969 + 3 ^ 40 * 7760950 * 2
def baseEnd_7760950 : Nat := 3985097685511515481133047

theorem tailTrace_7760950 : CollatzResearch.WordTrace tailWord_7760950 prefixEnd_7760950 3985097685511515481133047 := by
  unfold tailWord_7760950
  simp only [CollatzResearch.WordTrace]
  refine ⟨17691568827088193098717019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188710067488940726386314869 17691568827088193098717019)
  ·
    refine ⟨26537353240632289648075529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17691568827088193098717019 26537353240632289648075529)
    ·
      refine ⟨19903014930474217236056647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26537353240632289648075529 19903014930474217236056647)
      ·
        refine ⟨29854522395711325854084971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19903014930474217236056647 29854522395711325854084971)
        ·
          refine ⟨44781783593566988781127457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29854522395711325854084971 44781783593566988781127457)
          ·
            refine ⟨33586337695175241585845593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44781783593566988781127457 33586337695175241585845593)
            ·
              refine ⟨25189753271381431189384195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33586337695175241585845593 25189753271381431189384195)
              ·
                refine ⟨37784629907072146784076293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25189753271381431189384195 37784629907072146784076293)
                ·
                  refine ⟨7084618107576027522014305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37784629907072146784076293 7084618107576027522014305)
                  ·
                    refine ⟨5313463580682020641510729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7084618107576027522014305 5313463580682020641510729)
                    ·
                      refine ⟨3985097685511515481133047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5313463580682020641510729 3985097685511515481133047)
                      ·
                        rfl

theorem cell23_7760950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_7760950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760950 prefixEnd_7760950 := by exact prefixLift 7760950
  have htrace : WordTrace (prefixWord ++ tailWord_7760950) baseStart_7760950 baseEnd_7760950 := by
    simpa [prefixWord, tailWord_7760950, baseEnd_7760950] using wordTrace_append hprefix tailTrace_7760950
  have hstable : (prefixWord ++ tailWord_7760950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760950).length < 2 ^ (prefixWord ++ tailWord_7760950).sum := by decide
  have hdescent : baseEnd_7760950 < baseStart_7760950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760956 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 7]
def baseStart_7760956 : Nat := 118140960795 + 7760956 * 2 ^ 59
def prefixEnd_7760956 : Nat := 4983230072969 + 3 ^ 40 * 7760956 * 2
def baseEnd_7760956 : Nat := 442788974043938050850891

theorem tailTrace_7760956 : CollatzResearch.WordTrace tailWord_7760956 prefixEnd_7760956 442788974043938050850891 := by
  unfold tailWord_7760956
  simp only [CollatzResearch.WordTrace]
  refine ⟨141532660035694676302095361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188710213380926235069460481 141532660035694676302095361)
  ·
    refine ⟨106149495026771007226571521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141532660035694676302095361 106149495026771007226571521)
    ·
      refine ⟨79612121270078255419928641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106149495026771007226571521 79612121270078255419928641)
      ·
        refine ⟨59709090952558691564946481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79612121270078255419928641 59709090952558691564946481)
        ·
          refine ⟨44781818214419018673709861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59709090952558691564946481 44781818214419018673709861)
          ·
            refine ⟨8396590915203566001320599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44781818214419018673709861 8396590915203566001320599)
            ·
              refine ⟨12594886372805349001980899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8396590915203566001320599 12594886372805349001980899)
              ·
                refine ⟨18892329559208023502971349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12594886372805349001980899 18892329559208023502971349)
                ·
                  refine ⟨442788974043938050850891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18892329559208023502971349 442788974043938050850891)
                  ·
                    rfl

theorem cell23_7760956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 7].length) (baseStart_7760956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760956 prefixEnd_7760956 := by exact prefixLift 7760956
  have htrace : WordTrace (prefixWord ++ tailWord_7760956) baseStart_7760956 baseEnd_7760956 := by
    simpa [prefixWord, tailWord_7760956, baseEnd_7760956] using wordTrace_append hprefix tailTrace_7760956
  have hstable : (prefixWord ++ tailWord_7760956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760956).length < 2 ^ (prefixWord ++ tailWord_7760956).sum := by decide
  have hdescent : baseEnd_7760956 < baseStart_7760956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7760967 : List Nat := [1, 1, 4, 1, 3, 4, 2, 1, 2, 2, 2]
def baseStart_7760967 : Nat := 118140960795 + 7760967 * 2 ^ 59
def prefixEnd_7760967 : Nat := 4983230072969 + 3 ^ 40 * 7760967 * 2
def baseEnd_7760967 : Nat := 3985106414682641914620469

theorem tailTrace_7760967 : CollatzResearch.WordTrace tailWord_7760967 prefixEnd_7760967 3985106414682641914620469 := by
  unfold tailWord_7760967
  simp only [CollatzResearch.WordTrace]
  refine ⟨283065721274349501482841155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188710480849566334321894103 283065721274349501482841155)
  ·
    refine ⟨424598581911524252224261733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283065721274349501482841155 424598581911524252224261733)
    ·
      refine ⟨79612234108410797292049075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 424598581911524252224261733 79612234108410797292049075)
      ·
        refine ⟨119418351162616195938073613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79612234108410797292049075 119418351162616195938073613)
        ·
          refine ⟨44781881685981073476777605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119418351162616195938073613 44781881685981073476777605)
          ·
            refine ⟨8396602816121451276895801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44781881685981073476777605 8396602816121451276895801)
            ·
              refine ⟨6297452112091088457671851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8396602816121451276895801 6297452112091088457671851)
              ·
                refine ⟨9446178168136632686507777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6297452112091088457671851 9446178168136632686507777)
                ·
                  refine ⟨7084633626102474514880833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9446178168136632686507777 7084633626102474514880833)
                  ·
                    refine ⟨5313475219576855886160625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7084633626102474514880833 5313475219576855886160625)
                    ·
                      refine ⟨3985106414682641914620469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5313475219576855886160625 3985106414682641914620469)
                      ·
                        rfl

theorem cell23_7760967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_7760967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7760967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7760967 prefixEnd_7760967 := by exact prefixLift 7760967
  have htrace : WordTrace (prefixWord ++ tailWord_7760967) baseStart_7760967 baseEnd_7760967 := by
    simpa [prefixWord, tailWord_7760967, baseEnd_7760967] using wordTrace_append hprefix tailTrace_7760967
  have hstable : (prefixWord ++ tailWord_7760967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7760967).length < 2 ^ (prefixWord ++ tailWord_7760967).sum := by decide
  have hdescent : baseEnd_7760967 < baseStart_7760967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7760967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761050 : List Nat := [3, 1, 1, 5, 1, 1, 1, 5, 1, 4]
def baseStart_7761050 : Nat := 118140960795 + 7761050 * 2 ^ 59
def prefixEnd_7761050 : Nat := 4983230072969 + 3 ^ 40 * 7761050 * 2
def baseEnd_7761050 : Nat := 1328383011192321696627529

theorem tailTrace_7761050 : CollatzResearch.WordTrace tailWord_7761050 prefixEnd_7761050 1328383011192321696627529 := by
  unfold tailWord_7761050
  simp only [CollatzResearch.WordTrace]
  refine ⟨70767187133262201664528151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188712499022032537772075069 70767187133262201664528151)
  ·
    refine ⟨106150780699893302496792227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70767187133262201664528151 106150780699893302496792227)
    ·
      refine ⟨159226171049839953745188341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106150780699893302496792227 159226171049839953745188341)
      ·
        refine ⟨14927453535922495663611407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159226171049839953745188341 14927453535922495663611407)
        ·
          refine ⟨22391180303883743495417111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14927453535922495663611407 22391180303883743495417111)
          ·
            refine ⟨33586770455825615243125667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22391180303883743495417111 33586770455825615243125667)
            ·
              refine ⟨50380155683738422864688501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33586770455825615243125667 50380155683738422864688501)
              ·
                refine ⟨4723139595350477143564547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50380155683738422864688501 4723139595350477143564547)
                ·
                  refine ⟨7084709393025715715346821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723139595350477143564547 7084709393025715715346821)
                  ·
                    refine ⟨1328383011192321696627529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7084709393025715715346821 1328383011192321696627529)
                    ·
                      rfl

theorem cell23_7761050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 1, 4].length) (baseStart_7761050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761050 prefixEnd_7761050 := by exact prefixLift 7761050
  have htrace : WordTrace (prefixWord ++ tailWord_7761050) baseStart_7761050 baseEnd_7761050 := by
    simpa [prefixWord, tailWord_7761050, baseEnd_7761050] using wordTrace_append hprefix tailTrace_7761050
  have hstable : (prefixWord ++ tailWord_7761050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761050).length < 2 ^ (prefixWord ++ tailWord_7761050).sum := by decide
  have hdescent : baseEnd_7761050 < baseStart_7761050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761063 : List Nat := [1, 1, 6, 2, 1, 1, 3, 2, 6]
def baseStart_7761063 : Nat := 118140960795 + 7761063 * 2 ^ 59
def prefixEnd_7761063 : Nat := 4983230072969 + 3 ^ 40 * 7761063 * 2
def baseEnd_7761063 : Nat := 442795078758385948780003

theorem tailTrace_7761063 : CollatzResearch.WordTrace tailWord_7761063 prefixEnd_7761063 442795078758385948780003 := by
  unfold tailWord_7761063
  simp only [CollatzResearch.WordTrace]
  refine ⟨283069222682001709878335843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188712815121334473252223895 283069222682001709878335843)
  ·
    refine ⟨424603834023002564817503765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283069222682001709878335843 424603834023002564817503765)
    ·
      refine ⟨19903304719828245225820489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 424603834023002564817503765 19903304719828245225820489)
      ·
        refine ⟨14927478539871183919365367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19903304719828245225820489 14927478539871183919365367)
        ·
          refine ⟨22391217809806775879048051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14927478539871183919365367 22391217809806775879048051)
          ·
            refine ⟨33586826714710163818572077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22391217809806775879048051 33586826714710163818572077)
            ·
              refine ⟨12595060018016311431964529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33586826714710163818572077 12595060018016311431964529)
              ·
                refine ⟨9446295013512233573973397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12595060018016311431964529 9446295013512233573973397)
                ·
                  refine ⟨442795078758385948780003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9446295013512233573973397 442795078758385948780003)
                  ·
                    rfl

theorem cell23_7761063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 6].length) (baseStart_7761063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761063 prefixEnd_7761063 := by exact prefixLift 7761063
  have htrace : WordTrace (prefixWord ++ tailWord_7761063) baseStart_7761063 baseEnd_7761063 := by
    simpa [prefixWord, tailWord_7761063, baseEnd_7761063] using wordTrace_append hprefix tailTrace_7761063
  have hstable : (prefixWord ++ tailWord_7761063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761063).length < 2 ^ (prefixWord ++ tailWord_7761063).sum := by decide
  have hdescent : baseEnd_7761063 < baseStart_7761063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761096 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_7761096 : Nat := 118140960795 + 7761096 * 2 ^ 59
def prefixEnd_7761096 : Nat := 4983230072969 + 3 ^ 40 * 7761096 * 2
def baseEnd_7761096 : Nat := 3985172653687071909907375

theorem tailTrace_7761096 : CollatzResearch.WordTrace tailWord_7761096 prefixEnd_7761096 3985172653687071909907375 := by
  unfold tailWord_7761096
  simp only [CollatzResearch.WordTrace]
  refine ⟨141535213145441078257143571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188713617527254771009524761 141535213145441078257143571)
  ·
    refine ⟨212302819718161617385715357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141535213145441078257143571 212302819718161617385715357)
    ·
      refine ⟨79613557394310606519643259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212302819718161617385715357 79613557394310606519643259)
      ·
        refine ⟨119420336091465909779464889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79613557394310606519643259 119420336091465909779464889)
        ·
          refine ⟨89565252068599432334598667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119420336091465909779464889 89565252068599432334598667)
          ·
            refine ⟨134347878102899148501898001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89565252068599432334598667 134347878102899148501898001)
            ·
              refine ⟨100760908577174361376423501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134347878102899148501898001 100760908577174361376423501)
              ·
                refine ⟨37785340716440385516158813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100760908577174361376423501 37785340716440385516158813)
                ·
                  refine ⟨14169502768665144568559555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37785340716440385516158813 14169502768665144568559555)
                  ·
                    refine ⟨21254254152997716852839333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14169502768665144568559555 21254254152997716852839333)
                    ·
                      refine ⟨3985172653687071909907375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21254254152997716852839333 3985172653687071909907375)
                      ·
                        rfl

theorem cell23_7761096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_7761096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761096 prefixEnd_7761096 := by exact prefixLift 7761096
  have htrace : WordTrace (prefixWord ++ tailWord_7761096) baseStart_7761096 baseEnd_7761096 := by
    simpa [prefixWord, tailWord_7761096, baseEnd_7761096] using wordTrace_append hprefix tailTrace_7761096
  have hstable : (prefixWord ++ tailWord_7761096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761096).length < 2 ^ (prefixWord ++ tailWord_7761096).sum := by decide
  have hdescent : baseEnd_7761096 < baseStart_7761096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761101 : List Nat := [1, 6, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_7761101 : Nat := 118140960795 + 7761101 * 2 ^ 59
def prefixEnd_7761101 : Nat := 4983230072969 + 3 ^ 40 * 7761101 * 2
def baseEnd_7761101 : Nat := 1328391740363448130114951

theorem tailTrace_7761101 : CollatzResearch.WordTrace tailWord_7761101 prefixEnd_7761101 1328391740363448130114951 := by
  unfold tailWord_7761101
  simp only [CollatzResearch.WordTrace]
  refine ⟨283070608655864042368219157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188713739103909361578812771 283070608655864042368219157)
  ·
    refine ⟨13268934780743626986010273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 283070608655864042368219157 13268934780743626986010273)
    ·
      refine ⟨9951701085557720239507705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13268934780743626986010273 9951701085557720239507705)
      ·
        refine ⟨7463775814168290179630779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9951701085557720239507705 7463775814168290179630779)
        ·
          refine ⟨11195663721252435269446169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7463775814168290179630779 11195663721252435269446169)
          ·
            refine ⟨8396747790939326452084627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11195663721252435269446169 8396747790939326452084627)
            ·
              refine ⟨12595121686408989678126941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8396747790939326452084627 12595121686408989678126941)
              ·
                refine ⟨4723170632403371129297603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12595121686408989678126941 4723170632403371129297603)
                ·
                  refine ⟨7084755948605056693946405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723170632403371129297603 7084755948605056693946405)
                  ·
                    refine ⟨1328391740363448130114951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7084755948605056693946405 1328391740363448130114951)
                    ·
                      rfl

theorem cell23_7761101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_7761101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761101 prefixEnd_7761101 := by exact prefixLift 7761101
  have htrace : WordTrace (prefixWord ++ tailWord_7761101) baseStart_7761101 baseEnd_7761101 := by
    simpa [prefixWord, tailWord_7761101, baseEnd_7761101] using wordTrace_append hprefix tailTrace_7761101
  have hstable : (prefixWord ++ tailWord_7761101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761101).length < 2 ^ (prefixWord ++ tailWord_7761101).sum := by decide
  have hdescent : baseEnd_7761101 < baseStart_7761101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761106 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 3, 6]
def baseStart_7761106 : Nat := 118140960795 + 7761106 * 2 ^ 59
def prefixEnd_7761106 : Nat := 4983230072969 + 3 ^ 40 * 7761106 * 2
def baseEnd_7761106 : Nat := 1328392596164538956927443

theorem tailTrace_7761106 : CollatzResearch.WordTrace tailWord_7761106 prefixEnd_7761106 1328392596164538956927443 := by
  unfold tailWord_7761106
  simp only [CollatzResearch.WordTrace]
  refine ⟨70767697755211482055537793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188713860680563952148100781 70767697755211482055537793)
  ·
    refine ⟨53075773316408611541653345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70767697755211482055537793 53075773316408611541653345)
    ·
      refine ⟨39806829987306458656240009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53075773316408611541653345 39806829987306458656240009)
      ·
        refine ⟨29855122490479843992180007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39806829987306458656240009 29855122490479843992180007)
        ·
          refine ⟨44782683735719765988270011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29855122490479843992180007 44782683735719765988270011)
          ·
            refine ⟨67174025603579648982405017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44782683735719765988270011 67174025603579648982405017)
            ·
              refine ⟨50380519202684736736803763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67174025603579648982405017 50380519202684736736803763)
              ·
                refine ⟨75570778804027105105205645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50380519202684736736803763 75570778804027105105205645)
                ·
                  refine ⟨28339042051510164414452117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75570778804027105105205645 28339042051510164414452117)
                  ·
                    refine ⟨1328392596164538956927443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28339042051510164414452117 1328392596164538956927443)
                    ·
                      rfl

theorem cell23_7761106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_7761106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761106 prefixEnd_7761106 := by exact prefixLift 7761106
  have htrace : WordTrace (prefixWord ++ tailWord_7761106) baseStart_7761106 baseEnd_7761106 := by
    simpa [prefixWord, tailWord_7761106, baseEnd_7761106] using wordTrace_append hprefix tailTrace_7761106
  have hstable : (prefixWord ++ tailWord_7761106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761106).length < 2 ^ (prefixWord ++ tailWord_7761106).sum := by decide
  have hdescent : baseEnd_7761106 < baseStart_7761106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761117 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_7761117 : Nat := 118140960795 + 7761117 * 2 ^ 59
def prefixEnd_7761117 : Nat := 4983230072969 + 3 ^ 40 * 7761117 * 2
def baseEnd_7761117 : Nat := 3985183436780816327744779

theorem tailTrace_7761117 : CollatzResearch.WordTrace tailWord_7761117 prefixEnd_7761117 3985183436780816327744779 := by
  unfold tailWord_7761117
  simp only [CollatzResearch.WordTrace]
  refine ⟨283071192223806077100801605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188714128149204051400534403 283071192223806077100801605)
  ·
    refine ⟨53075848541963639456400301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283071192223806077100801605 53075848541963639456400301)
    ·
      refine ⟨19903443203236364796150113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53075848541963639456400301 19903443203236364796150113)
      ·
        refine ⟨14927582402427273597112585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19903443203236364796150113 14927582402427273597112585)
        ·
          refine ⟨11195686801820455197834439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14927582402427273597112585 11195686801820455197834439)
          ·
            refine ⟨16793530202730682796751659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11195686801820455197834439 16793530202730682796751659)
            ·
              refine ⟨25190295304096024195127489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16793530202730682796751659 25190295304096024195127489)
              ·
                refine ⟨18892721478072018146345617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25190295304096024195127489 18892721478072018146345617)
                ·
                  refine ⟨14169541108554013609759213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18892721478072018146345617 14169541108554013609759213)
                  ·
                    refine ⟨5313577915707755103659705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14169541108554013609759213 5313577915707755103659705)
                    ·
                      refine ⟨3985183436780816327744779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5313577915707755103659705 3985183436780816327744779)
                      ·
                        rfl

theorem cell23_7761117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_7761117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761117 prefixEnd_7761117 := by exact prefixLift 7761117
  have htrace : WordTrace (prefixWord ++ tailWord_7761117) baseStart_7761117 baseEnd_7761117 := by
    simpa [prefixWord, tailWord_7761117, baseEnd_7761117] using wordTrace_append hprefix tailTrace_7761117
  have hstable : (prefixWord ++ tailWord_7761117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761117).length < 2 ^ (prefixWord ++ tailWord_7761117).sum := by decide
  have hdescent : baseEnd_7761117 < baseStart_7761117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761119 : List Nat := [1, 1, 2, 3, 2, 1, 13]
def baseStart_7761119 : Nat := 118140960795 + 7761119 * 2 ^ 59
def prefixEnd_7761119 : Nat := 4983230072969 + 3 ^ 40 * 7761119 * 2
def baseEnd_7761119 : Nat := 49199808194347226171849

theorem tailTrace_7761119 : CollatzResearch.WordTrace tailWord_7761119 prefixEnd_7761119 49199808194347226171849 := by
  unfold tailWord_7761119
  simp only [CollatzResearch.WordTrace]
  refine ⟨283071265169798831442374411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188714176779865887628249607 283071265169798831442374411)
  ·
    refine ⟨424606897754698247163561617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283071265169798831442374411 424606897754698247163561617)
    ·
      refine ⟨318455173316023685372671213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424606897754698247163561617 318455173316023685372671213)
      ·
        refine ⟨119420689993508882014751705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318455173316023685372671213 119420689993508882014751705)
        ·
          refine ⟨89565517495131661511063779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119420689993508882014751705 89565517495131661511063779)
          ·
            refine ⟨134348276242697492266595669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89565517495131661511063779 134348276242697492266595669)
            ·
              refine ⟨49199808194347226171849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 134348276242697492266595669 49199808194347226171849)
              ·
                rfl

theorem cell23_7761119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 13].length) (baseStart_7761119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761119 prefixEnd_7761119 := by exact prefixLift 7761119
  have htrace : WordTrace (prefixWord ++ tailWord_7761119) baseStart_7761119 baseEnd_7761119 := by
    simpa [prefixWord, tailWord_7761119, baseEnd_7761119] using wordTrace_append hprefix tailTrace_7761119
  have hstable : (prefixWord ++ tailWord_7761119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761119).length < 2 ^ (prefixWord ++ tailWord_7761119).sum := by decide
  have hdescent : baseEnd_7761119 < baseStart_7761119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761129 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 7]
def baseStart_7761129 : Nat := 118140960795 + 7761129 * 2 ^ 59
def prefixEnd_7761129 : Nat := 4983230072969 + 3 ^ 40 * 7761129 * 2
def baseEnd_7761129 : Nat := 3985189598548670280794723

theorem tailTrace_7761129 : CollatzResearch.WordTrace tailWord_7761129 prefixEnd_7761129 3985189598548670280794723 := by
  unfold tailWord_7761129
  simp only [CollatzResearch.WordTrace]
  refine ⟨283071629899762603150238441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188714419933175068766825627 283071629899762603150238441)
  ·
    refine ⟨212303722424821952362678831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283071629899762603150238441 212303722424821952362678831)
    ·
      refine ⟨318455583637232928544018247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212303722424821952362678831 318455583637232928544018247)
      ·
        refine ⟨477683375455849392816027371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318455583637232928544018247 477683375455849392816027371)
        ·
          refine ⟨716525063183774089224041057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477683375455849392816027371 716525063183774089224041057)
          ·
            refine ⟨537393797387830566918030793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716525063183774089224041057 537393797387830566918030793)
            ·
              refine ⟨403045348040872925188523095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537393797387830566918030793 403045348040872925188523095)
              ·
                refine ⟨604568022061309387782784643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403045348040872925188523095 604568022061309387782784643)
                ·
                  refine ⟨906852033091964081674176965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 604568022061309387782784643 906852033091964081674176965)
                  ·
                    refine ⟨170034756204743265313908181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 906852033091964081674176965 170034756204743265313908181)
                    ·
                      refine ⟨3985189598548670280794723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170034756204743265313908181 3985189598548670280794723)
                      ·
                        rfl

theorem cell23_7761129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_7761129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761129 prefixEnd_7761129 := by exact prefixLift 7761129
  have htrace : WordTrace (prefixWord ++ tailWord_7761129) baseStart_7761129 baseEnd_7761129 := by
    simpa [prefixWord, tailWord_7761129, baseEnd_7761129] using wordTrace_append hprefix tailTrace_7761129
  have hstable : (prefixWord ++ tailWord_7761129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761129).length < 2 ^ (prefixWord ++ tailWord_7761129).sum := by decide
  have hdescent : baseEnd_7761129 < baseStart_7761129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761133 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_7761133 : Nat := 118140960795 + 7761133 * 2 ^ 59
def prefixEnd_7761133 : Nat := 4983230072969 + 3 ^ 40 * 7761133 * 2
def baseEnd_7761133 : Nat := 3985191652471288265144705

theorem tailTrace_7761133 : CollatzResearch.WordTrace tailWord_7761133 prefixEnd_7761133 3985191652471288265144705 := by
  unfold tailWord_7761133
  simp only [CollatzResearch.WordTrace]
  refine ⟨283071775791748111833384053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188714517194498741222256035 283071775791748111833384053)
  ·
    refine ⟨26537978980476385484379755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 283071775791748111833384053 26537978980476385484379755)
    ·
      refine ⟨39806968470714578226569633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26537978980476385484379755 39806968470714578226569633)
      ·
        refine ⟨29855226353035933669927225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39806968470714578226569633 29855226353035933669927225)
        ·
          refine ⟨22391419764776950252445419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29855226353035933669927225 22391419764776950252445419)
          ·
            refine ⟨33587129647165425378668129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22391419764776950252445419 33587129647165425378668129)
            ·
              refine ⟨25190347235374069034001097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33587129647165425378668129 25190347235374069034001097)
              ·
                refine ⟨18892760426530551775500823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25190347235374069034001097 18892760426530551775500823)
                ·
                  refine ⟨28339140639795827663251235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18892760426530551775500823 28339140639795827663251235)
                  ·
                    refine ⟨42508710959693741494876853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28339140639795827663251235 42508710959693741494876853)
                    ·
                      refine ⟨3985191652471288265144705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42508710959693741494876853 3985191652471288265144705)
                      ·
                        rfl

theorem cell23_7761133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_7761133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761133 prefixEnd_7761133 := by exact prefixLift 7761133
  have htrace : WordTrace (prefixWord ++ tailWord_7761133) baseStart_7761133 baseEnd_7761133 := by
    simpa [prefixWord, tailWord_7761133, baseEnd_7761133] using wordTrace_append hprefix tailTrace_7761133
  have hstable : (prefixWord ++ tailWord_7761133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761133).length < 2 ^ (prefixWord ++ tailWord_7761133).sum := by decide
  have hdescent : baseEnd_7761133 < baseStart_7761133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761150 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_7761150 : Nat := 118140960795 + 7761150 * 2 ^ 59
def prefixEnd_7761150 : Nat := 4983230072969 + 3 ^ 40 * 7761150 * 2
def baseEnd_7761150 : Nat := 3985200381642414698632127

theorem tailTrace_7761150 : CollatzResearch.WordTrace tailWord_7761150 prefixEnd_7761150 3985200381642414698632127 := by
  unfold tailWord_7761150
  simp only [CollatzResearch.WordTrace]
  refine ⟨35384049479085815467094113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188714930555124349157835269 35384049479085815467094113)
  ·
    refine ⟨26538037109314361600320585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35384049479085815467094113 26538037109314361600320585)
    ·
      refine ⟨19903527831985771200240439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26538037109314361600320585 19903527831985771200240439)
      ·
        refine ⟨29855291747978656800360659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19903527831985771200240439 29855291747978656800360659)
        ·
          refine ⟨44782937621967985200540989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29855291747978656800360659 44782937621967985200540989)
          ·
            refine ⟨16793601608237994450202871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44782937621967985200540989 16793601608237994450202871)
            ·
              refine ⟨25190402412356991675304307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16793601608237994450202871 25190402412356991675304307)
              ·
                refine ⟨37785603618535487512956461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25190402412356991675304307 37785603618535487512956461)
                ·
                  refine ⟨14169601356950807817358673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37785603618535487512956461 14169601356950807817358673)
                  ·
                    refine ⟨10627201017713105863019005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14169601356950807817358673 10627201017713105863019005)
                    ·
                      refine ⟨3985200381642414698632127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10627201017713105863019005 3985200381642414698632127)
                      ·
                        rfl

theorem cell23_7761150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_7761150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761150 prefixEnd_7761150 := by exact prefixLift 7761150
  have htrace : WordTrace (prefixWord ++ tailWord_7761150) baseStart_7761150 baseEnd_7761150 := by
    simpa [prefixWord, tailWord_7761150, baseEnd_7761150] using wordTrace_append hprefix tailTrace_7761150
  have hstable : (prefixWord ++ tailWord_7761150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761150).length < 2 ^ (prefixWord ++ tailWord_7761150).sum := by decide
  have hdescent : baseEnd_7761150 < baseStart_7761150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761163 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 3]
def baseStart_7761163 : Nat := 118140960795 + 7761163 * 2 ^ 59
def prefixEnd_7761163 : Nat := 4983230072969 + 3 ^ 40 * 7761163 * 2
def baseEnd_7761163 : Nat := 3985207056890923147769567

theorem tailTrace_7761163 : CollatzResearch.WordTrace tailWord_7761163 prefixEnd_7761163 3985207056890923147769567 := by
  unfold tailWord_7761163
  simp only [CollatzResearch.WordTrace]
  refine ⟨283072869981639426956976143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188715246654426284637984095 283072869981639426956976143)
  ·
    refine ⟨424609304972459140435464215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283072869981639426956976143 424609304972459140435464215)
    ·
      refine ⟨636913957458688710653196323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424609304972459140435464215 636913957458688710653196323)
      ·
        refine ⟨955370936188033065979794485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636913957458688710653196323 955370936188033065979794485)
        ·
          refine ⟨89566025267628099935605733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 955370936188033065979794485 89566025267628099935605733)
          ·
            refine ⟨16793629737680268737926075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89566025267628099935605733 16793629737680268737926075)
            ·
              refine ⟨25190444606520403106889113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16793629737680268737926075 25190444606520403106889113)
              ·
                refine ⟨18892833454890302330166835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25190444606520403106889113 18892833454890302330166835)
                ·
                  refine ⟨28339250182335453495250253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18892833454890302330166835 28339250182335453495250253)
                  ·
                    refine ⟨10627218818375795060718845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28339250182335453495250253 10627218818375795060718845)
                    ·
                      refine ⟨3985207056890923147769567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10627218818375795060718845 3985207056890923147769567)
                      ·
                        rfl

theorem cell23_7761163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 3].length) (baseStart_7761163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761163 prefixEnd_7761163 := by exact prefixLift 7761163
  have htrace : WordTrace (prefixWord ++ tailWord_7761163) baseStart_7761163 baseEnd_7761163 := by
    simpa [prefixWord, tailWord_7761163, baseEnd_7761163] using wordTrace_append hprefix tailTrace_7761163
  have hstable : (prefixWord ++ tailWord_7761163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761163).length < 2 ^ (prefixWord ++ tailWord_7761163).sum := by decide
  have hdescent : baseEnd_7761163 < baseStart_7761163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761170 : List Nat := [3, 2, 4, 2, 2, 10]
def baseStart_7761170 : Nat := 118140960795 + 7761170 * 2 ^ 59
def prefixEnd_7761170 : Nat := 4983230072969 + 3 ^ 40 * 7761170 * 2
def baseEnd_7761170 : Nat := 16400043832327179507745

theorem tailTrace_7761170 : CollatzResearch.WordTrace tailWord_7761170 prefixEnd_7761170 16400043832327179507745 := by
  unfold tailWord_7761170
  simp only [CollatzResearch.WordTrace]
  refine ⟨70768281323153516788120241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188715416861742711434987309 70768281323153516788120241)
  ·
    refine ⟨53076210992365137591090181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70768281323153516788120241 53076210992365137591090181)
    ·
      refine ⟨9951789561068463298329409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53076210992365137591090181 9951789561068463298329409)
      ·
        refine ⟨7463842170801347473747057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9951789561068463298329409 7463842170801347473747057)
        ·
          refine ⟨5597881628101010605310293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7463842170801347473747057 5597881628101010605310293)
          ·
            refine ⟨16400043832327179507745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5597881628101010605310293 16400043832327179507745)
            ·
              rfl

theorem cell23_7761170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 10].length) (baseStart_7761170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761170 prefixEnd_7761170 := by exact prefixLift 7761170
  have htrace : WordTrace (prefixWord ++ tailWord_7761170) baseStart_7761170 baseEnd_7761170 := by
    simpa [prefixWord, tailWord_7761170, baseEnd_7761170] using wordTrace_append hprefix tailTrace_7761170
  have hstable : (prefixWord ++ tailWord_7761170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761170).length < 2 ^ (prefixWord ++ tailWord_7761170).sum := by decide
  have hdescent : baseEnd_7761170 < baseStart_7761170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761180 : List Nat := [2, 2, 3, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_7761180 : Nat := 118140960795 + 7761180 * 2 ^ 59
def prefixEnd_7761180 : Nat := 4983230072969 + 3 ^ 40 * 7761180 * 2
def baseEnd_7761180 : Nat := 3985215786062049581256989

theorem tailTrace_7761180 : CollatzResearch.WordTrace tailWord_7761180 prefixEnd_7761180 3985215786062049581256989 := by
  unfold tailWord_7761180
  simp only [CollatzResearch.WordTrace]
  refine ⟨141536745011288919430172497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188715660015051892573563329 141536745011288919430172497)
  ·
    refine ⟨106152558758466689572629373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141536745011288919430172497 106152558758466689572629373)
    ·
      refine ⟨39807209534425008589736015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106152558758466689572629373 39807209534425008589736015)
      ·
        refine ⟨59710814301637512884604023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39807209534425008589736015 59710814301637512884604023)
        ·
          refine ⟨89566221452456269326906035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59710814301637512884604023 89566221452456269326906035)
          ·
            refine ⟨134349332178684403990359053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89566221452456269326906035 134349332178684403990359053)
            ·
              refine ⟨50380999567006651496384645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134349332178684403990359053 50380999567006651496384645)
              ·
                refine ⟨9446437418813747155572121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50380999567006651496384645 9446437418813747155572121)
                ·
                  refine ⟨7084828064110310366679091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9446437418813747155572121 7084828064110310366679091)
                  ·
                    refine ⟨10627242096165465550018637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7084828064110310366679091 10627242096165465550018637)
                    ·
                      refine ⟨3985215786062049581256989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10627242096165465550018637 3985215786062049581256989)
                      ·
                        rfl

theorem cell23_7761180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_7761180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761180 prefixEnd_7761180 := by exact prefixLift 7761180
  have htrace : WordTrace (prefixWord ++ tailWord_7761180) baseStart_7761180 baseEnd_7761180 := by
    simpa [prefixWord, tailWord_7761180, baseEnd_7761180] using wordTrace_append hprefix tailTrace_7761180
  have hstable : (prefixWord ++ tailWord_7761180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761180).length < 2 ^ (prefixWord ++ tailWord_7761180).sum := by decide
  have hdescent : baseEnd_7761180 < baseStart_7761180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761181 : List Nat := [1, 4, 2, 3, 1, 1, 4, 2, 1, 2, 2]
def baseStart_7761181 : Nat := 118140960795 + 7761181 * 2 ^ 59
def prefixEnd_7761181 : Nat := 4983230072969 + 3 ^ 40 * 7761181 * 2
def baseEnd_7761181 : Nat := 3985216299542704077344485

theorem tailTrace_7761181 : CollatzResearch.WordTrace tailWord_7761181 prefixEnd_7761181 3985216299542704077344485 := by
  unfold tailWord_7761181
  simp only [CollatzResearch.WordTrace]
  refine ⟨283073526495574216031131397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188715684330382810687420931 283073526495574216031131397)
  ·
    refine ⟨53076286217920165505837137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283073526495574216031131397 53076286217920165505837137)
    ·
      refine ⟨39807214663440124129377853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53076286217920165505837137 39807214663440124129377853)
      ·
        refine ⟨14927705498790046548516695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39807214663440124129377853 14927705498790046548516695)
        ·
          refine ⟨22391558248185069822775043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14927705498790046548516695 22391558248185069822775043)
          ·
            refine ⟨33587337372277604734162565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22391558248185069822775043 33587337372277604734162565)
            ·
              refine ⟨6297625757302050887655481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33587337372277604734162565 6297625757302050887655481)
              ·
                refine ⟨4723219317976538165741611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6297625757302050887655481 4723219317976538165741611)
                ·
                  refine ⟨7084828976964807248612417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723219317976538165741611 7084828976964807248612417)
                  ·
                    refine ⟨5313621732723605436459313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7084828976964807248612417 5313621732723605436459313)
                    ·
                      refine ⟨3985216299542704077344485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5313621732723605436459313 3985216299542704077344485)
                      ·
                        rfl

theorem cell23_7761181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_7761181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761181 prefixEnd_7761181 := by exact prefixLift 7761181
  have htrace : WordTrace (prefixWord ++ tailWord_7761181) baseStart_7761181 baseEnd_7761181 := by
    simpa [prefixWord, tailWord_7761181, baseEnd_7761181] using wordTrace_append hprefix tailTrace_7761181
  have hstable : (prefixWord ++ tailWord_7761181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761181).length < 2 ^ (prefixWord ++ tailWord_7761181).sum := by decide
  have hdescent : baseEnd_7761181 < baseStart_7761181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761197 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_7761197 : Nat := 118140960795 + 7761197 * 2 ^ 59
def prefixEnd_7761197 : Nat := 4983230072969 + 3 ^ 40 * 7761197 * 2
def baseEnd_7761197 : Nat := 3985224515233176014744411

theorem tailTrace_7761197 : CollatzResearch.WordTrace tailWord_7761197 prefixEnd_7761197 3985224515233176014744411 := by
  unfold tailWord_7761197
  simp only [CollatzResearch.WordTrace]
  refine ⟨283074110063516250763713845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188716073375677500509142563 283074110063516250763713845)
  ·
    refine ⟨26538197818454648509098173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 283074110063516250763713845 26538197818454648509098173)
    ·
      refine ⟨9951824181920493190911815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26538197818454648509098173 9951824181920493190911815)
      ·
        refine ⟨14927736272880739786367723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9951824181920493190911815 14927736272880739786367723)
        ·
          refine ⟨22391604409321109679551585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14927736272880739786367723 22391604409321109679551585)
          ·
            refine ⟨16793703306990832259663689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22391604409321109679551585 16793703306990832259663689)
            ·
              refine ⟨12595277480243124194747767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16793703306990832259663689 12595277480243124194747767)
              ·
                refine ⟨18892916220364686292121651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12595277480243124194747767 18892916220364686292121651)
                ·
                  refine ⟨28339374330547029438182477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18892916220364686292121651 28339374330547029438182477)
                  ·
                    refine ⟨10627265373955136039318429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28339374330547029438182477 10627265373955136039318429)
                    ·
                      refine ⟨3985224515233176014744411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10627265373955136039318429 3985224515233176014744411)
                      ·
                        rfl

theorem cell23_7761197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_7761197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761197 prefixEnd_7761197 := by exact prefixLift 7761197
  have htrace : WordTrace (prefixWord ++ tailWord_7761197) baseStart_7761197 baseEnd_7761197 := by
    simpa [prefixWord, tailWord_7761197, baseEnd_7761197] using wordTrace_append hprefix tailTrace_7761197
  have hstable : (prefixWord ++ tailWord_7761197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761197).length < 2 ^ (prefixWord ++ tailWord_7761197).sum := by decide
  have hdescent : baseEnd_7761197 < baseStart_7761197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761216 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 4]
def baseStart_7761216 : Nat := 118140960795 + 7761216 * 2 ^ 59
def prefixEnd_7761216 : Nat := 4983230072969 + 3 ^ 40 * 7761216 * 2
def baseEnd_7761216 : Nat := 3985234271365611440406823

theorem tailTrace_7761216 : CollatzResearch.WordTrace tailWord_7761216 prefixEnd_7761216 3985234271365611440406823 := by
  unfold tailWord_7761216
  simp only [CollatzResearch.WordTrace]
  refine ⟨141537401525223708504327751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188716535366964944672437001 141537401525223708504327751)
  ·
    refine ⟨212306102287835562756491627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141537401525223708504327751 212306102287835562756491627)
    ·
      refine ⟨318459153431753344134737441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212306102287835562756491627 318459153431753344134737441)
      ·
        refine ⟨238844365073815008101053081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318459153431753344134737441 238844365073815008101053081)
        ·
          refine ⟨179133273805361256075789811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238844365073815008101053081 179133273805361256075789811)
          ·
            refine ⟨268699910708041884113684717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179133273805361256075789811 268699910708041884113684717)
            ·
              refine ⟨100762466515515706542631769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268699910708041884113684717 100762466515515706542631769)
              ·
                refine ⟨75571849886636779906973827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100762466515515706542631769 75571849886636779906973827)
                ·
                  refine ⟨113357774829955169860460741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75571849886636779906973827 113357774829955169860460741)
                  ·
                    refine ⟨21254582780616594348836389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113357774829955169860460741 21254582780616594348836389)
                    ·
                      refine ⟨3985234271365611440406823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21254582780616594348836389 3985234271365611440406823)
                      ·
                        rfl

theorem cell23_7761216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_7761216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761216 prefixEnd_7761216 := by exact prefixLift 7761216
  have htrace : WordTrace (prefixWord ++ tailWord_7761216) baseStart_7761216 baseEnd_7761216 := by
    simpa [prefixWord, tailWord_7761216, baseEnd_7761216] using wordTrace_append hprefix tailTrace_7761216
  have hstable : (prefixWord ++ tailWord_7761216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761216).length < 2 ^ (prefixWord ++ tailWord_7761216).sum := by decide
  have hdescent : baseEnd_7761216 < baseStart_7761216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761237 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 4, 2, 2]
def baseStart_7761237 : Nat := 118140960795 + 7761237 * 2 ^ 59
def prefixEnd_7761237 : Nat := 4983230072969 + 3 ^ 40 * 7761237 * 2
def baseEnd_7761237 : Nat := 3985245054459355858244227

theorem tailTrace_7761237 : CollatzResearch.WordTrace tailWord_7761237 prefixEnd_7761237 3985245054459355858244227 := by
  unfold tailWord_7761237
  simp only [CollatzResearch.WordTrace]
  refine ⟨283075568983371337595169965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188717045988914225063446643 283075568983371337595169965)
  ·
    refine ⟨106153338368764251598188737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283075568983371337595169965 106153338368764251598188737)
    ·
      refine ⟨79615003776573188698641553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106153338368764251598188737 79615003776573188698641553)
      ·
        refine ⟨59711252832429891523981165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79615003776573188698641553 59711252832429891523981165)
        ·
          refine ⟨22391719812161209321492937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59711252832429891523981165 22391719812161209321492937)
          ·
            refine ⟨16793789859120906991119703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22391719812161209321492937 16793789859120906991119703)
            ·
              refine ⟨25190684788681360486679555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16793789859120906991119703 25190684788681360486679555)
              ·
                refine ⟨37786027183022040730019333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25190684788681360486679555 37786027183022040730019333)
                ·
                  refine ⟨7084880096816632636878625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37786027183022040730019333 7084880096816632636878625)
                  ·
                    refine ⟨5313660072612474477658969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7084880096816632636878625 5313660072612474477658969)
                    ·
                      refine ⟨3985245054459355858244227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5313660072612474477658969 3985245054459355858244227)
                      ·
                        rfl

theorem cell23_7761237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_7761237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761237 prefixEnd_7761237 := by exact prefixLift 7761237
  have htrace : WordTrace (prefixWord ++ tailWord_7761237) baseStart_7761237 baseEnd_7761237 := by
    simpa [prefixWord, tailWord_7761237, baseEnd_7761237] using wordTrace_append hprefix tailTrace_7761237
  have hstable : (prefixWord ++ tailWord_7761237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761237).length < 2 ^ (prefixWord ++ tailWord_7761237).sum := by decide
  have hdescent : baseEnd_7761237 < baseStart_7761237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761253 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 2, 3, 3]
def baseStart_7761253 : Nat := 118140960795 + 7761253 * 2 ^ 59
def prefixEnd_7761253 : Nat := 4983230072969 + 3 ^ 40 * 7761253 * 2
def baseEnd_7761253 : Nat := 3985253270149827795644153

theorem tailTrace_7761253 : CollatzResearch.WordTrace tailWord_7761253 prefixEnd_7761253 3985253270149827795644153 := by
  unfold tailWord_7761253
  simp only [CollatzResearch.WordTrace]
  refine ⟨283076152551313372327752413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188717435034208914885168275 283076152551313372327752413)
  ·
    refine ⟨106153557206742514622907155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283076152551313372327752413 106153557206742514622907155)
    ·
      refine ⟨159230335810113771934360733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106153557206742514622907155 159230335810113771934360733)
      ·
        refine ⟨59711375928792664475385275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159230335810113771934360733 59711375928792664475385275)
        ·
          refine ⟨89567063893188996713077913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59711375928792664475385275 89567063893188996713077913)
          ·
            refine ⟨67175297919891747534808435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89567063893188996713077913 67175297919891747534808435)
            ·
              refine ⟨100762946879837621302212653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67175297919891747534808435 100762946879837621302212653)
              ·
                refine ⟨37786105079939107988329745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100762946879837621302212653 37786105079939107988329745)
                ·
                  refine ⟨28339578809954330991247309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37786105079939107988329745 28339578809954330991247309)
                  ·
                    refine ⟨10627342053732874121717741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28339578809954330991247309 10627342053732874121717741)
                    ·
                      refine ⟨3985253270149827795644153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10627342053732874121717741 3985253270149827795644153)
                      ·
                        rfl

theorem cell23_7761253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_7761253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761253 prefixEnd_7761253 := by exact prefixLift 7761253
  have htrace : WordTrace (prefixWord ++ tailWord_7761253) baseStart_7761253 baseEnd_7761253 := by
    simpa [prefixWord, tailWord_7761253, baseEnd_7761253] using wordTrace_append hprefix tailTrace_7761253
  have hstable : (prefixWord ++ tailWord_7761253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761253).length < 2 ^ (prefixWord ++ tailWord_7761253).sum := by decide
  have hdescent : baseEnd_7761253 < baseStart_7761253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761294 : List Nat := [4, 1, 1, 4, 2, 1, 3, 2, 5]
def baseStart_7761294 : Nat := 118140960795 + 7761294 * 2 ^ 59
def prefixEnd_7761294 : Nat := 4983230072969 + 3 ^ 40 * 7761294 * 2
def baseEnd_7761294 : Nat := 442808258095184681692385

theorem tailTrace_7761294 : CollatzResearch.WordTrace tailWord_7761294 prefixEnd_7761294 442808258095184681692385 := by
  unfold tailWord_7761294
  simp only [CollatzResearch.WordTrace]
  refine ⟨35384705993020604541249367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188718431962776557553329957 35384705993020604541249367)
  ·
    refine ⟨53077058989530906811874051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35384705993020604541249367 53077058989530906811874051)
    ·
      refine ⟨79615588484296360217811077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53077058989530906811874051 79615588484296360217811077)
      ·
        refine ⟨14927922840805567540839577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79615588484296360217811077 14927922840805567540839577)
        ·
          refine ⟨11195942130604175655629683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14927922840805567540839577 11195942130604175655629683)
          ·
            refine ⟨16793913195906263483444525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11195942130604175655629683 16793913195906263483444525)
            ·
              refine ⟨6297717448464848806291697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16793913195906263483444525 6297717448464848806291697)
              ·
                refine ⟨4723288086348636604718773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6297717448464848806291697 4723288086348636604718773)
                ·
                  refine ⟨442808258095184681692385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4723288086348636604718773 442808258095184681692385)
                  ·
                    rfl

theorem cell23_7761294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_7761294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761294 prefixEnd_7761294 := by exact prefixLift 7761294
  have htrace : WordTrace (prefixWord ++ tailWord_7761294) baseStart_7761294 baseEnd_7761294 := by
    simpa [prefixWord, tailWord_7761294, baseEnd_7761294] using wordTrace_append hprefix tailTrace_7761294
  have hstable : (prefixWord ++ tailWord_7761294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761294).length < 2 ^ (prefixWord ++ tailWord_7761294).sum := by decide
  have hdescent : baseEnd_7761294 < baseStart_7761294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761300 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_7761300 : Nat := 118140960795 + 7761300 * 2 ^ 59
def prefixEnd_7761300 : Nat := 4983230072969 + 3 ^ 40 * 7761300 * 2
def baseEnd_7761300 : Nat := 3985277403740589111756437

theorem tailTrace_7761300 : CollatzResearch.WordTrace tailWord_7761300 prefixEnd_7761300 3985277403740589111756437 := by
  unfold tailWord_7761300
  simp only [CollatzResearch.WordTrace]
  refine ⟨141538933391071549677356677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188718577854762066236475569 141538933391071549677356677)
  ·
    refine ⟨26538550010825915564504377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141538933391071549677356677 26538550010825915564504377)
    ·
      refine ⟨19903912508119436673378283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26538550010825915564504377 19903912508119436673378283)
      ·
        refine ⟨29855868762179155010067425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19903912508119436673378283 29855868762179155010067425)
        ·
          refine ⟨22391901571634366257550569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29855868762179155010067425 22391901571634366257550569)
          ·
            refine ⟨16793926178725774693162927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22391901571634366257550569 16793926178725774693162927)
            ·
              refine ⟨25190889268088662039744391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16793926178725774693162927 25190889268088662039744391)
              ·
                refine ⟨37786333902132993059616587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25190889268088662039744391 37786333902132993059616587)
                ·
                  refine ⟨56679500853199489589424881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37786333902132993059616587 56679500853199489589424881)
                  ·
                    refine ⟨42509625639899617192068661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56679500853199489589424881 42509625639899617192068661)
                    ·
                      refine ⟨3985277403740589111756437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42509625639899617192068661 3985277403740589111756437)
                      ·
                        rfl

theorem cell23_7761300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_7761300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761300 prefixEnd_7761300 := by exact prefixLift 7761300
  have htrace : WordTrace (prefixWord ++ tailWord_7761300) baseStart_7761300 baseEnd_7761300 := by
    simpa [prefixWord, tailWord_7761300, baseEnd_7761300] using wordTrace_append hprefix tailTrace_7761300
  have hstable : (prefixWord ++ tailWord_7761300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761300).length < 2 ^ (prefixWord ++ tailWord_7761300).sum := by decide
  have hdescent : baseEnd_7761300 < baseStart_7761300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761354 : List Nat := [3, 1, 2, 1, 2, 3, 4, 2, 1, 4]
def baseStart_7761354 : Nat := 118140960795 + 7761354 * 2 ^ 59
def prefixEnd_7761354 : Nat := 4983230072969 + 3 ^ 40 * 7761354 * 2
def baseEnd_7761354 : Nat := 1328435043898643966827063

theorem tailTrace_7761354 : CollatzResearch.WordTrace tailWord_7761354 prefixEnd_7761354 1328435043898643966827063 := by
  unfold tailWord_7761354
  simp only [CollatzResearch.WordTrace]
  refine ⟨70769959080986866644294779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188719890882631644384786077 70769959080986866644294779)
  ·
    refine ⟨106154938621480299966442169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70769959080986866644294779 106154938621480299966442169)
    ·
      refine ⟨79616203966110224974831627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106154938621480299966442169 79616203966110224974831627)
      ·
        refine ⟨119424305949165337462247441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79616203966110224974831627 119424305949165337462247441)
        ·
          refine ⟨89568229461874003096685581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119424305949165337462247441 89568229461874003096685581)
          ·
            refine ⟨33588086048202751161257093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89568229461874003096685581 33588086048202751161257093)
            ·
              refine ⟨6297766134038015842735705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33588086048202751161257093 6297766134038015842735705)
              ·
                refine ⟨4723324600528511882051779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6297766134038015842735705 4723324600528511882051779)
                ·
                  refine ⟨7084986900792767823077669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723324600528511882051779 7084986900792767823077669)
                  ·
                    refine ⟨1328435043898643966827063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7084986900792767823077669 1328435043898643966827063)
                    ·
                      rfl

theorem cell23_7761354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_7761354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761354 prefixEnd_7761354 := by exact prefixLift 7761354
  have htrace : WordTrace (prefixWord ++ tailWord_7761354) baseStart_7761354 baseEnd_7761354 := by
    simpa [prefixWord, tailWord_7761354, baseEnd_7761354] using wordTrace_append hprefix tailTrace_7761354
  have hstable : (prefixWord ++ tailWord_7761354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761354).length < 2 ^ (prefixWord ++ tailWord_7761354).sum := by decide
  have hdescent : baseEnd_7761354 < baseStart_7761354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761377 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 3, 1, 3]
def baseStart_7761377 : Nat := 118140960795 + 7761377 * 2 ^ 59
def prefixEnd_7761377 : Nat := 4983230072969 + 3 ^ 40 * 7761377 * 2
def baseEnd_7761377 : Nat := 3985316941750985310493583

theorem tailTrace_7761377 : CollatzResearch.WordTrace tailWord_7761377 prefixEnd_7761377 3985316941750985310493583 := by
  unfold tailWord_7761377
  simp only [CollatzResearch.WordTrace]
  refine ⟨283080675202864141505266385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188720450135242761003510923 283080675202864141505266385)
  ·
    refine ⟨212310506402148106128949789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283080675202864141505266385 212310506402148106128949789)
    ·
      refine ⟨79616439900805539798356171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212310506402148106128949789 79616439900805539798356171)
      ·
        refine ⟨119424659851208309697534257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79616439900805539798356171 119424659851208309697534257)
        ·
          refine ⟨89568494888406232273150693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119424659851208309697534257 89568494888406232273150693)
          ·
            refine ⟨16794092791576168551215755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89568494888406232273150693 16794092791576168551215755)
            ·
              refine ⟨25191139187364252826823633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16794092791576168551215755 25191139187364252826823633)
              ·
                refine ⟨18893354390523189620117725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25191139187364252826823633 18893354390523189620117725)
                ·
                  refine ⟨7085007896446196107544147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18893354390523189620117725 7085007896446196107544147)
                  ·
                    refine ⟨10627511844669294161316221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7085007896446196107544147 10627511844669294161316221)
                    ·
                      refine ⟨3985316941750985310493583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10627511844669294161316221 3985316941750985310493583)
                      ·
                        rfl

theorem cell23_7761377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_7761377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761377 prefixEnd_7761377 := by exact prefixLift 7761377
  have htrace : WordTrace (prefixWord ++ tailWord_7761377) baseStart_7761377 baseEnd_7761377 := by
    simpa [prefixWord, tailWord_7761377, baseEnd_7761377] using wordTrace_append hprefix tailTrace_7761377
  have hstable : (prefixWord ++ tailWord_7761377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761377).length < 2 ^ (prefixWord ++ tailWord_7761377).sum := by decide
  have hdescent : baseEnd_7761377 < baseStart_7761377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761413 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 1, 1, 6]
def baseStart_7761413 : Nat := 118140960795 + 7761413 * 2 ^ 59
def prefixEnd_7761413 : Nat := 4983230072969 + 3 ^ 40 * 7761413 * 2
def baseEnd_7761413 : Nat := 3985335427054547169643417

theorem tailTrace_7761413 : CollatzResearch.WordTrace tailWord_7761413 prefixEnd_7761413 3985335427054547169643417 := by
  unfold tailWord_7761413
  simp only [CollatzResearch.WordTrace]
  refine ⟨283081988230733719653576893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188721325487155813102384595 283081988230733719653576893)
  ·
    refine ⟨106155745586525144870091335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283081988230733719653576893 106155745586525144870091335)
    ·
      refine ⟨159233618379787717305137003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106155745586525144870091335 159233618379787717305137003)
      ·
        refine ⟨238850427569681575957705505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159233618379787717305137003 238850427569681575957705505)
        ·
          refine ⟨179137820677261181968279129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238850427569681575957705505 179137820677261181968279129)
          ·
            refine ⟨134353365507945886476209347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179137820677261181968279129 134353365507945886476209347)
            ·
              refine ⟨201530048261918829714314021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134353365507945886476209347 201530048261918829714314021)
              ·
                refine ⟨37786884049109780571433879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201530048261918829714314021 37786884049109780571433879)
                ·
                  refine ⟨56680326073664670857150819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37786884049109780571433879 56680326073664670857150819)
                  ·
                    refine ⟨85020489110497006285726229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56680326073664670857150819 85020489110497006285726229)
                    ·
                      refine ⟨3985335427054547169643417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85020489110497006285726229 3985335427054547169643417)
                      ·
                        rfl

theorem cell23_7761413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_7761413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761413 prefixEnd_7761413 := by exact prefixLift 7761413
  have htrace : WordTrace (prefixWord ++ tailWord_7761413) baseStart_7761413 baseEnd_7761413 := by
    simpa [prefixWord, tailWord_7761413, baseEnd_7761413] using wordTrace_append hprefix tailTrace_7761413
  have hstable : (prefixWord ++ tailWord_7761413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761413).length < 2 ^ (prefixWord ++ tailWord_7761413).sum := by decide
  have hdescent : baseEnd_7761413 < baseStart_7761413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761440 : List Nat := [2, 1, 1, 6, 1, 2, 1, 9]
def baseStart_7761440 : Nat := 118140960795 + 7761440 * 2 ^ 59
def prefixEnd_7761440 : Nat := 4983230072969 + 3 ^ 40 * 7761440 * 2
def baseEnd_7761440 : Nat := 147605529297489576444659

theorem tailTrace_7761440 : CollatzResearch.WordTrace tailWord_7761440 prefixEnd_7761440 147605529297489576444659 := by
  unfold tailWord_7761440
  simp only [CollatzResearch.WordTrace]
  refine ⟨141541486500817951632404887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188721982001090602176539849 141541486500817951632404887)
  ·
    refine ⟨212312229751226927448607331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141541486500817951632404887 212312229751226927448607331)
    ·
      refine ⟨318468344626840391172910997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212312229751226927448607331 318468344626840391172910997)
      ·
        refine ⟨14928203654383143336230203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 318468344626840391172910997 14928203654383143336230203)
        ·
          refine ⟨22392305481574715004345305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14928203654383143336230203 22392305481574715004345305)
          ·
            refine ⟨16794229111181036253258979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22392305481574715004345305 16794229111181036253258979)
            ·
              refine ⟨25191343666771554379888469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16794229111181036253258979 25191343666771554379888469)
              ·
                refine ⟨147605529297489576444659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25191343666771554379888469 147605529297489576444659)
                ·
                  rfl

theorem cell23_7761440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 9].length) (baseStart_7761440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761440 prefixEnd_7761440 := by exact prefixLift 7761440
  have htrace : WordTrace (prefixWord ++ tailWord_7761440) baseStart_7761440 baseEnd_7761440 := by
    simpa [prefixWord, tailWord_7761440, baseEnd_7761440] using wordTrace_append hprefix tailTrace_7761440
  have hstable : (prefixWord ++ tailWord_7761440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761440).length < 2 ^ (prefixWord ++ tailWord_7761440).sum := by decide
  have hdescent : baseEnd_7761440 < baseStart_7761440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761454 : List Nat := [4, 1, 3, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_7761454 : Nat := 118140960795 + 7761454 * 2 ^ 59
def prefixEnd_7761454 : Nat := 4983230072969 + 3 ^ 40 * 7761454 * 2
def baseEnd_7761454 : Nat := 3985356479761381509230729

theorem tailTrace_7761454 : CollatzResearch.WordTrace tailWord_7761454 prefixEnd_7761454 3985356479761381509230729 := by
  unfold tailWord_7761454
  simp only [CollatzResearch.WordTrace]
  refine ⟨35385435452948147956977427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188722322415723455770546277 35385435452948147956977427)
  ·
    refine ⟨53078153179422221935466141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35385435452948147956977427 53078153179422221935466141)
    ·
      refine ⟨19904307442283333225799803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53078153179422221935466141 19904307442283333225799803)
      ·
        refine ⟨29856461163424999838699705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19904307442283333225799803 29856461163424999838699705)
        ·
          refine ⟨22392345872568749879024779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29856461163424999838699705 22392345872568749879024779)
          ·
            refine ⟨33588518808853124818537169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22392345872568749879024779 33588518808853124818537169)
            ·
              refine ⟨25191389106639843613902877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33588518808853124818537169 25191389106639843613902877)
              ·
                refine ⟨9446770914989941355213579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25191389106639843613902877 9446770914989941355213579)
                ·
                  refine ⟨14170156372484912032820369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9446770914989941355213579 14170156372484912032820369)
                  ·
                    refine ⟨10627617279363684024615277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14170156372484912032820369 10627617279363684024615277)
                    ·
                      refine ⟨3985356479761381509230729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10627617279363684024615277 3985356479761381509230729)
                      ·
                        rfl

theorem cell23_7761454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_7761454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761454 prefixEnd_7761454 := by exact prefixLift 7761454
  have htrace : WordTrace (prefixWord ++ tailWord_7761454) baseStart_7761454 baseEnd_7761454 := by
    simpa [prefixWord, tailWord_7761454, baseEnd_7761454] using wordTrace_append hprefix tailTrace_7761454
  have hstable : (prefixWord ++ tailWord_7761454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761454).length < 2 ^ (prefixWord ++ tailWord_7761454).sum := by decide
  have hdescent : baseEnd_7761454 < baseStart_7761454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761468 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 3, 2, 2]
def baseStart_7761468 : Nat := 118140960795 + 7761468 * 2 ^ 59
def prefixEnd_7761468 : Nat := 4983230072969 + 3 ^ 40 * 7761468 * 2
def baseEnd_7761468 : Nat := 3985363668490544454455665

theorem tailTrace_7761468 : CollatzResearch.WordTrace tailWord_7761468 prefixEnd_7761468 3985363668490544454455665 := by
  unfold tailWord_7761468
  simp only [CollatzResearch.WordTrace]
  refine ⟨141541997122767232023414529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188722662830356309364552705 141541997122767232023414529)
  ·
    refine ⟨106156497842075424017560897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141541997122767232023414529 106156497842075424017560897)
    ·
      refine ⟨79617373381556568013170673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106156497842075424017560897 79617373381556568013170673)
      ·
        refine ⟨59713030036167426009878005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79617373381556568013170673 59713030036167426009878005)
        ·
          refine ⟨5598096565890696188426063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59713030036167426009878005 5598096565890696188426063)
          ·
            refine ⟨8397144848836044282639095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5598096565890696188426063 8397144848836044282639095)
            ·
              refine ⟨12595717273254066423958643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8397144848836044282639095 12595717273254066423958643)
              ·
                refine ⟨18893575909881099635937965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12595717273254066423958643 18893575909881099635937965)
                ·
                  refine ⟨7085090966205412363476737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18893575909881099635937965 7085090966205412363476737)
                  ·
                    refine ⟨5313818224654059272607553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7085090966205412363476737 5313818224654059272607553)
                    ·
                      refine ⟨3985363668490544454455665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5313818224654059272607553 3985363668490544454455665)
                      ·
                        rfl

theorem cell23_7761468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_7761468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761468 prefixEnd_7761468 := by exact prefixLift 7761468
  have htrace : WordTrace (prefixWord ++ tailWord_7761468) baseStart_7761468 baseEnd_7761468 := by
    simpa [prefixWord, tailWord_7761468, baseEnd_7761468] using wordTrace_append hprefix tailTrace_7761468
  have hstable : (prefixWord ++ tailWord_7761468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761468).length < 2 ^ (prefixWord ++ tailWord_7761468).sum := by decide
  have hdescent : baseEnd_7761468 < baseStart_7761468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761477 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 3, 3, 2]
def baseStart_7761477 : Nat := 118140960795 + 7761477 * 2 ^ 59
def prefixEnd_7761477 : Nat := 4983230072969 + 3 ^ 40 * 7761477 * 2
def baseEnd_7761477 : Nat := 3985368289816434919243123

theorem tailTrace_7761477 : CollatzResearch.WordTrace tailWord_7761477 prefixEnd_7761477 3985368289816434919243123 := by
  unfold tailWord_7761477
  simp only [CollatzResearch.WordTrace]
  refine ⟨283084322502501858583906685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188722881668334572389271123 283084322502501858583906685)
  ·
    refine ⟨106156620938438196968965007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283084322502501858583906685 106156620938438196968965007)
    ·
      refine ⟨159234931407657295453447511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106156620938438196968965007 159234931407657295453447511)
      ·
        refine ⟨238852397111485943180171267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159234931407657295453447511 238852397111485943180171267)
        ·
          refine ⟨358278595667228914770256901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238852397111485943180171267 358278595667228914770256901)
          ·
            refine ⟨67177236687605421519423169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 358278595667228914770256901 67177236687605421519423169)
            ·
              refine ⟨50382927515704066139567377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67177236687605421519423169 50382927515704066139567377)
              ·
                refine ⟨37787195636778049604675533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50382927515704066139567377 37787195636778049604675533)
                ·
                  refine ⟨14170198363791768601753325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37787195636778049604675533 14170198363791768601753325)
                  ·
                    refine ⟨5313824386421913225657497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14170198363791768601753325 5313824386421913225657497)
                    ·
                      refine ⟨3985368289816434919243123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5313824386421913225657497 3985368289816434919243123)
                      ·
                        rfl

theorem cell23_7761477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 3, 2].length) (baseStart_7761477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761477 prefixEnd_7761477 := by exact prefixLift 7761477
  have htrace : WordTrace (prefixWord ++ tailWord_7761477) baseStart_7761477 baseEnd_7761477 := by
    simpa [prefixWord, tailWord_7761477, baseEnd_7761477] using wordTrace_append hprefix tailTrace_7761477
  have hstable : (prefixWord ++ tailWord_7761477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761477).length < 2 ^ (prefixWord ++ tailWord_7761477).sum := by decide
  have hdescent : baseEnd_7761477 < baseStart_7761477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761483 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 1, 8]
def baseStart_7761483 : Nat := 118140960795 + 7761483 * 2 ^ 59
def prefixEnd_7761483 : Nat := 4983230072969 + 3 ^ 40 * 7761483 * 2
def baseEnd_7761483 : Nat := 1328457123566787298589365

theorem tailTrace_7761483 : CollatzResearch.WordTrace tailWord_7761483 prefixEnd_7761483 1328457123566787298589365 := by
  unfold tailWord_7761483
  simp only [CollatzResearch.WordTrace]
  refine ⟨283084541340480121608625103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188723027560320081072416735 283084541340480121608625103)
  ·
    refine ⟨424626812010720182412937655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283084541340480121608625103 424626812010720182412937655)
    ·
      refine ⟨636940218016080273619406483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424626812010720182412937655 636940218016080273619406483)
      ·
        refine ⟨955410327024120410429109725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636940218016080273619406483 955410327024120410429109725)
        ·
          refine ⟨358278872634045153910916147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 955410327024120410429109725 358278872634045153910916147)
          ·
            refine ⟨537418308951067730866374221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358278872634045153910916147 537418308951067730866374221)
            ·
              refine ⟨201531865856650399074890333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 537418308951067730866374221 201531865856650399074890333)
              ·
                refine ⟨75574449696243899653083875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201531865856650399074890333 75574449696243899653083875)
                ·
                  refine ⟨113361674544365849479625813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75574449696243899653083875 113361674544365849479625813)
                  ·
                    refine ⟨1328457123566787298589365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113361674544365849479625813 1328457123566787298589365)
                    ·
                      rfl

theorem cell23_7761483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 8].length) (baseStart_7761483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761483 prefixEnd_7761483 := by exact prefixLift 7761483
  have htrace : WordTrace (prefixWord ++ tailWord_7761483) baseStart_7761483 baseEnd_7761483 := by
    simpa [prefixWord, tailWord_7761483, baseEnd_7761483] using wordTrace_append hprefix tailTrace_7761483
  have hstable : (prefixWord ++ tailWord_7761483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761483).length < 2 ^ (prefixWord ++ tailWord_7761483).sum := by decide
  have hdescent : baseEnd_7761483 < baseStart_7761483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761484 : List Nat := [2, 2, 1, 3, 1, 4, 1, 3, 2, 1, 3]
def baseStart_7761484 : Nat := 118140960795 + 7761484 * 2 ^ 59
def prefixEnd_7761484 : Nat := 4983230072969 + 3 ^ 40 * 7761484 * 2
def baseEnd_7761484 : Nat := 3985371884181016391855591

theorem tailTrace_7761484 : CollatzResearch.WordTrace tailWord_7761484 prefixEnd_7761484 3985371884181016391855591 := by
  unfold tailWord_7761484
  simp only [CollatzResearch.WordTrace]
  refine ⟨141542288906738249389705753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188723051875650999186274337 141542288906738249389705753)
  ·
    refine ⟨106156716680053687042279315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141542288906738249389705753 106156716680053687042279315)
    ·
      refine ⟨159235075020080530563418973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106156716680053687042279315 159235075020080530563418973)
      ·
        refine ⟨59713153132530198961282115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159235075020080530563418973 59713153132530198961282115)
        ·
          refine ⟨89569729698795298441923173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59713153132530198961282115 89569729698795298441923173)
          ·
            refine ⟨16794324318524118457860595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89569729698795298441923173 16794324318524118457860595)
            ·
              refine ⟨25191486477786177686790893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16794324318524118457860595 25191486477786177686790893)
              ·
                refine ⟨9446807429169816632546585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25191486477786177686790893 9446807429169816632546585)
                ·
                  refine ⟨7085105571877362474409939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9446807429169816632546585 7085105571877362474409939)
                  ·
                    refine ⟨10627658357816043711614909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7085105571877362474409939 10627658357816043711614909)
                    ·
                      refine ⟨3985371884181016391855591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10627658357816043711614909 3985371884181016391855591)
                      ·
                        rfl

theorem cell23_7761484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_7761484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761484 prefixEnd_7761484 := by exact prefixLift 7761484
  have htrace : WordTrace (prefixWord ++ tailWord_7761484) baseStart_7761484 baseEnd_7761484 := by
    simpa [prefixWord, tailWord_7761484, baseEnd_7761484] using wordTrace_append hprefix tailTrace_7761484
  have hstable : (prefixWord ++ tailWord_7761484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761484).length < 2 ^ (prefixWord ++ tailWord_7761484).sum := by decide
  have hdescent : baseEnd_7761484 < baseStart_7761484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761501 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_7761501 : Nat := 118140960795 + 7761501 * 2 ^ 59
def prefixEnd_7761501 : Nat := 4983230072969 + 3 ^ 40 * 7761501 * 2
def baseEnd_7761501 : Nat := 3985380613352142825343013

theorem tailTrace_7761501 : CollatzResearch.WordTrace tailWord_7761501 prefixEnd_7761501 3985380613352142825343013 := by
  unfold tailWord_7761501
  simp only [CollatzResearch.WordTrace]
  refine ⟨283085197854414910682780357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188723465236276607121853571 283085197854414910682780357)
  ·
    refine ⟨53078474597702795753021317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283085197854414910682780357 53078474597702795753021317)
    ·
      refine ⟨9952213987069274203691497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53078474597702795753021317 9952213987069274203691497)
      ·
        refine ⟨7464160490301955652768623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9952213987069274203691497 7464160490301955652768623)
        ·
          refine ⟨11196240735452933479152935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7464160490301955652768623 11196240735452933479152935)
          ·
            refine ⟨16794361103179400218729403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11196240735452933479152935 16794361103179400218729403)
            ·
              refine ⟨25191541654769100328094105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16794361103179400218729403 25191541654769100328094105)
              ·
                refine ⟨18893656241076825246070579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25191541654769100328094105 18893656241076825246070579)
                ·
                  refine ⟨28340484361615237869105869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18893656241076825246070579 28340484361615237869105869)
                  ·
                    refine ⟨10627681635605714200914701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28340484361615237869105869 10627681635605714200914701)
                    ·
                      refine ⟨3985380613352142825343013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10627681635605714200914701 3985380613352142825343013)
                      ·
                        rfl

theorem cell23_7761501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_7761501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761501 prefixEnd_7761501 := by exact prefixLift 7761501
  have htrace : WordTrace (prefixWord ++ tailWord_7761501) baseStart_7761501 baseEnd_7761501 := by
    simpa [prefixWord, tailWord_7761501, baseEnd_7761501] using wordTrace_append hprefix tailTrace_7761501
  have hstable : (prefixWord ++ tailWord_7761501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761501).length < 2 ^ (prefixWord ++ tailWord_7761501).sum := by decide
  have hdescent : baseEnd_7761501 < baseStart_7761501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761507 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 3, 4, 2]
def baseStart_7761507 : Nat := 118140960795 + 7761507 * 2 ^ 59
def prefixEnd_7761507 : Nat := 4983230072969 + 3 ^ 40 * 7761507 * 2
def baseEnd_7761507 : Nat := 3985383694236069801867985

theorem tailTrace_7761507 : CollatzResearch.WordTrace tailWord_7761507 prefixEnd_7761507 3985383694236069801867985 := by
  unfold tailWord_7761507
  simp only [CollatzResearch.WordTrace]
  refine ⟨283085416692393173707498775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188723611128262115804999183 283085416692393173707498775)
  ·
    refine ⟨424628125038589760561248163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283085416692393173707498775 424628125038589760561248163)
    ·
      refine ⟨636942187557884640841872245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424628125038589760561248163 636942187557884640841872245)
      ·
        refine ⟨59713330083551685078925523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 636942187557884640841872245 59713330083551685078925523)
        ·
          refine ⟨89569995125327527618388285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59713330083551685078925523 89569995125327527618388285)
          ·
            refine ⟨33588748171997822856895607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89569995125327527618388285 33588748171997822856895607)
            ·
              refine ⟨50383122257996734285343411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33588748171997822856895607 50383122257996734285343411)
              ·
                refine ⟨75574683386995101428015117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50383122257996734285343411 75574683386995101428015117)
                ·
                  refine ⟨28340506270123163035505669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75574683386995101428015117 28340506270123163035505669)
                  ·
                    refine ⟨5313844925648093069157313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28340506270123163035505669 5313844925648093069157313)
                    ·
                      refine ⟨3985383694236069801867985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5313844925648093069157313 3985383694236069801867985)
                      ·
                        rfl

theorem cell23_7761507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_7761507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761507 prefixEnd_7761507 := by exact prefixLift 7761507
  have htrace : WordTrace (prefixWord ++ tailWord_7761507) baseStart_7761507 baseEnd_7761507 := by
    simpa [prefixWord, tailWord_7761507, baseEnd_7761507] using wordTrace_append hprefix tailTrace_7761507
  have hstable : (prefixWord ++ tailWord_7761507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761507).length < 2 ^ (prefixWord ++ tailWord_7761507).sum := by decide
  have hdescent : baseEnd_7761507 < baseStart_7761507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761537 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_7761537 : Nat := 118140960795 + 7761537 * 2 ^ 59
def prefixEnd_7761537 : Nat := 4983230072969 + 3 ^ 40 * 7761537 * 2
def baseEnd_7761537 : Nat := 3985399098655704684492847

theorem tailTrace_7761537 : CollatzResearch.WordTrace tailWord_7761537 prefixEnd_7761537 3985399098655704684492847 := by
  unfold tailWord_7761537
  simp only [CollatzResearch.WordTrace]
  refine ⟨283086510882284488831090865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188724340588189659220727243 283086510882284488831090865)
  ·
    refine ⟨212314883161713366623318149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283086510882284488831090865 212314883161713366623318149)
    ·
      refine ⟨39809040592821256241872153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212314883161713366623318149 39809040592821256241872153)
      ·
        refine ⟨29856780444615942181404115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39809040592821256241872153 29856780444615942181404115)
        ·
          refine ⟨44785170666923913272106173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29856780444615942181404115 44785170666923913272106173)
          ·
            refine ⟨16794439000096467477039815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44785170666923913272106173 16794439000096467477039815)
            ·
              refine ⟨25191658500144701215559723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16794439000096467477039815 25191658500144701215559723)
              ·
                refine ⟨37787487750217051823339585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25191658500144701215559723 37787487750217051823339585)
                ·
                  refine ⟨28340615812662788867504689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37787487750217051823339585 28340615812662788867504689)
                  ·
                    refine ⟨21255461859497091650628517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28340615812662788867504689 21255461859497091650628517)
                    ·
                      refine ⟨3985399098655704684492847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21255461859497091650628517 3985399098655704684492847)
                      ·
                        rfl

theorem cell23_7761537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_7761537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761537 prefixEnd_7761537 := by exact prefixLift 7761537
  have htrace : WordTrace (prefixWord ++ tailWord_7761537) baseStart_7761537 baseEnd_7761537 := by
    simpa [prefixWord, tailWord_7761537, baseEnd_7761537] using wordTrace_append hprefix tailTrace_7761537
  have hstable : (prefixWord ++ tailWord_7761537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761537).length < 2 ^ (prefixWord ++ tailWord_7761537).sum := by decide
  have hdescent : baseEnd_7761537 < baseStart_7761537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761607 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 3, 4]
def baseStart_7761607 : Nat := 118140960795 + 7761607 * 2 ^ 59
def prefixEnd_7761607 : Nat := 4983230072969 + 3 ^ 40 * 7761607 * 2
def baseEnd_7761607 : Nat := 1328478347433839803539175

theorem tailTrace_7761607 : CollatzResearch.WordTrace tailWord_7761607 prefixEnd_7761607 1328478347433839803539175 := by
  unfold tailWord_7761607
  simp only [CollatzResearch.WordTrace]
  refine ⟨283089063992030890786139075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188726042661353927190759383 283089063992030890786139075)
  ·
    refine ⟨424633595988046336179208613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283089063992030890786139075 424633595988046336179208613)
    ·
      refine ⟨79618799247758688033601615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 424633595988046336179208613 79618799247758688033601615)
      ·
        refine ⟨119428198871638032050402423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79618799247758688033601615 119428198871638032050402423)
        ·
          refine ⟨179142298307457048075603635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119428198871638032050402423 179142298307457048075603635)
          ·
            refine ⟨268713447461185572113405453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179142298307457048075603635 268713447461185572113405453)
            ·
              refine ⟨100767542797944589542527045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268713447461185572113405453 100767542797944589542527045)
              ·
                refine ⟨18893914274614610539223821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100767542797944589542527045 18893914274614610539223821)
                ·
                  refine ⟨7085217852980478952208933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18893914274614610539223821 7085217852980478952208933)
                  ·
                    refine ⟨1328478347433839803539175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7085217852980478952208933 1328478347433839803539175)
                    ·
                      rfl

theorem cell23_7761607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_7761607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761607 prefixEnd_7761607 := by exact prefixLift 7761607
  have htrace : WordTrace (prefixWord ++ tailWord_7761607) baseStart_7761607 baseEnd_7761607 := by
    simpa [prefixWord, tailWord_7761607, baseEnd_7761607] using wordTrace_append hprefix tailTrace_7761607
  have hstable : (prefixWord ++ tailWord_7761607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761607).length < 2 ^ (prefixWord ++ tailWord_7761607).sum := by decide
  have hdescent : baseEnd_7761607 < baseStart_7761607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761617 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 1, 4, 3]
def baseStart_7761617 : Nat := 118140960795 + 7761617 * 2 ^ 59
def prefixEnd_7761617 : Nat := 4983230072969 + 3 ^ 40 * 7761617 * 2
def baseEnd_7761617 : Nat := 3985440177108064371492479

theorem tailTrace_7761617 : CollatzResearch.WordTrace tailWord_7761617 prefixEnd_7761617 3985440177108064371492479 := by
  unfold tailWord_7761617
  simp only [CollatzResearch.WordTrace]
  refine ⟨283089428721994662494003105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188726285814663108329335403 283089428721994662494003105)
  ·
    refine ⟨212317071541495996870502329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283089428721994662494003105 212317071541495996870502329)
    ·
      refine ⟨159237803656121997652876747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212317071541495996870502329 159237803656121997652876747)
      ·
        refine ⟨238856705484182996479315121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159237803656121997652876747 238856705484182996479315121)
        ·
          refine ⟨179142529113137247359486341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238856705484182996479315121 179142529113137247359486341)
          ·
            refine ⟨33589224208713233879903689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179142529113137247359486341 33589224208713233879903689)
            ·
              refine ⟨25191918156534925409927767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33589224208713233879903689 25191918156534925409927767)
              ·
                refine ⟨37787877234802388114891651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25191918156534925409927767 37787877234802388114891651)
                ·
                  refine ⟨56681815852203582172337477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37787877234802388114891651 56681815852203582172337477)
                  ·
                    refine ⟨10627840472288171657313277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56681815852203582172337477 10627840472288171657313277)
                    ·
                      refine ⟨3985440177108064371492479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10627840472288171657313277 3985440177108064371492479)
                      ·
                        rfl

theorem cell23_7761617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_7761617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761617 prefixEnd_7761617 := by exact prefixLift 7761617
  have htrace : WordTrace (prefixWord ++ tailWord_7761617) baseStart_7761617 baseEnd_7761617 := by
    simpa [prefixWord, tailWord_7761617, baseEnd_7761617] using wordTrace_append hprefix tailTrace_7761617
  have hstable : (prefixWord ++ tailWord_7761617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761617).length < 2 ^ (prefixWord ++ tailWord_7761617).sum := by decide
  have hdescent : baseEnd_7761617 < baseStart_7761617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761637 : List Nat := [1, 3, 1, 4, 1, 1, 2, 4, 6]
def baseStart_7761637 : Nat := 118140960795 + 7761637 * 2 ^ 59
def prefixEnd_7761637 : Nat := 4983230072969 + 3 ^ 40 * 7761637 * 2
def baseEnd_7761637 : Nat := 442827827413461588138043

theorem tailTrace_7761637 : CollatzResearch.WordTrace tailWord_7761637 prefixEnd_7761637 442827827413461588138043 := by
  unfold tailWord_7761637
  simp only [CollatzResearch.WordTrace]
  refine ⟨283090158181922205909731165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188726772121281470606487443 283090158181922205909731165)
  ·
    refine ⟨106158809318220827216149187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283090158181922205909731165 106158809318220827216149187)
    ·
      refine ⟨159238213977331240824223781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106158809318220827216149187 159238213977331240824223781)
      ·
        refine ⟨29857165120749607654541959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159238213977331240824223781 29857165120749607654541959)
        ·
          refine ⟨44785747681124411481812939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29857165120749607654541959 44785747681124411481812939)
          ·
            refine ⟨67178621521686617222719409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44785747681124411481812939 67178621521686617222719409)
            ·
              refine ⟨50383966141264962917039557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67178621521686617222719409 50383966141264962917039557)
              ·
                refine ⟨9446993651487180546944917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50383966141264962917039557 9446993651487180546944917)
                ·
                  refine ⟨442827827413461588138043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9446993651487180546944917 442827827413461588138043)
                  ·
                    rfl

theorem cell23_7761637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 6].length) (baseStart_7761637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761637 prefixEnd_7761637 := by exact prefixLift 7761637
  have htrace : WordTrace (prefixWord ++ tailWord_7761637) baseStart_7761637 baseEnd_7761637 := by
    simpa [prefixWord, tailWord_7761637, baseEnd_7761637] using wordTrace_append hprefix tailTrace_7761637
  have hstable : (prefixWord ++ tailWord_7761637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761637).length < 2 ^ (prefixWord ++ tailWord_7761637).sum := by decide
  have hdescent : baseEnd_7761637 < baseStart_7761637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761654 : List Nat := [5, 1, 1, 1, 1, 4, 1, 3, 6]
def baseStart_7761654 : Nat := 118140960795 + 7761654 * 2 ^ 59
def prefixEnd_7761654 : Nat := 4983230072969 + 3 ^ 40 * 7761654 * 2
def baseEnd_7761654 : Nat := 442828797321364525192201

theorem tailTrace_7761654 : CollatzResearch.WordTrace tailWord_7761654 prefixEnd_7761654 442828797321364525192201 := by
  unfold tailWord_7761654
  simp only [CollatzResearch.WordTrace]
  refine ⟨17693173638928788613318751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188727185481907078542066677 17693173638928788613318751)
  ·
    refine ⟨26539760458393182919978127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17693173638928788613318751 26539760458393182919978127)
    ·
      refine ⟨39809640687589774379967191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26539760458393182919978127 39809640687589774379967191)
      ·
        refine ⟨59714461031384661569950787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39809640687589774379967191 59714461031384661569950787)
        ·
          refine ⟨89571691547076992354926181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59714461031384661569950787 89571691547076992354926181)
          ·
            refine ⟨16794692165076936066548659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89571691547076992354926181 16794692165076936066548659)
            ·
              refine ⟨25192038247615404099822989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16794692165076936066548659 25192038247615404099822989)
              ·
                refine ⟨9447014342855776537433621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25192038247615404099822989 9447014342855776537433621)
                ·
                  refine ⟨442828797321364525192201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9447014342855776537433621 442828797321364525192201)
                  ·
                    rfl

theorem cell23_7761654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_7761654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761654 prefixEnd_7761654 := by exact prefixLift 7761654
  have htrace : WordTrace (prefixWord ++ tailWord_7761654) baseStart_7761654 baseEnd_7761654 := by
    simpa [prefixWord, tailWord_7761654, baseEnd_7761654] using wordTrace_append hprefix tailTrace_7761654
  have hstable : (prefixWord ++ tailWord_7761654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761654).length < 2 ^ (prefixWord ++ tailWord_7761654).sum := by decide
  have hdescent : baseEnd_7761654 < baseStart_7761654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761681 : List Nat := [1, 2, 2, 1, 1, 3, 1, 7, 1, 1, 3]
def baseStart_7761681 : Nat := 118140960795 + 7761681 * 2 ^ 59
def prefixEnd_7761681 : Nat := 4983230072969 + 3 ^ 40 * 7761681 * 2
def baseEnd_7761681 : Nat := 3985473039869952121092185

theorem tailTrace_7761681 : CollatzResearch.WordTrace tailWord_7761681 prefixEnd_7761681 3985473039869952121092185 := by
  unfold tailWord_7761681
  simp only [CollatzResearch.WordTrace]
  refine ⟨283091762993762801424332897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188727841995841867616221931 283091762993762801424332897)
  ·
    refine ⟨212318822245322101068249673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283091762993762801424332897 212318822245322101068249673)
    ·
      refine ⟨159239116683991575801187255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212318822245322101068249673 159239116683991575801187255)
      ·
        refine ⟨238858675025987363701780883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159239116683991575801187255 238858675025987363701780883)
        ·
          refine ⟨358288012538981045552671325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238858675025987363701780883 358288012538981045552671325)
          ·
            refine ⟨134358004702117892082251747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358288012538981045552671325 134358004702117892082251747)
            ·
              refine ⟨201537007053176838123377621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134358004702117892082251747 201537007053176838123377621)
              ·
                refine ⟨4723523602808832143516663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 201537007053176838123377621 4723523602808832143516663)
                ·
                  refine ⟨7085285404213248215274995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723523602808832143516663 7085285404213248215274995)
                  ·
                    refine ⟨10627928106319872322912493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7085285404213248215274995 10627928106319872322912493)
                    ·
                      refine ⟨3985473039869952121092185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10627928106319872322912493 3985473039869952121092185)
                      ·
                        rfl

theorem cell23_7761681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 1, 1, 3].length) (baseStart_7761681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761681 prefixEnd_7761681 := by exact prefixLift 7761681
  have htrace : WordTrace (prefixWord ++ tailWord_7761681) baseStart_7761681 baseEnd_7761681 := by
    simpa [prefixWord, tailWord_7761681, baseEnd_7761681] using wordTrace_append hprefix tailTrace_7761681
  have hstable : (prefixWord ++ tailWord_7761681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761681).length < 2 ^ (prefixWord ++ tailWord_7761681).sum := by decide
  have hdescent : baseEnd_7761681 < baseStart_7761681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761698 : List Nat := [3, 3, 1, 1, 2, 1, 3, 4, 1, 1, 3]
def baseStart_7761698 : Nat := 118140960795 + 7761698 * 2 ^ 59
def prefixEnd_7761698 : Nat := 4983230072969 + 3 ^ 40 * 7761698 * 2
def baseEnd_7761698 : Nat := 3985481769041078554579607

theorem tailTrace_7761698 : CollatzResearch.WordTrace tailWord_7761698 prefixEnd_7761698 3985481769041078554579607 := by
  unfold tailWord_7761698
  simp only [CollatzResearch.WordTrace]
  refine ⟨70773095758675303331925437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188728255356467475551801165 70773095758675303331925437)
  ·
    refine ⟨26539910909503238749472039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70773095758675303331925437 26539910909503238749472039)
    ·
      refine ⟨39809866364254858124208059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26539910909503238749472039 39809866364254858124208059)
      ·
        refine ⟨59714799546382287186312089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39809866364254858124208059 59714799546382287186312089)
        ·
          refine ⟨44786099659786715389734067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59714799546382287186312089 44786099659786715389734067)
          ·
            refine ⟨67179149489680073084601101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44786099659786715389734067 67179149489680073084601101)
            ·
              refine ⟨25192181058630027406725413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67179149489680073084601101 25192181058630027406725413)
              ·
                refine ⟨4723533948493130138761015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25192181058630027406725413 4723533948493130138761015)
                ·
                  refine ⟨7085300922739695208141523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723533948493130138761015 7085300922739695208141523)
                  ·
                    refine ⟨10627951384109542812212285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7085300922739695208141523 10627951384109542812212285)
                    ·
                      refine ⟨3985481769041078554579607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10627951384109542812212285 3985481769041078554579607)
                      ·
                        rfl

theorem cell23_7761698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_7761698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761698 prefixEnd_7761698 := by exact prefixLift 7761698
  have htrace : WordTrace (prefixWord ++ tailWord_7761698) baseStart_7761698 baseEnd_7761698 := by
    simpa [prefixWord, tailWord_7761698, baseEnd_7761698] using wordTrace_append hprefix tailTrace_7761698
  have hstable : (prefixWord ++ tailWord_7761698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761698).length < 2 ^ (prefixWord ++ tailWord_7761698).sum := by decide
  have hdescent : baseEnd_7761698 < baseStart_7761698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761704 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_7761704 : Nat := 118140960795 + 7761704 * 2 ^ 59
def prefixEnd_7761704 : Nat := 4983230072969 + 3 ^ 40 * 7761704 * 2
def baseEnd_7761704 : Nat := 3985484849925005531104579

theorem tailTrace_7761704 : CollatzResearch.WordTrace tailWord_7761704 prefixEnd_7761704 3985484849925005531104579 := by
  unfold tailWord_7761704
  simp only [CollatzResearch.WordTrace]
  refine ⟨141546300936339738176210083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188728401248452984234946777 141546300936339738176210083)
  ·
    refine ⟨212319451404509607264315125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141546300936339738176210083 212319451404509607264315125)
    ·
      refine ⟨19904948569172775681029543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212319451404509607264315125 19904948569172775681029543)
      ·
        refine ⟨29857422853759163521544315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19904948569172775681029543 29857422853759163521544315)
        ·
          refine ⟨44786134280638745282316473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29857422853759163521544315 44786134280638745282316473)
          ·
            refine ⟨33589600710479058961737355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44786134280638745282316473 33589600710479058961737355)
            ·
              refine ⟨50384401065718588442606033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33589600710479058961737355 50384401065718588442606033)
              ·
                refine ⟨37788300799288941331954525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50384401065718588442606033 37788300799288941331954525)
                ·
                  refine ⟨14170612799733352999482947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37788300799288941331954525 14170612799733352999482947)
                  ·
                    refine ⟨21255919199600029499224421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14170612799733352999482947 21255919199600029499224421)
                    ·
                      refine ⟨3985484849925005531104579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21255919199600029499224421 3985484849925005531104579)
                      ·
                        rfl

theorem cell23_7761704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_7761704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761704 prefixEnd_7761704 := by exact prefixLift 7761704
  have htrace : WordTrace (prefixWord ++ tailWord_7761704) baseStart_7761704 baseEnd_7761704 := by
    simpa [prefixWord, tailWord_7761704, baseEnd_7761704] using wordTrace_append hprefix tailTrace_7761704
  have hstable : (prefixWord ++ tailWord_7761704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761704).length < 2 ^ (prefixWord ++ tailWord_7761704).sum := by decide
  have hdescent : baseEnd_7761704 < baseStart_7761704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761714 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 1, 6]
def baseStart_7761714 : Nat := 118140960795 + 7761714 * 2 ^ 59
def prefixEnd_7761714 : Nat := 4983230072969 + 3 ^ 40 * 7761714 * 2
def baseEnd_7761714 : Nat := 1328496661577183497326511

theorem tailTrace_7761714 : CollatzResearch.WordTrace tailWord_7761714 prefixEnd_7761714 1328496661577183497326511 := by
  unfold tailWord_7761714
  simp only [CollatzResearch.WordTrace]
  refine ⟨70773241650660812015071049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188728644401762165373522797 70773241650660812015071049)
  ·
    refine ⟨53079931237995609011303287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70773241650660812015071049 53079931237995609011303287)
    ·
      refine ⟨79619896856993413516954931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53079931237995609011303287 79619896856993413516954931)
      ·
        refine ⟨119429845285490120275432397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79619896856993413516954931 119429845285490120275432397)
        ·
          refine ⟨44786191982058795103287149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119429845285490120275432397 44786191982058795103287149)
          ·
            refine ⟨16794821993272048163732681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44786191982058795103287149 16794821993272048163732681)
            ·
              refine ⟨12596116494954036122799511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16794821993272048163732681 12596116494954036122799511)
              ·
                refine ⟨18894174742431054184199267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12596116494954036122799511 18894174742431054184199267)
                ·
                  refine ⟨28341262113646581276298901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18894174742431054184199267 28341262113646581276298901)
                  ·
                    refine ⟨1328496661577183497326511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28341262113646581276298901 1328496661577183497326511)
                    ·
                      rfl

theorem cell23_7761714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_7761714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761714 prefixEnd_7761714 := by exact prefixLift 7761714
  have htrace : WordTrace (prefixWord ++ tailWord_7761714) baseStart_7761714 baseEnd_7761714 := by
    simpa [prefixWord, tailWord_7761714, baseEnd_7761714] using wordTrace_append hprefix tailTrace_7761714
  have hstable : (prefixWord ++ tailWord_7761714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761714).length < 2 ^ (prefixWord ++ tailWord_7761714).sum := by decide
  have hdescent : baseEnd_7761714 < baseStart_7761714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761724 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 3, 2, 3]
def baseStart_7761724 : Nat := 118140960795 + 7761724 * 2 ^ 59
def prefixEnd_7761724 : Nat := 4983230072969 + 3 ^ 40 * 7761724 * 2
def baseEnd_7761724 : Nat := 3985495119538095452854487

theorem tailTrace_7761724 : CollatzResearch.WordTrace tailWord_7761724 prefixEnd_7761724 3985495119538095452854487 := by
  unfold tailWord_7761724
  simp only [CollatzResearch.WordTrace]
  refine ⟨141546665666303509884074113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188728887555071346512098817 141546665666303509884074113)
  ·
    refine ⟨106159999249727632413055585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141546665666303509884074113 106159999249727632413055585)
    ·
      refine ⟨79619999437295724309791689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106159999249727632413055585 79619999437295724309791689)
      ·
        refine ⟨59714999577971793232343767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79619999437295724309791689 59714999577971793232343767)
        ·
          refine ⟨89572499366957689848515651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59714999577971793232343767 89572499366957689848515651)
          ·
            refine ⟨134358749050436534772773477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89572499366957689848515651 134358749050436534772773477)
            ·
              refine ⟨25192265446956850269895027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134358749050436534772773477 25192265446956850269895027)
              ·
                refine ⟨37788398170435275404842541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25192265446956850269895027 37788398170435275404842541)
                ·
                  refine ⟨14170649313913228276815953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37788398170435275404842541 14170649313913228276815953)
                  ·
                    refine ⟨10627986985434921207611965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14170649313913228276815953 10627986985434921207611965)
                    ·
                      refine ⟨3985495119538095452854487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10627986985434921207611965 3985495119538095452854487)
                      ·
                        rfl

theorem cell23_7761724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_7761724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761724 prefixEnd_7761724 := by exact prefixLift 7761724
  have htrace : WordTrace (prefixWord ++ tailWord_7761724) baseStart_7761724 baseEnd_7761724 := by
    simpa [prefixWord, tailWord_7761724, baseEnd_7761724] using wordTrace_append hprefix tailTrace_7761724
  have hstable : (prefixWord ++ tailWord_7761724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761724).length < 2 ^ (prefixWord ++ tailWord_7761724).sum := by decide
  have hdescent : baseEnd_7761724 < baseStart_7761724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761748 : List Nat := [2, 4, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_7761748 : Nat := 118140960795 + 7761748 * 2 ^ 59
def prefixEnd_7761748 : Nat := 4983230072969 + 3 ^ 40 * 7761748 * 2
def baseEnd_7761748 : Nat := 1328502481024601119651459

theorem tailTrace_7761748 : CollatzResearch.WordTrace tailWord_7761748 prefixEnd_7761748 1328502481024601119651459 := by
  unfold tailWord_7761748
  simp only [CollatzResearch.WordTrace]
  refine ⟨141547103342260035933510949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188729471123013381244681265 141547103342260035933510949)
  ·
    refine ⟨26540081876673756737533303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141547103342260035933510949 26540081876673756737533303)
    ·
      refine ⟨39810122815010635106299955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26540081876673756737533303 39810122815010635106299955)
      ·
        refine ⟨59715184222515952659449933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39810122815010635106299955 59715184222515952659449933)
        ·
          refine ⟨22393194083443482247293725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59715184222515952659449933 22393194083443482247293725)
          ·
            refine ⟨8397447781291305842735147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22393194083443482247293725 8397447781291305842735147)
            ·
              refine ⟨12596171671936958764102721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8397447781291305842735147 12596171671936958764102721)
              ·
                refine ⟨9447128753952719073077041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12596171671936958764102721 9447128753952719073077041)
                ·
                  refine ⟨7085346565464539304807781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9447128753952719073077041 7085346565464539304807781)
                  ·
                    refine ⟨1328502481024601119651459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7085346565464539304807781 1328502481024601119651459)
                    ·
                      rfl

theorem cell23_7761748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_7761748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761748 prefixEnd_7761748 := by exact prefixLift 7761748
  have htrace : WordTrace (prefixWord ++ tailWord_7761748) baseStart_7761748 baseEnd_7761748 := by
    simpa [prefixWord, tailWord_7761748, baseEnd_7761748] using wordTrace_append hprefix tailTrace_7761748
  have hstable : (prefixWord ++ tailWord_7761748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761748).length < 2 ^ (prefixWord ++ tailWord_7761748).sum := by decide
  have hdescent : baseEnd_7761748 < baseStart_7761748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761822 : List Nat := [4, 3, 1, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_7761822 : Nat := 118140960795 + 7761822 * 2 ^ 59
def prefixEnd_7761822 : Nat := 4983230072969 + 3 ^ 40 * 7761822 * 2
def baseEnd_7761822 : Nat := 3985545440642236069429037

theorem tailTrace_7761822 : CollatzResearch.WordTrace tailWord_7761822 prefixEnd_7761822 3985545440642236069429037 := by
  unfold tailWord_7761822
  simp only [CollatzResearch.WordTrace]
  refine ⟨35387113210781497813151965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188731270457501321670143813 35387113210781497813151965)
  ·
    refine ⟨13270167454043061679931987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35387113210781497813151965 13270167454043061679931987)
    ·
      refine ⟨19905251181064592519897981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13270167454043061679931987 19905251181064592519897981)
      ·
        refine ⟨7464469192899222194961743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19905251181064592519897981 7464469192899222194961743)
        ·
          refine ⟨11196703789348833292442615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7464469192899222194961743 11196703789348833292442615)
          ·
            refine ⟨16795055684023249938663923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11196703789348833292442615 16795055684023249938663923)
            ·
              refine ⟨25192583526034874907995885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16795055684023249938663923 25192583526034874907995885)
              ·
                refine ⟨9447218822263078090498457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25192583526034874907995885 9447218822263078090498457)
                ·
                  refine ⟨7085414116697308567873843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9447218822263078090498457 7085414116697308567873843)
                  ·
                    refine ⟨10628121175045962851810765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7085414116697308567873843 10628121175045962851810765)
                    ·
                      refine ⟨3985545440642236069429037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10628121175045962851810765 3985545440642236069429037)
                      ·
                        rfl

theorem cell23_7761822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_7761822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761822 prefixEnd_7761822 := by exact prefixLift 7761822
  have htrace : WordTrace (prefixWord ++ tailWord_7761822) baseStart_7761822 baseEnd_7761822 := by
    simpa [prefixWord, tailWord_7761822, baseEnd_7761822] using wordTrace_append hprefix tailTrace_7761822
  have hstable : (prefixWord ++ tailWord_7761822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761822).length < 2 ^ (prefixWord ++ tailWord_7761822).sum := by decide
  have hdescent : baseEnd_7761822 < baseStart_7761822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761868 : List Nat := [2, 2, 1, 4, 1, 2, 4, 2, 5]
def baseStart_7761868 : Nat := 118140960795 + 7761868 * 2 ^ 59
def prefixEnd_7761868 : Nat := 4983230072969 + 3 ^ 40 * 7761868 * 2
def baseEnd_7761868 : Nat := 442841006750260321050425

theorem tailTrace_7761868 : CollatzResearch.WordTrace tailWord_7761868 prefixEnd_7761868 442841006750260321050425 := by
  unfold tailWord_7761868
  simp only [CollatzResearch.WordTrace]
  refine ⟨141549291722042666180695129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188732388962723554907593505 141549291722042666180695129)
  ·
    refine ⟨106161968791531999635521347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141549291722042666180695129 106161968791531999635521347)
    ·
      refine ⟨159242953187297999453282021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106161968791531999635521347 159242953187297999453282021)
      ·
        refine ⟨29858053722618374897490379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159242953187297999453282021 29858053722618374897490379)
        ·
          refine ⟨44787080583927562346235569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29858053722618374897490379 44787080583927562346235569)
          ·
            refine ⟨33590310437945671759676677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44787080583927562346235569 33590310437945671759676677)
            ·
              refine ⟨6298183207114813454939377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33590310437945671759676677 6298183207114813454939377)
              ·
                refine ⟨4723637405336110091204533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6298183207114813454939377 4723637405336110091204533)
                ·
                  refine ⟨442841006750260321050425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4723637405336110091204533 442841006750260321050425)
                  ·
                    rfl

theorem cell23_7761868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 5].length) (baseStart_7761868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761868 prefixEnd_7761868 := by exact prefixLift 7761868
  have htrace : WordTrace (prefixWord ++ tailWord_7761868) baseStart_7761868 baseEnd_7761868 := by
    simpa [prefixWord, tailWord_7761868, baseEnd_7761868] using wordTrace_append hprefix tailTrace_7761868
  have hstable : (prefixWord ++ tailWord_7761868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761868).length < 2 ^ (prefixWord ++ tailWord_7761868).sum := by decide
  have hdescent : baseEnd_7761868 < baseStart_7761868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761921 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_7761921 : Nat := 118140960795 + 7761921 * 2 ^ 59
def prefixEnd_7761921 : Nat := 4983230072969 + 3 ^ 40 * 7761921 * 2
def baseEnd_7761921 : Nat := 3985596275227031182091081

theorem tailTrace_7761921 : CollatzResearch.WordTrace tailWord_7761921 prefixEnd_7761921 3985596275227031182091081 := by
  unfold tailWord_7761921
  simp only [CollatzResearch.WordTrace]
  refine ⟨283100516512893322413069617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188733677675262214942046411 283100516512893322413069617)
  ·
    refine ⟨212325387384669991809802213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283100516512893322413069617 212325387384669991809802213)
    ·
      refine ⟨39811010134625623464337915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212325387384669991809802213 39811010134625623464337915)
      ·
        refine ⟨59716515201938435196506873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39811010134625623464337915 59716515201938435196506873)
        ·
          refine ⟨44787386401453826397380155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59716515201938435196506873 44787386401453826397380155)
          ·
            refine ⟨67181079602180739596070233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44787386401453826397380155 67181079602180739596070233)
            ·
              refine ⟨50385809701635554697052675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67181079602180739596070233 50385809701635554697052675)
              ·
                refine ⟨75578714552453332045579013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50385809701635554697052675 75578714552453332045579013)
                ·
                  refine ⟨14171008978584999758546065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75578714552453332045579013 14171008978584999758546065)
                  ·
                    refine ⟨10628256733938749818909549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14171008978584999758546065 10628256733938749818909549)
                    ·
                      refine ⟨3985596275227031182091081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10628256733938749818909549 3985596275227031182091081)
                      ·
                        rfl

theorem cell23_7761921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_7761921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761921 prefixEnd_7761921 := by exact prefixLift 7761921
  have htrace : WordTrace (prefixWord ++ tailWord_7761921) baseStart_7761921 baseEnd_7761921 := by
    simpa [prefixWord, tailWord_7761921, baseEnd_7761921] using wordTrace_append hprefix tailTrace_7761921
  have hstable : (prefixWord ++ tailWord_7761921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761921).length < 2 ^ (prefixWord ++ tailWord_7761921).sum := by decide
  have hdescent : baseEnd_7761921 < baseStart_7761921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761928 : List Nat := [2, 1, 3, 2, 1, 2, 1, 6, 1, 4]
def baseStart_7761928 : Nat := 118140960795 + 7761928 * 2 ^ 59
def prefixEnd_7761928 : Nat := 4983230072969 + 3 ^ 40 * 7761928 * 2
def baseEnd_7761928 : Nat := 1328533289863870884901183

theorem tailTrace_7761928 : CollatzResearch.WordTrace tailWord_7761928 prefixEnd_7761928 1328533289863870884901183 := by
  unfold tailWord_7761928
  simp only [CollatzResearch.WordTrace]
  refine ⟨141550385911933981304287219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188733847882578641739049625 141550385911933981304287219)
  ·
    refine ⟨212325578867900971956430829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141550385911933981304287219 212325578867900971956430829)
    ·
      refine ⟨79622092075462864483661561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212325578867900971956430829 79622092075462864483661561)
      ·
        refine ⟨59716569056597148362746171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79622092075462864483661561 59716569056597148362746171)
        ·
          refine ⟨89574853584895722544119257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59716569056597148362746171 89574853584895722544119257)
          ·
            refine ⟨67181140188671791908089443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89574853584895722544119257 67181140188671791908089443)
            ·
              refine ⟨100771710283007687862134165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67181140188671791908089443 100771710283007687862134165)
              ·
                refine ⟨4723673919515985368537539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100771710283007687862134165 4723673919515985368537539)
                ·
                  refine ⟨7085510879273978052806309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723673919515985368537539 7085510879273978052806309)
                  ·
                    refine ⟨1328533289863870884901183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7085510879273978052806309 1328533289863870884901183)
                    ·
                      rfl

theorem cell23_7761928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_7761928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761928 prefixEnd_7761928 := by exact prefixLift 7761928
  have htrace : WordTrace (prefixWord ++ tailWord_7761928) baseStart_7761928 baseEnd_7761928 := by
    simpa [prefixWord, tailWord_7761928, baseEnd_7761928] using wordTrace_append hprefix tailTrace_7761928
  have hstable : (prefixWord ++ tailWord_7761928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761928).length < 2 ^ (prefixWord ++ tailWord_7761928).sum := by decide
  have hdescent : baseEnd_7761928 < baseStart_7761928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761944 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 1, 2, 6]
def baseStart_7761944 : Nat := 118140960795 + 7761944 * 2 ^ 59
def prefixEnd_7761944 : Nat := 4983230072969 + 3 ^ 40 * 7761944 * 2
def baseEnd_7761944 : Nat := 3985608085282084592103475

theorem tailTrace_7761944 : CollatzResearch.WordTrace tailWord_7761944 prefixEnd_7761944 3985608085282084592103475 := by
  unfold tailWord_7761944
  simp only [CollatzResearch.WordTrace]
  refine ⟨141550677695904998670578443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188734236927873331560771257 141550677695904998670578443)
  ·
    refine ⟨212326016543857498005867665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141550677695904998670578443 212326016543857498005867665)
    ·
      refine ⟨159244512407893123504400749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212326016543857498005867665 159244512407893123504400749)
      ·
        refine ⟨59716692152959921314150281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159244512407893123504400749 59716692152959921314150281)
        ·
          refine ⟨44787519114719940985612711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59716692152959921314150281 44787519114719940985612711)
          ·
            refine ⟨67181278672079911478419067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44787519114719940985612711 67181278672079911478419067)
            ·
              refine ⟨100771918008119867217628601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67181278672079911478419067 100771918008119867217628601)
              ·
                refine ⟨75578938506089900413221451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100771918008119867217628601 75578938506089900413221451)
                ·
                  refine ⟨113368407759134850619832177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75578938506089900413221451 113368407759134850619832177)
                  ·
                    refine ⟨85026305819351137964874133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113368407759134850619832177 85026305819351137964874133)
                    ·
                      refine ⟨3985608085282084592103475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85026305819351137964874133 3985608085282084592103475)
                      ·
                        rfl

theorem cell23_7761944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_7761944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761944 prefixEnd_7761944 := by exact prefixLift 7761944
  have htrace : WordTrace (prefixWord ++ tailWord_7761944) baseStart_7761944 baseEnd_7761944 := by
    simpa [prefixWord, tailWord_7761944, baseEnd_7761944] using wordTrace_append hprefix tailTrace_7761944
  have hstable : (prefixWord ++ tailWord_7761944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761944).length < 2 ^ (prefixWord ++ tailWord_7761944).sum := by decide
  have hdescent : baseEnd_7761944 < baseStart_7761944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761962 : List Nat := [3, 1, 4, 1, 2, 3, 1, 3, 1, 4]
def baseStart_7761962 : Nat := 118140960795 + 7761962 * 2 ^ 59
def prefixEnd_7761962 : Nat := 4983230072969 + 3 ^ 40 * 7761962 * 2
def baseEnd_7761962 : Nat := 1328539109311288507226131

theorem tailTrace_7761962 : CollatzResearch.WordTrace tailWord_7761962 prefixEnd_7761962 1328539109311288507226131 := by
  unfold tailWord_7761962
  simp only [CollatzResearch.WordTrace]
  refine ⟨70775502976436196603828035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188734674603829857610208093 70775502976436196603828035)
  ·
    refine ⟨106163254464654294905742053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70775502976436196603828035 106163254464654294905742053)
    ·
      refine ⟨19905610212122680294826635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106163254464654294905742053 19905610212122680294826635)
      ·
        refine ⟨29858415318184020442239953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19905610212122680294826635 29858415318184020442239953)
        ·
          refine ⟨22393811488638015331679965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29858415318184020442239953 22393811488638015331679965)
          ·
            refine ⟨8397679308239255749379987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22393811488638015331679965 8397679308239255749379987)
            ·
              refine ⟨12596518962358883624069981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8397679308239255749379987 12596518962358883624069981)
              ·
                refine ⟨4723694610884581359026243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12596518962358883624069981 4723694610884581359026243)
                ·
                  refine ⟨7085541916326872038539365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723694610884581359026243 7085541916326872038539365)
                  ·
                    refine ⟨1328539109311288507226131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7085541916326872038539365 1328539109311288507226131)
                    ·
                      rfl

theorem cell23_7761962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_7761962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761962 prefixEnd_7761962 := by exact prefixLift 7761962
  have htrace : WordTrace (prefixWord ++ tailWord_7761962) baseStart_7761962 baseEnd_7761962 := by
    simpa [prefixWord, tailWord_7761962, baseEnd_7761962] using wordTrace_append hprefix tailTrace_7761962
  have hstable : (prefixWord ++ tailWord_7761962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761962).length < 2 ^ (prefixWord ++ tailWord_7761962).sum := by decide
  have hdescent : baseEnd_7761962 < baseStart_7761962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761971 : List Nat := [1, 1, 1, 2, 4, 1, 4, 3, 1, 5]
def baseStart_7761971 : Nat := 118140960795 + 7761971 * 2 ^ 59
def prefixEnd_7761971 : Nat := 4983230072969 + 3 ^ 40 * 7761971 * 2
def baseEnd_7761971 : Nat := 1328540649753251995488617

theorem tailTrace_7761971 : CollatzResearch.WordTrace tailWord_7761971 prefixEnd_7761971 1328540649753251995488617 := by
  unfold tailWord_7761971
  simp only [CollatzResearch.WordTrace]
  refine ⟨283102340162712180952389767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188734893441808120634926511 283102340162712180952389767)
  ·
    refine ⟨424653510244068271428584651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283102340162712180952389767 424653510244068271428584651)
    ·
      refine ⟨636980265366102407142876977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424653510244068271428584651 636980265366102407142876977)
      ·
        refine ⟨477735199024576805357157733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 636980265366102407142876977 477735199024576805357157733)
        ·
          refine ⟨89575349817108151004467075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 477735199024576805357157733 89575349817108151004467075)
          ·
            refine ⟨134363024725662226506700613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89575349817108151004467075 134363024725662226506700613)
            ·
              refine ⟨25193067136061667470006365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134363024725662226506700613 25193067136061667470006365)
              ·
                refine ⟨9447400176023125301252387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25193067136061667470006365 9447400176023125301252387)
                ·
                  refine ⟨14171100264034687951878581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9447400176023125301252387 14171100264034687951878581)
                  ·
                    refine ⟨1328540649753251995488617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14171100264034687951878581 1328540649753251995488617)
                    ·
                      rfl

theorem cell23_7761971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 5].length) (baseStart_7761971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761971 prefixEnd_7761971 := by exact prefixLift 7761971
  have htrace : WordTrace (prefixWord ++ tailWord_7761971) baseStart_7761971 baseEnd_7761971 := by
    simpa [prefixWord, tailWord_7761971, baseEnd_7761971] using wordTrace_append hprefix tailTrace_7761971
  have hstable : (prefixWord ++ tailWord_7761971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761971).length < 2 ^ (prefixWord ++ tailWord_7761971).sum := by decide
  have hdescent : baseEnd_7761971 < baseStart_7761971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761985 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_7761985 : Nat := 118140960795 + 7761985 * 2 ^ 59
def prefixEnd_7761985 : Nat := 4983230072969 + 3 ^ 40 * 7761985 * 2
def baseEnd_7761985 : Nat := 3985629137988918931690787

theorem tailTrace_7761985 : CollatzResearch.WordTrace tailWord_7761985 prefixEnd_7761985 3985629137988918931690787 := by
  unfold tailWord_7761985
  simp only [CollatzResearch.WordTrace]
  refine ⟨283102850784661461343399409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188735233856440974228932939 283102850784661461343399409)
  ·
    refine ⟨212327138088496096007549557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283102850784661461343399409 212327138088496096007549557)
    ·
      refine ⟨19905669195796509000707771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212327138088496096007549557 19905669195796509000707771)
      ·
        refine ⟨29858503793694763501061657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19905669195796509000707771 29858503793694763501061657)
        ·
          refine ⟨22393877845271072625796243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29858503793694763501061657 22393877845271072625796243)
          ·
            refine ⟨33590816767906608938694365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22393877845271072625796243 33590816767906608938694365)
            ·
              refine ⟨12596556287964978352010387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33590816767906608938694365 12596556287964978352010387)
              ·
                refine ⟨18894834431947467528015581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12596556287964978352010387 18894834431947467528015581)
                ·
                  refine ⟨7085562911980300323005843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18894834431947467528015581 7085562911980300323005843)
                  ·
                    refine ⟨10628344367970450484508765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7085562911980300323005843 10628344367970450484508765)
                    ·
                      refine ⟨3985629137988918931690787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10628344367970450484508765 3985629137988918931690787)
                      ·
                        rfl

theorem cell23_7761985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_7761985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761985 prefixEnd_7761985 := by exact prefixLift 7761985
  have htrace : WordTrace (prefixWord ++ tailWord_7761985) baseStart_7761985 baseEnd_7761985 := by
    simpa [prefixWord, tailWord_7761985, baseEnd_7761985] using wordTrace_append hprefix tailTrace_7761985
  have hstable : (prefixWord ++ tailWord_7761985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761985).length < 2 ^ (prefixWord ++ tailWord_7761985).sum := by decide
  have hdescent : baseEnd_7761985 < baseStart_7761985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7761991 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_7761991 : Nat := 118140960795 + 7761991 * 2 ^ 59
def prefixEnd_7761991 : Nat := 4983230072969 + 3 ^ 40 * 7761991 * 2
def baseEnd_7761991 : Nat := 3985632218872845908215759

theorem tailTrace_7761991 : CollatzResearch.WordTrace tailWord_7761991 prefixEnd_7761991 3985632218872845908215759 := by
  unfold tailWord_7761991
  simp only [CollatzResearch.WordTrace]
  refine ⟨283103069622639724368117827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188735379748426482912078551 283103069622639724368117827)
  ·
    refine ⟨424654604433959586552176741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283103069622639724368117827 424654604433959586552176741)
    ·
      refine ⟨79622738331367422478533139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 424654604433959586552176741 79622738331367422478533139)
      ·
        refine ⟨119434107497051133717799709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79622738331367422478533139 119434107497051133717799709)
        ·
          refine ⟨44787790311394175144174891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119434107497051133717799709 44787790311394175144174891)
          ·
            refine ⟨67181685467091262716262337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44787790311394175144174891 67181685467091262716262337)
            ·
              refine ⟨50386264100318447037196753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67181685467091262716262337 50386264100318447037196753)
              ·
                refine ⟨37789698075238835277897565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50386264100318447037196753 37789698075238835277897565)
                ·
                  refine ⟨14171136778214563229211587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37789698075238835277897565 14171136778214563229211587)
                  ·
                    refine ⟨21256705167321844843817381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14171136778214563229211587 21256705167321844843817381)
                    ·
                      refine ⟨3985632218872845908215759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21256705167321844843817381 3985632218872845908215759)
                      ·
                        rfl

theorem cell23_7761991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_7761991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7761991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7761991 prefixEnd_7761991 := by exact prefixLift 7761991
  have htrace : WordTrace (prefixWord ++ tailWord_7761991) baseStart_7761991 baseEnd_7761991 := by
    simpa [prefixWord, tailWord_7761991, baseEnd_7761991] using wordTrace_append hprefix tailTrace_7761991
  have hstable : (prefixWord ++ tailWord_7761991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7761991).length < 2 ^ (prefixWord ++ tailWord_7761991).sum := by decide
  have hdescent : baseEnd_7761991 < baseStart_7761991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7761991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762008 : List Nat := [2, 1, 2, 2, 1, 4, 3, 2, 1, 1, 4]
def baseStart_7762008 : Nat := 118140960795 + 7762008 * 2 ^ 59
def prefixEnd_7762008 : Nat := 4983230072969 + 3 ^ 40 * 7762008 * 2
def baseEnd_7762008 : Nat := 3985640948043972341703181

theorem tailTrace_7762008 : CollatzResearch.WordTrace tailWord_7762008 prefixEnd_7762008 3985640948043972341703181 := by
  unfold tailWord_7762008
  simp only [CollatzResearch.WordTrace]
  refine ⟨141551844831789068135743339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188735793109052090847657785 141551844831789068135743339)
  ·
    refine ⟨212327767247683602203615009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141551844831789068135743339 212327767247683602203615009)
    ·
      refine ⟨159245825435762701652711257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212327767247683602203615009 159245825435762701652711257)
      ·
        refine ⟨119434369076822026239533443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159245825435762701652711257 119434369076822026239533443)
        ·
          refine ⟨179151553615233039359300165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119434369076822026239533443 179151553615233039359300165)
          ·
            refine ⟨33590916302856194879868781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179151553615233039359300165 33590916302856194879868781)
            ·
              refine ⟨12596593613571073079950793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33590916302856194879868781 12596593613571073079950793)
              ·
                refine ⟨9447445210178304809963095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12596593613571073079950793 9447445210178304809963095)
                ·
                  refine ⟨14171167815267457214944643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9447445210178304809963095 14171167815267457214944643)
                  ·
                    refine ⟨21256751722901185822416965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14171167815267457214944643 21256751722901185822416965)
                    ·
                      refine ⟨3985640948043972341703181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21256751722901185822416965 3985640948043972341703181)
                      ·
                        rfl

theorem cell23_7762008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_7762008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762008 prefixEnd_7762008 := by exact prefixLift 7762008
  have htrace : WordTrace (prefixWord ++ tailWord_7762008) baseStart_7762008 baseEnd_7762008 := by
    simpa [prefixWord, tailWord_7762008, baseEnd_7762008] using wordTrace_append hprefix tailTrace_7762008
  have hstable : (prefixWord ++ tailWord_7762008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762008).length < 2 ^ (prefixWord ++ tailWord_7762008).sum := by decide
  have hdescent : baseEnd_7762008 < baseStart_7762008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762021 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 3, 2, 4]
def baseStart_7762021 : Nat := 118140960795 + 7762021 * 2 ^ 59
def prefixEnd_7762021 : Nat := 4983230072969 + 3 ^ 40 * 7762021 * 2
def baseEnd_7762021 : Nat := 3985647623292480790840621

theorem tailTrace_7762021 : CollatzResearch.WordTrace tailWord_7762021 prefixEnd_7762021 3985647623292480790840621 := by
  unfold tailWord_7762021
  simp only [CollatzResearch.WordTrace]
  refine ⟨283104163812531039491709917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188736109208354026327806611 283104163812531039491709917)
  ·
    refine ⟨106164061429699139809391219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283104163812531039491709917 106164061429699139809391219)
    ·
      refine ⟨159246092144548709714086829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106164061429699139809391219 159246092144548709714086829)
      ·
        refine ⟨59717284554205766142782561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159246092144548709714086829 59717284554205766142782561)
        ·
          refine ⟨44787963415654324607086921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59717284554205766142782561 44787963415654324607086921)
          ·
            refine ⟨33590972561740743455315191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44787963415654324607086921 33590972561740743455315191)
            ·
              refine ⟨50386458842611115182972787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33590972561740743455315191 50386458842611115182972787)
              ·
                refine ⟨75579688263916672774459181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50386458842611115182972787 75579688263916672774459181)
                ·
                  refine ⟨28342383098968752290422193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75579688263916672774459181 28342383098968752290422193)
                  ·
                    refine ⟨21256787324226564217816645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28342383098968752290422193 21256787324226564217816645)
                    ·
                      refine ⟨3985647623292480790840621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21256787324226564217816645 3985647623292480790840621)
                      ·
                        rfl

theorem cell23_7762021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_7762021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762021 prefixEnd_7762021 := by exact prefixLift 7762021
  have htrace : WordTrace (prefixWord ++ tailWord_7762021) baseStart_7762021 baseEnd_7762021 := by
    simpa [prefixWord, tailWord_7762021, baseEnd_7762021] using wordTrace_append hprefix tailTrace_7762021
  have hstable : (prefixWord ++ tailWord_7762021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762021).length < 2 ^ (prefixWord ++ tailWord_7762021).sum := by decide
  have hdescent : baseEnd_7762021 < baseStart_7762021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762028 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 5]
def baseStart_7762028 : Nat := 118140960795 + 7762028 * 2 ^ 59
def prefixEnd_7762028 : Nat := 4983230072969 + 3 ^ 40 * 7762028 * 2
def baseEnd_7762028 : Nat := 3985651217657062263453089

theorem tailTrace_7762028 : CollatzResearch.WordTrace tailWord_7762028 prefixEnd_7762028 3985651217657062263453089 := by
  unfold tailWord_7762028
  simp only [CollatzResearch.WordTrace]
  refine ⟨141552209561752839843607369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188736279415670453124809825 141552209561752839843607369)
  ·
    refine ⟨106164157171314629882705527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141552209561752839843607369 106164157171314629882705527)
    ·
      refine ⟨159246235756971944824058291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106164157171314629882705527 159246235756971944824058291)
      ·
        refine ⟨238869353635457917236087437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159246235756971944824058291 238869353635457917236087437)
        ·
          refine ⟨89576007613296718963532789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238869353635457917236087437 89576007613296718963532789)
          ·
            refine ⟨8397750713746567402831199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89576007613296718963532789 8397750713746567402831199)
            ·
              refine ⟨12596626070619851104246799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8397750713746567402831199 12596626070619851104246799)
              ·
                refine ⟨18894939105929776656370199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12596626070619851104246799 18894939105929776656370199)
                ·
                  refine ⟨28342408658894664984555299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18894939105929776656370199 28342408658894664984555299)
                  ·
                    refine ⟨42513612988341997476832949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28342408658894664984555299 42513612988341997476832949)
                    ·
                      refine ⟨3985651217657062263453089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42513612988341997476832949 3985651217657062263453089)
                      ·
                        rfl

theorem cell23_7762028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_7762028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762028 prefixEnd_7762028 := by exact prefixLift 7762028
  have htrace : WordTrace (prefixWord ++ tailWord_7762028) baseStart_7762028 baseEnd_7762028 := by
    simpa [prefixWord, tailWord_7762028, baseEnd_7762028] using wordTrace_append hprefix tailTrace_7762028
  have hstable : (prefixWord ++ tailWord_7762028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762028).length < 2 ^ (prefixWord ++ tailWord_7762028).sum := by decide
  have hdescent : baseEnd_7762028 < baseStart_7762028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762058 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 1, 3, 3]
def baseStart_7762058 : Nat := 118140960795 + 7762058 * 2 ^ 59
def prefixEnd_7762058 : Nat := 4983230072969 + 3 ^ 40 * 7762058 * 2
def baseEnd_7762058 : Nat := 3985666622076697146077951

theorem tailTrace_7762058 : CollatzResearch.WordTrace tailWord_7762058 prefixEnd_7762058 3985666622076697146077951 := by
  unfold tailWord_7762058
  simp only [CollatzResearch.WordTrace]
  refine ⟨70776378328349248702701707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188737008875597996540537885 70776378328349248702701707)
  ·
    refine ⟨106164567492523873054052561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70776378328349248702701707 106164567492523873054052561)
    ·
      refine ⟨79623425619392904790539421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106164567492523873054052561 79623425619392904790539421)
      ·
        refine ⟨29858784607272339296452283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79623425619392904790539421 29858784607272339296452283)
        ·
          refine ⟨44788176910908508944678425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29858784607272339296452283 44788176910908508944678425)
          ·
            refine ⟨33591132683181381708508819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44788176910908508944678425 33591132683181381708508819)
            ·
              refine ⟨50386699024772072562763229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33591132683181381708508819 50386699024772072562763229)
              ·
                refine ⟨18895012134289527211036211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50386699024772072562763229 18895012134289527211036211)
                ·
                  refine ⟨28342518201434290816554317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18895012134289527211036211 28342518201434290816554317)
                  ·
                    refine ⟨10628444325537859056207869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28342518201434290816554317 10628444325537859056207869)
                    ·
                      refine ⟨3985666622076697146077951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10628444325537859056207869 3985666622076697146077951)
                      ·
                        rfl

theorem cell23_7762058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_7762058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762058 prefixEnd_7762058 := by exact prefixLift 7762058
  have htrace : WordTrace (prefixWord ++ tailWord_7762058) baseStart_7762058 baseEnd_7762058 := by
    simpa [prefixWord, tailWord_7762058, baseEnd_7762058] using wordTrace_append hprefix tailTrace_7762058
  have hstable : (prefixWord ++ tailWord_7762058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762058).length < 2 ^ (prefixWord ++ tailWord_7762058).sum := by decide
  have hdescent : baseEnd_7762058 < baseStart_7762058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762070 : List Nat := [5, 3, 2, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_7762070 : Nat := 118140960795 + 7762070 * 2 ^ 59
def prefixEnd_7762070 : Nat := 4983230072969 + 3 ^ 40 * 7762070 * 2
def baseEnd_7762070 : Nat := 3985672783844551099127897

theorem tailTrace_7762070 : CollatzResearch.WordTrace tailWord_7762070 prefixEnd_7762070 3985672783844551099127897 := by
  unfold tailWord_7762070
  simp only [CollatzResearch.WordTrace]
  refine ⟨17694121936834595053765229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188737300659569013906829109 17694121936834595053765229)
  ·
    refine ⟨6635295726312973145161961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17694121936834595053765229 6635295726312973145161961)
    ·
      refine ⟨4976471794734729858871471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6635295726312973145161961 4976471794734729858871471)
      ·
        refine ⟨7464707692102094788307207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4976471794734729858871471 7464707692102094788307207)
        ·
          refine ⟨11197061538153142182460811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7464707692102094788307207 11197061538153142182460811)
          ·
            refine ⟨16795592307229713273691217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11197061538153142182460811 16795592307229713273691217)
            ·
              refine ⟨12596694230422284955268413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16795592307229713273691217 12596694230422284955268413)
              ·
                refine ⟨4723760336408356858225655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12596694230422284955268413 4723760336408356858225655)
                ·
                  refine ⟨7085640504612535287338483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723760336408356858225655 7085640504612535287338483)
                  ·
                    refine ⟨10628460756918802931007725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7085640504612535287338483 10628460756918802931007725)
                    ·
                      refine ⟨3985672783844551099127897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10628460756918802931007725 3985672783844551099127897)
                      ·
                        rfl

theorem cell23_7762070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_7762070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762070 prefixEnd_7762070 := by exact prefixLift 7762070
  have htrace : WordTrace (prefixWord ++ tailWord_7762070) baseStart_7762070 baseEnd_7762070 := by
    simpa [prefixWord, tailWord_7762070, baseEnd_7762070] using wordTrace_append hprefix tailTrace_7762070
  have hstable : (prefixWord ++ tailWord_7762070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762070).length < 2 ^ (prefixWord ++ tailWord_7762070).sum := by decide
  have hdescent : baseEnd_7762070 < baseStart_7762070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762085 : List Nat := [1, 3, 1, 2, 1, 3, 3, 3, 1, 3, 2]
def baseStart_7762085 : Nat := 118140960795 + 7762085 * 2 ^ 59
def prefixEnd_7762085 : Nat := 4983230072969 + 3 ^ 40 * 7762085 * 2
def baseEnd_7762085 : Nat := 3985680486054368540440327

theorem tailTrace_7762085 : CollatzResearch.WordTrace tailWord_7762085 prefixEnd_7762085 3985680486054368540440327 := by
  unfold tailWord_7762085
  simp only [CollatzResearch.WordTrace]
  refine ⟨283106498084299178422039709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188737665389532785614693139 283106498084299178422039709)
  ·
    refine ⟨106164936781612191908264891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283106498084299178422039709 106164936781612191908264891)
    ·
      refine ⟨159247405172418287862397337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106164936781612191908264891 159247405172418287862397337)
      ·
        refine ⟨119435553879313715896798003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159247405172418287862397337 119435553879313715896798003)
        ·
          refine ⟨179153330818970573845197005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119435553879313715896798003 179153330818970573845197005)
          ·
            refine ⟨67182499057113965191948877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179153330818970573845197005 67182499057113965191948877)
            ·
              refine ⟨25193437146417736946980829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67182499057113965191948877 25193437146417736946980829)
              ·
                refine ⟨9447538929906651355117811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25193437146417736946980829 9447538929906651355117811)
                ·
                  refine ⟨14171308394859977032676717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9447538929906651355117811 14171308394859977032676717)
                  ·
                    refine ⟨5314240648072491387253769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14171308394859977032676717 5314240648072491387253769)
                    ·
                      refine ⟨3985680486054368540440327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5314240648072491387253769 3985680486054368540440327)
                      ·
                        rfl

theorem cell23_7762085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_7762085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762085 prefixEnd_7762085 := by exact prefixLift 7762085
  have htrace : WordTrace (prefixWord ++ tailWord_7762085) baseStart_7762085 baseEnd_7762085 := by
    simpa [prefixWord, tailWord_7762085, baseEnd_7762085] using wordTrace_append hprefix tailTrace_7762085
  have hstable : (prefixWord ++ tailWord_7762085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762085).length < 2 ^ (prefixWord ++ tailWord_7762085).sum := by decide
  have hdescent : baseEnd_7762085 < baseStart_7762085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762155 : List Nat := [1, 1, 1, 1, 2, 5, 5, 2, 5]
def baseStart_7762155 : Nat := 118140960795 + 7762155 * 2 ^ 59
def prefixEnd_7762155 : Nat := 4983230072969 + 3 ^ 40 * 7762155 * 2
def baseEnd_7762155 : Nat := 442857381077798140729445

theorem tailTrace_7762155 : CollatzResearch.WordTrace tailWord_7762155 prefixEnd_7762155 442857381077798140729445 := by
  unfold tailWord_7762155
  simp only [CollatzResearch.WordTrace]
  refine ⟨283109051194045580377087919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188739367462697053584725279 283109051194045580377087919)
  ·
    refine ⟨424663576791068370565631879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283109051194045580377087919 424663576791068370565631879)
    ·
      refine ⟨636995365186602555848447819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424663576791068370565631879 636995365186602555848447819)
      ·
        refine ⟨955493047779903833772671729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636995365186602555848447819 955493047779903833772671729)
        ·
          refine ⟨716619785834927875329503797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 955493047779903833772671729 716619785834927875329503797)
          ·
            refine ⟨67183104922024488312140981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 716619785834927875329503797 67183104922024488312140981)
            ·
              refine ⟨6298416086439795779263217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67183104922024488312140981 6298416086439795779263217)
              ·
                refine ⟨4723812064829846834447413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6298416086439795779263217 4723812064829846834447413)
                ·
                  refine ⟨442857381077798140729445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4723812064829846834447413 442857381077798140729445)
                  ·
                    rfl

theorem cell23_7762155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 5].length) (baseStart_7762155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762155 prefixEnd_7762155 := by exact prefixLift 7762155
  have htrace : WordTrace (prefixWord ++ tailWord_7762155) baseStart_7762155 baseEnd_7762155 := by
    simpa [prefixWord, tailWord_7762155, baseEnd_7762155] using wordTrace_append hprefix tailTrace_7762155
  have hstable : (prefixWord ++ tailWord_7762155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762155).length < 2 ^ (prefixWord ++ tailWord_7762155).sum := by decide
  have hdescent : baseEnd_7762155 < baseStart_7762155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762161 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 7]
def baseStart_7762161 : Nat := 118140960795 + 7762161 * 2 ^ 59
def prefixEnd_7762161 : Nat := 4983230072969 + 3 ^ 40 * 7762161 * 2
def baseEnd_7762161 : Nat := 3985719510584110243089977

theorem tailTrace_7762161 : CollatzResearch.WordTrace tailWord_7762161 prefixEnd_7762161 3985719510584110243089977 := by
  unfold tailWord_7762161
  simp only [CollatzResearch.WordTrace]
  refine ⟨283109270032023843401806337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188739513354682562267870891 283109270032023843401806337)
  ·
    refine ⟨212331952524017882551354753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283109270032023843401806337 212331952524017882551354753)
    ·
      refine ⟨159248964393013411913516065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212331952524017882551354753 159248964393013411913516065)
      ·
        refine ⟨119436723294760058935137049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159248964393013411913516065 119436723294760058935137049)
        ·
          refine ⟨89577542471070044201352787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119436723294760058935137049 89577542471070044201352787)
          ·
            refine ⟨134366313706605066302029181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89577542471070044201352787 134366313706605066302029181)
            ·
              refine ⟨50387367639976899863260943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134366313706605066302029181 50387367639976899863260943)
              ·
                refine ⟨75581051459965349794891415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50387367639976899863260943 75581051459965349794891415)
                ·
                  refine ⟨113371577189948024692337123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75581051459965349794891415 113371577189948024692337123)
                  ·
                    refine ⟨170057365784922037038505685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113371577189948024692337123 170057365784922037038505685)
                    ·
                      refine ⟨3985719510584110243089977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170057365784922037038505685 3985719510584110243089977)
                      ·
                        rfl

theorem cell23_7762161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_7762161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762161 prefixEnd_7762161 := by exact prefixLift 7762161
  have htrace : WordTrace (prefixWord ++ tailWord_7762161) baseStart_7762161 baseEnd_7762161 := by
    simpa [prefixWord, tailWord_7762161, baseEnd_7762161] using wordTrace_append hprefix tailTrace_7762161
  have hstable : (prefixWord ++ tailWord_7762161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762161).length < 2 ^ (prefixWord ++ tailWord_7762161).sum := by decide
  have hdescent : baseEnd_7762161 < baseStart_7762161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762206 : List Nat := [4, 3, 2, 1, 1, 3, 2, 2, 5]
def baseStart_7762206 : Nat := 118140960795 + 7762206 * 2 ^ 59
def prefixEnd_7762206 : Nat := 4983230072969 + 3 ^ 40 * 7762206 * 2
def baseEnd_7762206 : Nat := 442860290801506951891919

theorem tailTrace_7762206 : CollatzResearch.WordTrace tailWord_7762206 prefixEnd_7762206 442860290801506951891919 := by
  unfold tailWord_7762206
  simp only [CollatzResearch.WordTrace]
  refine ⟨35388863914607602010899309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188740607544573877391462981 35388863914607602010899309)
  ·
    refine ⟨13270823967977850754087241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35388863914607602010899309 13270823967977850754087241)
    ·
      refine ⟨9953117975983388065565431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13270823967977850754087241 9953117975983388065565431)
      ·
        refine ⟨14929676963975082098348147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9953117975983388065565431 14929676963975082098348147)
        ·
          refine ⟨22394515445962623147522221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14929676963975082098348147 22394515445962623147522221)
          ·
            refine ⟨8397943292235983680320833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22394515445962623147522221 8397943292235983680320833)
            ·
              refine ⟨6298457469176987760240625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8397943292235983680320833 6298457469176987760240625)
              ·
                refine ⟨4723843101882740820180469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6298457469176987760240625 4723843101882740820180469)
                ·
                  refine ⟨442860290801506951891919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4723843101882740820180469 442860290801506951891919)
                  ·
                    rfl

theorem cell23_7762206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_7762206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762206 prefixEnd_7762206 := by exact prefixLift 7762206
  have htrace : WordTrace (prefixWord ++ tailWord_7762206) baseStart_7762206 baseEnd_7762206 := by
    simpa [prefixWord, tailWord_7762206, baseEnd_7762206] using wordTrace_append hprefix tailTrace_7762206
  have hstable : (prefixWord ++ tailWord_7762206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762206).length < 2 ^ (prefixWord ++ tailWord_7762206).sum := by decide
  have hdescent : baseEnd_7762206 < baseStart_7762206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762265 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 4, 3, 2]
def baseStart_7762265 : Nat := 118140960795 + 7762265 * 2 ^ 59
def prefixEnd_7762265 : Nat := 4983230072969 + 3 ^ 40 * 7762265 * 2
def baseEnd_7762265 : Nat := 3985772912572177836189499

theorem tailTrace_7762265 : CollatzResearch.WordTrace tailWord_7762265 prefixEnd_7762265 3985772912572177836189499 := by
  unfold tailWord_7762265
  simp only [CollatzResearch.WordTrace]
  refine ⟨283113063223647069163592249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188742042149098046109061499 283113063223647069163592249)
  ·
    refine ⟨212334797417735301872694187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283113063223647069163592249 212334797417735301872694187)
    ·
      refine ⟨318502196126602952809041281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212334797417735301872694187 318502196126602952809041281)
      ·
        refine ⟨238876647094952214606780961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318502196126602952809041281 238876647094952214606780961)
        ·
          refine ⟨179157485321214160955085721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238876647094952214606780961 179157485321214160955085721)
          ·
            refine ⟨134368113990910620716314291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179157485321214160955085721 134368113990910620716314291)
            ·
              refine ⟨201552170986365931074471437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134368113990910620716314291 201552170986365931074471437)
              ·
                refine ⟨75582064119887224152926789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201552170986365931074471437 75582064119887224152926789)
                ·
                  refine ⟨14171637022478854528673773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75582064119887224152926789 14171637022478854528673773)
                  ·
                    refine ⟨5314363883429570448252665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14171637022478854528673773 5314363883429570448252665)
                    ·
                      refine ⟨3985772912572177836189499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5314363883429570448252665 3985772912572177836189499)
                      ·
                        rfl

theorem cell23_7762265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 3, 2].length) (baseStart_7762265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762265 prefixEnd_7762265 := by exact prefixLift 7762265
  have htrace : WordTrace (prefixWord ++ tailWord_7762265) baseStart_7762265 baseEnd_7762265 := by
    simpa [prefixWord, tailWord_7762265, baseEnd_7762265] using wordTrace_append hprefix tailTrace_7762265
  have hstable : (prefixWord ++ tailWord_7762265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762265).length < 2 ^ (prefixWord ++ tailWord_7762265).sum := by decide
  have hdescent : baseEnd_7762265 < baseStart_7762265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762282 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 1, 5, 2]
def baseStart_7762282 : Nat := 118140960795 + 7762282 * 2 ^ 59
def prefixEnd_7762282 : Nat := 4983230072969 + 3 ^ 40 * 7762282 * 2
def baseEnd_7762282 : Nat := 3985781641743304269676921

theorem tailTrace_7762282 : CollatzResearch.WordTrace tailWord_7762282 prefixEnd_7762282 3985781641743304269676921 := by
  unfold tailWord_7762282
  simp only [CollatzResearch.WordTrace]
  refine ⟨70778420816146370266740275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188742455509723654044640733 70778420816146370266740275)
  ·
    refine ⟨106167631224219555400110413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70778420816146370266740275 106167631224219555400110413)
    ·
      refine ⟨39812861709082333275041405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106167631224219555400110413 39812861709082333275041405)
      ·
        refine ⟨14929823140905874978140527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39812861709082333275041405 14929823140905874978140527)
        ·
          refine ⟨22394734711358812467210791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14929823140905874978140527 22394734711358812467210791)
          ·
            refine ⟨33592102067038218700816187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22394734711358812467210791 33592102067038218700816187)
            ·
              refine ⟨50388153100557328051224281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33592102067038218700816187 50388153100557328051224281)
              ·
                refine ⟨37791114825417996038418211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50388153100557328051224281 37791114825417996038418211)
                ·
                  refine ⟨56686672238126994057627317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37791114825417996038418211 56686672238126994057627317)
                  ·
                    refine ⟨5314375522324405692902561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56686672238126994057627317 5314375522324405692902561)
                    ·
                      refine ⟨3985781641743304269676921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5314375522324405692902561 3985781641743304269676921)
                      ·
                        rfl

theorem cell23_7762282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_7762282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762282 prefixEnd_7762282 := by exact prefixLift 7762282
  have htrace : WordTrace (prefixWord ++ tailWord_7762282) baseStart_7762282 baseEnd_7762282 := by
    simpa [prefixWord, tailWord_7762282, baseEnd_7762282] using wordTrace_append hprefix tailTrace_7762282
  have hstable : (prefixWord ++ tailWord_7762282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762282).length < 2 ^ (prefixWord ++ tailWord_7762282).sum := by decide
  have hdescent : baseEnd_7762282 < baseStart_7762282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762315 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 5]
def baseStart_7762315 : Nat := 118140960795 + 7762315 * 2 ^ 59
def prefixEnd_7762315 : Nat := 4983230072969 + 3 ^ 40 * 7762315 * 2
def baseEnd_7762315 : Nat := 3985798586604902640564269

theorem tailTrace_7762315 : CollatzResearch.WordTrace tailWord_7762315 prefixEnd_7762315 3985798586604902640564269 := by
  unfold tailWord_7762315
  simp only [CollatzResearch.WordTrace]
  refine ⟨283114886873465927702912399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188743257915643951801941599 283114886873465927702912399)
  ·
    refine ⟨424672330310198891554368599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283114886873465927702912399 424672330310198891554368599)
    ·
      refine ⟨637008495465298337331552899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424672330310198891554368599 637008495465298337331552899)
      ·
        refine ⟨955512743197947505997329349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637008495465298337331552899 955512743197947505997329349)
        ·
          refine ⟨179158639349615157374499253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 955512743197947505997329349 179158639349615157374499253)
          ·
            refine ⟨16796122439026421003859305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179158639349615157374499253 16796122439026421003859305)
            ·
              refine ⟨12597091829269815752894479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16796122439026421003859305 12597091829269815752894479)
              ·
                refine ⟨18895637743904723629341719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12597091829269815752894479 18895637743904723629341719)
                ·
                  refine ⟨28343456615857085444012579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18895637743904723629341719 28343456615857085444012579)
                  ·
                    refine ⟨42515184923785628166018869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28343456615857085444012579 42515184923785628166018869)
                    ·
                      refine ⟨3985798586604902640564269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42515184923785628166018869 3985798586604902640564269)
                      ·
                        rfl

theorem cell23_7762315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 5].length) (baseStart_7762315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762315 prefixEnd_7762315 := by exact prefixLift 7762315
  have htrace : WordTrace (prefixWord ++ tailWord_7762315) baseStart_7762315 baseEnd_7762315 := by
    simpa [prefixWord, tailWord_7762315, baseEnd_7762315] using wordTrace_append hprefix tailTrace_7762315
  have hstable : (prefixWord ++ tailWord_7762315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762315).length < 2 ^ (prefixWord ++ tailWord_7762315).sum := by decide
  have hdescent : baseEnd_7762315 < baseStart_7762315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762339 : List Nat := [1, 1, 1, 4, 1, 6, 2, 1, 2, 4]
def baseStart_7762339 : Nat := 118140960795 + 7762339 * 2 ^ 59
def prefixEnd_7762339 : Nat := 4983230072969 + 3 ^ 40 * 7762339 * 2
def baseEnd_7762339 : Nat := 1328603636713536848888053

theorem tailTrace_7762339 : CollatzResearch.WordTrace tailWord_7762339 prefixEnd_7762339 1328603636713536848888053 := by
  unfold tailWord_7762339
  simp only [CollatzResearch.WordTrace]
  refine ⟨283115762225378979801786071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188743841483585986534524047 283115762225378979801786071)
  ·
    refine ⟨424673643338068469702679107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283115762225378979801786071 424673643338068469702679107)
    ·
      refine ⟨637010465007102704554018661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424673643338068469702679107 637010465007102704554018661)
      ·
        refine ⟨119439462188831757103878499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 637010465007102704554018661 119439462188831757103878499)
        ·
          refine ⟨179159193283247635655817749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119439462188831757103878499 179159193283247635655817749)
          ·
            refine ⟨8398087185152232921366457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 179159193283247635655817749 8398087185152232921366457)
            ·
              refine ⟨6298565388864174691024843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8398087185152232921366457 6298565388864174691024843)
              ·
                refine ⟨9447848083296262036537265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6298565388864174691024843 9447848083296262036537265)
                ·
                  refine ⟨7085886062472196527402949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9447848083296262036537265 7085886062472196527402949)
                  ·
                    refine ⟨1328603636713536848888053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7085886062472196527402949 1328603636713536848888053)
                    ·
                      rfl

theorem cell23_7762339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 2, 4].length) (baseStart_7762339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762339 prefixEnd_7762339 := by exact prefixLift 7762339
  have htrace : WordTrace (prefixWord ++ tailWord_7762339) baseStart_7762339 baseEnd_7762339 := by
    simpa [prefixWord, tailWord_7762339, baseEnd_7762339] using wordTrace_append hprefix tailTrace_7762339
  have hstable : (prefixWord ++ tailWord_7762339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762339).length < 2 ^ (prefixWord ++ tailWord_7762339).sum := by decide
  have hdescent : baseEnd_7762339 < baseStart_7762339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762346 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_7762346 : Nat := 118140960795 + 7762346 * 2 ^ 59
def prefixEnd_7762346 : Nat := 4983230072969 + 3 ^ 40 * 7762346 * 2
def baseEnd_7762346 : Nat := 3985814504505192019276627

theorem tailTrace_7762346 : CollatzResearch.WordTrace tailWord_7762346 prefixEnd_7762346 3985814504505192019276627 := by
  unfold tailWord_7762346
  simp only [CollatzResearch.WordTrace]
  refine ⟨70779004384088404999322723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188744011690902413331527261 70779004384088404999322723)
  ·
    refine ⟨106168506576132607498984085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70779004384088404999322723 106168506576132607498984085)
    ·
      refine ⟨4976648745756215976514879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106168506576132607498984085 4976648745756215976514879)
      ·
        refine ⟨7464973118634323964772319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4976648745756215976514879 7464973118634323964772319)
        ·
          refine ⟨11197459677951485947158479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7464973118634323964772319 11197459677951485947158479)
          ·
            refine ⟨16796189516927228920737719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11197459677951485947158479 16796189516927228920737719)
            ·
              refine ⟨25194284275390843381106579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16796189516927228920737719 25194284275390843381106579)
              ·
                refine ⟨37791426413086265071659869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25194284275390843381106579 37791426413086265071659869)
                ·
                  refine ⟨14171784904907349401872451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37791426413086265071659869 14171784904907349401872451)
                  ·
                    refine ⟨21257677357361024102808677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14171784904907349401872451 21257677357361024102808677)
                    ·
                      refine ⟨3985814504505192019276627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21257677357361024102808677 3985814504505192019276627)
                      ·
                        rfl

theorem cell23_7762346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_7762346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762346 prefixEnd_7762346 := by exact prefixLift 7762346
  have htrace : WordTrace (prefixWord ++ tailWord_7762346) baseStart_7762346 baseEnd_7762346 := by
    simpa [prefixWord, tailWord_7762346, baseEnd_7762346] using wordTrace_append hprefix tailTrace_7762346
  have hstable : (prefixWord ++ tailWord_7762346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762346).length < 2 ^ (prefixWord ++ tailWord_7762346).sum := by decide
  have hdescent : baseEnd_7762346 < baseStart_7762346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762349 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_7762349 : Nat := 118140960795 + 7762349 * 2 ^ 59
def prefixEnd_7762349 : Nat := 4983230072969 + 3 ^ 40 * 7762349 * 2
def baseEnd_7762349 : Nat := 3985816044947155507539113

theorem tailTrace_7762349 : CollatzResearch.WordTrace tailWord_7762349 prefixEnd_7762349 3985816044947155507539113 := by
  unfold tailWord_7762349
  simp only [CollatzResearch.WordTrace]
  refine ⟨283116126955342751509650101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188744084636895167673100067 283116126955342751509650101)
  ·
    refine ⟨26542136902063382954029697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 283116126955342751509650101 26542136902063382954029697)
    ·
      refine ⟨19906602676547537215522273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26542136902063382954029697 19906602676547537215522273)
      ·
        refine ⟨14929952007410652911641705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19906602676547537215522273 14929952007410652911641705)
        ·
          refine ⟨11197464005557989683731279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14929952007410652911641705 11197464005557989683731279)
          ·
            refine ⟨16796196008336984525596919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11197464005557989683731279 16796196008336984525596919)
            ·
              refine ⟨25194294012505476788395379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16796196008336984525596919 25194294012505476788395379)
              ·
                refine ⟨37791441018758215182593069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25194294012505476788395379 37791441018758215182593069)
                ·
                  refine ⟨14171790382034330693472401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37791441018758215182593069 14171790382034330693472401)
                  ·
                    refine ⟨10628842786525748020104301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14171790382034330693472401 10628842786525748020104301)
                    ·
                      refine ⟨3985816044947155507539113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10628842786525748020104301 3985816044947155507539113)
                      ·
                        rfl

theorem cell23_7762349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_7762349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762349 prefixEnd_7762349 := by exact prefixLift 7762349
  have htrace : WordTrace (prefixWord ++ tailWord_7762349) baseStart_7762349 baseEnd_7762349 := by
    simpa [prefixWord, tailWord_7762349, baseEnd_7762349] using wordTrace_append hprefix tailTrace_7762349
  have hstable : (prefixWord ++ tailWord_7762349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762349).length < 2 ^ (prefixWord ++ tailWord_7762349).sum := by decide
  have hdescent : baseEnd_7762349 < baseStart_7762349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762369 : List Nat := [1, 2, 7, 1, 2, 10]
def baseStart_7762369 : Nat := 118140960795 + 7762369 * 2 ^ 59
def prefixEnd_7762369 : Nat := 4983230072969 + 3 ^ 40 * 7762369 * 2
def baseEnd_7762369 : Nat := 16402577426173849503247

theorem tailTrace_7762369 : CollatzResearch.WordTrace tailWord_7762369 prefixEnd_7762369 16402577426173849503247 := by
  unfold tailWord_7762369
  simp only [CollatzResearch.WordTrace]
  refine ⟨283116856415270294925378161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188744570943513529950252107 283116856415270294925378161)
  ·
    refine ⟨212337642311452721194033621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283116856415270294925378161 212337642311452721194033621)
    ·
      refine ⟨4976663491674673152985163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 212337642311452721194033621 4976663491674673152985163)
      ·
        refine ⟨7464995237512009729477745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4976663491674673152985163 7464995237512009729477745)
        ·
          refine ⟨5598746428134007297108309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7464995237512009729477745 5598746428134007297108309)
          ·
            refine ⟨16402577426173849503247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5598746428134007297108309 16402577426173849503247)
            ·
              rfl

theorem cell23_7762369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 10].length) (baseStart_7762369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762369 prefixEnd_7762369 := by exact prefixLift 7762369
  have htrace : WordTrace (prefixWord ++ tailWord_7762369) baseStart_7762369 baseEnd_7762369 := by
    simpa [prefixWord, tailWord_7762369, baseEnd_7762369] using wordTrace_append hprefix tailTrace_7762369
  have hstable : (prefixWord ++ tailWord_7762369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762369).length < 2 ^ (prefixWord ++ tailWord_7762369).sum := by decide
  have hdescent : baseEnd_7762369 < baseStart_7762369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762380 : List Nat := [2, 2, 1, 4, 3, 2, 2, 2, 1, 2, 2]
def baseStart_7762380 : Nat := 118140960795 + 7762380 * 2 ^ 59
def prefixEnd_7762380 : Nat := 4983230072969 + 3 ^ 40 * 7762380 * 2
def baseEnd_7762380 : Nat := 3985831962847444886251471

theorem tailTrace_7762380 : CollatzResearch.WordTrace tailWord_7762380 prefixEnd_7762380 3985831962847444886251471 := by
  unfold tailWord_7762380
  simp only [CollatzResearch.WordTrace]
  refine ⟨141558628809115221902014297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188744838412153629202685729 141558628809115221902014297)
  ·
    refine ⟨106168971606836416426510723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141558628809115221902014297 106168971606836416426510723)
    ·
      refine ⟨159253457410254624639766085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106168971606836416426510723 159253457410254624639766085)
      ·
        refine ⟨29860023264422742119956141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159253457410254624639766085 29860023264422742119956141)
        ·
          refine ⟨11197508724158528294983553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29860023264422742119956141 11197508724158528294983553)
          ·
            refine ⟨8398131543118896221237665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11197508724158528294983553 8398131543118896221237665)
            ·
              refine ⟨6298598657339172165928249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8398131543118896221237665 6298598657339172165928249)
              ·
                refine ⟨4723948993004379124446187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6298598657339172165928249 4723948993004379124446187)
                ·
                  refine ⟨7085923489506568686669281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723948993004379124446187 7085923489506568686669281)
                  ·
                    refine ⟨5314442617129926515001961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7085923489506568686669281 5314442617129926515001961)
                    ·
                      refine ⟨3985831962847444886251471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5314442617129926515001961 3985831962847444886251471)
                      ·
                        rfl

theorem cell23_7762380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_7762380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762380 prefixEnd_7762380 := by exact prefixLift 7762380
  have htrace : WordTrace (prefixWord ++ tailWord_7762380) baseStart_7762380 baseEnd_7762380 := by
    simpa [prefixWord, tailWord_7762380, baseEnd_7762380] using wordTrace_append hprefix tailTrace_7762380
  have hstable : (prefixWord ++ tailWord_7762380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762380).length < 2 ^ (prefixWord ++ tailWord_7762380).sum := by decide
  have hdescent : baseEnd_7762380 < baseStart_7762380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762435 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 3]
def baseStart_7762435 : Nat := 118140960795 + 7762435 * 2 ^ 59
def prefixEnd_7762435 : Nat := 4983230072969 + 3 ^ 40 * 7762435 * 2
def baseEnd_7762435 : Nat := 3985860204283442171063717

theorem tailTrace_7762435 : CollatzResearch.WordTrace tailWord_7762435 prefixEnd_7762435 3985860204283442171063717 := by
  unfold tailWord_7762435
  simp only [CollatzResearch.WordTrace]
  refine ⟨283119263633031188197280759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188746175755354125464853839 283119263633031188197280759)
  ·
    refine ⟨424678895449546782295921139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283119263633031188197280759 424678895449546782295921139)
    ·
      refine ⟨637018343174320173443881709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424678895449546782295921139 637018343174320173443881709)
      ·
        refine ⟨238881878690370065041455641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 637018343174320173443881709 238881878690370065041455641)
        ·
          refine ⟨179161409017777548781091731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238881878690370065041455641 179161409017777548781091731)
          ·
            refine ⟨268742113526666323171637597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179161409017777548781091731 268742113526666323171637597)
            ·
              refine ⟨100778292572499871189364099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268742113526666323171637597 100778292572499871189364099)
              ·
                refine ⟨151167438858749806784046149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100778292572499871189364099 151167438858749806784046149)
                ·
                  refine ⟨28343894786015588772008653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151167438858749806784046149 28343894786015588772008653)
                  ·
                    refine ⟨10628960544755845789503245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28343894786015588772008653 10628960544755845789503245)
                    ·
                      refine ⟨3985860204283442171063717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10628960544755845789503245 3985860204283442171063717)
                      ·
                        rfl

theorem cell23_7762435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_7762435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762435 prefixEnd_7762435 := by exact prefixLift 7762435
  have htrace : WordTrace (prefixWord ++ tailWord_7762435) baseStart_7762435 baseEnd_7762435 := by
    simpa [prefixWord, tailWord_7762435, baseEnd_7762435] using wordTrace_append hprefix tailTrace_7762435
  have hstable : (prefixWord ++ tailWord_7762435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762435).length < 2 ^ (prefixWord ++ tailWord_7762435).sum := by decide
  have hdescent : baseEnd_7762435 < baseStart_7762435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762436 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 4, 2, 2]
def baseStart_7762436 : Nat := 118140960795 + 7762436 * 2 ^ 59
def prefixEnd_7762436 : Nat := 4983230072969 + 3 ^ 40 * 7762436 * 2
def baseEnd_7762436 : Nat := 3985860717764096667151213

theorem tailTrace_7762436 : CollatzResearch.WordTrace tailWord_7762436 prefixEnd_7762436 3985860717764096667151213 := by
  unfold tailWord_7762436
  simp only [CollatzResearch.WordTrace]
  refine ⟨141559650053013782684033581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188746200070685043578711441 141559650053013782684033581)
  ·
    refine ⟨53084868769880168506512593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141559650053013782684033581 53084868769880168506512593)
    ·
      refine ⟨39813651577410126379884445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53084868769880168506512593 39813651577410126379884445)
      ·
        refine ⟨14930119341528797392456667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39813651577410126379884445 14930119341528797392456667)
        ·
          refine ⟨22395179012293196088685001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14930119341528797392456667 22395179012293196088685001)
          ·
            refine ⟨16796384259219897066513751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22395179012293196088685001 16796384259219897066513751)
            ·
              refine ⟨25194576388829845599770627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16796384259219897066513751 25194576388829845599770627)
              ·
                refine ⟨37791864583244768399655941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25194576388829845599770627 37791864583244768399655941)
                ·
                  refine ⟨7085974609358394074935489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37791864583244768399655941 7085974609358394074935489)
                  ·
                    refine ⟨5314480957018795556201617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7085974609358394074935489 5314480957018795556201617)
                    ·
                      refine ⟨3985860717764096667151213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5314480957018795556201617 3985860717764096667151213)
                      ·
                        rfl

theorem cell23_7762436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_7762436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762436 prefixEnd_7762436 := by exact prefixLift 7762436
  have htrace : WordTrace (prefixWord ++ tailWord_7762436) baseStart_7762436 baseEnd_7762436 := by
    simpa [prefixWord, tailWord_7762436, baseEnd_7762436] using wordTrace_append hprefix tailTrace_7762436
  have hstable : (prefixWord ++ tailWord_7762436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762436).length < 2 ^ (prefixWord ++ tailWord_7762436).sum := by decide
  have hdescent : baseEnd_7762436 < baseStart_7762436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762442 : List Nat := [3, 1, 2, 2, 2, 1, 1, 6, 5]
def baseStart_7762442 : Nat := 118140960795 + 7762442 * 2 ^ 59
def prefixEnd_7762442 : Nat := 4983230072969 + 3 ^ 40 * 7762442 * 2
def baseEnd_7762442 : Nat := 442873755405335960408465

theorem tailTrace_7762442 : CollatzResearch.WordTrace tailWord_7762442 prefixEnd_7762442 442873755405335960408465 := by
  unfold tailWord_7762442
  simp only [CollatzResearch.WordTrace]
  refine ⟨70779879736001457098196395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188746345962670552261857053 70779879736001457098196395)
  ·
    refine ⟨106169819604002185647294593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70779879736001457098196395 106169819604002185647294593)
    ·
      refine ⟨79627364703001639235470945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106169819604002185647294593 79627364703001639235470945)
      ·
        refine ⟨59720523527251229426603209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79627364703001639235470945 59720523527251229426603209)
        ·
          refine ⟨44790392645438422069952407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59720523527251229426603209 44790392645438422069952407)
          ·
            refine ⟨67185588968157633104928611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44790392645438422069952407 67185588968157633104928611)
            ·
              refine ⟨100778383452236449657392917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67185588968157633104928611 100778383452236449657392917)
              ·
                refine ⟨4723986724323583577690293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100778383452236449657392917 4723986724323583577690293)
                ·
                  refine ⟨442873755405335960408465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4723986724323583577690293 442873755405335960408465)
                  ·
                    rfl

theorem cell23_7762442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 5].length) (baseStart_7762442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762442 prefixEnd_7762442 := by exact prefixLift 7762442
  have htrace : WordTrace (prefixWord ++ tailWord_7762442) baseStart_7762442 baseEnd_7762442 := by
    simpa [prefixWord, tailWord_7762442, baseEnd_7762442] using wordTrace_append hprefix tailTrace_7762442
  have hstable : (prefixWord ++ tailWord_7762442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762442).length < 2 ^ (prefixWord ++ tailWord_7762442).sum := by decide
  have hdescent : baseEnd_7762442 < baseStart_7762442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762472 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 1, 7]
def baseStart_7762472 : Nat := 118140960795 + 7762472 * 2 ^ 59
def prefixEnd_7762472 : Nat := 4983230072969 + 3 ^ 40 * 7762472 * 2
def baseEnd_7762472 : Nat := 1328626401022552842100349

theorem tailTrace_7762472 : CollatzResearch.WordTrace tailWord_7762472 prefixEnd_7762472 1328626401022552842100349 := by
  unfold tailWord_7762472
  simp only [CollatzResearch.WordTrace]
  refine ⟨141560306566948571758188835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188747075422598095677585113 141560306566948571758188835)
  ·
    refine ⟨212340459850422857637283253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141560306566948571758188835 212340459850422857637283253)
    ·
      refine ⟨19906918110977142903495305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212340459850422857637283253 19906918110977142903495305)
      ·
        refine ⟨14930188583232857177621479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19906918110977142903495305 14930188583232857177621479)
        ·
          refine ⟨22395282874849285766432219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14930188583232857177621479 22395282874849285766432219)
          ·
            refine ⟨33592924312273928649648329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22395282874849285766432219 33592924312273928649648329)
            ·
              refine ⟨25194693234205446487236247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33592924312273928649648329 25194693234205446487236247)
              ·
                refine ⟨37792039851308169730854371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25194693234205446487236247 37792039851308169730854371)
                ·
                  refine ⟨56688059776962254596281557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37792039851308169730854371 56688059776962254596281557)
                  ·
                    refine ⟨1328626401022552842100349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56688059776962254596281557 1328626401022552842100349)
                    ·
                      rfl

theorem cell23_7762472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_7762472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762472 prefixEnd_7762472 := by exact prefixLift 7762472
  have htrace : WordTrace (prefixWord ++ tailWord_7762472) baseStart_7762472 baseEnd_7762472 := by
    simpa [prefixWord, tailWord_7762472, baseEnd_7762472] using wordTrace_append hprefix tailTrace_7762472
  have hstable : (prefixWord ++ tailWord_7762472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762472).length < 2 ^ (prefixWord ++ tailWord_7762472).sum := by decide
  have hdescent : baseEnd_7762472 < baseStart_7762472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762475 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 4]
def baseStart_7762475 : Nat := 118140960795 + 7762475 * 2 ^ 59
def prefixEnd_7762475 : Nat := 4983230072969 + 3 ^ 40 * 7762475 * 2
def baseEnd_7762475 : Nat := 3985880743509622014563533

theorem tailTrace_7762475 : CollatzResearch.WordTrace tailWord_7762475 prefixEnd_7762475 3985880743509622014563533 := by
  unfold tailWord_7762475
  simp only [CollatzResearch.WordTrace]
  refine ⟨283120722552886275028736879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188747148368590850019157919 283120722552886275028736879)
  ·
    refine ⟨424681083829329412543105319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283120722552886275028736879 424681083829329412543105319)
    ·
      refine ⟨637021625743994118814657979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424681083829329412543105319 637021625743994118814657979)
      ·
        refine ⟨955532438615991178221986969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637021625743994118814657979 955532438615991178221986969)
        ·
          refine ⟨716649328961993383666490227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 955532438615991178221986969 716649328961993383666490227)
          ·
            refine ⟨1074973993442990075499735341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716649328961993383666490227 1074973993442990075499735341)
            ·
              refine ⟨403115247541121278312400753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1074973993442990075499735341 403115247541121278312400753)
              ·
                refine ⟨302336435655840958734300565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403115247541121278312400753 302336435655840958734300565)
                ·
                  refine ⟨14172020421367544940670339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 302336435655840958734300565 14172020421367544940670339)
                  ·
                    refine ⟨21258030632051317411005509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14172020421367544940670339 21258030632051317411005509)
                    ·
                      refine ⟨3985880743509622014563533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21258030632051317411005509 3985880743509622014563533)
                      ·
                        rfl

theorem cell23_7762475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 4].length) (baseStart_7762475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762475 prefixEnd_7762475 := by exact prefixLift 7762475
  have htrace : WordTrace (prefixWord ++ tailWord_7762475) baseStart_7762475 baseEnd_7762475 := by
    simpa [prefixWord, tailWord_7762475, baseEnd_7762475] using wordTrace_append hprefix tailTrace_7762475
  have hstable : (prefixWord ++ tailWord_7762475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762475).length < 2 ^ (prefixWord ++ tailWord_7762475).sum := by decide
  have hdescent : baseEnd_7762475 < baseStart_7762475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762492 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_7762492 : Nat := 118140960795 + 7762492 * 2 ^ 59
def prefixEnd_7762492 : Nat := 4983230072969 + 3 ^ 40 * 7762492 * 2
def baseEnd_7762492 : Nat := 3985889472680748448050955

theorem tailTrace_7762492 : CollatzResearch.WordTrace tailWord_7762492 prefixEnd_7762492 3985889472680748448050955 := by
  unfold tailWord_7762492
  simp only [CollatzResearch.WordTrace]
  refine ⟨141560671296912343466052865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188747561729216457954737153 141560671296912343466052865)
  ·
    refine ⟨106170503472684257599539649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141560671296912343466052865 106170503472684257599539649)
    ·
      refine ⟨79627877604513193199654737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106170503472684257599539649 79627877604513193199654737)
      ·
        refine ⟨59720908203384894899741053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79627877604513193199654737 59720908203384894899741053)
        ·
          refine ⟨22395340576269335587402895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59720908203384894899741053 22395340576269335587402895)
          ·
            refine ⟨33593010864404003381104343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22395340576269335587402895 33593010864404003381104343)
            ·
              refine ⟨50389516296606005071656515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33593010864404003381104343 50389516296606005071656515)
              ·
                refine ⟨75584274444909007607484773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50389516296606005071656515 75584274444909007607484773)
                ·
                  refine ⟨14172051458420438926403395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75584274444909007607484773 14172051458420438926403395)
                  ·
                    refine ⟨21258077187630658389605093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14172051458420438926403395 21258077187630658389605093)
                    ·
                      refine ⟨3985889472680748448050955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21258077187630658389605093 3985889472680748448050955)
                      ·
                        rfl

theorem cell23_7762492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_7762492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762492 prefixEnd_7762492 := by exact prefixLift 7762492
  have htrace : WordTrace (prefixWord ++ tailWord_7762492) baseStart_7762492 baseEnd_7762492 := by
    simpa [prefixWord, tailWord_7762492, baseEnd_7762492] using wordTrace_append hprefix tailTrace_7762492
  have hstable : (prefixWord ++ tailWord_7762492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762492).length < 2 ^ (prefixWord ++ tailWord_7762492).sum := by decide
  have hdescent : baseEnd_7762492 < baseStart_7762492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762529 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 2, 2, 3]
def baseStart_7762529 : Nat := 118140960795 + 7762529 * 2 ^ 59
def prefixEnd_7762529 : Nat := 4983230072969 + 3 ^ 40 * 7762529 * 2
def baseEnd_7762529 : Nat := 3985908471464964803288285

theorem tailTrace_7762529 : CollatzResearch.WordTrace tailWord_7762529 prefixEnd_7762529 3985908471464964803288285 := by
  unfold tailWord_7762529
  simp only [CollatzResearch.WordTrace]
  refine ⟨283122692094690642251202641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188748461396460428167468427 283122692094690642251202641)
  ·
    refine ⟨212342019071017981688401981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283122692094690642251202641 212342019071017981688401981)
    ·
      refine ⟨79628257151631743133150743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212342019071017981688401981 79628257151631743133150743)
      ·
        refine ⟨119442385727447614699726115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79628257151631743133150743 119442385727447614699726115)
        ·
          refine ⟨179163578591171422049589173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119442385727447614699726115 179163578591171422049589173)
          ·
            refine ⟨16796585492922320817148985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179163578591171422049589173 16796585492922320817148985)
            ·
              refine ⟨12597439119691740612861739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16796585492922320817148985 12597439119691740612861739)
              ·
                refine ⟨18896158679537610919292609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12597439119691740612861739 18896158679537610919292609)
                ·
                  refine ⟨14172119009653208189469457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18896158679537610919292609 14172119009653208189469457)
                  ·
                    refine ⟨10629089257239906142102093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14172119009653208189469457 10629089257239906142102093)
                    ·
                      refine ⟨3985908471464964803288285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10629089257239906142102093 3985908471464964803288285)
                      ·
                        rfl

theorem cell23_7762529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_7762529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762529 prefixEnd_7762529 := by exact prefixLift 7762529
  have htrace : WordTrace (prefixWord ++ tailWord_7762529) baseStart_7762529 baseEnd_7762529 := by
    simpa [prefixWord, tailWord_7762529, baseEnd_7762529] using wordTrace_append hprefix tailTrace_7762529
  have hstable : (prefixWord ++ tailWord_7762529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762529).length < 2 ^ (prefixWord ++ tailWord_7762529).sum := by decide
  have hdescent : baseEnd_7762529 < baseStart_7762529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762535 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_7762535 : Nat := 118140960795 + 7762535 * 2 ^ 59
def prefixEnd_7762535 : Nat := 4983230072969 + 3 ^ 40 * 7762535 * 2
def baseEnd_7762535 : Nat := 3985911552348891779813257

theorem tailTrace_7762535 : CollatzResearch.WordTrace tailWord_7762535 prefixEnd_7762535 3985911552348891779813257 := by
  unfold tailWord_7762535
  simp only [CollatzResearch.WordTrace]
  refine ⟨283122910932668905275921059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188748607288445936850614039 283122910932668905275921059)
  ·
    refine ⟨424684366399003357913881589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283122910932668905275921059 424684366399003357913881589)
    ·
      refine ⟨39814159349906564804426399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 424684366399003357913881589 39814159349906564804426399)
      ·
        refine ⟨59721239024859847206639599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39814159349906564804426399 59721239024859847206639599)
        ·
          refine ⟨89581858537289770809959399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59721239024859847206639599 89581858537289770809959399)
          ·
            refine ⟨134372787805934656214939099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89581858537289770809959399 134372787805934656214939099)
            ·
              refine ⟨201559181708901984322408649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134372787805934656214939099 201559181708901984322408649)
              ·
                refine ⟨151169386281676488241806487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201559181708901984322408649 151169386281676488241806487)
                ·
                  refine ⟨226754079422514732362709731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151169386281676488241806487 226754079422514732362709731)
                  ·
                    refine ⟨340131119133772098544064597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 226754079422514732362709731 340131119133772098544064597)
                    ·
                      refine ⟨3985911552348891779813257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 340131119133772098544064597 3985911552348891779813257)
                      ·
                        rfl

theorem cell23_7762535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_7762535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762535 prefixEnd_7762535 := by exact prefixLift 7762535
  have htrace : WordTrace (prefixWord ++ tailWord_7762535) baseStart_7762535 baseEnd_7762535 := by
    simpa [prefixWord, tailWord_7762535, baseEnd_7762535] using wordTrace_append hprefix tailTrace_7762535
  have hstable : (prefixWord ++ tailWord_7762535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762535).length < 2 ^ (prefixWord ++ tailWord_7762535).sum := by decide
  have hdescent : baseEnd_7762535 < baseStart_7762535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762553 : List Nat := [1, 2, 1, 3, 3, 4, 2, 2, 1, 4]
def baseStart_7762553 : Nat := 118140960795 + 7762553 * 2 ^ 59
def prefixEnd_7762553 : Nat := 4983230072969 + 3 ^ 40 * 7762553 * 2
def baseEnd_7762553 : Nat := 1328640265000224236462725

theorem tailTrace_7762553 : CollatzResearch.WordTrace tailWord_7762553 prefixEnd_7762553 1328640265000224236462725 := by
  unfold tailWord_7762553
  simp only [CollatzResearch.WordTrace]
  refine ⟨283123567446603694350076313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188749044964402462900050875 283123567446603694350076313)
  ·
    refine ⟨212342675584952770762557235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283123567446603694350076313 212342675584952770762557235)
    ·
      refine ⟨318514013377429156143835853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212342675584952770762557235 318514013377429156143835853)
      ·
        refine ⟨119442755016535933553938445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318514013377429156143835853 119442755016535933553938445)
        ·
          refine ⟨44791033131200975082726917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119442755016535933553938445 44791033131200975082726917)
          ·
            refine ⟨8398318712100182828011297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44791033131200975082726917 8398318712100182828011297)
            ·
              refine ⟨6298739034075137121008473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8398318712100182828011297 6298739034075137121008473)
              ·
                refine ⟨4724054275556352840756355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6298739034075137121008473 4724054275556352840756355)
                ·
                  refine ⟨7086081413334529261134533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4724054275556352840756355 7086081413334529261134533)
                  ·
                    refine ⟨1328640265000224236462725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7086081413334529261134533 1328640265000224236462725)
                    ·
                      rfl

theorem cell23_7762553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 1, 4].length) (baseStart_7762553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762553 prefixEnd_7762553 := by exact prefixLift 7762553
  have htrace : WordTrace (prefixWord ++ tailWord_7762553) baseStart_7762553 baseEnd_7762553 := by
    simpa [prefixWord, tailWord_7762553, baseEnd_7762553] using wordTrace_append hprefix tailTrace_7762553
  have hstable : (prefixWord ++ tailWord_7762553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762553).length < 2 ^ (prefixWord ++ tailWord_7762553).sum := by decide
  have hdescent : baseEnd_7762553 < baseStart_7762553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762575 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 5, 6]
def baseStart_7762575 : Nat := 118140960795 + 7762575 * 2 ^ 59
def prefixEnd_7762575 : Nat := 4983230072969 + 3 ^ 40 * 7762575 * 2
def baseEnd_7762575 : Nat := 1328644030525023874437691

theorem tailTrace_7762575 : CollatzResearch.WordTrace tailWord_7762575 prefixEnd_7762575 1328644030525023874437691 := by
  unfold tailWord_7762575
  simp only [CollatzResearch.WordTrace]
  refine ⟨283124369852523992107377179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188749579901682661404918119 283124369852523992107377179)
  ·
    refine ⟨424686554778785988161065769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283124369852523992107377179 424686554778785988161065769)
    ·
      refine ⟨318514916084089491120799327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424686554778785988161065769 318514916084089491120799327)
      ·
        refine ⟨477772374126134236681198991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318514916084089491120799327 477772374126134236681198991)
        ·
          refine ⟨716658561189201355021798487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477772374126134236681198991 716658561189201355021798487)
          ·
            refine ⟨1074987841783802032532697731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716658561189201355021798487 1074987841783802032532697731)
            ·
              refine ⟨1612481762675703048799046597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074987841783802032532697731 1612481762675703048799046597)
              ·
                refine ⟨302340330501694321649821237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1612481762675703048799046597 302340330501694321649821237)
                ·
                  refine ⟨28344405984533842654670741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 302340330501694321649821237 28344405984533842654670741)
                  ·
                    refine ⟨1328644030525023874437691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28344405984533842654670741 1328644030525023874437691)
                    ·
                      rfl

theorem cell23_7762575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 6].length) (baseStart_7762575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762575 prefixEnd_7762575 := by exact prefixLift 7762575
  have htrace : WordTrace (prefixWord ++ tailWord_7762575) baseStart_7762575 baseEnd_7762575 := by
    simpa [prefixWord, tailWord_7762575, baseEnd_7762575] using wordTrace_append hprefix tailTrace_7762575
  have hstable : (prefixWord ++ tailWord_7762575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762575).length < 2 ^ (prefixWord ++ tailWord_7762575).sum := by decide
  have hdescent : baseEnd_7762575 < baseStart_7762575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762622 : List Nat := [4, 2, 1, 1, 2, 1, 2, 10]
def baseStart_7762622 : Nat := 118140960795 + 7762622 * 2 ^ 59
def prefixEnd_7762622 : Nat := 4983230072969 + 3 ^ 40 * 7762622 * 2
def baseEnd_7762622 : Nat := 147628008339475294052791

theorem tailTrace_7762622 : CollatzResearch.WordTrace tailWord_7762622 prefixEnd_7762622 147628008339475294052791 := by
  unfold tailWord_7762622
  simp only [CollatzResearch.WordTrace]
  refine ⟨35390760510419214891792265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188750722722235812756225413 35390760510419214891792265)
  ·
    refine ⟨26543070382814411168844199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35390760510419214891792265 26543070382814411168844199)
    ·
      refine ⟨39814605574221616753266299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26543070382814411168844199 39814605574221616753266299)
      ·
        refine ⟨59721908361332425129899449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39814605574221616753266299 59721908361332425129899449)
        ·
          refine ⟨44791431270999318847424587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59721908361332425129899449 44791431270999318847424587)
          ·
            refine ⟨67187146906498978271136881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44791431270999318847424587 67187146906498978271136881)
            ·
              refine ⟨50390360179874233703352661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67187146906498978271136881 50390360179874233703352661)
              ·
                refine ⟨147628008339475294052791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50390360179874233703352661 147628008339475294052791)
                ·
                  rfl

theorem cell23_7762622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 10].length) (baseStart_7762622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762622 prefixEnd_7762622 := by exact prefixLift 7762622
  have htrace : WordTrace (prefixWord ++ tailWord_7762622) baseStart_7762622 baseEnd_7762622 := by
    simpa [prefixWord, tailWord_7762622, baseEnd_7762622] using wordTrace_append hprefix tailTrace_7762622
  have hstable : (prefixWord ++ tailWord_7762622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762622).length < 2 ^ (prefixWord ++ tailWord_7762622).sum := by decide
  have hdescent : baseEnd_7762622 < baseStart_7762622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762630 : List Nat := [6, 1, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_7762630 : Nat := 118140960795 + 7762630 * 2 ^ 59
def prefixEnd_7762630 : Nat := 4983230072969 + 3 ^ 40 * 7762630 * 2
def baseEnd_7762630 : Nat := 1328653444337022969375107

theorem tailTrace_7762630 : CollatzResearch.WordTrace tailWord_7762630 prefixEnd_7762630 1328653444337022969375107 := by
  unfold tailWord_7762630
  simp only [CollatzResearch.WordTrace]
  refine ⟨8847699245853898015644667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 188750917244883157667086229 8847699245853898015644667)
  ·
    refine ⟨13271548868780847023467001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8847699245853898015644667 13271548868780847023467001)
    ·
      refine ⟨9953661651585635267600251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13271548868780847023467001 9953661651585635267600251)
      ·
        refine ⟨14930492477378452901400377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9953661651585635267600251 14930492477378452901400377)
        ·
          refine ⟨11197869358033839676050283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14930492477378452901400377 11197869358033839676050283)
          ·
            refine ⟨16796804037050759514075425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11197869358033839676050283 16796804037050759514075425)
            ·
              refine ⟨12597603027788069635556569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16796804037050759514075425 12597603027788069635556569)
              ·
                refine ⟨9448202270841052226667427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12597603027788069635556569 9448202270841052226667427)
                ·
                  refine ⟨14172303406261578340001141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9448202270841052226667427 14172303406261578340001141)
                  ·
                    refine ⟨1328653444337022969375107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14172303406261578340001141 1328653444337022969375107)
                    ·
                      rfl

theorem cell23_7762630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_7762630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762630 prefixEnd_7762630 := by exact prefixLift 7762630
  have htrace : WordTrace (prefixWord ++ tailWord_7762630) baseStart_7762630 baseEnd_7762630 := by
    simpa [prefixWord, tailWord_7762630, baseEnd_7762630] using wordTrace_append hprefix tailTrace_7762630
  have hstable : (prefixWord ++ tailWord_7762630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762630).length < 2 ^ (prefixWord ++ tailWord_7762630).sum := by decide
  have hdescent : baseEnd_7762630 < baseStart_7762630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762636 : List Nat := [2, 2, 1, 5, 1, 1, 1, 4, 1, 2, 3]
def baseStart_7762636 : Nat := 118140960795 + 7762636 * 2 ^ 59
def prefixEnd_7762636 : Nat := 4983230072969 + 3 ^ 40 * 7762636 * 2
def baseEnd_7762636 : Nat := 3985963413894995884650293

theorem tailTrace_7762636 : CollatzResearch.WordTrace tailWord_7762636 prefixEnd_7762636 3985963413894995884650293 := by
  unfold tailWord_7762636
  simp only [CollatzResearch.WordTrace]
  refine ⟨141563297352651499762673881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188751063136868666350231841 141563297352651499762673881)
  ·
    refine ⟨106172473014488624822005411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141563297352651499762673881 106172473014488624822005411)
    ·
      refine ⟨159258709521732937233008117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106172473014488624822005411 159258709521732937233008117)
      ·
        refine ⟨14930504017662462865594511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159258709521732937233008117 14930504017662462865594511)
        ·
          refine ⟨22395756026493694298391767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14930504017662462865594511 22395756026493694298391767)
          ·
            refine ⟨33593634039740541447587651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22395756026493694298391767 33593634039740541447587651)
            ·
              refine ⟨50390451059610812171381477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33593634039740541447587651 50390451059610812171381477)
              ·
                refine ⟨9448209573677027282134027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50390451059610812171381477 9448209573677027282134027)
                ·
                  refine ⟨14172314360515540923201041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9448209573677027282134027 14172314360515540923201041)
                  ·
                    refine ⟨10629235770386655692400781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14172314360515540923201041 10629235770386655692400781)
                    ·
                      refine ⟨3985963413894995884650293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10629235770386655692400781 3985963413894995884650293)
                      ·
                        rfl

theorem cell23_7762636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_7762636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762636 prefixEnd_7762636 := by exact prefixLift 7762636
  have htrace : WordTrace (prefixWord ++ tailWord_7762636) baseStart_7762636 baseEnd_7762636 := by
    simpa [prefixWord, tailWord_7762636, baseEnd_7762636] using wordTrace_append hprefix tailTrace_7762636
  have hstable : (prefixWord ++ tailWord_7762636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762636).length < 2 ^ (prefixWord ++ tailWord_7762636).sum := by decide
  have hdescent : baseEnd_7762636 < baseStart_7762636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762649 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 6, 1, 3]
def baseStart_7762649 : Nat := 118140960795 + 7762649 * 2 ^ 59
def prefixEnd_7762649 : Nat := 4983230072969 + 3 ^ 40 * 7762649 * 2
def baseEnd_7762649 : Nat := 3985970089143504333787733

theorem tailTrace_7762649 : CollatzResearch.WordTrace tailWord_7762649 prefixEnd_7762649 3985970089143504333787733 := by
  unfold tailWord_7762649
  simp only [CollatzResearch.WordTrace]
  refine ⟨283127068854255902745571001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188751379236170601830380667 283127068854255902745571001)
  ·
    refine ⟨212345301640691927059178251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283127068854255902745571001 212345301640691927059178251)
    ·
      refine ⟨318517952461037890588767377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212345301640691927059178251 318517952461037890588767377)
      ·
        refine ⟨238888464345778417941575533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318517952461037890588767377 238888464345778417941575533)
        ·
          refine ⟨89583174129666906728090825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238888464345778417941575533 89583174129666906728090825)
          ·
            refine ⟨67187380597250180046068119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89583174129666906728090825 67187380597250180046068119)
            ·
              refine ⟨100781070895875270069102179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67187380597250180046068119 100781070895875270069102179)
              ·
                refine ⟨151171606343812905103653269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100781070895875270069102179 151171606343812905103653269)
                ·
                  refine ⟨7086169047366229926733747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151171606343812905103653269 7086169047366229926733747)
                  ·
                    refine ⟨10629253571049344890100621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7086169047366229926733747 10629253571049344890100621)
                    ·
                      refine ⟨3985970089143504333787733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10629253571049344890100621 3985970089143504333787733)
                      ·
                        rfl

theorem cell23_7762649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 1, 3].length) (baseStart_7762649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762649 prefixEnd_7762649 := by exact prefixLift 7762649
  have htrace : WordTrace (prefixWord ++ tailWord_7762649) baseStart_7762649 baseEnd_7762649 := by
    simpa [prefixWord, tailWord_7762649, baseEnd_7762649] using wordTrace_append hprefix tailTrace_7762649
  have hstable : (prefixWord ++ tailWord_7762649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762649).length < 2 ^ (prefixWord ++ tailWord_7762649).sum := by decide
  have hdescent : baseEnd_7762649 < baseStart_7762649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762666 : List Nat := [3, 1, 3, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_7762666 : Nat := 118140960795 + 7762666 * 2 ^ 59
def prefixEnd_7762666 : Nat := 4983230072969 + 3 ^ 40 * 7762666 * 2
def baseEnd_7762666 : Nat := 3985978818314630767275155

theorem tailTrace_7762666 : CollatzResearch.WordTrace tailWord_7762666 prefixEnd_7762666 3985978818314630767275155 := by
  unfold tailWord_7762666
  simp only [CollatzResearch.WordTrace]
  refine ⟨70781922223798578662234963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188751792596796209765959901 70781922223798578662234963)
  ·
    refine ⟨106172883335697867993352445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70781922223798578662234963 106172883335697867993352445)
    ·
      refine ⟨39814831250886700497507167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106172883335697867993352445 39814831250886700497507167)
      ·
        refine ⟨59722246876330050746260751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39814831250886700497507167 59722246876330050746260751)
        ·
          refine ⟨89583370314495076119391127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59722246876330050746260751 89583370314495076119391127)
          ·
            refine ⟨134375055471742614179086691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89583370314495076119391127 134375055471742614179086691)
            ·
              refine ⟨201562583207613921268630037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134375055471742614179086691 201562583207613921268630037)
              ·
                refine ⟨9448246087856902559467033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201562583207613921268630037 9448246087856902559467033)
                ·
                  refine ⟨7086184565892676919600275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9448246087856902559467033 7086184565892676919600275)
                  ·
                    refine ⟨10629276848839015379400413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7086184565892676919600275 10629276848839015379400413)
                    ·
                      refine ⟨3985978818314630767275155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10629276848839015379400413 3985978818314630767275155)
                      ·
                        rfl

theorem cell23_7762666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_7762666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762666 prefixEnd_7762666 := by exact prefixLift 7762666
  have htrace : WordTrace (prefixWord ++ tailWord_7762666) baseStart_7762666 baseEnd_7762666 := by
    simpa [prefixWord, tailWord_7762666, baseEnd_7762666] using wordTrace_append hprefix tailTrace_7762666
  have hstable : (prefixWord ++ tailWord_7762666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762666).length < 2 ^ (prefixWord ++ tailWord_7762666).sum := by decide
  have hdescent : baseEnd_7762666 < baseStart_7762666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762672 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 4]
def baseStart_7762672 : Nat := 118140960795 + 7762672 * 2 ^ 59
def prefixEnd_7762672 : Nat := 4983230072969 + 3 ^ 40 * 7762672 * 2
def baseEnd_7762672 : Nat := 3985981899198557743800127

theorem tailTrace_7762672 : CollatzResearch.WordTrace tailWord_7762672 prefixEnd_7762672 3985981899198557743800127 := by
  unfold tailWord_7762672
  simp only [CollatzResearch.WordTrace]
  refine ⟨141563953866586288836829135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188751938488781718449105513 141563953866586288836829135)
  ·
    refine ⟨212345930799879433255243703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141563953866586288836829135 212345930799879433255243703)
    ·
      refine ⟨318518896199819149882865555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212345930799879433255243703 318518896199819149882865555)
      ·
        refine ⟨477778344299728724824298333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318518896199819149882865555 477778344299728724824298333)
        ·
          refine ⟨179166879112398271809111875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 477778344299728724824298333 179166879112398271809111875)
          ·
            refine ⟨268750318668597407713667813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179166879112398271809111875 268750318668597407713667813)
            ·
              refine ⟨50390684750362013946312715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268750318668597407713667813 50390684750362013946312715)
              ·
                refine ⟨75586027125543020919469073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50390684750362013946312715 75586027125543020919469073)
                ·
                  refine ⟨56689520344157265689601805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75586027125543020919469073 56689520344157265689601805)
                  ·
                    refine ⟨21258570129058974633600677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56689520344157265689601805 21258570129058974633600677)
                    ·
                      refine ⟨3985981899198557743800127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21258570129058974633600677 3985981899198557743800127)
                      ·
                        rfl

theorem cell23_7762672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_7762672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762672 prefixEnd_7762672 := by exact prefixLift 7762672
  have htrace : WordTrace (prefixWord ++ tailWord_7762672) baseStart_7762672 baseEnd_7762672 := by
    simpa [prefixWord, tailWord_7762672, baseEnd_7762672] using wordTrace_append hprefix tailTrace_7762672
  have hstable : (prefixWord ++ tailWord_7762672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762672).length < 2 ^ (prefixWord ++ tailWord_7762672).sum := by decide
  have hdescent : baseEnd_7762672 < baseStart_7762672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762682 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 2, 6]
def baseStart_7762682 : Nat := 118140960795 + 7762682 * 2 ^ 59
def prefixEnd_7762682 : Nat := 4983230072969 + 3 ^ 40 * 7762682 * 2
def baseEnd_7762682 : Nat := 1328662344668367568225027

theorem tailTrace_7762682 : CollatzResearch.WordTrace tailWord_7762682 prefixEnd_7762682 1328662344668367568225027 := by
  unfold tailWord_7762682
  simp only [CollatzResearch.WordTrace]
  refine ⟨70782068115784087345380575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188752181642090899587681533 70782068115784087345380575)
  ·
    refine ⟨106173102173676131018070863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70782068115784087345380575 106173102173676131018070863)
    ·
      refine ⟨159259653260514196527106295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106173102173676131018070863 159259653260514196527106295)
      ·
        refine ⟨238889479890771294790659443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159259653260514196527106295 238889479890771294790659443)
        ·
          refine ⟨358334219836156942185989165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238889479890771294790659443 358334219836156942185989165)
          ·
            refine ⟨134375332438558853319745937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358334219836156942185989165 134375332438558853319745937)
            ·
              refine ⟨100781499328919139989809453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134375332438558853319745937 100781499328919139989809453)
              ·
                refine ⟨37793062248344677496178545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100781499328919139989809453 37793062248344677496178545)
                ·
                  refine ⟨28344796686258508122133909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37793062248344677496178545 28344796686258508122133909)
                  ·
                    refine ⟨1328662344668367568225027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28344796686258508122133909 1328662344668367568225027)
                    ·
                      rfl

theorem cell23_7762682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_7762682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762682 prefixEnd_7762682 := by exact prefixLift 7762682
  have htrace : WordTrace (prefixWord ++ tailWord_7762682) baseStart_7762682 baseEnd_7762682 := by
    simpa [prefixWord, tailWord_7762682, baseEnd_7762682] using wordTrace_append hprefix tailTrace_7762682
  have hstable : (prefixWord ++ tailWord_7762682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762682).length < 2 ^ (prefixWord ++ tailWord_7762682).sum := by decide
  have hdescent : baseEnd_7762682 < baseStart_7762682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762729 : List Nat := [1, 2, 1, 1, 1, 1, 1, 10, 5]
def baseStart_7762729 : Nat := 118140960795 + 7762729 * 2 ^ 59
def prefixEnd_7762729 : Nat := 4983230072969 + 3 ^ 40 * 7762729 * 2
def baseEnd_7762729 : Nat := 442890129732873780087485

theorem tailTrace_7762729 : CollatzResearch.WordTrace tailWord_7762729 prefixEnd_7762729 442890129732873780087485 := by
  unfold tailWord_7762729
  simp only [CollatzResearch.WordTrace]
  refine ⟨283129986693966076408483241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188753324462644050938988827 283129986693966076408483241)
  ·
    refine ⟨212347490020474557306362431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283129986693966076408483241 212347490020474557306362431)
    ·
      refine ⟨318521235030711835959543647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212347490020474557306362431 318521235030711835959543647)
      ·
        refine ⟨477781852546067753939315471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318521235030711835959543647 477781852546067753939315471)
        ·
          refine ⟨716672778819101630908973207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477781852546067753939315471 716672778819101630908973207)
          ·
            refine ⟨1075009168228652446363459811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716672778819101630908973207 1075009168228652446363459811)
            ·
              refine ⟨1612513752342978669545189717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075009168228652446363459811 1612513752342978669545189717)
              ·
                refine ⟨4724161383817320320933173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1612513752342978669545189717 4724161383817320320933173)
                ·
                  refine ⟨442890129732873780087485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4724161383817320320933173 442890129732873780087485)
                  ·
                    rfl

theorem cell23_7762729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 5].length) (baseStart_7762729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762729 prefixEnd_7762729 := by exact prefixLift 7762729
  have htrace : WordTrace (prefixWord ++ tailWord_7762729) baseStart_7762729 baseEnd_7762729 := by
    simpa [prefixWord, tailWord_7762729, baseEnd_7762729] using wordTrace_append hprefix tailTrace_7762729
  have hstable : (prefixWord ++ tailWord_7762729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762729).length < 2 ^ (prefixWord ++ tailWord_7762729).sum := by decide
  have hdescent : baseEnd_7762729 < baseStart_7762729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762733 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_7762733 : Nat := 118140960795 + 7762733 * 2 ^ 59
def prefixEnd_7762733 : Nat := 4983230072969 + 3 ^ 40 * 7762733 * 2
def baseEnd_7762733 : Nat := 1328671073839494001712449

theorem tailTrace_7762733 : CollatzResearch.WordTrace tailWord_7762733 prefixEnd_7762733 1328671073839494001712449 := by
  unfold tailWord_7762733
  simp only [CollatzResearch.WordTrace]
  refine ⟨283130132585951585091628853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188753421723967723394419235 283130132585951585091628853)
  ·
    refine ⟨26543449929932961102340205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 283130132585951585091628853 26543449929932961102340205)
    ·
      refine ⟨9953793723724860413377577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26543449929932961102340205 9953793723724860413377577)
      ·
        refine ⟨7465345292793645310033183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9953793723724860413377577 7465345292793645310033183)
        ·
          refine ⟨11198017939190467965049775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7465345292793645310033183 11198017939190467965049775)
          ·
            refine ⟨16797026908785701947574663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11198017939190467965049775 16797026908785701947574663)
            ·
              refine ⟨25195540363178552921361995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16797026908785701947574663 25195540363178552921361995)
              ·
                refine ⟨37793310544767829382042993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25195540363178552921361995 37793310544767829382042993)
                ·
                  refine ⟨28344982908575872036532245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37793310544767829382042993 28344982908575872036532245)
                  ·
                    refine ⟨1328671073839494001712449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28344982908575872036532245 1328671073839494001712449)
                    ·
                      rfl

theorem cell23_7762733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_7762733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762733 prefixEnd_7762733 := by exact prefixLift 7762733
  have htrace : WordTrace (prefixWord ++ tailWord_7762733) baseStart_7762733 baseEnd_7762733 := by
    simpa [prefixWord, tailWord_7762733, baseEnd_7762733] using wordTrace_append hprefix tailTrace_7762733
  have hstable : (prefixWord ++ tailWord_7762733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762733).length < 2 ^ (prefixWord ++ tailWord_7762733).sum := by decide
  have hdescent : baseEnd_7762733 < baseStart_7762733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762739 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 3]
def baseStart_7762739 : Nat := 118140960795 + 7762739 * 2 ^ 59
def prefixEnd_7762739 : Nat := 4983230072969 + 3 ^ 40 * 7762739 * 2
def baseEnd_7762739 : Nat := 3986016302402408981662319

theorem tailTrace_7762739 : CollatzResearch.WordTrace tailWord_7762739 prefixEnd_7762739 3986016302402408981662319 := by
  unfold tailWord_7762739
  simp only [CollatzResearch.WordTrace]
  refine ⟨283130351423929848116347271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188753567615953232077564847 283130351423929848116347271)
  ·
    refine ⟨424695527135894772174520907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283130351423929848116347271 424695527135894772174520907)
    ·
      refine ⟨637043290703842158261781361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424695527135894772174520907 637043290703842158261781361)
      ·
        refine ⟨477782468027881618696336021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 637043290703842158261781361 477782468027881618696336021)
        ·
          refine ⟨22396053188806950876390751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 477782468027881618696336021 22396053188806950876390751)
          ·
            refine ⟨33594079783210426314586127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22396053188806950876390751 33594079783210426314586127)
            ·
              refine ⟨50391119674815639471879191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33594079783210426314586127 50391119674815639471879191)
              ·
                refine ⟨75586679512223459207818787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50391119674815639471879191 75586679512223459207818787)
                ·
                  refine ⟨113380019268335188811728181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75586679512223459207818787 113380019268335188811728181)
                  ·
                    refine ⟨10629376806406423951099517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113380019268335188811728181 10629376806406423951099517)
                    ·
                      refine ⟨3986016302402408981662319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10629376806406423951099517 3986016302402408981662319)
                      ·
                        rfl

theorem cell23_7762739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 3].length) (baseStart_7762739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762739 prefixEnd_7762739 := by exact prefixLift 7762739
  have htrace : WordTrace (prefixWord ++ tailWord_7762739) baseStart_7762739 baseEnd_7762739 := by
    simpa [prefixWord, tailWord_7762739, baseEnd_7762739] using wordTrace_append hprefix tailTrace_7762739
  have hstable : (prefixWord ++ tailWord_7762739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762739).length < 2 ^ (prefixWord ++ tailWord_7762739).sum := by decide
  have hdescent : baseEnd_7762739 < baseStart_7762739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762740 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_7762740 : Nat := 118140960795 + 7762740 * 2 ^ 59
def prefixEnd_7762740 : Nat := 4983230072969 + 3 ^ 40 * 7762740 * 2
def baseEnd_7762740 : Nat := 3986016815883063477749815

theorem tailTrace_7762740 : CollatzResearch.WordTrace tailWord_7762740 prefixEnd_7762740 3986016815883063477749815 := by
  unfold tailWord_7762740
  simp only [CollatzResearch.WordTrace]
  refine ⟨141565193948463112643566837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188753591931284150191422449 141565193948463112643566837)
  ·
    refine ⟨13271736932668416810334391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141565193948463112643566837 13271736932668416810334391)
    ·
      refine ⟨19907605399002625215501587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13271736932668416810334391 19907605399002625215501587)
      ·
        refine ⟨29861408098503937823252381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19907605399002625215501587 29861408098503937823252381)
        ·
          refine ⟨11198028036938976683719643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29861408098503937823252381 11198028036938976683719643)
          ·
            refine ⟨16797042055408465025579465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11198028036938976683719643 16797042055408465025579465)
            ·
              refine ⟨12597781541556348769184599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16797042055408465025579465 12597781541556348769184599)
              ·
                refine ⟨18896672312334523153776899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12597781541556348769184599 18896672312334523153776899)
                ·
                  refine ⟨28345008468501784730665349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18896672312334523153776899 28345008468501784730665349)
                  ·
                    refine ⟨5314689087844084636999753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28345008468501784730665349 5314689087844084636999753)
                    ·
                      refine ⟨3986016815883063477749815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5314689087844084636999753 3986016815883063477749815)
                      ·
                        rfl

theorem cell23_7762740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_7762740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762740 prefixEnd_7762740 := by exact prefixLift 7762740
  have htrace : WordTrace (prefixWord ++ tailWord_7762740) baseStart_7762740 baseEnd_7762740 := by
    simpa [prefixWord, tailWord_7762740, baseEnd_7762740] using wordTrace_append hprefix tailTrace_7762740
  have hstable : (prefixWord ++ tailWord_7762740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762740).length < 2 ^ (prefixWord ++ tailWord_7762740).sum := by decide
  have hdescent : baseEnd_7762740 < baseStart_7762740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762752 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 7]
def baseStart_7762752 : Nat := 118140960795 + 7762752 * 2 ^ 59
def prefixEnd_7762752 : Nat := 4983230072969 + 3 ^ 40 * 7762752 * 2
def baseEnd_7762752 : Nat := 3986022977650917430799759

theorem tailTrace_7762752 : CollatzResearch.WordTrace tailWord_7762752 prefixEnd_7762752 3986022977650917430799759 := by
  unfold tailWord_7762752
  simp only [CollatzResearch.WordTrace]
  refine ⟨141565412786441375668285255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188753883715255167557713673 141565412786441375668285255)
  ·
    refine ⟨212348119179662063502427883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141565412786441375668285255 212348119179662063502427883)
    ·
      refine ⟨318522178769493095253641825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212348119179662063502427883 318522178769493095253641825)
      ·
        refine ⟨238891634077119821440231369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318522178769493095253641825 238891634077119821440231369)
        ·
          refine ⟨179168725557839866080173527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238891634077119821440231369 179168725557839866080173527)
          ·
            refine ⟨268753088336759799120260291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179168725557839866080173527 268753088336759799120260291)
            ·
              refine ⟨403129632505139698680390437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268753088336759799120260291 403129632505139698680390437)
              ·
                refine ⟨75586806094713693502573207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 403129632505139698680390437 75586806094713693502573207)
                ·
                  refine ⟨113380209142070540253859811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75586806094713693502573207 113380209142070540253859811)
                  ·
                    refine ⟨170070313713105810380789717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113380209142070540253859811 170070313713105810380789717)
                    ·
                      refine ⟨3986022977650917430799759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170070313713105810380789717 3986022977650917430799759)
                      ·
                        rfl

theorem cell23_7762752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_7762752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762752 prefixEnd_7762752 := by exact prefixLift 7762752
  have htrace : WordTrace (prefixWord ++ tailWord_7762752) baseStart_7762752 baseEnd_7762752 := by
    simpa [prefixWord, tailWord_7762752, baseEnd_7762752] using wordTrace_append hprefix tailTrace_7762752
  have hstable : (prefixWord ++ tailWord_7762752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762752).length < 2 ^ (prefixWord ++ tailWord_7762752).sum := by decide
  have hdescent : baseEnd_7762752 < baseStart_7762752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762796 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 2, 4, 2]
def baseStart_7762796 : Nat := 118140960795 + 7762796 * 2 ^ 59
def prefixEnd_7762796 : Nat := 4983230072969 + 3 ^ 40 * 7762796 * 2
def baseEnd_7762796 : Nat := 3986045570799715258649557

theorem tailTrace_7762796 : CollatzResearch.WordTrace tailWord_7762796 prefixEnd_7762796 3986045570799715258649557 := by
  unfold tailWord_7762796
  simp only [CollatzResearch.WordTrace]
  refine ⟨141566215192361673425586121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188754953589815564567448161 141566215192361673425586121)
  ·
    refine ⟨106174661394271255069189591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141566215192361673425586121 106174661394271255069189591)
    ·
      refine ⟨159261992091406882603784387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106174661394271255069189591 159261992091406882603784387)
      ·
        refine ⟨238892988137110323905676581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159261992091406882603784387 238892988137110323905676581)
        ·
          refine ⟨44792435275708185732314359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238892988137110323905676581 44792435275708185732314359)
          ·
            refine ⟨67188652913562278598471539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44792435275708185732314359 67188652913562278598471539)
            ·
              refine ⟨100782979370343417897707309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67188652913562278598471539 100782979370343417897707309)
              ·
                refine ⟨37793617263878781711640241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100782979370343417897707309 37793617263878781711640241)
                ·
                  refine ⟨28345212947909086283730181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37793617263878781711640241 28345212947909086283730181)
                  ·
                    refine ⟨5314727427732953678199409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28345212947909086283730181 5314727427732953678199409)
                    ·
                      refine ⟨3986045570799715258649557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5314727427732953678199409 3986045570799715258649557)
                      ·
                        rfl

theorem cell23_7762796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 4, 2].length) (baseStart_7762796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762796 prefixEnd_7762796 := by exact prefixLift 7762796
  have htrace : WordTrace (prefixWord ++ tailWord_7762796) baseStart_7762796 baseEnd_7762796 := by
    simpa [prefixWord, tailWord_7762796, baseEnd_7762796] using wordTrace_append hprefix tailTrace_7762796
  have hstable : (prefixWord ++ tailWord_7762796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762796).length < 2 ^ (prefixWord ++ tailWord_7762796).sum := by decide
  have hdescent : baseEnd_7762796 < baseStart_7762796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762836 : List Nat := [2, 4, 2, 1, 1, 1, 2, 4, 6]
def baseStart_7762836 : Nat := 118140960795 + 7762836 * 2 ^ 59
def prefixEnd_7762836 : Nat := 4983230072969 + 3 ^ 40 * 7762836 * 2
def baseEnd_7762836 : Nat := 442896234447321678016597

theorem tailTrace_7762836 : CollatzResearch.WordTrace tailWord_7762836 prefixEnd_7762836 442896234447321678016597 := by
  unfold tailWord_7762836
  simp only [CollatzResearch.WordTrace]
  refine ⟨141566944652289216841314181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188755926203052289121752241 141566944652289216841314181)
  ·
    refine ⟨26543802122304228157746409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141566944652289216841314181 26543802122304228157746409)
    ·
      refine ⟨19907851591728171118309807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26543802122304228157746409 19907851591728171118309807)
      ·
        refine ⟨29861777387592256677464711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19907851591728171118309807 29861777387592256677464711)
        ·
          refine ⟨44792666081388385016197067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29861777387592256677464711 44792666081388385016197067)
          ·
            refine ⟨67188999122082577524295601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44792666081388385016197067 67188999122082577524295601)
            ·
              refine ⟨50391749341561933143221701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67188999122082577524295601 50391749341561933143221701)
              ·
                refine ⟨9448453001542862464354069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50391749341561933143221701 9448453001542862464354069)
                ·
                  refine ⟨442896234447321678016597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9448453001542862464354069 442896234447321678016597)
                  ·
                    rfl

theorem cell23_7762836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_7762836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762836 prefixEnd_7762836 := by exact prefixLift 7762836
  have htrace : WordTrace (prefixWord ++ tailWord_7762836) baseStart_7762836 baseEnd_7762836 := by
    simpa [prefixWord, tailWord_7762836, baseEnd_7762836] using wordTrace_append hprefix tailTrace_7762836
  have hstable : (prefixWord ++ tailWord_7762836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762836).length < 2 ^ (prefixWord ++ tailWord_7762836).sum := by decide
  have hdescent : baseEnd_7762836 < baseStart_7762836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762873 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 2, 3, 2]
def baseStart_7762873 : Nat := 118140960795 + 7762873 * 2 ^ 59
def prefixEnd_7762873 : Nat := 4983230072969 + 3 ^ 40 * 7762873 * 2
def baseEnd_7762873 : Nat := 3986085108810111457386703

theorem tailTrace_7762873 : CollatzResearch.WordTrace tailWord_7762873 prefixEnd_7762873 3986085108810111457386703 := by
  unfold tailWord_7762873
  simp only [CollatzResearch.WordTrace]
  refine ⟨283135238805444389001725273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188756825870296259334483515 283135238805444389001725273)
  ·
    refine ⟨212351429104083291751293955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283135238805444389001725273 212351429104083291751293955)
    ·
      refine ⟨318527143656124937626940933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212351429104083291751293955 318527143656124937626940933)
      ·
        refine ⟨59723839435523425805051425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318527143656124937626940933 59723839435523425805051425)
        ·
          refine ⟨44792879576642569353788569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59723839435523425805051425 44792879576642569353788569)
          ·
            refine ⟨33594659682481927015341427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44792879576642569353788569 33594659682481927015341427)
            ·
              refine ⟨50391989523722890523012141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33594659682481927015341427 50391989523722890523012141)
              ·
                refine ⟨18896996071396083946129553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50391989523722890523012141 18896996071396083946129553)
                ·
                  refine ⟨14172747053547062959597165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18896996071396083946129553 14172747053547062959597165)
                  ·
                    refine ⟨5314780145080148609848937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14172747053547062959597165 5314780145080148609848937)
                    ·
                      refine ⟨3986085108810111457386703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5314780145080148609848937 3986085108810111457386703)
                      ·
                        rfl

theorem cell23_7762873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_7762873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762873 prefixEnd_7762873 := by exact prefixLift 7762873
  have htrace : WordTrace (prefixWord ++ tailWord_7762873) baseStart_7762873 baseEnd_7762873 := by
    simpa [prefixWord, tailWord_7762873, baseEnd_7762873] using wordTrace_append hprefix tailTrace_7762873
  have hstable : (prefixWord ++ tailWord_7762873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762873).length < 2 ^ (prefixWord ++ tailWord_7762873).sum := by decide
  have hdescent : baseEnd_7762873 < baseStart_7762873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762937 : List Nat := [1, 2, 1, 3, 1, 3, 4, 3, 1, 2, 2]
def baseStart_7762937 : Nat := 118140960795 + 7762937 * 2 ^ 59
def prefixEnd_7762937 : Nat := 4983230072969 + 3 ^ 40 * 7762937 * 2
def baseEnd_7762937 : Nat := 3986117971571999206986409

theorem tailTrace_7762937 : CollatzResearch.WordTrace tailWord_7762937 prefixEnd_7762937 3986117971571999206986409 := by
  unfold tailWord_7762937
  simp only [CollatzResearch.WordTrace]
  refine ⟨283137573077212527932055065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188758382051475018621370043 283137573077212527932055065)
  ·
    refine ⟨212353179807909395949041299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283137573077212527932055065 212353179807909395949041299)
    ·
      refine ⟨318529769711864093923561949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212353179807909395949041299 318529769711864093923561949)
      ·
        refine ⟨119448663641949035221335731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318529769711864093923561949 119448663641949035221335731)
        ·
          refine ⟨179172995462923552832003597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119448663641949035221335731 179172995462923552832003597)
          ·
            refine ⟨67189873298596332312001349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179172995462923552832003597 67189873298596332312001349)
            ·
              refine ⟨12598101243486812308500253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67189873298596332312001349 12598101243486812308500253)
              ·
                refine ⟨4724287966307554615687595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12598101243486812308500253 4724287966307554615687595)
                ·
                  refine ⟨7086431949461331923531393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4724287966307554615687595 7086431949461331923531393)
                  ·
                    refine ⟨5314823962095998942648545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7086431949461331923531393 5314823962095998942648545)
                    ·
                      refine ⟨3986117971571999206986409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5314823962095998942648545 3986117971571999206986409)
                      ·
                        rfl

theorem cell23_7762937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_7762937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762937 prefixEnd_7762937 := by exact prefixLift 7762937
  have htrace : WordTrace (prefixWord ++ tailWord_7762937) baseStart_7762937 baseEnd_7762937 := by
    simpa [prefixWord, tailWord_7762937, baseEnd_7762937] using wordTrace_append hprefix tailTrace_7762937
  have hstable : (prefixWord ++ tailWord_7762937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762937).length < 2 ^ (prefixWord ++ tailWord_7762937).sum := by decide
  have hdescent : baseEnd_7762937 < baseStart_7762937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762940 : List Nat := [2, 2, 2, 1, 2, 3, 4, 1, 1, 2, 3]
def baseStart_7762940 : Nat := 118140960795 + 7762940 * 2 ^ 59
def prefixEnd_7762940 : Nat := 4983230072969 + 3 ^ 40 * 7762940 * 2
def baseEnd_7762940 : Nat := 3986119512013962695248895

theorem tailTrace_7762940 : CollatzResearch.WordTrace tailWord_7762940 prefixEnd_7762940 3986119512013962695248895 := by
  unfold tailWord_7762940
  simp only [CollatzResearch.WordTrace]
  refine ⟨141568841248100829722207137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188758454997467772962942849 141568841248100829722207137)
  ·
    refine ⟨106176630936075622291655353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141568841248100829722207137 106176630936075622291655353)
    ·
      refine ⟨79632473202056716718741515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106176630936075622291655353 79632473202056716718741515)
      ·
        refine ⟨119448709803085075078112273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79632473202056716718741515 119448709803085075078112273)
        ·
          refine ⟨89586532352313806308584205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119448709803085075078112273 89586532352313806308584205)
          ·
            refine ⟨33594949632117677365719077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89586532352313806308584205 33594949632117677365719077)
            ·
              refine ⟨6299053056022064506072327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33594949632117677365719077 6299053056022064506072327)
              ·
                refine ⟨9448579584033096759108491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6299053056022064506072327 9448579584033096759108491)
                ·
                  refine ⟨14172869376049645138662737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9448579584033096759108491 14172869376049645138662737)
                  ·
                    refine ⟨10629652032037233853997053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14172869376049645138662737 10629652032037233853997053)
                    ·
                      refine ⟨3986119512013962695248895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10629652032037233853997053 3986119512013962695248895)
                      ·
                        rfl

theorem cell23_7762940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_7762940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762940 prefixEnd_7762940 := by exact prefixLift 7762940
  have htrace : WordTrace (prefixWord ++ tailWord_7762940) baseStart_7762940 baseEnd_7762940 := by
    simpa [prefixWord, tailWord_7762940, baseEnd_7762940] using wordTrace_append hprefix tailTrace_7762940
  have hstable : (prefixWord ++ tailWord_7762940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762940).length < 2 ^ (prefixWord ++ tailWord_7762940).sum := by decide
  have hdescent : baseEnd_7762940 < baseStart_7762940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762983 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_7762983 : Nat := 118140960795 + 7762983 * 2 ^ 59
def prefixEnd_7762983 : Nat := 4983230072969 + 3 ^ 40 * 7762983 * 2
def baseEnd_7762983 : Nat := 3986141591682106027011197

theorem tailTrace_7762983 : CollatzResearch.WordTrace tailWord_7762983 prefixEnd_7762983 3986141591682106027011197 := by
  unfold tailWord_7762983
  simp only [CollatzResearch.WordTrace]
  refine ⟨283139250835045877788229603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188759500556697251858819735 283139250835045877788229603)
  ·
    refine ⟨424708876252568816682344405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283139250835045877788229603 424708876252568816682344405)
    ·
      refine ⟨9954114287169581640992447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 424708876252568816682344405 9954114287169581640992447)
      ·
        refine ⟨14931171430754372461488671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9954114287169581640992447 14931171430754372461488671)
        ·
          refine ⟨22396757146131558692233007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14931171430754372461488671 22396757146131558692233007)
          ·
            refine ⟨33595135719197338038349511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22396757146131558692233007 33595135719197338038349511)
            ·
              refine ⟨50392703578796007057524267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33595135719197338038349511 50392703578796007057524267)
              ·
                refine ⟨75589055368194010586286401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50392703578796007057524267 75589055368194010586286401)
                ·
                  refine ⟨56691791526145507939714801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75589055368194010586286401 56691791526145507939714801)
                  ·
                    refine ⟨42518843644609130954786101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56691791526145507939714801 42518843644609130954786101)
                    ·
                      refine ⟨3986141591682106027011197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42518843644609130954786101 3986141591682106027011197)
                      ·
                        rfl

theorem cell23_7762983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_7762983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762983 prefixEnd_7762983 := by exact prefixLift 7762983
  have htrace : WordTrace (prefixWord ++ tailWord_7762983) baseStart_7762983 baseEnd_7762983 := by
    simpa [prefixWord, tailWord_7762983, baseEnd_7762983] using wordTrace_append hprefix tailTrace_7762983
  have hstable : (prefixWord ++ tailWord_7762983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762983).length < 2 ^ (prefixWord ++ tailWord_7762983).sum := by decide
  have hdescent : baseEnd_7762983 < baseStart_7762983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762993 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 3, 4, 2]
def baseStart_7762993 : Nat := 118140960795 + 7762993 * 2 ^ 59
def prefixEnd_7762993 : Nat := 4983230072969 + 3 ^ 40 * 7762993 * 2
def baseEnd_7762993 : Nat := 3986146726488650987886151

theorem tailTrace_7762993 : CollatzResearch.WordTrace tailWord_7762993 prefixEnd_7762993 3986146726488650987886151 := by
  unfold tailWord_7762993
  simp only [CollatzResearch.WordTrace]
  refine ⟨283139615565009649496093633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188759743710006432997395755 283139615565009649496093633)
  ·
    refine ⟨212354711673757237122070225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283139615565009649496093633 212354711673757237122070225)
    ·
      refine ⟨159266033755317927841552669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212354711673757237122070225 159266033755317927841552669)
      ·
        refine ⟨59724762658244222940582251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159266033755317927841552669 59724762658244222940582251)
        ·
          refine ⟨89587143987366334410873377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59724762658244222940582251 89587143987366334410873377)
          ·
            refine ⟨67190357990524750808155033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89587143987366334410873377 67190357990524750808155033)
            ·
              refine ⟨50392768492893563106116275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67190357990524750808155033 50392768492893563106116275)
              ·
                refine ⟨75589152739340344659174413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50392768492893563106116275 75589152739340344659174413)
                ·
                  refine ⟨28345932277252629247190405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75589152739340344659174413 28345932277252629247190405)
                  ·
                    refine ⟨5314862301984867983848201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28345932277252629247190405 5314862301984867983848201)
                    ·
                      refine ⟨3986146726488650987886151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5314862301984867983848201 3986146726488650987886151)
                      ·
                        rfl

theorem cell23_7762993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_7762993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762993 prefixEnd_7762993 := by exact prefixLift 7762993
  have htrace : WordTrace (prefixWord ++ tailWord_7762993) baseStart_7762993 baseEnd_7762993 := by
    simpa [prefixWord, tailWord_7762993, baseEnd_7762993] using wordTrace_append hprefix tailTrace_7762993
  have hstable : (prefixWord ++ tailWord_7762993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762993).length < 2 ^ (prefixWord ++ tailWord_7762993).sum := by decide
  have hdescent : baseEnd_7762993 < baseStart_7762993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763056 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 5]
def baseStart_7763056 : Nat := 118140960795 + 7763056 * 2 ^ 59
def prefixEnd_7763056 : Nat := 4983230072969 + 3 ^ 40 * 7763056 * 2
def baseEnd_7763056 : Nat := 3986179075769884241398361

theorem tailTrace_7763056 : CollatzResearch.WordTrace tailWord_7763056 prefixEnd_7763056 3986179075769884241398361 := by
  unfold tailWord_7763056
  simp only [CollatzResearch.WordTrace]
  refine ⟨141570956681890705627818511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188761275575854274170424681 141570956681890705627818511)
  ·
    refine ⟨212356435022836058441727767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141570956681890705627818511 212356435022836058441727767)
    ·
      refine ⟨318534652534254087662591651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212356435022836058441727767 318534652534254087662591651)
      ·
        refine ⟨477801978801381131493887477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318534652534254087662591651 477801978801381131493887477)
        ·
          refine ⟨44793935512629481077551951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 477801978801381131493887477 44793935512629481077551951)
          ·
            refine ⟨67190903268944221616327927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44793935512629481077551951 67190903268944221616327927)
            ·
              refine ⟨100786354903416332424491891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67190903268944221616327927 100786354903416332424491891)
              ·
                refine ⟨151179532355124498636737837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100786354903416332424491891 151179532355124498636737837)
                ·
                  refine ⟨56692324633171686988776689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151179532355124498636737837 56692324633171686988776689)
                  ·
                    refine ⟨42519243474878765241582517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56692324633171686988776689 42519243474878765241582517)
                    ·
                      refine ⟨3986179075769884241398361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42519243474878765241582517 3986179075769884241398361)
                      ·
                        rfl

theorem cell23_7763056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_7763056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763056 prefixEnd_7763056 := by exact prefixLift 7763056
  have htrace : WordTrace (prefixWord ++ tailWord_7763056) baseStart_7763056 baseEnd_7763056 := by
    simpa [prefixWord, tailWord_7763056, baseEnd_7763056] using wordTrace_append hprefix tailTrace_7763056
  have hstable : (prefixWord ++ tailWord_7763056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763056).length < 2 ^ (prefixWord ++ tailWord_7763056).sum := by decide
  have hdescent : baseEnd_7763056 < baseStart_7763056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763061 : List Nat := [1, 3, 4, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_7763061 : Nat := 118140960795 + 7763061 * 2 ^ 59
def prefixEnd_7763061 : Nat := 4983230072969 + 3 ^ 40 * 7763061 * 2
def baseEnd_7763061 : Nat := 3986181643173156721835839

theorem tailTrace_7763061 : CollatzResearch.WordTrace tailWord_7763061 prefixEnd_7763061 3986181643173156721835839 := by
  unfold tailWord_7763061
  simp only [CollatzResearch.WordTrace]
  refine ⟨283142095728763297109569037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188761397152508864739712691 283142095728763297109569037)
  ·
    refine ⟨106178285898286236416088389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283142095728763297109569037 106178285898286236416088389)
    ·
      refine ⟨19908428605928669328016573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106178285898286236416088389 19908428605928669328016573)
      ·
        refine ⟨7465660727223250998006215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19908428605928669328016573 7465660727223250998006215)
        ·
          refine ⟨11198491090834876497009323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7465660727223250998006215 11198491090834876497009323)
          ·
            refine ⟨16797736636252314745513985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11198491090834876497009323 16797736636252314745513985)
            ·
              refine ⟨12598302477189236059135489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16797736636252314745513985 12598302477189236059135489)
              ·
                refine ⟨9448726857891927044351617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12598302477189236059135489 9448726857891927044351617)
                ·
                  refine ⟨7086545143418945283263713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9448726857891927044351617 7086545143418945283263713)
                  ·
                    refine ⟨5314908857564208962447785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7086545143418945283263713 5314908857564208962447785)
                    ·
                      refine ⟨3986181643173156721835839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5314908857564208962447785 3986181643173156721835839)
                      ·
                        rfl

theorem cell23_7763061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_7763061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763061 prefixEnd_7763061 := by exact prefixLift 7763061
  have htrace : WordTrace (prefixWord ++ tailWord_7763061) baseStart_7763061 baseEnd_7763061 := by
    simpa [prefixWord, tailWord_7763061, baseEnd_7763061] using wordTrace_append hprefix tailTrace_7763061
  have hstable : (prefixWord ++ tailWord_7763061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763061).length < 2 ^ (prefixWord ++ tailWord_7763061).sum := by decide
  have hdescent : baseEnd_7763061 < baseStart_7763061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763073 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_7763073 : Nat := 118140960795 + 7763073 * 2 ^ 59
def prefixEnd_7763073 : Nat := 4983230072969 + 3 ^ 40 * 7763073 * 2
def baseEnd_7763073 : Nat := 3986187804941010674885783

theorem tailTrace_7763073 : CollatzResearch.WordTrace tailWord_7763073 prefixEnd_7763073 3986187804941010674885783 := by
  unfold tailWord_7763073
  simp only [CollatzResearch.WordTrace]
  refine ⟨283142533404719823159005873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188761688936479882106003915 283142533404719823159005873)
  ·
    refine ⟨212356900053539867369254405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283142533404719823159005873 212356900053539867369254405)
    ·
      refine ⟨39816918760038725131735201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212356900053539867369254405 39816918760038725131735201)
      ·
        refine ⟨29862689070029043848801401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39816918760038725131735201 29862689070029043848801401)
        ·
          refine ⟨22397016802521782886601051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29862689070029043848801401 22397016802521782886601051)
          ·
            refine ⟨33595525203782674329901577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22397016802521782886601051 33595525203782674329901577)
            ·
              refine ⟨25196643902837005747426183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33595525203782674329901577 25196643902837005747426183)
              ·
                refine ⟨37794965854255508621139275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25196643902837005747426183 37794965854255508621139275)
                ·
                  refine ⟨56692448781383262931708913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37794965854255508621139275 56692448781383262931708913)
                  ·
                    refine ⟨42519336586037447198781685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56692448781383262931708913 42519336586037447198781685)
                    ·
                      refine ⟨3986187804941010674885783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42519336586037447198781685 3986187804941010674885783)
                      ·
                        rfl

theorem cell23_7763073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_7763073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763073 prefixEnd_7763073 := by exact prefixLift 7763073
  have htrace : WordTrace (prefixWord ++ tailWord_7763073) baseStart_7763073 baseEnd_7763073 := by
    simpa [prefixWord, tailWord_7763073, baseEnd_7763073] using wordTrace_append hprefix tailTrace_7763073
  have hstable : (prefixWord ++ tailWord_7763073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763073).length < 2 ^ (prefixWord ++ tailWord_7763073).sum := by decide
  have hdescent : baseEnd_7763073 < baseStart_7763073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763100 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_7763100 : Nat := 118140960795 + 7763100 * 2 ^ 59
def prefixEnd_7763100 : Nat := 4983230072969 + 3 ^ 40 * 7763100 * 2
def baseEnd_7763100 : Nat := 3986201668918682069248159

theorem tailTrace_7763100 : CollatzResearch.WordTrace tailWord_7763100 prefixEnd_7763100 3986201668918682069248159 := by
  unfold tailWord_7763100
  simp only [CollatzResearch.WordTrace]
  refine ⟨141571759087811003385119377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188762345450414671180159169 141571759087811003385119377)
  ·
    refine ⟨106178819315858252538839533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141571759087811003385119377 106178819315858252538839533)
    ·
      refine ⟨39817057243446844702064825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106178819315858252538839533 39817057243446844702064825)
      ·
        refine ⟨29862792932585133526548619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39817057243446844702064825 29862792932585133526548619)
        ·
          refine ⟨44794189398877700289822929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29862792932585133526548619 44794189398877700289822929)
          ·
            refine ⟨33595642049158275217367197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44794189398877700289822929 33595642049158275217367197)
            ·
              refine ⟨12598365768434353206512699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33595642049158275217367197 12598365768434353206512699)
              ·
                refine ⟨18897548652651529809769049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12598365768434353206512699 18897548652651529809769049)
                ·
                  refine ⟨14173161489488647357326787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18897548652651529809769049 14173161489488647357326787)
                  ·
                    refine ⟨21259742234232971035990181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14173161489488647357326787 21259742234232971035990181)
                    ·
                      refine ⟨3986201668918682069248159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21259742234232971035990181 3986201668918682069248159)
                      ·
                        rfl

theorem cell23_7763100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_7763100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763100 prefixEnd_7763100 := by exact prefixLift 7763100
  have htrace : WordTrace (prefixWord ++ tailWord_7763100) baseStart_7763100 baseEnd_7763100 := by
    simpa [prefixWord, tailWord_7763100, baseEnd_7763100] using wordTrace_append hprefix tailTrace_7763100
  have hstable : (prefixWord ++ tailWord_7763100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763100).length < 2 ^ (prefixWord ++ tailWord_7763100).sum := by decide
  have hdescent : baseEnd_7763100 < baseStart_7763100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763123 : List Nat := [1, 1, 1, 2, 3, 2, 5, 2, 6]
def baseStart_7763123 : Nat := 118140960795 + 7763123 * 2 ^ 59
def prefixEnd_7763123 : Nat := 4983230072969 + 3 ^ 40 * 7763123 * 2
def baseEnd_7763123 : Nat := 442912608774859497695617

theorem tailTrace_7763123 : CollatzResearch.WordTrace tailWord_7763123 prefixEnd_7763123 442912608774859497695617 := by
  unfold tailWord_7763123
  simp only [CollatzResearch.WordTrace]
  refine ⟨283144357054538681698326023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188762904703025787798884015 283144357054538681698326023)
  ·
    refine ⟨424716535581808022547489035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283144357054538681698326023 424716535581808022547489035)
    ·
      refine ⟨637074803372712033821233553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424716535581808022547489035 637074803372712033821233553)
      ·
        refine ⟨477806102529534025365925165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 637074803372712033821233553 477806102529534025365925165)
        ·
          refine ⟨179177288448575259512221937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 477806102529534025365925165 179177288448575259512221937)
          ·
            refine ⟨134382966336431444634166453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179177288448575259512221937 134382966336431444634166453)
            ·
              refine ⟨12598403094040447934453105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134382966336431444634166453 12598403094040447934453105)
              ·
                refine ⟨9448802320530335950839829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12598403094040447934453105 9448802320530335950839829)
                ·
                  refine ⟨442912608774859497695617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9448802320530335950839829 442912608774859497695617)
                  ·
                    rfl

theorem cell23_7763123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 6].length) (baseStart_7763123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763123 prefixEnd_7763123 := by exact prefixLift 7763123
  have htrace : WordTrace (prefixWord ++ tailWord_7763123) baseStart_7763123 baseEnd_7763123 := by
    simpa [prefixWord, tailWord_7763123, baseEnd_7763123] using wordTrace_append hprefix tailTrace_7763123
  have hstable : (prefixWord ++ tailWord_7763123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763123).length < 2 ^ (prefixWord ++ tailWord_7763123).sum := by decide
  have hdescent : baseEnd_7763123 < baseStart_7763123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763190 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_7763190 : Nat := 118140960795 + 7763190 * 2 ^ 59
def prefixEnd_7763190 : Nat := 4983230072969 + 3 ^ 40 * 7763190 * 2
def baseEnd_7763190 : Nat := 3986247882177586717122745

theorem tailTrace_7763190 : CollatzResearch.WordTrace tailWord_7763190 prefixEnd_7763190 3986247882177586717122745 := by
  unfold tailWord_7763190
  simp only [CollatzResearch.WordTrace]
  refine ⟨17696675046580997008813439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188764533830197301427343349 17696675046580997008813439)
  ·
    refine ⟨26545012569871495513220159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17696675046580997008813439 26545012569871495513220159)
    ·
      refine ⟨39817518854807243269830239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26545012569871495513220159 39817518854807243269830239)
      ·
        refine ⟨59726278282210864904745359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39817518854807243269830239 59726278282210864904745359)
        ·
          refine ⟨89589417423316297357118039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59726278282210864904745359 89589417423316297357118039)
          ·
            refine ⟨134384126134974446035677059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89589417423316297357118039 134384126134974446035677059)
            ·
              refine ⟨201576189202461669053515589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134384126134974446035677059 201576189202461669053515589)
              ·
                refine ⟨37795535475461562947534173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201576189202461669053515589 37795535475461562947534173)
                ·
                  refine ⟨14173325803298086105325315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37795535475461562947534173 14173325803298086105325315)
                  ·
                    refine ⟨21259988704947129157987973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14173325803298086105325315 21259988704947129157987973)
                    ·
                      refine ⟨3986247882177586717122745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21259988704947129157987973 3986247882177586717122745)
                      ·
                        rfl

theorem cell23_7763190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_7763190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763190 prefixEnd_7763190 := by exact prefixLift 7763190
  have htrace : WordTrace (prefixWord ++ tailWord_7763190) baseStart_7763190 baseEnd_7763190 := by
    simpa [prefixWord, tailWord_7763190, baseEnd_7763190] using wordTrace_append hprefix tailTrace_7763190
  have hstable : (prefixWord ++ tailWord_7763190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763190).length < 2 ^ (prefixWord ++ tailWord_7763190).sum := by decide
  have hdescent : baseEnd_7763190 < baseStart_7763190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763193 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 1, 1, 5]
def baseStart_7763193 : Nat := 118140960795 + 7763193 * 2 ^ 59
def prefixEnd_7763193 : Nat := 4983230072969 + 3 ^ 40 * 7763193 * 2
def baseEnd_7763193 : Nat := 3986249422619550205385231

theorem tailTrace_7763193 : CollatzResearch.WordTrace tailWord_7763193 prefixEnd_7763193 3986249422619550205385231 := by
  unfold tailWord_7763193
  simp only [CollatzResearch.WordTrace]
  refine ⟨283146910164285083653374233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188764606776190055768916155 283146910164285083653374233)
  ·
    refine ⟨212360182623213812740030675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283146910164285083653374233 212360182623213812740030675)
    ·
      refine ⟨318540273934820719110046013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212360182623213812740030675 318540273934820719110046013)
      ·
        refine ⟨119452602725557769666267255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318540273934820719110046013 119452602725557769666267255)
        ·
          refine ⟨179178904088336654499400883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119452602725557769666267255 179178904088336654499400883)
          ·
            refine ⟨268768356132504981749101325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179178904088336654499400883 268768356132504981749101325)
            ·
              refine ⟨100788133549689368155912997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268768356132504981749101325 100788133549689368155912997)
              ·
                refine ⟨18897775040566756529233687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100788133549689368155912997 18897775040566756529233687)
                ·
                  refine ⟨28346662560850134793850531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18897775040566756529233687 28346662560850134793850531)
                  ·
                    refine ⟨42519993841275202190775797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28346662560850134793850531 42519993841275202190775797)
                    ·
                      refine ⟨3986249422619550205385231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42519993841275202190775797 3986249422619550205385231)
                      ·
                        rfl

theorem cell23_7763193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_7763193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763193 prefixEnd_7763193 := by exact prefixLift 7763193
  have htrace : WordTrace (prefixWord ++ tailWord_7763193) baseStart_7763193 baseEnd_7763193 := by
    simpa [prefixWord, tailWord_7763193, baseEnd_7763193] using wordTrace_append hprefix tailTrace_7763193
  have hstable : (prefixWord ++ tailWord_7763193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763193).length < 2 ^ (prefixWord ++ tailWord_7763193).sum := by decide
  have hdescent : baseEnd_7763193 < baseStart_7763193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763203 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 6]
def baseStart_7763203 : Nat := 118140960795 + 7763203 * 2 ^ 59
def prefixEnd_7763203 : Nat := 4983230072969 + 3 ^ 40 * 7763203 * 2
def baseEnd_7763203 : Nat := 3986254557426095166260185

theorem tailTrace_7763203 : CollatzResearch.WordTrace tailWord_7763203 prefixEnd_7763203 3986254557426095166260185 := by
  unfold tailWord_7763203
  simp only [CollatzResearch.WordTrace]
  refine ⟨283147274894248855361238263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188764849929499236907492175 283147274894248855361238263)
  ·
    refine ⟨424720912341373283041857395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283147274894248855361238263 424720912341373283041857395)
    ·
      refine ⟨637081368512059924562786093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424720912341373283041857395 637081368512059924562786093)
      ·
        refine ⟨238905513192022471711044785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 637081368512059924562786093 238905513192022471711044785)
        ·
          refine ⟨179179134894016853783283589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238905513192022471711044785 179179134894016853783283589)
          ·
            refine ⟨33596087792628160084365673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179179134894016853783283589 33596087792628160084365673)
            ·
              refine ⟨25197065844471120063274255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33596087792628160084365673 25197065844471120063274255)
              ·
                refine ⟨37795598766706680094911383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25197065844471120063274255 37795598766706680094911383)
                ·
                  refine ⟨56693398150060020142367075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37795598766706680094911383 56693398150060020142367075)
                  ·
                    refine ⟨85040097225090030213550613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56693398150060020142367075 85040097225090030213550613)
                    ·
                      refine ⟨3986254557426095166260185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85040097225090030213550613 3986254557426095166260185)
                      ·
                        rfl

theorem cell23_7763203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_7763203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763203 prefixEnd_7763203 := by exact prefixLift 7763203
  have htrace : WordTrace (prefixWord ++ tailWord_7763203) baseStart_7763203 baseEnd_7763203 := by
    simpa [prefixWord, tailWord_7763203, baseEnd_7763203] using wordTrace_append hprefix tailTrace_7763203
  have hstable : (prefixWord ++ tailWord_7763203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763203).length < 2 ^ (prefixWord ++ tailWord_7763203).sum := by decide
  have hdescent : baseEnd_7763203 < baseStart_7763203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763230 : List Nat := [4, 3, 2, 1, 13]
def baseStart_7763230 : Nat := 118140960795 + 7763230 * 2 ^ 59
def prefixEnd_7763230 : Nat := 4983230072969 + 3 ^ 40 * 7763230 * 2
def baseEnd_7763230 : Nat := 5468132265300091304009

theorem tailTrace_7763230 : CollatzResearch.WordTrace tailWord_7763230 prefixEnd_7763230 5468132265300091304009 := by
  unfold tailWord_7763230
  simp only [CollatzResearch.WordTrace]
  refine ⟨35393532458143879871558893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188765506443434025981647429 35393532458143879871558893)
  ·
    refine ⟨13272574671803954951834585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35393532458143879871558893 13272574671803954951834585)
    ·
      refine ⟨9954431003852966213875939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13272574671803954951834585 9954431003852966213875939)
      ·
        refine ⟨14931646505779449320813909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9954431003852966213875939 14931646505779449320813909)
        ·
          refine ⟨5468132265300091304009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 14931646505779449320813909 5468132265300091304009)
          ·
            rfl

theorem cell23_7763230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 13].length) (baseStart_7763230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763230 prefixEnd_7763230 := by exact prefixLift 7763230
  have htrace : WordTrace (prefixWord ++ tailWord_7763230) baseStart_7763230 baseEnd_7763230 := by
    simpa [prefixWord, tailWord_7763230, baseEnd_7763230] using wordTrace_append hprefix tailTrace_7763230
  have hstable : (prefixWord ++ tailWord_7763230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763230).length < 2 ^ (prefixWord ++ tailWord_7763230).sum := by decide
  have hdescent : baseEnd_7763230 < baseStart_7763230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763234 : List Nat := [3, 3, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_7763234 : Nat := 118140960795 + 7763234 * 2 ^ 59
def prefixEnd_7763234 : Nat := 4983230072969 + 3 ^ 40 * 7763234 * 2
def baseEnd_7763234 : Nat := 1328756825108794848324181

theorem tailTrace_7763234 : CollatzResearch.WordTrace tailWord_7763234 prefixEnd_7763234 1328756825108794848324181 := by
  unfold tailWord_7763234
  simp only [CollatzResearch.WordTrace]
  refine ⟨70787101389284136913904189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188765603704757698437077837 70787101389284136913904189)
  ·
    refine ⟨26545163020981551342714071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70787101389284136913904189 26545163020981551342714071)
    ·
      refine ⟨39817744531472327014071107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26545163020981551342714071 39817744531472327014071107)
      ·
        refine ⟨59726616797208490521106661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39817744531472327014071107 59726616797208490521106661)
        ·
          refine ⟨11198740649476591972707499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59726616797208490521106661 11198740649476591972707499)
          ·
            refine ⟨16798110974214887959061249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11198740649476591972707499 16798110974214887959061249)
            ·
              refine ⟨12598583230661165969295937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16798110974214887959061249 12598583230661165969295937)
              ·
                refine ⟨9448937422995874476971953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12598583230661165969295937 9448937422995874476971953)
                ·
                  refine ⟨7086703067246905857728965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9448937422995874476971953 7086703067246905857728965)
                  ·
                    refine ⟨1328756825108794848324181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7086703067246905857728965 1328756825108794848324181)
                    ·
                      rfl

theorem cell23_7763234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_7763234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763234 prefixEnd_7763234 := by exact prefixLift 7763234
  have htrace : WordTrace (prefixWord ++ tailWord_7763234) baseStart_7763234 baseEnd_7763234 := by
    simpa [prefixWord, tailWord_7763234, baseEnd_7763234] using wordTrace_append hprefix tailTrace_7763234
  have hstable : (prefixWord ++ tailWord_7763234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763234).length < 2 ^ (prefixWord ++ tailWord_7763234).sum := by decide
  have hdescent : baseEnd_7763234 < baseStart_7763234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763267 : List Nat := [1, 1, 1, 3, 1, 3, 1, 6, 1, 3, 2]
def baseStart_7763267 : Nat := 118140960795 + 7763267 * 2 ^ 59
def prefixEnd_7763267 : Nat := 4983230072969 + 3 ^ 40 * 7763267 * 2
def baseEnd_7763267 : Nat := 3986287420187982915859891

theorem tailTrace_7763267 : CollatzResearch.WordTrace tailWord_7763267 prefixEnd_7763267 3986287420187982915859891 := by
  unfold tailWord_7763267
  simp only [CollatzResearch.WordTrace]
  refine ⟨283149609166016994291568055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188766406110677996194378703 283149609166016994291568055)
  ·
    refine ⟨424724413749025491437352083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283149609166016994291568055 424724413749025491437352083)
    ·
      refine ⟨637086620623538237156028125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424724413749025491437352083 637086620623538237156028125)
      ·
        refine ⟨238907482733826838933510547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 637086620623538237156028125 238907482733826838933510547)
        ·
          refine ⟨358361224100740258400265821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238907482733826838933510547 358361224100740258400265821)
          ·
            refine ⟨134385459037777596900099683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358361224100740258400265821 134385459037777596900099683)
            ·
              refine ⟨201578188556666395350149525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134385459037777596900099683 201578188556666395350149525)
              ·
                refine ⟨9448977588593737282038259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201578188556666395350149525 9448977588593737282038259)
                ·
                  refine ⟨14173466382890605923057389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9448977588593737282038259 14173466382890605923057389)
                  ·
                    refine ⟨5315049893583977221146521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14173466382890605923057389 5315049893583977221146521)
                    ·
                      refine ⟨3986287420187982915859891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5315049893583977221146521 3986287420187982915859891)
                      ·
                        rfl

theorem cell23_7763267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 3, 2].length) (baseStart_7763267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763267 prefixEnd_7763267 := by exact prefixLift 7763267
  have htrace : WordTrace (prefixWord ++ tailWord_7763267) baseStart_7763267 baseEnd_7763267 := by
    simpa [prefixWord, tailWord_7763267, baseEnd_7763267] using wordTrace_append hprefix tailTrace_7763267
  have hstable : (prefixWord ++ tailWord_7763267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763267).length < 2 ^ (prefixWord ++ tailWord_7763267).sum := by decide
  have hdescent : baseEnd_7763267 < baseStart_7763267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763283 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 5]
def baseStart_7763283 : Nat := 118140960795 + 7763283 * 2 ^ 59
def prefixEnd_7763283 : Nat := 4983230072969 + 3 ^ 40 * 7763283 * 2
def baseEnd_7763283 : Nat := 3986295635878454853259817

theorem tailTrace_7763283 : CollatzResearch.WordTrace tailWord_7763283 prefixEnd_7763283 3986295635878454853259817 := by
  unfold tailWord_7763283
  simp only [CollatzResearch.WordTrace]
  refine ⟨283150192733959029024150503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188766795155972686016100335 283150192733959029024150503)
  ·
    refine ⟨424725289100938543536225755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283150192733959029024150503 424725289100938543536225755)
    ·
      refine ⟨637087933651407815304338633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424725289100938543536225755 637087933651407815304338633)
      ·
        refine ⟨477815950238555861478253975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 637087933651407815304338633 477815950238555861478253975)
        ·
          refine ⟨716723925357833792217380963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477815950238555861478253975 716723925357833792217380963)
          ·
            refine ⟨1075085888036750688326071445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716723925357833792217380963 1075085888036750688326071445)
            ·
              refine ⟨50394651001722688515284599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1075085888036750688326071445 50394651001722688515284599)
              ·
                refine ⟨75591976502584032772926899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50394651001722688515284599 75591976502584032772926899)
                ·
                  refine ⟨113387964753876049159390349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75591976502584032772926899 113387964753876049159390349)
                  ·
                    refine ⟨42520486782703518434771381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113387964753876049159390349 42520486782703518434771381)
                    ·
                      refine ⟨3986295635878454853259817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42520486782703518434771381 3986295635878454853259817)
                      ·
                        rfl

theorem cell23_7763283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_7763283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763283 prefixEnd_7763283 := by exact prefixLift 7763283
  have htrace : WordTrace (prefixWord ++ tailWord_7763283) baseStart_7763283 baseEnd_7763283 := by
    simpa [prefixWord, tailWord_7763283, baseEnd_7763283] using wordTrace_append hprefix tailTrace_7763283
  have hstable : (prefixWord ++ tailWord_7763283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763283).length < 2 ^ (prefixWord ++ tailWord_7763283).sum := by decide
  have hdescent : baseEnd_7763283 < baseStart_7763283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763284 : List Nat := [2, 4, 1, 1, 2, 1, 3, 3, 1, 3, 2]
def baseStart_7763284 : Nat := 118140960795 + 7763284 * 2 ^ 59
def prefixEnd_7763284 : Nat := 4983230072969 + 3 ^ 40 * 7763284 * 2
def baseEnd_7763284 : Nat := 3986296149359109349347313

theorem tailTrace_7763284 : CollatzResearch.WordTrace tailWord_7763284 prefixEnd_7763284 3986296149359109349347313 := by
  unfold tailWord_7763284
  simp only [CollatzResearch.WordTrace]
  refine ⟨141575114603477703097468453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188766819471303604129957937 141575114603477703097468453)
  ·
    refine ⟨26545333988152069330775335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141575114603477703097468453 26545333988152069330775335)
    ·
      refine ⟨39818000982228103996163003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26545333988152069330775335 39818000982228103996163003)
      ·
        refine ⟨59727001473342155994244505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39818000982228103996163003 59727001473342155994244505)
        ·
          refine ⟨44795251105006616995683379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59727001473342155994244505 44795251105006616995683379)
          ·
            refine ⟨67192876657509925493525069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44795251105006616995683379 67192876657509925493525069)
            ·
              refine ⟨25197328746566222060071901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67192876657509925493525069 25197328746566222060071901)
              ·
                refine ⟨9448998279962333272526963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25197328746566222060071901 9448998279962333272526963)
                ·
                  refine ⟨14173497419943499908790445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9448998279962333272526963 14173497419943499908790445)
                  ·
                    refine ⟨5315061532478812465796417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14173497419943499908790445 5315061532478812465796417)
                    ·
                      refine ⟨3986296149359109349347313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5315061532478812465796417 3986296149359109349347313)
                      ·
                        rfl

theorem cell23_7763284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_7763284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763284 prefixEnd_7763284 := by exact prefixLift 7763284
  have htrace : WordTrace (prefixWord ++ tailWord_7763284) baseStart_7763284 baseEnd_7763284 := by
    simpa [prefixWord, tailWord_7763284, baseEnd_7763284] using wordTrace_append hprefix tailTrace_7763284
  have hstable : (prefixWord ++ tailWord_7763284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763284).length < 2 ^ (prefixWord ++ tailWord_7763284).sum := by decide
  have hdescent : baseEnd_7763284 < baseStart_7763284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763354 : List Nat := [3, 1, 1, 4, 1, 1, 5, 2, 5]
def baseStart_7763354 : Nat := 118140960795 + 7763354 * 2 ^ 59
def prefixEnd_7763354 : Nat := 4983230072969 + 3 ^ 40 * 7763354 * 2
def baseEnd_7763354 : Nat := 442925788111658230607999

theorem tailTrace_7763354 : CollatzResearch.WordTrace tailWord_7763354 prefixEnd_7763354 442925788111658230607999 := by
  unfold tailWord_7763354
  simp only [CollatzResearch.WordTrace]
  refine ⟨70788195579175452037496279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188768521544467872099990077 70788195579175452037496279)
  ·
    refine ⟨106182293368763178056244419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70788195579175452037496279 106182293368763178056244419)
    ·
      refine ⟨159273440053144767084366629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106182293368763178056244419 159273440053144767084366629)
      ·
        refine ⟨29863770009964643828318743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159273440053144767084366629 29863770009964643828318743)
        ·
          refine ⟨44795655014946965742478115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29863770009964643828318743 44795655014946965742478115)
          ·
            refine ⟨67193482522420448613717173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44795655014946965742478115 67193482522420448613717173)
            ·
              refine ⟨6299388986476917057535985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67193482522420448613717173 6299388986476917057535985)
              ·
                refine ⟨4724541739857687793151989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6299388986476917057535985 4724541739857687793151989)
                ·
                  refine ⟨442925788111658230607999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4724541739857687793151989 442925788111658230607999)
                  ·
                    rfl

theorem cell23_7763354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 5].length) (baseStart_7763354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763354 prefixEnd_7763354 := by exact prefixLift 7763354
  have htrace : WordTrace (prefixWord ++ tailWord_7763354) baseStart_7763354 baseEnd_7763354 := by
    simpa [prefixWord, tailWord_7763354, baseEnd_7763354] using wordTrace_append hprefix tailTrace_7763354
  have hstable : (prefixWord ++ tailWord_7763354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763354).length < 2 ^ (prefixWord ++ tailWord_7763354).sum := by decide
  have hdescent : baseEnd_7763354 < baseStart_7763354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763360 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 5]
def baseStart_7763360 : Nat := 118140960795 + 7763360 * 2 ^ 59
def prefixEnd_7763360 : Nat := 4983230072969 + 3 ^ 40 * 7763360 * 2
def baseEnd_7763360 : Nat := 3986335173888851051996963

theorem tailTrace_7763360 : CollatzResearch.WordTrace tailWord_7763360 prefixEnd_7763360 3986335173888851051996963 := by
  unfold tailWord_7763360
  simp only [CollatzResearch.WordTrace]
  refine ⟨141576500577340035587351767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188768667436453380783135689 141576500577340035587351767)
  ·
    refine ⟨212364750866010053381027651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141576500577340035587351767 212364750866010053381027651)
    ·
      refine ⟨318547126299015080071541477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212364750866010053381027651 318547126299015080071541477)
      ·
        refine ⟨59727586181065327513414027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318547126299015080071541477 59727586181065327513414027)
        ·
          refine ⟨89591379271597991270121041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59727586181065327513414027 89591379271597991270121041)
          ·
            refine ⟨67193534453698493452590781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89591379271597991270121041 67193534453698493452590781)
            ·
              refine ⟨25197575420136935044721543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67193534453698493452590781 25197575420136935044721543)
              ·
                refine ⟨37796363130205402567082315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25197575420136935044721543 37796363130205402567082315)
                ·
                  refine ⟨56694544695308103850623473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37796363130205402567082315 56694544695308103850623473)
                  ·
                    refine ⟨42520908521481077887967605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56694544695308103850623473 42520908521481077887967605)
                    ·
                      refine ⟨3986335173888851051996963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42520908521481077887967605 3986335173888851051996963)
                      ·
                        rfl

theorem cell23_7763360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_7763360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763360 prefixEnd_7763360 := by exact prefixLift 7763360
  have htrace : WordTrace (prefixWord ++ tailWord_7763360) baseStart_7763360 baseEnd_7763360 := by
    simpa [prefixWord, tailWord_7763360, baseEnd_7763360] using wordTrace_append hprefix tailTrace_7763360
  have hstable : (prefixWord ++ tailWord_7763360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763360).length < 2 ^ (prefixWord ++ tailWord_7763360).sum := by decide
  have hdescent : baseEnd_7763360 < baseStart_7763360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763400 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_7763400 : Nat := 118140960795 + 7763400 * 2 ^ 59
def prefixEnd_7763400 : Nat := 4983230072969 + 3 ^ 40 * 7763400 * 2
def baseEnd_7763400 : Nat := 3986355713115030895496779

theorem tailTrace_7763400 : CollatzResearch.WordTrace tailWord_7763400 prefixEnd_7763400 3986355713115030895496779 := by
  unfold tailWord_7763400
  simp only [CollatzResearch.WordTrace]
  refine ⟨141577230037267579003079827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188769640049690105337439769 141577230037267579003079827)
  ·
    refine ⟨212365845055901368504619741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141577230037267579003079827 212365845055901368504619741)
    ·
      refine ⟨79637191895963013189232403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212365845055901368504619741 79637191895963013189232403)
      ·
        refine ⟨119455787843944519783848605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79637191895963013189232403 119455787843944519783848605)
        ·
          refine ⟨44795920441479194918943227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119455787843944519783848605 44795920441479194918943227)
          ·
            refine ⟨67193880662218792378414841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44795920441479194918943227 67193880662218792378414841)
            ·
              refine ⟨50395410496664094283811131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67193880662218792378414841 50395410496664094283811131)
              ·
                refine ⟨75593115744996141425716697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50395410496664094283811131 75593115744996141425716697)
                ·
                  refine ⟨56694836808747106069287523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75593115744996141425716697 56694836808747106069287523)
                  ·
                    refine ⟨85042255213120659103931285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56694836808747106069287523 85042255213120659103931285)
                    ·
                      refine ⟨3986355713115030895496779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85042255213120659103931285 3986355713115030895496779)
                      ·
                        rfl

theorem cell23_7763400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_7763400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763400 prefixEnd_7763400 := by exact prefixLift 7763400
  have htrace : WordTrace (prefixWord ++ tailWord_7763400) baseStart_7763400 baseEnd_7763400 := by
    simpa [prefixWord, tailWord_7763400, baseEnd_7763400] using wordTrace_append hprefix tailTrace_7763400
  have hstable : (prefixWord ++ tailWord_7763400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763400).length < 2 ^ (prefixWord ++ tailWord_7763400).sum := by decide
  have hdescent : baseEnd_7763400 < baseStart_7763400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763407 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 3]
def baseStart_7763407 : Nat := 118140960795 + 7763407 * 2 ^ 59
def prefixEnd_7763407 : Nat := 4983230072969 + 3 ^ 40 * 7763407 * 2
def baseEnd_7763407 : Nat := 3986359307479612368109247

theorem tailTrace_7763407 : CollatzResearch.WordTrace tailWord_7763407 prefixEnd_7763407 3986359307479612368109247 := by
  unfold tailWord_7763407
  simp only [CollatzResearch.WordTrace]
  refine ⟨283154715385509798201664475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188769810257006532134442983 283154715385509798201664475)
  ·
    refine ⟨424732073078264697302496713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283154715385509798201664475 424732073078264697302496713)
    ·
      refine ⟨318549054808698522976872535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424732073078264697302496713 318549054808698522976872535)
      ·
        refine ⟨477823582213047784465308803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318549054808698522976872535 477823582213047784465308803)
        ·
          refine ⟨716735373319571676697963205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477823582213047784465308803 716735373319571676697963205)
          ·
            refine ⟨134387882497419689380868101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 716735373319571676697963205 134387882497419689380868101)
            ·
              refine ⟨25197727968266191758912769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134387882497419689380868101 25197727968266191758912769)
              ·
                refine ⟨18898295976199643819184577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25197727968266191758912769 18898295976199643819184577)
                ·
                  refine ⟨14173721982149732864388433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18898295976199643819184577 14173721982149732864388433)
                  ·
                    refine ⟨10630291486612299648291325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14173721982149732864388433 10630291486612299648291325)
                    ·
                      refine ⟨3986359307479612368109247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10630291486612299648291325 3986359307479612368109247)
                      ·
                        rfl

theorem cell23_7763407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 3].length) (baseStart_7763407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763407 prefixEnd_7763407 := by exact prefixLift 7763407
  have htrace : WordTrace (prefixWord ++ tailWord_7763407) baseStart_7763407 baseEnd_7763407 := by
    simpa [prefixWord, tailWord_7763407, baseEnd_7763407] using wordTrace_append hprefix tailTrace_7763407
  have hstable : (prefixWord ++ tailWord_7763407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763407).length < 2 ^ (prefixWord ++ tailWord_7763407).sum := by decide
  have hdescent : baseEnd_7763407 < baseStart_7763407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763427 : List Nat := [1, 1, 1, 6, 2, 1, 2, 3, 6]
def baseStart_7763427 : Nat := 118140960795 + 7763427 * 2 ^ 59
def prefixEnd_7763427 : Nat := 4983230072969 + 3 ^ 40 * 7763427 * 2
def baseEnd_7763427 : Nat := 442929953010300254428795

theorem tailTrace_7763427 : CollatzResearch.WordTrace tailWord_7763427 prefixEnd_7763427 442929953010300254428795 := by
  unfold tailWord_7763427
  simp only [CollatzResearch.WordTrace]
  refine ⟨283155444845437341617392535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188770296563624894411595023 283155444845437341617392535)
  ·
    refine ⟨424733167268156012426088803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283155444845437341617392535 424733167268156012426088803)
    ·
      refine ⟨637099750902234018639133205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424733167268156012426088803 637099750902234018639133205)
      ·
        refine ⟨29864050823542219623709369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 637099750902234018639133205 29864050823542219623709369)
        ·
          refine ⟨22398038117656664717782027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29864050823542219623709369 22398038117656664717782027)
          ·
            refine ⟨33597057176484997076673041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22398038117656664717782027 33597057176484997076673041)
            ·
              refine ⟨25197792882363747807504781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33597057176484997076673041 25197792882363747807504781)
              ·
                refine ⟨9449172330886405427814293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25197792882363747807504781 9449172330886405427814293)
                ·
                  refine ⟨442929953010300254428795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9449172330886405427814293 442929953010300254428795)
                  ·
                    rfl

theorem cell23_7763427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 6].length) (baseStart_7763427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763427 prefixEnd_7763427 := by exact prefixLift 7763427
  have htrace : WordTrace (prefixWord ++ tailWord_7763427) baseStart_7763427 baseEnd_7763427 := by
    simpa [prefixWord, tailWord_7763427, baseEnd_7763427] using wordTrace_append hprefix tailTrace_7763427
  have hstable : (prefixWord ++ tailWord_7763427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763427).length < 2 ^ (prefixWord ++ tailWord_7763427).sum := by decide
  have hdescent : baseEnd_7763427 < baseStart_7763427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763464 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 2, 3, 2]
def baseStart_7763464 : Nat := 118140960795 + 7763464 * 2 ^ 59
def prefixEnd_7763464 : Nat := 4983230072969 + 3 ^ 40 * 7763464 * 2
def baseEnd_7763464 : Nat := 3986388575876918645096485

theorem tailTrace_7763464 : CollatzResearch.WordTrace tailWord_7763464 prefixEnd_7763464 3986388575876918645096485 := by
  unfold tailWord_7763464
  simp only [CollatzResearch.WordTrace]
  refine ⟨141578397173151648468244723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188771196230868864624326297 141578397173151648468244723)
  ·
    refine ⟨212367595759727472702367085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141578397173151648468244723 212367595759727472702367085)
    ·
      refine ⟨79637848409897802263387657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212367595759727472702367085 79637848409897802263387657)
      ·
        refine ⟨59728386307423351697540743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79637848409897802263387657 59728386307423351697540743)
        ·
          refine ⟨89592579461135027546311115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59728386307423351697540743 89592579461135027546311115)
          ·
            refine ⟨134388869191702541319466673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89592579461135027546311115 134388869191702541319466673)
            ·
              refine ⟨100791651893776905989600005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134388869191702541319466673 100791651893776905989600005)
              ·
                refine ⟨18898434730083169873050001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100791651893776905989600005 18898434730083169873050001)
                ·
                  refine ⟨14173826047562377404787501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18898434730083169873050001 14173826047562377404787501)
                  ·
                    refine ⟨5315184767835891526795313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14173826047562377404787501 5315184767835891526795313)
                    ·
                      refine ⟨3986388575876918645096485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5315184767835891526795313 3986388575876918645096485)
                      ·
                        rfl

theorem cell23_7763464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_7763464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763464 prefixEnd_7763464 := by exact prefixLift 7763464
  have htrace : WordTrace (prefixWord ++ tailWord_7763464) baseStart_7763464 baseEnd_7763464 := by
    simpa [prefixWord, tailWord_7763464, baseEnd_7763464] using wordTrace_append hprefix tailTrace_7763464
  have hstable : (prefixWord ++ tailWord_7763464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763464).length < 2 ^ (prefixWord ++ tailWord_7763464).sum := by decide
  have hdescent : baseEnd_7763464 < baseStart_7763464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763487 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 1, 6]
def baseStart_7763487 : Nat := 118140960795 + 7763487 * 2 ^ 59
def prefixEnd_7763487 : Nat := 4983230072969 + 3 ^ 40 * 7763487 * 2
def baseEnd_7763487 : Nat := 1328800128643990685036293

theorem tailTrace_7763487 : CollatzResearch.WordTrace tailWord_7763487 prefixEnd_7763487 1328800128643990685036293 := by
  unfold tailWord_7763487
  simp only [CollatzResearch.WordTrace]
  refine ⟨283157633225219971864576715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188771755483479981243051143 283157633225219971864576715)
  ·
    refine ⟨424736449837829957796865073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283157633225219971864576715 424736449837829957796865073)
    ·
      refine ⟨318552337378372468347648805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424736449837829957796865073 318552337378372468347648805)
      ·
        refine ⟨59728563258444837815184151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318552337378372468347648805 59728563258444837815184151)
        ·
          refine ⟨89592844887667256722776227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59728563258444837815184151 89592844887667256722776227)
          ·
            refine ⟨134389267331500885084164341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89592844887667256722776227 134389267331500885084164341)
            ·
              refine ⟨12598993812328207976640407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134389267331500885084164341 12598993812328207976640407)
              ·
                refine ⟨18898490718492311964960611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12598993812328207976640407 18898490718492311964960611)
                ·
                  refine ⟨28347736077738467947440917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18898490718492311964960611 28347736077738467947440917)
                  ·
                    refine ⟨1328800128643990685036293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28347736077738467947440917 1328800128643990685036293)
                    ·
                      rfl

theorem cell23_7763487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 6].length) (baseStart_7763487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763487 prefixEnd_7763487 := by exact prefixLift 7763487
  have htrace : WordTrace (prefixWord ++ tailWord_7763487) baseStart_7763487 baseEnd_7763487 := by
    simpa [prefixWord, tailWord_7763487, baseEnd_7763487] using wordTrace_append hprefix tailTrace_7763487
  have hstable : (prefixWord ++ tailWord_7763487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763487).length < 2 ^ (prefixWord ++ tailWord_7763487).sum := by decide
  have hdescent : baseEnd_7763487 < baseStart_7763487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763514 : List Nat := [3, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3]
def baseStart_7763514 : Nat := 118140960795 + 7763514 * 2 ^ 59
def prefixEnd_7763514 : Nat := 4983230072969 + 3 ^ 40 * 7763514 * 2
def baseEnd_7763514 : Nat := 3986414249909643449471255

theorem tailTrace_7763514 : CollatzResearch.WordTrace tailWord_7763514 prefixEnd_7763514 3986414249909643449471255 := by
  unfold tailWord_7763514
  simp only [CollatzResearch.WordTrace]
  refine ⟨70789654499030538868952399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188772411997414770317206397 70789654499030538868952399)
  ·
    refine ⟨106184481748545808303428599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70789654499030538868952399 106184481748545808303428599)
    ·
      refine ⟨159276722622818712455142899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106184481748545808303428599 159276722622818712455142899)
      ·
        refine ⟨238915083934228068682714349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159276722622818712455142899 238915083934228068682714349)
        ·
          refine ⟨89593156475335525756017881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238915083934228068682714349 89593156475335525756017881)
          ·
            refine ⟨67194867356501644317013411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89593156475335525756017881 67194867356501644317013411)
            ·
              refine ⟨100792301034752466475520117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67194867356501644317013411 100792301034752466475520117)
              ·
                refine ⟨9449278222008043732080011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100792301034752466475520117 9449278222008043732080011)
                ·
                  refine ⟨14173917333012065598120017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9449278222008043732080011 14173917333012065598120017)
                  ·
                    refine ⟨10630437999759049198590013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14173917333012065598120017 10630437999759049198590013)
                    ·
                      refine ⟨3986414249909643449471255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10630437999759049198590013 3986414249909643449471255)
                      ·
                        rfl

theorem cell23_7763514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_7763514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763514 prefixEnd_7763514 := by exact prefixLift 7763514
  have htrace : WordTrace (prefixWord ++ tailWord_7763514) baseStart_7763514 baseEnd_7763514 := by
    simpa [prefixWord, tailWord_7763514, baseEnd_7763514] using wordTrace_append hprefix tailTrace_7763514
  have hstable : (prefixWord ++ tailWord_7763514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763514).length < 2 ^ (prefixWord ++ tailWord_7763514).sum := by decide
  have hdescent : baseEnd_7763514 < baseStart_7763514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763538 : List Nat := [3, 2, 2, 1, 2, 4, 2, 1, 2, 4]
def baseStart_7763538 : Nat := 118140960795 + 7763538 * 2 ^ 59
def prefixEnd_7763538 : Nat := 4983230072969 + 3 ^ 40 * 7763538 * 2
def baseEnd_7763538 : Nat := 1328808857815117118523715

theorem tailTrace_7763538 : CollatzResearch.WordTrace tailWord_7763538 prefixEnd_7763538 1328808857815117118523715 := by
  unfold tailWord_7763538
  simp only [CollatzResearch.WordTrace]
  refine ⟨70789873337008801893670817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188772995565356805049788845 70789873337008801893670817)
  ·
    refine ⟨53092405002756601420253113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70789873337008801893670817 53092405002756601420253113)
    ·
      refine ⟨39819303752067451065189835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53092405002756601420253113 39819303752067451065189835)
      ·
        refine ⟨59728955628101176597784753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39819303752067451065189835 59728955628101176597784753)
        ·
          refine ⟨44796716721075882448338565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59728955628101176597784753 44796716721075882448338565)
          ·
            refine ⟨8399384385201727959063481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44796716721075882448338565 8399384385201727959063481)
            ·
              refine ⟨6299538288901295969297611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8399384385201727959063481 6299538288901295969297611)
              ·
                refine ⟨9449307433351943953946417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6299538288901295969297611 9449307433351943953946417)
                ·
                  refine ⟨7086980575013957965459813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9449307433351943953946417 7086980575013957965459813)
                  ·
                    refine ⟨1328808857815117118523715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7086980575013957965459813 1328808857815117118523715)
                    ·
                      rfl

theorem cell23_7763538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_7763538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763538 prefixEnd_7763538 := by exact prefixLift 7763538
  have htrace : WordTrace (prefixWord ++ tailWord_7763538) baseStart_7763538 baseEnd_7763538 := by
    simpa [prefixWord, tailWord_7763538, baseEnd_7763538] using wordTrace_append hprefix tailTrace_7763538
  have hstable : (prefixWord ++ tailWord_7763538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763538).length < 2 ^ (prefixWord ++ tailWord_7763538).sum := by decide
  have hdescent : baseEnd_7763538 < baseStart_7763538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763542 : List Nat := [5, 2, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_7763542 : Nat := 118140960795 + 7763542 * 2 ^ 59
def prefixEnd_7763542 : Nat := 4983230072969 + 3 ^ 40 * 7763542 * 2
def baseEnd_7763542 : Nat := 1328809542455989779973709

theorem tailTrace_7763542 : CollatzResearch.WordTrace tailWord_7763542 prefixEnd_7763542 1328809542455989779973709 := by
  unfold tailWord_7763542
  simp only [CollatzResearch.WordTrace]
  refine ⟨17697477452501294766114305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188773092826680477505219253 17697477452501294766114305)
  ·
    refine ⟨13273108089375971074585729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17697477452501294766114305 13273108089375971074585729)
    ·
      refine ⟨9954831067031978305939297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13273108089375971074585729 9954831067031978305939297)
      ·
        refine ⟨7466123300273983729454473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9954831067031978305939297 7466123300273983729454473)
        ·
          refine ⟨5599592475205487797090855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7466123300273983729454473 5599592475205487797090855)
          ·
            refine ⟨8399388712808231695636283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5599592475205487797090855 8399388712808231695636283)
            ·
              refine ⟨12599083069212347543454425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8399388712808231695636283 12599083069212347543454425)
              ·
                refine ⟨9449312301909260657590819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12599083069212347543454425 9449312301909260657590819)
                ·
                  refine ⟨14173968452863890986386229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9449312301909260657590819 14173968452863890986386229)
                  ·
                    refine ⟨1328809542455989779973709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14173968452863890986386229 1328809542455989779973709)
                    ·
                      rfl

theorem cell23_7763542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_7763542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763542 prefixEnd_7763542 := by exact prefixLift 7763542
  have htrace : WordTrace (prefixWord ++ tailWord_7763542) baseStart_7763542 baseEnd_7763542 := by
    simpa [prefixWord, tailWord_7763542, baseEnd_7763542] using wordTrace_append hprefix tailTrace_7763542
  have hstable : (prefixWord ++ tailWord_7763542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763542).length < 2 ^ (prefixWord ++ tailWord_7763542).sum := by decide
  have hdescent : baseEnd_7763542 < baseStart_7763542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763548 : List Nat := [2, 2, 4, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_7763548 : Nat := 118140960795 + 7763548 * 2 ^ 59
def prefixEnd_7763548 : Nat := 4983230072969 + 3 ^ 40 * 7763548 * 2
def baseEnd_7763548 : Nat := 3986431708251896316446099

theorem tailTrace_7763548 : CollatzResearch.WordTrace tailWord_7763548 prefixEnd_7763548 3986431708251896316446099 := by
  unfold tailWord_7763548
  simp only [CollatzResearch.WordTrace]
  refine ⟨141579929038999489641273649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188773238718665986188364865 141579929038999489641273649)
  ·
    refine ⟨106184946779249617230955237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141579929038999489641273649 106184946779249617230955237)
    ·
      refine ⟨19909677521109303230804107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106184946779249617230955237 19909677521109303230804107)
      ·
        refine ⟨29864516281663954846206161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19909677521109303230804107 29864516281663954846206161)
        ·
          refine ⟨22398387211247966134654621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29864516281663954846206161 22398387211247966134654621)
          ·
            refine ⟨8399395204217987300495483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22398387211247966134654621 8399395204217987300495483)
            ·
              refine ⟨12599092806326980950743225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8399395204217987300495483 12599092806326980950743225)
              ·
                refine ⟨9449319604745235713057419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12599092806326980950743225 9449319604745235713057419)
                ·
                  refine ⟨14173979407117853569586129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9449319604745235713057419 14173979407117853569586129)
                  ·
                    refine ⟨10630484555338390177189597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14173979407117853569586129 10630484555338390177189597)
                    ·
                      refine ⟨3986431708251896316446099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10630484555338390177189597 3986431708251896316446099)
                      ·
                        rfl

theorem cell23_7763548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_7763548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763548 prefixEnd_7763548 := by exact prefixLift 7763548
  have htrace : WordTrace (prefixWord ++ tailWord_7763548) baseStart_7763548 baseEnd_7763548 := by
    simpa [prefixWord, tailWord_7763548, baseEnd_7763548] using wordTrace_append hprefix tailTrace_7763548
  have hstable : (prefixWord ++ tailWord_7763548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763548).length < 2 ^ (prefixWord ++ tailWord_7763548).sum := by decide
  have hdescent : baseEnd_7763548 < baseStart_7763548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763577 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 2, 6]
def baseStart_7763577 : Nat := 118140960795 + 7763577 * 2 ^ 59
def prefixEnd_7763577 : Nat := 4983230072969 + 3 ^ 40 * 7763577 * 2
def baseEnd_7763577 : Nat := 1328815533063625567661155

theorem tailTrace_7763577 : CollatzResearch.WordTrace tailWord_7763577 prefixEnd_7763577 1328815533063625567661155 := by
  unfold tailWord_7763577
  simp only [CollatzResearch.WordTrace]
  refine ⟨283160915794893917235352985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188773943863262611490235323 283160915794893917235352985)
  ·
    refine ⟨212370686846170437926514739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283160915794893917235352985 212370686846170437926514739)
    ·
      refine ⟨318556030269255656889772109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212370686846170437926514739 318556030269255656889772109)
      ·
        refine ⟨119458511350970871333664541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318556030269255656889772109 119458511350970871333664541)
        ·
          refine ⟨44796941756614076750124203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119458511350970871333664541 44796941756614076750124203)
          ·
            refine ⟨67195412634921115125186305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44796941756614076750124203 67195412634921115125186305)
            ·
              refine ⟨50396559476190836343889729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67195412634921115125186305 50396559476190836343889729)
              ·
                refine ⟨37797419607143127257917297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50396559476190836343889729 37797419607143127257917297)
                ·
                  refine ⟨28348064705357345443437973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37797419607143127257917297 28348064705357345443437973)
                  ·
                    refine ⟨1328815533063625567661155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28348064705357345443437973 1328815533063625567661155)
                    ·
                      rfl

theorem cell23_7763577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 6].length) (baseStart_7763577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763577 prefixEnd_7763577 := by exact prefixLift 7763577
  have htrace : WordTrace (prefixWord ++ tailWord_7763577) baseStart_7763577 baseEnd_7763577 := by
    simpa [prefixWord, tailWord_7763577, baseEnd_7763577] using wordTrace_append hprefix tailTrace_7763577
  have hstable : (prefixWord ++ tailWord_7763577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763577).length < 2 ^ (prefixWord ++ tailWord_7763577).sum := by decide
  have hdescent : baseEnd_7763577 < baseStart_7763577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763584 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 3, 4, 2]
def baseStart_7763584 : Nat := 118140960795 + 7763584 * 2 ^ 59
def prefixEnd_7763584 : Nat := 4983230072969 + 3 ^ 40 * 7763584 * 2
def baseEnd_7763584 : Nat := 3986450193555458175595933

theorem tailTrace_7763584 : CollatzResearch.WordTrace tailWord_7763584 prefixEnd_7763584 3986450193555458175595933 := by
  unfold tailWord_7763584
  simp only [CollatzResearch.WordTrace]
  refine ⟨141580585552934278715428903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188774114070579038287238537 141580585552934278715428903)
  ·
    refine ⟨212370878329401418073143355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141580585552934278715428903 212370878329401418073143355)
    ·
      refine ⟨318556317494102127109715033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212370878329401418073143355 318556317494102127109715033)
      ·
        refine ⟨238917238120576595332286275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318556317494102127109715033 238917238120576595332286275)
        ·
          refine ⟨358375857180864892998429413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238917238120576595332286275 358375857180864892998429413)
          ·
            refine ⟨67195473221412167437205515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 358375857180864892998429413 67195473221412167437205515)
            ·
              refine ⟨100793209832118251155808273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67195473221412167437205515 100793209832118251155808273)
              ·
                refine ⟨75594907374088688366856205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100793209832118251155808273 75594907374088688366856205)
                ·
                  refine ⟨28348090265283258137571077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75594907374088688366856205 28348090265283258137571077)
                  ·
                    refine ⟨5315266924740610900794577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28348090265283258137571077 5315266924740610900794577)
                    ·
                      refine ⟨3986450193555458175595933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5315266924740610900794577 3986450193555458175595933)
                      ·
                        rfl

theorem cell23_7763584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3, 4, 2].length) (baseStart_7763584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763584 prefixEnd_7763584 := by exact prefixLift 7763584
  have htrace : WordTrace (prefixWord ++ tailWord_7763584) baseStart_7763584 baseEnd_7763584 := by
    simpa [prefixWord, tailWord_7763584, baseEnd_7763584] using wordTrace_append hprefix tailTrace_7763584
  have hstable : (prefixWord ++ tailWord_7763584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763584).length < 2 ^ (prefixWord ++ tailWord_7763584).sum := by decide
  have hdescent : baseEnd_7763584 < baseStart_7763584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763594 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 2, 6]
def baseStart_7763594 : Nat := 118140960795 + 7763594 * 2 ^ 59
def prefixEnd_7763594 : Nat := 4983230072969 + 3 ^ 40 * 7763594 * 2
def baseEnd_7763594 : Nat := 1328818442787334378823629

theorem tailTrace_7763594 : CollatzResearch.WordTrace tailWord_7763594 prefixEnd_7763594 1328818442787334378823629 := by
  unfold tailWord_7763594
  simp only [CollatzResearch.WordTrace]
  refine ⟨70790383958958082284680459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188774357223888219425814557 70790383958958082284680459)
  ·
    refine ⟨106185575938437123427020689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70790383958958082284680459 106185575938437123427020689)
    ·
      refine ⟨79639181953827842570265517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106185575938437123427020689 79639181953827842570265517)
      ·
        refine ⟨29864693232685440963849569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79639181953827842570265517 29864693232685440963849569)
        ·
          refine ⟨22398519924514080722887177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29864693232685440963849569 22398519924514080722887177)
          ·
            refine ⟨16798889943385560542165383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22398519924514080722887177 16798889943385560542165383)
            ·
              refine ⟨25198334915078340813248075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16798889943385560542165383 25198334915078340813248075)
              ·
                refine ⟨37797502372617511219872113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25198334915078340813248075 37797502372617511219872113)
                ·
                  refine ⟨28348126779463133414904085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37797502372617511219872113 28348126779463133414904085)
                  ·
                    refine ⟨1328818442787334378823629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28348126779463133414904085 1328818442787334378823629)
                    ·
                      rfl

theorem cell23_7763594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_7763594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763594 prefixEnd_7763594 := by exact prefixLift 7763594
  have htrace : WordTrace (prefixWord ++ tailWord_7763594) baseStart_7763594 baseEnd_7763594 := by
    simpa [prefixWord, tailWord_7763594, baseEnd_7763594] using wordTrace_append hprefix tailTrace_7763594
  have hstable : (prefixWord ++ tailWord_7763594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763594).length < 2 ^ (prefixWord ++ tailWord_7763594).sum := by decide
  have hdescent : baseEnd_7763594 < baseStart_7763594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763607 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 9]
def baseStart_7763607 : Nat := 118140960795 + 7763607 * 2 ^ 59
def prefixEnd_7763607 : Nat := 4983230072969 + 3 ^ 40 * 7763607 * 2
def baseEnd_7763607 : Nat := 442940222623390176178703

theorem tailTrace_7763607 : CollatzResearch.WordTrace tailWord_7763607 prefixEnd_7763607 442940222623390176178703 := by
  unfold tailWord_7763607
  simp only [CollatzResearch.WordTrace]
  refine ⟨283162009984785232358945075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188774673323190154905963383 283162009984785232358945075)
  ·
    refine ⟨424743014977177848538417613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283162009984785232358945075 424743014977177848538417613)
    ·
      refine ⟨159278630616441693201906605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424743014977177848538417613 159278630616441693201906605)
      ·
        refine ⟨59729486481165634950714977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159278630616441693201906605 59729486481165634950714977)
        ·
          refine ⟨44797114860874226213036233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59729486481165634950714977 44797114860874226213036233)
          ·
            refine ⟨33597836145655669659777175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44797114860874226213036233 33597836145655669659777175)
            ·
              refine ⟨50396754218483504489665763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33597836145655669659777175 50396754218483504489665763)
              ·
                refine ⟨75595131327725256734498645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50396754218483504489665763 75595131327725256734498645)
                ·
                  refine ⟨442940222623390176178703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75595131327725256734498645 442940222623390176178703)
                  ·
                    rfl

theorem cell23_7763607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 9].length) (baseStart_7763607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763607 prefixEnd_7763607 := by exact prefixLift 7763607
  have htrace : WordTrace (prefixWord ++ tailWord_7763607) baseStart_7763607 baseEnd_7763607 := by
    simpa [prefixWord, tailWord_7763607, baseEnd_7763607] using wordTrace_append hprefix tailTrace_7763607
  have hstable : (prefixWord ++ tailWord_7763607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763607).length < 2 ^ (prefixWord ++ tailWord_7763607).sum := by decide
  have hdescent : baseEnd_7763607 < baseStart_7763607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763634 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3]
def baseStart_7763634 : Nat := 118140960795 + 7763634 * 2 ^ 59
def prefixEnd_7763634 : Nat := 4983230072969 + 3 ^ 40 * 7763634 * 2
def baseEnd_7763634 : Nat := 3986475867588182979970703

theorem tailTrace_7763634 : CollatzResearch.WordTrace tailWord_7763634 prefixEnd_7763634 3986475867588182979970703 := by
  unfold tailWord_7763634
  simp only [CollatzResearch.WordTrace]
  refine ⟨70790748688921853992544489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188775329837124943980118637 70790748688921853992544489)
  ·
    refine ⟨53093061516691390494408367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70790748688921853992544489 53093061516691390494408367)
    ·
      refine ⟨79639592275037085741612551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53093061516691390494408367 79639592275037085741612551)
      ·
        refine ⟨119459388412555628612418827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79639592275037085741612551 119459388412555628612418827)
        ·
          refine ⟨179189082618833442918628241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119459388412555628612418827 179189082618833442918628241)
          ·
            refine ⟨134391811964125082188971181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179189082618833442918628241 134391811964125082188971181)
            ·
              refine ⟨50396929486546905820864193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134391811964125082188971181 50396929486546905820864193)
              ·
                refine ⟨37797697114910179365648145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50396929486546905820864193 37797697114910179365648145)
                ·
                  refine ⟨28348272836182634524236109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37797697114910179365648145 28348272836182634524236109)
                  ·
                    refine ⟨10630602313568487946588541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28348272836182634524236109 10630602313568487946588541)
                    ·
                      refine ⟨3986475867588182979970703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10630602313568487946588541 3986475867588182979970703)
                      ·
                        rfl

theorem cell23_7763634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_7763634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763634 prefixEnd_7763634 := by exact prefixLift 7763634
  have htrace : WordTrace (prefixWord ++ tailWord_7763634) baseStart_7763634 baseEnd_7763634 := by
    simpa [prefixWord, tailWord_7763634, baseEnd_7763634] using wordTrace_append hprefix tailTrace_7763634
  have hstable : (prefixWord ++ tailWord_7763634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763634).length < 2 ^ (prefixWord ++ tailWord_7763634).sum := by decide
  have hdescent : baseEnd_7763634 < baseStart_7763634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763647 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 7]
def baseStart_7763647 : Nat := 118140960795 + 7763647 * 2 ^ 59
def prefixEnd_7763647 : Nat := 4983230072969 + 3 ^ 40 * 7763647 * 2
def baseEnd_7763647 : Nat := 3986482542836691429108143

theorem tailTrace_7763647 : CollatzResearch.WordTrace tailWord_7763647 prefixEnd_7763647 3986482542836691429108143 := by
  unfold tailWord_7763647
  simp only [CollatzResearch.WordTrace]
  refine ⟨283163468904640319190401195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188775645936426879460267463 283163468904640319190401195)
  ·
    refine ⟨424745203356960478785601793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283163468904640319190401195 424745203356960478785601793)
    ·
      refine ⟨318558902517720359089201345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424745203356960478785601793 318558902517720359089201345)
      ·
        refine ⟨238919176888290269316901009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318558902517720359089201345 238919176888290269316901009)
        ·
          refine ⟨179189382666217701987675757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238919176888290269316901009 179189382666217701987675757)
          ·
            refine ⟨67196018499831638245378409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179189382666217701987675757 67196018499831638245378409)
            ·
              refine ⟨50397013874873728684033807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67196018499831638245378409 50397013874873728684033807)
              ·
                refine ⟨75595520812310593026050711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50397013874873728684033807 75595520812310593026050711)
                ·
                  refine ⟨113393281218465889539076067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75595520812310593026050711 113393281218465889539076067)
                  ·
                    refine ⟨170089921827698834308614101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113393281218465889539076067 170089921827698834308614101)
                    ·
                      refine ⟨3986482542836691429108143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170089921827698834308614101 3986482542836691429108143)
                      ·
                        rfl

theorem cell23_7763647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_7763647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763647 prefixEnd_7763647 := by exact prefixLift 7763647
  have htrace : WordTrace (prefixWord ++ tailWord_7763647) baseStart_7763647 baseEnd_7763647 := by
    simpa [prefixWord, tailWord_7763647, baseEnd_7763647] using wordTrace_append hprefix tailTrace_7763647
  have hstable : (prefixWord ++ tailWord_7763647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763647).length < 2 ^ (prefixWord ++ tailWord_7763647).sum := by decide
  have hdescent : baseEnd_7763647 < baseStart_7763647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763674 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4]
def baseStart_7763674 : Nat := 118140960795 + 7763674 * 2 ^ 59
def prefixEnd_7763674 : Nat := 4983230072969 + 3 ^ 40 * 7763674 * 2
def baseEnd_7763674 : Nat := 3986496406814362823470519

theorem tailTrace_7763674 : CollatzResearch.WordTrace tailWord_7763674 prefixEnd_7763674 3986496406814362823470519 := by
  unfold tailWord_7763674
  simp only [CollatzResearch.WordTrace]
  refine ⟨70791113418885625700408519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188776302450361668534422717 70791113418885625700408519)
  ·
    refine ⟨106186670128328438550612779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70791113418885625700408519 106186670128328438550612779)
    ·
      refine ⟨159280005192492657825919169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106186670128328438550612779 159280005192492657825919169)
      ·
        refine ⟨119460003894369493369439377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159280005192492657825919169 119460003894369493369439377)
        ·
          refine ⟨89595002920777120027079533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119460003894369493369439377 89595002920777120027079533)
          ·
            refine ⟨33598126095291420010154825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89595002920777120027079533 33598126095291420010154825)
            ·
              refine ⟨25198594571468565007616119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33598126095291420010154825 25198594571468565007616119)
              ·
                refine ⟨37797891857202847511424179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25198594571468565007616119 37797891857202847511424179)
                ·
                  refine ⟨56696837785804271267136269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37797891857202847511424179 56696837785804271267136269)
                  ·
                    refine ⟨21261314169676601725176101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56696837785804271267136269 21261314169676601725176101)
                    ·
                      refine ⟨3986496406814362823470519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21261314169676601725176101 3986496406814362823470519)
                      ·
                        rfl

theorem cell23_7763674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_7763674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763674 prefixEnd_7763674 := by exact prefixLift 7763674
  have htrace : WordTrace (prefixWord ++ tailWord_7763674) baseStart_7763674 baseEnd_7763674 := by
    simpa [prefixWord, tailWord_7763674, baseEnd_7763674] using wordTrace_append hprefix tailTrace_7763674
  have hstable : (prefixWord ++ tailWord_7763674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763674).length < 2 ^ (prefixWord ++ tailWord_7763674).sum := by decide
  have hdescent : baseEnd_7763674 < baseStart_7763674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763724 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 2, 5, 3]
def baseStart_7763724 : Nat := 118140960795 + 7763724 * 2 ^ 59
def prefixEnd_7763724 : Nat := 4983230072969 + 3 ^ 40 * 7763724 * 2
def baseEnd_7763724 : Nat := 3986522080847087627845289

theorem tailTrace_7763724 : CollatzResearch.WordTrace tailWord_7763724 prefixEnd_7763724 3986522080847087627845289 := by
  unfold tailWord_7763724
  simp only [CollatzResearch.WordTrace]
  refine ⟨141583138662680680670477113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188777518216907574227302817 141583138662680680670477113)
  ·
    refine ⟨106187353997010510502857835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141583138662680680670477113 106187353997010510502857835)
    ·
      refine ⟨159281030995515765754286753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106187353997010510502857835 159281030995515765754286753)
      ·
        refine ⟨119460773246636824315715065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159281030995515765754286753 119460773246636824315715065)
        ·
          refine ⟨89595579934977618236786299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119460773246636824315715065 89595579934977618236786299)
          ·
            refine ⟨134393369902466427355179449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89595579934977618236786299 134393369902466427355179449)
            ·
              refine ⟨100795027426849820516384587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134393369902466427355179449 100795027426849820516384587)
              ·
                refine ⟨151192541140274730774576881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100795027426849820516384587 151192541140274730774576881)
                ·
                  refine ⟨113394405855206048080932661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151192541140274730774576881 113394405855206048080932661)
                  ·
                    refine ⟨10630725548925567007587437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113394405855206048080932661 10630725548925567007587437)
                    ·
                      refine ⟨3986522080847087627845289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10630725548925567007587437 3986522080847087627845289)
                      ·
                        rfl

theorem cell23_7763724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_7763724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763724 prefixEnd_7763724 := by exact prefixLift 7763724
  have htrace : WordTrace (prefixWord ++ tailWord_7763724) baseStart_7763724 baseEnd_7763724 := by
    simpa [prefixWord, tailWord_7763724, baseEnd_7763724] using wordTrace_append hprefix tailTrace_7763724
  have hstable : (prefixWord ++ tailWord_7763724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763724).length < 2 ^ (prefixWord ++ tailWord_7763724).sum := by decide
  have hdescent : baseEnd_7763724 < baseStart_7763724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763752 : List Nat := [2, 1, 5, 1, 1, 4, 2, 2, 1, 4]
def baseStart_7763752 : Nat := 118140960795 + 7763752 * 2 ^ 59
def prefixEnd_7763752 : Nat := 4983230072969 + 3 ^ 40 * 7763752 * 2
def baseEnd_7763752 : Nat := 1328845486101804506098387

theorem tailTrace_7763752 : CollatzResearch.WordTrace tailWord_7763752 prefixEnd_7763752 1328845486101804506098387 := by
  unfold tailWord_7763752
  simp only [CollatzResearch.WordTrace]
  refine ⟨141583649284629961061486755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188778199046173281415315673 141583649284629961061486755)
  ·
    refine ⟨212375473926944941592230133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141583649284629961061486755 212375473926944941592230133)
    ·
      refine ⟨19910200680651088274271575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212375473926944941592230133 19910200680651088274271575)
      ·
        refine ⟨29865301020976632411407363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19910200680651088274271575 29865301020976632411407363)
        ·
          refine ⟨44797951531464948617111045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29865301020976632411407363 44797951531464948617111045)
          ·
            refine ⟨8399615912149677865708321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44797951531464948617111045 8399615912149677865708321)
            ·
              refine ⟨6299711934112258399281241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8399615912149677865708321 6299711934112258399281241)
              ·
                refine ⟨4724783950584193799460931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6299711934112258399281241 4724783950584193799460931)
                ·
                  refine ⟨7087175925876290699191397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4724783950584193799460931 7087175925876290699191397)
                  ·
                    refine ⟨1328845486101804506098387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7087175925876290699191397 1328845486101804506098387)
                    ·
                      rfl

theorem cell23_7763752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_7763752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763752 prefixEnd_7763752 := by exact prefixLift 7763752
  have htrace : WordTrace (prefixWord ++ tailWord_7763752) baseStart_7763752 baseEnd_7763752 := by
    simpa [prefixWord, tailWord_7763752, baseEnd_7763752] using wordTrace_append hprefix tailTrace_7763752
  have hstable : (prefixWord ++ tailWord_7763752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763752).length < 2 ^ (prefixWord ++ tailWord_7763752).sum := by decide
  have hdescent : baseEnd_7763752 < baseStart_7763752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763781 : List Nat := [1, 3, 1, 1, 1, 2, 4, 4, 1, 1, 4]
def baseStart_7763781 : Nat := 118140960795 + 7763781 * 2 ^ 59
def prefixEnd_7763781 : Nat := 4983230072969 + 3 ^ 40 * 7763781 * 2
def baseEnd_7763781 : Nat := 3986551349244393904832527

theorem tailTrace_7763781 : CollatzResearch.WordTrace tailWord_7763781 prefixEnd_7763781 3986551349244393904832527 := by
  unfold tailWord_7763781
  simp only [CollatzResearch.WordTrace]
  refine ⟨283168356286154860075779197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188778904190769906717186131 283168356286154860075779197)
  ·
    refine ⟨106188133607308072528417199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283168356286154860075779197 106188133607308072528417199)
    ·
      refine ⟨159282200410962108792625799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106188133607308072528417199 159282200410962108792625799)
      ·
        refine ⟨238923300616443163188938699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159282200410962108792625799 238923300616443163188938699)
        ·
          refine ⟨358384950924664744783408049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238923300616443163188938699 358384950924664744783408049)
          ·
            refine ⟨268788713193498558587556037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358384950924664744783408049 268788713193498558587556037)
            ·
              refine ⟨50397883723780979735166757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268788713193498558587556037 50397883723780979735166757)
              ·
                refine ⟨9449603198208933700343767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50397883723780979735166757 9449603198208933700343767)
                ·
                  refine ⟨14174404797313400550515651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9449603198208933700343767 14174404797313400550515651)
                  ·
                    refine ⟨21261607195970100825773477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14174404797313400550515651 21261607195970100825773477)
                    ·
                      refine ⟨3986551349244393904832527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21261607195970100825773477 3986551349244393904832527)
                      ·
                        rfl

theorem cell23_7763781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_7763781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763781 prefixEnd_7763781 := by exact prefixLift 7763781
  have htrace : WordTrace (prefixWord ++ tailWord_7763781) baseStart_7763781 baseEnd_7763781 := by
    simpa [prefixWord, tailWord_7763781, baseEnd_7763781] using wordTrace_append hprefix tailTrace_7763781
  have hstable : (prefixWord ++ tailWord_7763781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763781).length < 2 ^ (prefixWord ++ tailWord_7763781).sum := by decide
  have hdescent : baseEnd_7763781 < baseStart_7763781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763808 : List Nat := [2, 1, 1, 3, 3, 2, 3, 2, 2, 4]
def baseStart_7763808 : Nat := 118140960795 + 7763808 * 2 ^ 59
def prefixEnd_7763808 : Nat := 4983230072969 + 3 ^ 40 * 7763808 * 2
def baseEnd_7763808 : Nat := 1328855071074021766398301

theorem tailTrace_7763808 : CollatzResearch.WordTrace tailWord_7763808 prefixEnd_7763808 1328855071074021766398301 := by
  unfold tailWord_7763808
  simp only [CollatzResearch.WordTrace]
  refine ⟨141584670528528521843506039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188779560704704695791341385 141584670528528521843506039)
  ·
    refine ⟨212377005792792782765259059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141584670528528521843506039 212377005792792782765259059)
    ·
      refine ⟨318565508689189174147888589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212377005792792782765259059 318565508689189174147888589)
      ·
        refine ⟨119462065758445940305458221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318565508689189174147888589 119462065758445940305458221)
        ·
          refine ⟨44798274659417227614546833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119462065758445940305458221 44798274659417227614546833)
          ·
            refine ⟨33598705994562920710910125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44798274659417227614546833 33598705994562920710910125)
            ·
              refine ⟨12599514747961095266591297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33598705994562920710910125 12599514747961095266591297)
              ·
                refine ⟨9449636060970821449943473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12599514747961095266591297 9449636060970821449943473)
                ·
                  refine ⟨7087227045728116087457605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9449636060970821449943473 7087227045728116087457605)
                  ·
                    refine ⟨1328855071074021766398301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7087227045728116087457605 1328855071074021766398301)
                    ·
                      rfl

theorem cell23_7763808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 2, 4].length) (baseStart_7763808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763808 prefixEnd_7763808 := by exact prefixLift 7763808
  have htrace : WordTrace (prefixWord ++ tailWord_7763808) baseStart_7763808 baseEnd_7763808 := by
    simpa [prefixWord, tailWord_7763808, baseEnd_7763808] using wordTrace_append hprefix tailTrace_7763808
  have hstable : (prefixWord ++ tailWord_7763808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763808).length < 2 ^ (prefixWord ++ tailWord_7763808).sum := by decide
  have hdescent : baseEnd_7763808 < baseStart_7763808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763815 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 3, 2, 2]
def baseStart_7763815 : Nat := 118140960795 + 7763815 * 2 ^ 59
def prefixEnd_7763815 : Nat := 4983230072969 + 3 ^ 40 * 7763815 * 2
def baseEnd_7763815 : Nat := 3986568807586646771807371

theorem tailTrace_7763815 : CollatzResearch.WordTrace tailWord_7763815 prefixEnd_7763815 3986568807586646771807371 := by
  unfold tailWord_7763815
  simp only [CollatzResearch.WordTrace]
  refine ⟨283169596368031683882516899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188779730912021122588344599 283169596368031683882516899)
  ·
    refine ⟨424754394552047525823775349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283169596368031683882516899 424754394552047525823775349)
    ·
      refine ⟨39820724489254455545978939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 424754394552047525823775349 39820724489254455545978939)
      ·
        refine ⟨59731086733881683318968409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39820724489254455545978939 59731086733881683318968409)
        ·
          refine ⟨44798315050411262489226307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59731086733881683318968409 44798315050411262489226307)
          ·
            refine ⟨67197472575616893733839461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44798315050411262489226307 67197472575616893733839461)
            ·
              refine ⟨12599526107928167575094899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67197472575616893733839461 12599526107928167575094899)
              ·
                refine ⟨18899289161892251362642349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12599526107928167575094899 18899289161892251362642349)
                ·
                  refine ⟨7087233435709594260990881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18899289161892251362642349 7087233435709594260990881)
                  ·
                    refine ⟨5315425076782195695743161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7087233435709594260990881 5315425076782195695743161)
                    ·
                      refine ⟨3986568807586646771807371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5315425076782195695743161 3986568807586646771807371)
                      ·
                        rfl

theorem cell23_7763815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_7763815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763815 prefixEnd_7763815 := by exact prefixLift 7763815
  have htrace : WordTrace (prefixWord ++ tailWord_7763815) baseStart_7763815 baseEnd_7763815 := by
    simpa [prefixWord, tailWord_7763815, baseEnd_7763815] using wordTrace_append hprefix tailTrace_7763815
  have hstable : (prefixWord ++ tailWord_7763815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763815).length < 2 ^ (prefixWord ++ tailWord_7763815).sum := by decide
  have hdescent : baseEnd_7763815 < baseStart_7763815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763834 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 2, 7]
def baseStart_7763834 : Nat := 118140960795 + 7763834 * 2 ^ 59
def prefixEnd_7763834 : Nat := 4983230072969 + 3 ^ 40 * 7763834 * 2
def baseEnd_7763834 : Nat := 1328859521239694065823261

theorem tailTrace_7763834 : CollatzResearch.WordTrace tailWord_7763834 prefixEnd_7763834 1328859521239694065823261 := by
  unfold tailWord_7763834
  simp only [CollatzResearch.WordTrace]
  refine ⟨70792572338740712531864639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188780192903308566751639037 70792572338740712531864639)
  ·
    refine ⟨106188858508111068797796959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70792572338740712531864639 106188858508111068797796959)
    ·
      refine ⟨159283287762166603196695439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106188858508111068797796959 159283287762166603196695439)
      ·
        refine ⟨238924931643249904795043159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159283287762166603196695439 238924931643249904795043159)
        ·
          refine ⟨358387397464874857192564739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238924931643249904795043159 358387397464874857192564739)
          ·
            refine ⟨537581096197312285788847109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358387397464874857192564739 537581096197312285788847109)
            ·
              refine ⟨100796455536996053585408833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 537581096197312285788847109 100796455536996053585408833)
              ·
                refine ⟨75597341652747040189056625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100796455536996053585408833 75597341652747040189056625)
                ·
                  refine ⟨56698006239560280141792469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75597341652747040189056625 56698006239560280141792469)
                  ·
                    refine ⟨1328859521239694065823261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56698006239560280141792469 1328859521239694065823261)
                    ·
                      rfl

theorem cell23_7763834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_7763834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763834 prefixEnd_7763834 := by exact prefixLift 7763834
  have htrace : WordTrace (prefixWord ++ tailWord_7763834) baseStart_7763834 baseEnd_7763834 := by
    simpa [prefixWord, tailWord_7763834, baseEnd_7763834] using wordTrace_append hprefix tailTrace_7763834
  have hstable : (prefixWord ++ tailWord_7763834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763834).length < 2 ^ (prefixWord ++ tailWord_7763834).sum := by decide
  have hdescent : baseEnd_7763834 < baseStart_7763834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763838 : List Nat := [4, 2, 3, 1, 1, 2, 1, 9]
def baseStart_7763838 : Nat := 118140960795 + 7763838 * 2 ^ 59
def prefixEnd_7763838 : Nat := 4983230072969 + 3 ^ 40 * 7763838 * 2
def baseEnd_7763838 : Nat := 147651133986729636363695

theorem tailTrace_7763838 : CollatzResearch.WordTrace tailWord_7763838 prefixEnd_7763838 147651133986729636363695 := by
  unfold tailWord_7763838
  simp only [CollatzResearch.WordTrace]
  refine ⟨35396304405868544851325521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188780290164632239207069445 35396304405868544851325521)
  ·
    refine ⟨26547228304401408638494141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35396304405868544851325521 26547228304401408638494141)
    ·
      refine ⟨9955210614150528239435303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26547228304401408638494141 9955210614150528239435303)
      ·
        refine ⟨14932815921225792359152955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9955210614150528239435303 14932815921225792359152955)
        ·
          refine ⟨22399223881838688538729433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14932815921225792359152955 22399223881838688538729433)
          ·
            refine ⟨16799417911379016404047075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22399223881838688538729433 16799417911379016404047075)
            ·
              refine ⟨25199126867068524606070613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16799417911379016404047075 25199126867068524606070613)
              ·
                refine ⟨147651133986729636363695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25199126867068524606070613 147651133986729636363695)
                ·
                  rfl

theorem cell23_7763838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 9].length) (baseStart_7763838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763838 prefixEnd_7763838 := by exact prefixLift 7763838
  have htrace : WordTrace (prefixWord ++ tailWord_7763838) baseStart_7763838 baseEnd_7763838 := by
    simpa [prefixWord, tailWord_7763838, baseEnd_7763838] using wordTrace_append hprefix tailTrace_7763838
  have hstable : (prefixWord ++ tailWord_7763838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763838).length < 2 ^ (prefixWord ++ tailWord_7763838).sum := by decide
  have hdescent : baseEnd_7763838 < baseStart_7763838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763886 : List Nat := [4, 1, 5, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_7763886 : Nat := 118140960795 + 7763886 * 2 ^ 59
def prefixEnd_7763886 : Nat := 4983230072969 + 3 ^ 40 * 7763886 * 2
def baseEnd_7763886 : Nat := 3986605264713115994019545

theorem tailTrace_7763886 : CollatzResearch.WordTrace tailWord_7763886 prefixEnd_7763886 3986605264713115994019545 := by
  unfold tailWord_7763886
  simp only [CollatzResearch.WordTrace]
  refine ⟨35396523243846807876043939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188781457300516308672234341 35396523243846807876043939)
  ·
    refine ⟨53094784865770211814065909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35396523243846807876043939 53094784865770211814065909)
    ·
      refine ⟨4977636081165957357568679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53094784865770211814065909 4977636081165957357568679)
      ·
        refine ⟨7466454121748936036353019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4977636081165957357568679 7466454121748936036353019)
        ·
          refine ⟨11199681182623404054529529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7466454121748936036353019 11199681182623404054529529)
          ·
            refine ⟨8399760886967553040897147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11199681182623404054529529 8399760886967553040897147)
            ·
              refine ⟨12599641330451329561345721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8399760886967553040897147 12599641330451329561345721)
              ·
                refine ⟨9449730997838497171009291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12599641330451329561345721 9449730997838497171009291)
                ·
                  refine ⟨14174596496757745756513937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9449730997838497171009291 14174596496757745756513937)
                  ·
                    refine ⟨10630947372568309317385453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14174596496757745756513937 10630947372568309317385453)
                    ·
                      refine ⟨3986605264713115994019545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10630947372568309317385453 3986605264713115994019545)
                      ·
                        rfl

theorem cell23_7763886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_7763886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763886 prefixEnd_7763886 := by exact prefixLift 7763886
  have htrace : WordTrace (prefixWord ++ tailWord_7763886) baseStart_7763886 baseEnd_7763886 := by
    simpa [prefixWord, tailWord_7763886, baseEnd_7763886] using wordTrace_append hprefix tailTrace_7763886
  have hstable : (prefixWord ++ tailWord_7763886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763886).length < 2 ^ (prefixWord ++ tailWord_7763886).sum := by decide
  have hdescent : baseEnd_7763886 < baseStart_7763886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763928 : List Nat := [2, 1, 2, 2, 2, 2, 3, 4, 5]
def baseStart_7763928 : Nat := 118140960795 + 7763928 * 2 ^ 59
def prefixEnd_7763928 : Nat := 4983230072969 + 3 ^ 40 * 7763928 * 2
def baseEnd_7763928 : Nat := 442958536766733869966039

theorem tailTrace_7763928 : CollatzResearch.WordTrace tailWord_7763928 prefixEnd_7763928 442958536766733869966039 := by
  unfold tailWord_7763928
  simp only [CollatzResearch.WordTrace]
  refine ⟨141586858908311152090690219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188782478544414869454253625 141586858908311152090690219)
  ·
    refine ⟨212380288362466728136035329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141586858908311152090690219 212380288362466728136035329)
    ·
      refine ⟨159285216271850046102026497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212380288362466728136035329 159285216271850046102026497)
      ·
        refine ⟨119463912203887534576519873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159285216271850046102026497 119463912203887534576519873)
        ·
          refine ⟨89597934152915650932389905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119463912203887534576519873 89597934152915650932389905)
          ·
            refine ⟨67198450614686738199292429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89597934152915650932389905 67198450614686738199292429)
            ·
              refine ⟨25199418980507526824734661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67198450614686738199292429 25199418980507526824734661)
              ·
                refine ⟨4724891058845161279637749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25199418980507526824734661 4724891058845161279637749)
                ·
                  refine ⟨442958536766733869966039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4724891058845161279637749 442958536766733869966039)
                  ·
                    rfl

theorem cell23_7763928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 5].length) (baseStart_7763928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763928 prefixEnd_7763928 := by exact prefixLift 7763928
  have htrace : WordTrace (prefixWord ++ tailWord_7763928) baseStart_7763928 baseEnd_7763928 := by
    simpa [prefixWord, tailWord_7763928, baseEnd_7763928] using wordTrace_append hprefix tailTrace_7763928
  have hstable : (prefixWord ++ tailWord_7763928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763928).length < 2 ^ (prefixWord ++ tailWord_7763928).sum := by decide
  have hdescent : baseEnd_7763928 < baseStart_7763928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7763932 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 2, 6]
def baseStart_7763932 : Nat := 118140960795 + 7763932 * 2 ^ 59
def prefixEnd_7763932 : Nat := 4983230072969 + 3 ^ 40 * 7763932 * 2
def baseEnd_7763932 : Nat := 1328876294941074271348111

theorem tailTrace_7763932 : CollatzResearch.WordTrace tailWord_7763932 prefixEnd_7763932 1328876294941074271348111 := by
  unfold tailWord_7763932
  simp only [CollatzResearch.WordTrace]
  refine ⟨141586931854303906432263025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188782575805738541909684033 141586931854303906432263025)
  ·
    refine ⟨106190198890727929824197269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141586931854303906432263025 106190198890727929824197269)
    ·
      refine ⟨4977665573002871710509247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106190198890727929824197269 4977665573002871710509247)
      ·
        refine ⟨7466498359504307565763871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4977665573002871710509247 7466498359504307565763871)
        ·
          refine ⟨11199747539256461348645807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7466498359504307565763871 11199747539256461348645807)
          ·
            refine ⟨16799621308884692022968711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11199747539256461348645807 16799621308884692022968711)
            ·
              refine ⟨25199431963327038034453067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16799621308884692022968711 25199431963327038034453067)
              ·
                refine ⟨37799147944990557051679601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25199431963327038034453067 37799147944990557051679601)
                ·
                  refine ⟨28349360958742917788759701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37799147944990557051679601 28349360958742917788759701)
                  ·
                    refine ⟨1328876294941074271348111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28349360958742917788759701 1328876294941074271348111)
                    ·
                      rfl

theorem cell23_7763932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_7763932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7763932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7763932 prefixEnd_7763932 := by exact prefixLift 7763932
  have htrace : WordTrace (prefixWord ++ tailWord_7763932) baseStart_7763932 baseEnd_7763932 := by
    simpa [prefixWord, tailWord_7763932, baseEnd_7763932] using wordTrace_append hprefix tailTrace_7763932
  have hstable : (prefixWord ++ tailWord_7763932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7763932).length < 2 ^ (prefixWord ++ tailWord_7763932).sum := by decide
  have hdescent : baseEnd_7763932 < baseStart_7763932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7763932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764082 : List Nat := [3, 2, 1, 2, 2, 3, 3, 1, 1, 5]
def baseStart_7764082 : Nat := 118140960795 + 7764082 * 2 ^ 59
def prefixEnd_7764082 : Nat := 4983230072969 + 3 ^ 40 * 7764082 * 2
def baseEnd_7764082 : Nat := 1328901968973799075722881

theorem tailTrace_7764082 : CollatzResearch.WordTrace tailWord_7764082 prefixEnd_7764082 1328901968973799075722881 := by
  unfold tailWord_7764082
  simp only [CollatzResearch.WordTrace]
  refine ⟨70794833664516097120621625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188786223105376258988324333 70794833664516097120621625)
  ·
    refine ⟨53096125248387072840466219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70794833664516097120621625 53096125248387072840466219)
    ·
      refine ⟨79644187872580609260699329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53096125248387072840466219 79644187872580609260699329)
      ·
        refine ⟨59733140904435456945524497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79644187872580609260699329 59733140904435456945524497)
        ·
          refine ⟨44799855678326592709143373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59733140904435456945524497 44799855678326592709143373)
          ·
            refine ⟨16799945879372472265928765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44799855678326592709143373 16799945879372472265928765)
            ·
              refine ⟨6299979704764677099723287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16799945879372472265928765 6299979704764677099723287)
              ·
                refine ⟨9449969557147015649584931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6299979704764677099723287 9449969557147015649584931)
                ·
                  refine ⟨14174954335720523474377397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9449969557147015649584931 14174954335720523474377397)
                  ·
                    refine ⟨1328901968973799075722881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14174954335720523474377397 1328901968973799075722881)
                    ·
                      rfl

theorem cell23_7764082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_7764082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764082 prefixEnd_7764082 := by exact prefixLift 7764082
  have htrace : WordTrace (prefixWord ++ tailWord_7764082) baseStart_7764082 baseEnd_7764082 := by
    simpa [prefixWord, tailWord_7764082, baseEnd_7764082] using wordTrace_append hprefix tailTrace_7764082
  have hstable : (prefixWord ++ tailWord_7764082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764082).length < 2 ^ (prefixWord ++ tailWord_7764082).sum := by decide
  have hdescent : baseEnd_7764082 < baseStart_7764082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764119 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 3, 2, 2]
def baseStart_7764119 : Nat := 118140960795 + 7764119 * 2 ^ 59
def prefixEnd_7764119 : Nat := 4983230072969 + 3 ^ 40 * 7764119 * 2
def baseEnd_7764119 : Nat := 3986724905705613582405973

theorem tailTrace_7764119 : CollatzResearch.WordTrace tailWord_7764119 prefixEnd_7764119 3986724905705613582405973 := by
  unfold tailWord_7764119
  simp only [CollatzResearch.WordTrace]
  refine ⟨283180684158930343801583411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188787122772620229201055607 283180684158930343801583411)
  ·
    refine ⟨424771026238395515702375117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283180684158930343801583411 424771026238395515702375117)
    ·
      refine ⟨159289134839398318388390669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424771026238395515702375117 159289134839398318388390669)
      ·
        refine ⟨59733425564774369395646501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159289134839398318388390669 59733425564774369395646501)
        ·
          refine ⟨11200017293395194261683719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59733425564774369395646501 11200017293395194261683719)
          ·
            refine ⟨16800025940092791392525579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11200017293395194261683719 16800025940092791392525579)
            ·
              refine ⟨25200038910139187088788369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16800025940092791392525579 25200038910139187088788369)
              ·
                refine ⟨18900029182604390316591277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25200038910139187088788369 18900029182604390316591277)
                ·
                  refine ⟨7087510943476646368721729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18900029182604390316591277 7087510943476646368721729)
                  ·
                    refine ⟨5315633207607484776541297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7087510943476646368721729 5315633207607484776541297)
                    ·
                      refine ⟨3986724905705613582405973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5315633207607484776541297 3986724905705613582405973)
                      ·
                        rfl

theorem cell23_7764119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_7764119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764119 prefixEnd_7764119 := by exact prefixLift 7764119
  have htrace : WordTrace (prefixWord ++ tailWord_7764119) baseStart_7764119 baseEnd_7764119 := by
    simpa [prefixWord, tailWord_7764119, baseEnd_7764119] using wordTrace_append hprefix tailTrace_7764119
  have hstable : (prefixWord ++ tailWord_7764119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764119).length < 2 ^ (prefixWord ++ tailWord_7764119).sum := by decide
  have hdescent : baseEnd_7764119 < baseStart_7764119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764125 : List Nat := [1, 4, 2, 1, 1, 4, 3, 7]
def baseStart_7764125 : Nat := 118140960795 + 7764125 * 2 ^ 59
def prefixEnd_7764125 : Nat := 4983230072969 + 3 ^ 40 * 7764125 * 2
def baseEnd_7764125 : Nat := 147656592095908909590035

theorem tailTrace_7764125 : CollatzResearch.WordTrace tailWord_7764125 prefixEnd_7764125 147656592095908909590035 := by
  unfold tailWord_7764125
  simp only [CollatzResearch.WordTrace]
  refine ⟨283180902996908606826301829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188787268664605737884201219 283180902996908606826301829)
  ·
    refine ⟨53096419311920363779931593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283180902996908606826301829 53096419311920363779931593)
    ·
      refine ⟨39822314483940272834948695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53096419311920363779931593 39822314483940272834948695)
      ·
        refine ⟨59733471725910409252423043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39822314483940272834948695 59733471725910409252423043)
        ·
          refine ⟨89600207588865613878634565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59733471725910409252423043 89600207588865613878634565)
          ·
            refine ⟨16800038922912302602243981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89600207588865613878634565 16800038922912302602243981)
            ·
              refine ⟨6300014596092113475841493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16800038922912302602243981 6300014596092113475841493)
              ·
                refine ⟨147656592095908909590035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6300014596092113475841493 147656592095908909590035)
                ·
                  rfl

theorem cell23_7764125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 7].length) (baseStart_7764125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764125 prefixEnd_7764125 := by exact prefixLift 7764125
  have htrace : WordTrace (prefixWord ++ tailWord_7764125) baseStart_7764125 baseEnd_7764125 := by
    simpa [prefixWord, tailWord_7764125, baseEnd_7764125] using wordTrace_append hprefix tailTrace_7764125
  have hstable : (prefixWord ++ tailWord_7764125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764125).length < 2 ^ (prefixWord ++ tailWord_7764125).sum := by decide
  have hdescent : baseEnd_7764125 < baseStart_7764125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764142 : List Nat := [4, 1, 4, 2, 1, 1, 10]
def baseStart_7764142 : Nat := 118140960795 + 7764142 * 2 ^ 59
def prefixEnd_7764142 : Nat := 4983230072969 + 3 ^ 40 * 7764142 * 2
def baseEnd_7764142 : Nat := 49218971799514407313807

theorem tailTrace_7764142 : CollatzResearch.WordTrace tailWord_7764142 prefixEnd_7764142 49218971799514407313807 := by
  unfold tailWord_7764142
  simp only [CollatzResearch.WordTrace]
  refine ⟨35397690379730877341208835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188787682025231345819780453 35397690379730877341208835)
  ·
    refine ⟨53096535569596316011813253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35397690379730877341208835 53096535569596316011813253)
    ·
      refine ⟨9955600419299309252214985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53096535569596316011813253 9955600419299309252214985)
      ·
        refine ⟨7466700314474481939161239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9955600419299309252214985 7466700314474481939161239)
        ·
          refine ⟨11200050471711722908741859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7466700314474481939161239 11200050471711722908741859)
          ·
            refine ⟨16800075707567584363112789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11200050471711722908741859 16800075707567584363112789)
            ·
              refine ⟨49218971799514407313807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16800075707567584363112789 49218971799514407313807)
              ·
                rfl

theorem cell23_7764142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 10].length) (baseStart_7764142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764142 prefixEnd_7764142 := by exact prefixLift 7764142
  have htrace : WordTrace (prefixWord ++ tailWord_7764142) baseStart_7764142 baseEnd_7764142 := by
    simpa [prefixWord, tailWord_7764142, baseEnd_7764142] using wordTrace_append hprefix tailTrace_7764142
  have hstable : (prefixWord ++ tailWord_7764142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764142).length < 2 ^ (prefixWord ++ tailWord_7764142).sum := by decide
  have hdescent : baseEnd_7764142 < baseStart_7764142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764182 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_7764182 : Nat := 118140960795 + 7764182 * 2 ^ 59
def prefixEnd_7764182 : Nat := 4983230072969 + 3 ^ 40 * 7764182 * 2
def baseEnd_7764182 : Nat := 3986757254986846835918183

theorem tailTrace_7764182 : CollatzResearch.WordTrace tailWord_7764182 prefixEnd_7764182 3986757254986846835918183 := by
  unfold tailWord_7764182
  simp only [CollatzResearch.WordTrace]
  refine ⟨17698936372356381597570425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188788654638468070374084533 17698936372356381597570425)
  ·
    refine ⟨13274202279267286198177819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17698936372356381597570425 13274202279267286198177819)
    ·
      refine ⟨19911303418900929297266729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13274202279267286198177819 19911303418900929297266729)
      ·
        refine ⟨14933477564175696972950047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19911303418900929297266729 14933477564175696972950047)
        ·
          refine ⟨22400216346263545459425071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14933477564175696972950047 22400216346263545459425071)
          ·
            refine ⟨33600324519395318189137607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22400216346263545459425071 33600324519395318189137607)
            ·
              refine ⟨50400486779092977283706411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33600324519395318189137607 50400486779092977283706411)
              ·
                refine ⟨75600730168639465925559617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50400486779092977283706411 75600730168639465925559617)
                ·
                  refine ⟨56700547626479599444169713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75600730168639465925559617 56700547626479599444169713)
                  ·
                    refine ⟨42525410719859699583127285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56700547626479599444169713 42525410719859699583127285)
                    ·
                      refine ⟨3986757254986846835918183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42525410719859699583127285 3986757254986846835918183)
                      ·
                        rfl

theorem cell23_7764182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_7764182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764182 prefixEnd_7764182 := by exact prefixLift 7764182
  have htrace : WordTrace (prefixWord ++ tailWord_7764182) baseStart_7764182 baseEnd_7764182 := by
    simpa [prefixWord, tailWord_7764182, baseEnd_7764182] using wordTrace_append hprefix tailTrace_7764182
  have hstable : (prefixWord ++ tailWord_7764182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764182).length < 2 ^ (prefixWord ++ tailWord_7764182).sum := by decide
  have hdescent : baseEnd_7764182 < baseStart_7764182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764192 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 6, 2, 2]
def baseStart_7764192 : Nat := 118140960795 + 7764192 * 2 ^ 59
def prefixEnd_7764192 : Nat := 4983230072969 + 3 ^ 40 * 7764192 * 2
def baseEnd_7764192 : Nat := 3986762389793391796793137

theorem tailTrace_7764192 : CollatzResearch.WordTrace tailWord_7764192 prefixEnd_7764192 3986762389793391796793137 := by
  unfold tailWord_7764192
  simp only [CollatzResearch.WordTrace]
  refine ⟨141591673343832938634495415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188788897791777251512660553 141591673343832938634495415)
  ·
    refine ⟨212387510015749407951743123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141591673343832938634495415 212387510015749407951743123)
    ·
      refine ⟨318581265023624111927614685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212387510015749407951743123 318581265023624111927614685)
      ·
        refine ⟨119467974383859041972855507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318581265023624111927614685 119467974383859041972855507)
        ·
          refine ⟨179201961575788562959283261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119467974383859041972855507 179201961575788562959283261)
          ·
            refine ⟨67200735590920711109731223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179201961575788562959283261 67200735590920711109731223)
            ·
              refine ⟨100801103386381066664596835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67200735590920711109731223 100801103386381066664596835)
              ·
                refine ⟨151201655079571599996895253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100801103386381066664596835 151201655079571599996895253)
                ·
                  refine ⟨7087577581854918749854465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151201655079571599996895253 7087577581854918749854465)
                  ·
                    refine ⟨5315683186391189062390849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7087577581854918749854465 5315683186391189062390849)
                    ·
                      refine ⟨3986762389793391796793137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5315683186391189062390849 3986762389793391796793137)
                      ·
                        rfl

theorem cell23_7764192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_7764192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764192 prefixEnd_7764192 := by exact prefixLift 7764192
  have htrace : WordTrace (prefixWord ++ tailWord_7764192) baseStart_7764192 baseEnd_7764192 := by
    simpa [prefixWord, tailWord_7764192, baseEnd_7764192] using wordTrace_append hprefix tailTrace_7764192
  have hstable : (prefixWord ++ tailWord_7764192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764192).length < 2 ^ (prefixWord ++ tailWord_7764192).sum := by decide
  have hdescent : baseEnd_7764192 < baseStart_7764192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764225 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_7764225 : Nat := 118140960795 + 7764225 * 2 ^ 59
def prefixEnd_7764225 : Nat := 4983230072969 + 3 ^ 40 * 7764225 * 2
def baseEnd_7764225 : Nat := 3986779334654990167680485

theorem tailTrace_7764225 : CollatzResearch.WordTrace tailWord_7764225 prefixEnd_7764225 3986779334654990167680485 := by
  unfold tailWord_7764225
  simp only [CollatzResearch.WordTrace]
  refine ⟨283184550296546323904942129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188789700197697549269961419 283184550296546323904942129)
  ·
    refine ⟨212388412722409742928706597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283184550296546323904942129 212388412722409742928706597)
    ·
      refine ⟨39822827385451826799132487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212388412722409742928706597 39822827385451826799132487)
      ·
        refine ⟨59734241078177740198698731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39822827385451826799132487 59734241078177740198698731)
        ·
          refine ⟨89601361617266610298048097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59734241078177740198698731 89601361617266610298048097)
          ·
            refine ⟨67201021212949957723536073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89601361617266610298048097 67201021212949957723536073)
            ·
              refine ⟨50400765909712468292652055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67201021212949957723536073 50400765909712468292652055)
              ·
                refine ⟨75601148864568702438978083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50400765909712468292652055 75601148864568702438978083)
                ·
                  refine ⟨113401723296853053658467125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75601148864568702438978083 113401723296853053658467125)
                  ·
                    refine ⟨10631411559079973780481293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113401723296853053658467125 10631411559079973780481293)
                    ·
                      refine ⟨3986779334654990167680485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10631411559079973780481293 3986779334654990167680485)
                      ·
                        rfl

theorem cell23_7764225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_7764225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764225 prefixEnd_7764225 := by exact prefixLift 7764225
  have htrace : WordTrace (prefixWord ++ tailWord_7764225) baseStart_7764225 baseEnd_7764225 := by
    simpa [prefixWord, tailWord_7764225, baseEnd_7764225] using wordTrace_append hprefix tailTrace_7764225
  have hstable : (prefixWord ++ tailWord_7764225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764225).length < 2 ^ (prefixWord ++ tailWord_7764225).sum := by decide
  have hdescent : baseEnd_7764225 < baseStart_7764225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764245 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 2, 5]
def baseStart_7764245 : Nat := 118140960795 + 7764245 * 2 ^ 59
def prefixEnd_7764245 : Nat := 4983230072969 + 3 ^ 40 * 7764245 * 2
def baseEnd_7764245 : Nat := 1328929868089360029810131

theorem tailTrace_7764245 : CollatzResearch.WordTrace tailWord_7764245 prefixEnd_7764245 1328929868089360029810131 := by
  unfold tailWord_7764245
  simp only [CollatzResearch.WordTrace]
  refine ⟨283185279756473867320670189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188790186504315911547113459 283185279756473867320670189)
  ·
    refine ⟨106194479908677700245251321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283185279756473867320670189 106194479908677700245251321)
    ·
      refine ⟨79645859931508275183938491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106194479908677700245251321 79645859931508275183938491)
      ·
        refine ⟨119468789897262412775907737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79645859931508275183938491 119468789897262412775907737)
        ·
          refine ⟨89601592422946809581930803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119468789897262412775907737 89601592422946809581930803)
          ·
            refine ⟨134402388634420214372896205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89601592422946809581930803 134402388634420214372896205)
            ·
              refine ⟨50400895737907580389836077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134402388634420214372896205 50400895737907580389836077)
              ·
                refine ⟨18900335901715342646188529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50400895737907580389836077 18900335901715342646188529)
                ·
                  refine ⟨14175251926286506984641397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18900335901715342646188529 14175251926286506984641397)
                  ·
                    refine ⟨1328929868089360029810131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14175251926286506984641397 1328929868089360029810131)
                    ·
                      rfl

theorem cell23_7764245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_7764245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764245 prefixEnd_7764245 := by exact prefixLift 7764245
  have htrace : WordTrace (prefixWord ++ tailWord_7764245) baseStart_7764245 baseEnd_7764245 := by
    simpa [prefixWord, tailWord_7764245, baseEnd_7764245] using wordTrace_append hprefix tailTrace_7764245
  have hstable : (prefixWord ++ tailWord_7764245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764245).length < 2 ^ (prefixWord ++ tailWord_7764245).sum := by decide
  have hdescent : baseEnd_7764245 < baseStart_7764245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764255 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 5]
def baseStart_7764255 : Nat := 118140960795 + 7764255 * 2 ^ 59
def prefixEnd_7764255 : Nat := 4983230072969 + 3 ^ 40 * 7764255 * 2
def baseEnd_7764255 : Nat := 3986794739074625050305347

theorem tailTrace_7764255 : CollatzResearch.WordTrace tailWord_7764255 prefixEnd_7764255 3986794739074625050305347 := by
  unfold tailWord_7764255
  simp only [CollatzResearch.WordTrace]
  refine ⟨283185644486437639028534219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188790429657625092685689479 283185644486437639028534219)
  ·
    refine ⟨424778466729656458542801329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283185644486437639028534219 424778466729656458542801329)
    ·
      refine ⟨318583850047242343907100997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424778466729656458542801329 318583850047242343907100997)
      ·
        refine ⟨59734471883857939482581437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318583850047242343907100997 59734471883857939482581437)
        ·
          refine ⟨22400426956446727305968039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59734471883857939482581437 22400426956446727305968039)
          ·
            refine ⟨33600640434670090958952059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22400426956446727305968039 33600640434670090958952059)
            ·
              refine ⟨50400960652005136438428089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33600640434670090958952059 50400960652005136438428089)
              ·
                refine ⟨37800720489003852328821067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50400960652005136438428089 37800720489003852328821067)
                ·
                  refine ⟨56701080733505778493231601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37800720489003852328821067 56701080733505778493231601)
                  ·
                    refine ⟨42525810550129333869923701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56701080733505778493231601 42525810550129333869923701)
                    ·
                      refine ⟨3986794739074625050305347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42525810550129333869923701 3986794739074625050305347)
                      ·
                        rfl

theorem cell23_7764255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_7764255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764255 prefixEnd_7764255 := by exact prefixLift 7764255
  have htrace : WordTrace (prefixWord ++ tailWord_7764255) baseStart_7764255 baseEnd_7764255 := by
    simpa [prefixWord, tailWord_7764255, baseEnd_7764255] using wordTrace_append hprefix tailTrace_7764255
  have hstable : (prefixWord ++ tailWord_7764255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764255).length < 2 ^ (prefixWord ++ tailWord_7764255).sum := by decide
  have hdescent : baseEnd_7764255 < baseStart_7764255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764282 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2]
def baseStart_7764282 : Nat := 118140960795 + 7764282 * 2 ^ 59
def prefixEnd_7764282 : Nat := 4983230072969 + 3 ^ 40 * 7764282 * 2
def baseEnd_7764282 : Nat := 3986808603052296444667723

theorem tailTrace_7764282 : CollatzResearch.WordTrace tailWord_7764282 prefixEnd_7764282 3986808603052296444667723 := by
  unfold tailWord_7764282
  simp only [CollatzResearch.WordTrace]
  refine ⟨70796657314334955659941775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188791086171559881759844733 70796657314334955659941775)
  ·
    refine ⟨106194985971502433489912663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70796657314334955659941775 106194985971502433489912663)
    ·
      refine ⟨159292478957253650234868995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106194985971502433489912663 159292478957253650234868995)
      ·
        refine ⟨238938718435880475352303493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159292478957253650234868995 238938718435880475352303493)
        ·
          refine ⟨44801009706727589128556905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238938718435880475352303493 44801009706727589128556905)
          ·
            refine ⟨33600757280045691846417679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44801009706727589128556905 33600757280045691846417679)
            ·
              refine ⟨50401135920068537769626519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33600757280045691846417679 50401135920068537769626519)
              ·
                refine ⟨75601703880102806654439779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50401135920068537769626519 75601703880102806654439779)
                ·
                  refine ⟨113402555820154209981659669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75601703880102806654439779 113402555820154209981659669)
                  ·
                    refine ⟨5315744804069728592890297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113402555820154209981659669 5315744804069728592890297)
                    ·
                      refine ⟨3986808603052296444667723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5315744804069728592890297 3986808603052296444667723)
                      ·
                        rfl

theorem cell23_7764282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2].length) (baseStart_7764282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764282 prefixEnd_7764282 := by exact prefixLift 7764282
  have htrace : WordTrace (prefixWord ++ tailWord_7764282) baseStart_7764282 baseEnd_7764282 := by
    simpa [prefixWord, tailWord_7764282, baseEnd_7764282] using wordTrace_append hprefix tailTrace_7764282
  have hstable : (prefixWord ++ tailWord_7764282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764282).length < 2 ^ (prefixWord ++ tailWord_7764282).sum := by decide
  have hdescent : baseEnd_7764282 < baseStart_7764282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764302 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3]
def baseStart_7764302 : Nat := 118140960795 + 7764302 * 2 ^ 59
def prefixEnd_7764302 : Nat := 4983230072969 + 3 ^ 40 * 7764302 * 2
def baseEnd_7764302 : Nat := 3986818872665386366417631

theorem tailTrace_7764302 : CollatzResearch.WordTrace tailWord_7764302 prefixEnd_7764302 3986818872665386366417631 := by
  unfold tailWord_7764302
  simp only [CollatzResearch.WordTrace]
  refine ⟨35398419839658420756936895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188791572478178244036996773 35398419839658420756936895)
  ·
    refine ⟨53097629759487631135405343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35398419839658420756936895 53097629759487631135405343)
    ·
      refine ⟨79646444639231446703108015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53097629759487631135405343 79646444639231446703108015)
      ·
        refine ⟨119469666958847170054662023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79646444639231446703108015 119469666958847170054662023)
        ·
          refine ⟨179204500438270755081993035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119469666958847170054662023 179204500438270755081993035)
          ·
            refine ⟨268806750657406132622989553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179204500438270755081993035 268806750657406132622989553)
            ·
              refine ⟨201605062993054599467242165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268806750657406132622989553 201605062993054599467242165)
              ·
                refine ⟨18900474655598868700053953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201605062993054599467242165 18900474655598868700053953)
                ·
                  refine ⟨14175355991699151525040465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18900474655598868700053953 14175355991699151525040465)
                  ·
                    refine ⟨10631516993774363643780349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14175355991699151525040465 10631516993774363643780349)
                    ·
                      refine ⟨3986818872665386366417631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10631516993774363643780349 3986818872665386366417631)
                      ·
                        rfl

theorem cell23_7764302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_7764302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764302 prefixEnd_7764302 := by exact prefixLift 7764302
  have htrace : WordTrace (prefixWord ++ tailWord_7764302) baseStart_7764302 baseEnd_7764302 := by
    simpa [prefixWord, tailWord_7764302, baseEnd_7764302] using wordTrace_append hprefix tailTrace_7764302
  have hstable : (prefixWord ++ tailWord_7764302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764302).length < 2 ^ (prefixWord ++ tailWord_7764302).sum := by decide
  have hdescent : baseEnd_7764302 < baseStart_7764302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764322 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 8]
def baseStart_7764322 : Nat := 118140960795 + 7764322 * 2 ^ 59
def prefixEnd_7764322 : Nat := 4983230072969 + 3 ^ 40 * 7764322 * 2
def baseEnd_7764322 : Nat := 442981015808719587574171

theorem tailTrace_7764322 : CollatzResearch.WordTrace tailWord_7764322 prefixEnd_7764322 442981015808719587574171 := by
  unfold tailWord_7764322
  simp only [CollatzResearch.WordTrace]
  refine ⟨70797022044298727367805805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188792058784796606314148813 70797022044298727367805805)
  ·
    refine ⟨26548883266612022762927177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70797022044298727367805805 26548883266612022762927177)
    ·
      refine ⟨19911662449959017072195383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26548883266612022762927177 19911662449959017072195383)
      ·
        refine ⟨29867493674938525608293075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19911662449959017072195383 29867493674938525608293075)
        ·
          refine ⟨44801240512407788412439613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29867493674938525608293075 44801240512407788412439613)
          ·
            refine ⟨16800465192152920654664855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44801240512407788412439613 16800465192152920654664855)
            ·
              refine ⟨25200697788229380981997283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16800465192152920654664855 25200697788229380981997283)
              ·
                refine ⟨37801046682344071472995925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25200697788229380981997283 37801046682344071472995925)
                ·
                  refine ⟨442981015808719587574171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37801046682344071472995925 442981015808719587574171)
                  ·
                    rfl

theorem cell23_7764322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_7764322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764322 prefixEnd_7764322 := by exact prefixLift 7764322
  have htrace : WordTrace (prefixWord ++ tailWord_7764322) baseStart_7764322 baseEnd_7764322 := by
    simpa [prefixWord, tailWord_7764322, baseEnd_7764322] using wordTrace_append hprefix tailTrace_7764322
  have hstable : (prefixWord ++ tailWord_7764322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764322).length < 2 ^ (prefixWord ++ tailWord_7764322).sum := by decide
  have hdescent : baseEnd_7764322 < baseStart_7764322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764325 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 1, 2, 6]
def baseStart_7764325 : Nat := 118140960795 + 7764325 * 2 ^ 59
def prefixEnd_7764325 : Nat := 4983230072969 + 3 ^ 40 * 7764325 * 2
def baseEnd_7764325 : Nat := 3986830682720439776430025

theorem tailTrace_7764325 : CollatzResearch.WordTrace tailWord_7764325 prefixEnd_7764325 3986830682720439776430025 := by
  unfold tailWord_7764325
  simp only [CollatzResearch.WordTrace]
  refine ⟨283188197596184040983582429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188792131730789360655721619 283188197596184040983582429)
  ·
    refine ⟨106195574098569015368843411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283188197596184040983582429 106195574098569015368843411)
    ·
      refine ⟨159293361147853523053265117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106195574098569015368843411 159293361147853523053265117)
      ·
        refine ⟨59735010430445071144974419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159293361147853523053265117 59735010430445071144974419)
        ·
          refine ⟨89602515645667606717461629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59735010430445071144974419 89602515645667606717461629)
          ·
            refine ⟨33600943367125352519048111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89602515645667606717461629 33600943367125352519048111)
            ·
              refine ⟨50401415050688028778572167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33600943367125352519048111 50401415050688028778572167)
              ·
                refine ⟨75602122576032043167858251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50401415050688028778572167 75602122576032043167858251)
                ·
                  refine ⟨113403183864048064751787377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75602122576032043167858251 113403183864048064751787377)
                  ·
                    refine ⟨85052387898036048563840533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113403183864048064751787377 85052387898036048563840533)
                    ·
                      refine ⟨3986830682720439776430025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85052387898036048563840533 3986830682720439776430025)
                      ·
                        rfl

theorem cell23_7764325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_7764325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764325 prefixEnd_7764325 := by exact prefixLift 7764325
  have htrace : WordTrace (prefixWord ++ tailWord_7764325) baseStart_7764325 baseEnd_7764325 := by
    simpa [prefixWord, tailWord_7764325, baseEnd_7764325] using wordTrace_append hprefix tailTrace_7764325
  have hstable : (prefixWord ++ tailWord_7764325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764325).length < 2 ^ (prefixWord ++ tailWord_7764325).sum := by decide
  have hdescent : baseEnd_7764325 < baseStart_7764325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764335 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 3, 5]
def baseStart_7764335 : Nat := 118140960795 + 7764335 * 2 ^ 59
def prefixEnd_7764335 : Nat := 4983230072969 + 3 ^ 40 * 7764335 * 2
def baseEnd_7764335 : Nat := 1328945272508994912434993

theorem tailTrace_7764335 : CollatzResearch.WordTrace tailWord_7764335 prefixEnd_7764335 1328945272508994912434993 := by
  unfold tailWord_7764335
  simp only [CollatzResearch.WordTrace]
  refine ⟨283188562326147812691446459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188792374884098541794297639 283188562326147812691446459)
  ·
    refine ⟨424782843489221719037169689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283188562326147812691446459 424782843489221719037169689)
    ·
      refine ⟨318587132616916289277877267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424782843489221719037169689 318587132616916289277877267)
      ·
        refine ⟨477880698925374433916815901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318587132616916289277877267 477880698925374433916815901)
        ·
          refine ⟨179205262097015412718805963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 477880698925374433916815901 179205262097015412718805963)
          ·
            refine ⟨268807893145523119078208945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179205262097015412718805963 268807893145523119078208945)
            ·
              refine ⟨201605919859142339308656709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268807893145523119078208945 201605919859142339308656709)
              ·
                refine ⟨37801109973589188620373133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201605919859142339308656709 37801109973589188620373133)
                ·
                  refine ⟨14175416240095945732639925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37801109973589188620373133 14175416240095945732639925)
                  ·
                    refine ⟨1328945272508994912434993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14175416240095945732639925 1328945272508994912434993)
                    ·
                      rfl

theorem cell23_7764335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 5].length) (baseStart_7764335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764335 prefixEnd_7764335 := by exact prefixLift 7764335
  have htrace : WordTrace (prefixWord ++ tailWord_7764335) baseStart_7764335 baseEnd_7764335 := by
    simpa [prefixWord, tailWord_7764335, baseEnd_7764335] using wordTrace_append hprefix tailTrace_7764335
  have hstable : (prefixWord ++ tailWord_7764335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764335).length < 2 ^ (prefixWord ++ tailWord_7764335).sum := by decide
  have hdescent : baseEnd_7764335 < baseStart_7764335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764349 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 3, 1, 3]
def baseStart_7764349 : Nat := 118140960795 + 7764349 * 2 ^ 59
def prefixEnd_7764349 : Nat := 4983230072969 + 3 ^ 40 * 7764349 * 2
def baseEnd_7764349 : Nat := 3986843006256147682529915

theorem tailTrace_7764349 : CollatzResearch.WordTrace tailWord_7764349 prefixEnd_7764349 3986843006256147682529915 := by
  unfold tailWord_7764349
  simp only [CollatzResearch.WordTrace]
  refine ⟨283189072948097093082456101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188792715298731395388304067 283189072948097093082456101)
  ·
    refine ⟨53097951177768204952960519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283189072948097093082456101 53097951177768204952960519)
    ·
      refine ⟨79646926766652307429440779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53097951177768204952960519 79646926766652307429440779)
      ·
        refine ⟨119470390149978461144161169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79646926766652307429440779 119470390149978461144161169)
        ·
          refine ⟨89602792612483845858120877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119470390149978461144161169 89602792612483845858120877)
          ·
            refine ⟨33601047229681442196795329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89602792612483845858120877 33601047229681442196795329)
            ·
              refine ⟨25200785422261081647596497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33601047229681442196795329 25200785422261081647596497)
              ·
                refine ⟨18900589066695811235697373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25200785422261081647596497 18900589066695811235697373)
                ·
                  refine ⟨7087720900010929213386515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18900589066695811235697373 7087720900010929213386515)
                  ·
                    refine ⟨10631581350016393820079773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7087720900010929213386515 10631581350016393820079773)
                    ·
                      refine ⟨3986843006256147682529915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10631581350016393820079773 3986843006256147682529915)
                      ·
                        rfl

theorem cell23_7764349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_7764349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764349 prefixEnd_7764349 := by exact prefixLift 7764349
  have htrace : WordTrace (prefixWord ++ tailWord_7764349) baseStart_7764349 baseEnd_7764349 := by
    simpa [prefixWord, tailWord_7764349, baseEnd_7764349] using wordTrace_append hprefix tailTrace_7764349
  have hstable : (prefixWord ++ tailWord_7764349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764349).length < 2 ^ (prefixWord ++ tailWord_7764349).sum := by decide
  have hdescent : baseEnd_7764349 < baseStart_7764349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764359 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 2, 3, 2]
def baseStart_7764359 : Nat := 118140960795 + 7764359 * 2 ^ 59
def prefixEnd_7764359 : Nat := 4983230072969 + 3 ^ 40 * 7764359 * 2
def baseEnd_7764359 : Nat := 3986848141062692643404869

theorem tailTrace_7764359 : CollatzResearch.WordTrace tailWord_7764359 prefixEnd_7764359 3986848141062692643404869 := by
  unfold tailWord_7764359
  simp only [CollatzResearch.WordTrace]
  refine ⟨283189437678060864790320131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188792958452040576526880087 283189437678060864790320131)
  ·
    refine ⟨424784156517091297185480197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283189437678060864790320131 424784156517091297185480197)
    ·
      refine ⟨79647029346954618222277537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 424784156517091297185480197 79647029346954618222277537)
      ·
        refine ⟨59735272010215963666708153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79647029346954618222277537 59735272010215963666708153)
        ·
          refine ⟨44801454007661972750031115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59735272010215963666708153 44801454007661972750031115)
          ·
            refine ⟨67202181011492959125046673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44801454007661972750031115 67202181011492959125046673)
            ·
              refine ⟨50401635758619719343785005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67202181011492959125046673 50401635758619719343785005)
              ·
                refine ⟨18900613409482394753919377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50401635758619719343785005 18900613409482394753919377)
                ·
                  refine ⟨14175460057111796065439533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18900613409482394753919377 14175460057111796065439533)
                  ·
                    refine ⟨5315797521416923524539825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14175460057111796065439533 5315797521416923524539825)
                    ·
                      refine ⟨3986848141062692643404869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5315797521416923524539825 3986848141062692643404869)
                      ·
                        rfl

theorem cell23_7764359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_7764359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764359 prefixEnd_7764359 := by exact prefixLift 7764359
  have htrace : WordTrace (prefixWord ++ tailWord_7764359) baseStart_7764359 baseEnd_7764359 := by
    simpa [prefixWord, tailWord_7764359, baseEnd_7764359] using wordTrace_append hprefix tailTrace_7764359
  have hstable : (prefixWord ++ tailWord_7764359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764359).length < 2 ^ (prefixWord ++ tailWord_7764359).sum := by decide
  have hdescent : baseEnd_7764359 < baseStart_7764359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764376 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 2, 3, 2]
def baseStart_7764376 : Nat := 118140960795 + 7764376 * 2 ^ 59
def prefixEnd_7764376 : Nat := 4983230072969 + 3 ^ 40 * 7764376 * 2
def baseEnd_7764376 : Nat := 3986856870233819076892291

theorem tailTrace_7764376 : CollatzResearch.WordTrace tailWord_7764376 prefixEnd_7764376 3986856870233819076892291 := by
  unfold tailWord_7764376
  simp only [CollatzResearch.WordTrace]
  refine ⟨141595028859499638346844491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188793371812666184462459321 141595028859499638346844491)
  ·
    refine ⟨212392543289249457520266737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141595028859499638346844491 212392543289249457520266737)
    ·
      refine ⟨159294407466937093140200053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212392543289249457520266737 159294407466937093140200053)
      ·
        refine ⟨14933850700025352481893755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159294407466937093140200053 14933850700025352481893755)
        ·
          refine ⟨22400776050038028722840633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14933850700025352481893755 22400776050038028722840633)
          ·
            refine ⟨16800582037528521542130475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22400776050038028722840633 16800582037528521542130475)
            ·
              refine ⟨25200873056292782313195713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16800582037528521542130475 25200873056292782313195713)
              ·
                refine ⟨18900654792219586734896785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25200873056292782313195713 18900654792219586734896785)
                ·
                  refine ⟨14175491094164690051172589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18900654792219586734896785 14175491094164690051172589)
                  ·
                    refine ⟨5315809160311758769189721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14175491094164690051172589 5315809160311758769189721)
                    ·
                      refine ⟨3986856870233819076892291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5315809160311758769189721 3986856870233819076892291)
                      ·
                        rfl

theorem cell23_7764376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_7764376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764376 prefixEnd_7764376 := by exact prefixLift 7764376
  have htrace : WordTrace (prefixWord ++ tailWord_7764376) baseStart_7764376 baseEnd_7764376 := by
    simpa [prefixWord, tailWord_7764376, baseEnd_7764376] using wordTrace_append hprefix tailTrace_7764376
  have hstable : (prefixWord ++ tailWord_7764376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764376).length < 2 ^ (prefixWord ++ tailWord_7764376).sum := by decide
  have hdescent : baseEnd_7764376 < baseStart_7764376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764383 : List Nat := [1, 1, 2, 5, 1, 1, 5, 2, 1, 1, 3]
def baseStart_7764383 : Nat := 118140960795 + 7764383 * 2 ^ 59
def prefixEnd_7764383 : Nat := 4983230072969 + 3 ^ 40 * 7764383 * 2
def baseEnd_7764383 : Nat := 3986860464598400549504759

theorem tailTrace_7764383 : CollatzResearch.WordTrace tailWord_7764383 prefixEnd_7764383 3986860464598400549504759 := by
  unfold tailWord_7764383
  simp only [CollatzResearch.WordTrace]
  refine ⟨283190313029973916889193803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188793542019982611259462535 283190313029973916889193803)
  ·
    refine ⟨424785469544960875333790705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283190313029973916889193803 424785469544960875333790705)
    ·
      refine ⟨318589102158720656500343029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424785469544960875333790705 318589102158720656500343029)
      ·
        refine ⟨29867728327380061546907159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 318589102158720656500343029 29867728327380061546907159)
        ·
          refine ⟨44801592491070092320360739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29867728327380061546907159 44801592491070092320360739)
          ·
            refine ⟨67202388736605138480541109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44801592491070092320360739 67202388736605138480541109)
            ·
              refine ⟨6300223944056731732550729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67202388736605138480541109 6300223944056731732550729)
              ·
                refine ⟨4725167958042548799413047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6300223944056731732550729 4725167958042548799413047)
                ·
                  refine ⟨7087751937063823199119571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4725167958042548799413047 7087751937063823199119571)
                  ·
                    refine ⟨10631627905595734798679357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7087751937063823199119571 10631627905595734798679357)
                    ·
                      refine ⟨3986860464598400549504759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10631627905595734798679357 3986860464598400549504759)
                      ·
                        rfl

theorem cell23_7764383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_7764383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764383 prefixEnd_7764383 := by exact prefixLift 7764383
  have htrace : WordTrace (prefixWord ++ tailWord_7764383) baseStart_7764383 baseEnd_7764383 := by
    simpa [prefixWord, tailWord_7764383, baseEnd_7764383] using wordTrace_append hprefix tailTrace_7764383
  have hstable : (prefixWord ++ tailWord_7764383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764383).length < 2 ^ (prefixWord ++ tailWord_7764383).sum := by decide
  have hdescent : baseEnd_7764383 < baseStart_7764383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764402 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_7764402 : Nat := 118140960795 + 7764402 * 2 ^ 59
def prefixEnd_7764402 : Nat := 4983230072969 + 3 ^ 40 * 7764402 * 2
def baseEnd_7764402 : Nat := 3986870220730835975167171

theorem tailTrace_7764402 : CollatzResearch.WordTrace tailWord_7764402 prefixEnd_7764402 3986870220730835975167171 := by
  unfold tailWord_7764402
  simp only [CollatzResearch.WordTrace]
  refine ⟨70797751504226270783533865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188794004011270055422756973 70797751504226270783533865)
  ·
    refine ⟨53098313628169703087650399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70797751504226270783533865 53098313628169703087650399)
    ·
      refine ⟨79647470442254554631475599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53098313628169703087650399 79647470442254554631475599)
      ·
        refine ⟨119471205663381831947213399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79647470442254554631475599 119471205663381831947213399)
        ·
          refine ⟨179206808495072747920820099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119471205663381831947213399 179206808495072747920820099)
          ·
            refine ⟨268810212742609121881230149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179206808495072747920820099 268810212742609121881230149)
            ·
              refine ⟨50401914889239210352730653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268810212742609121881230149 50401914889239210352730653)
              ·
                refine ⟨18900718083464703882273995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50401914889239210352730653 18900718083464703882273995)
                ·
                  refine ⟨28351077125197055823410993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18900718083464703882273995 28351077125197055823410993)
                  ·
                    refine ⟨21263307843897791867558245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28351077125197055823410993 21263307843897791867558245)
                    ·
                      refine ⟨3986870220730835975167171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21263307843897791867558245 3986870220730835975167171)
                      ·
                        rfl

theorem cell23_7764402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_7764402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764402 prefixEnd_7764402 := by exact prefixLift 7764402
  have htrace : WordTrace (prefixWord ++ tailWord_7764402) baseStart_7764402 baseEnd_7764402 := by
    simpa [prefixWord, tailWord_7764402, baseEnd_7764402] using wordTrace_append hprefix tailTrace_7764402
  have hstable : (prefixWord ++ tailWord_7764402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764402).length < 2 ^ (prefixWord ++ tailWord_7764402).sum := by decide
  have hdescent : baseEnd_7764402 < baseStart_7764402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764409 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 3, 2, 3]
def baseStart_7764409 : Nat := 118140960795 + 7764409 * 2 ^ 59
def prefixEnd_7764409 : Nat := 4983230072969 + 3 ^ 40 * 7764409 * 2
def baseEnd_7764409 : Nat := 3986873815095417447779639

theorem tailTrace_7764409 : CollatzResearch.WordTrace tailWord_7764409 prefixEnd_7764409 3986873815095417447779639 := by
  unfold tailWord_7764409
  simp only [CollatzResearch.WordTrace]
  refine ⟨283191261327879723329640281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188794174218586482219760187 283191261327879723329640281)
  ·
    refine ⟨212393445995909792497230211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283191261327879723329640281 212393445995909792497230211)
    ·
      refine ⟨318590168993864688745845317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212393445995909792497230211 318590168993864688745845317)
      ·
        refine ⟨59735656686349629139845997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318590168993864688745845317 59735656686349629139845997)
        ·
          refine ⟨22400871257381110927442249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59735656686349629139845997 22400871257381110927442249)
          ·
            refine ⟨16800653443035833195581687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22400871257381110927442249 16800653443035833195581687)
            ·
              refine ⟨25200980164553749793372531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16800653443035833195581687 25200980164553749793372531)
              ·
                refine ⟨37801470246830624690058797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25200980164553749793372531 37801470246830624690058797)
                ·
                  refine ⟨14175551342561484258772049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37801470246830624690058797 14175551342561484258772049)
                  ·
                    refine ⟨10631663506921113194079037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14175551342561484258772049 10631663506921113194079037)
                    ·
                      refine ⟨3986873815095417447779639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10631663506921113194079037 3986873815095417447779639)
                      ·
                        rfl

theorem cell23_7764409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_7764409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764409 prefixEnd_7764409 := by exact prefixLift 7764409
  have htrace : WordTrace (prefixWord ++ tailWord_7764409) baseStart_7764409 baseEnd_7764409 := by
    simpa [prefixWord, tailWord_7764409, baseEnd_7764409] using wordTrace_append hprefix tailTrace_7764409
  have hstable : (prefixWord ++ tailWord_7764409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764409).length < 2 ^ (prefixWord ++ tailWord_7764409).sum := by decide
  have hdescent : baseEnd_7764409 < baseStart_7764409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764412 : List Nat := [2, 2, 2, 4, 1, 1, 2, 9]
def baseStart_7764412 : Nat := 118140960795 + 7764412 * 2 ^ 59
def prefixEnd_7764412 : Nat := 4983230072969 + 3 ^ 40 * 7764412 * 2
def baseEnd_7764412 : Nat := 147662050205088182816375

theorem tailTrace_7764412 : CollatzResearch.WordTrace tailWord_7764412 prefixEnd_7764412 147662050205088182816375 := by
  unfold tailWord_7764412
  simp only [CollatzResearch.WordTrace]
  refine ⟨141595685373434427420999745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188794247164579236561332993 141595685373434427420999745)
  ·
    refine ⟨106196764030075820565749809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141595685373434427420999745 106196764030075820565749809)
    ·
      refine ⟨79647573022556865424312357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106196764030075820565749809 79647573022556865424312357)
      ·
        refine ⟨14933919941729412267058567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79647573022556865424312357 14933919941729412267058567)
        ·
          refine ⟨22400879912594118400587851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14933919941729412267058567 22400879912594118400587851)
          ·
            refine ⟨33601319868891177600881777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22400879912594118400587851 33601319868891177600881777)
            ·
              refine ⟨25200989901668383200661333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33601319868891177600881777 25200989901668383200661333)
              ·
                refine ⟨147662050205088182816375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25200989901668383200661333 147662050205088182816375)
                ·
                  rfl

theorem cell23_7764412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 9].length) (baseStart_7764412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764412 prefixEnd_7764412 := by exact prefixLift 7764412
  have htrace : WordTrace (prefixWord ++ tailWord_7764412) baseStart_7764412 baseEnd_7764412 := by
    simpa [prefixWord, tailWord_7764412, baseEnd_7764412] using wordTrace_append hprefix tailTrace_7764412
  have hstable : (prefixWord ++ tailWord_7764412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764412).length < 2 ^ (prefixWord ++ tailWord_7764412).sum := by decide
  have hdescent : baseEnd_7764412 < baseStart_7764412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764426 : List Nat := [3, 1, 2, 1, 2, 2, 5, 1, 1, 2, 3]
def baseStart_7764426 : Nat := 118140960795 + 7764426 * 2 ^ 59
def prefixEnd_7764426 : Nat := 4983230072969 + 3 ^ 40 * 7764426 * 2
def baseEnd_7764426 : Nat := 3986882544266543881267061

theorem tailTrace_7764426 : CollatzResearch.WordTrace tailWord_7764426 prefixEnd_7764426 3986882544266543881267061 := by
  unfold tailWord_7764426
  simp only [CollatzResearch.WordTrace]
  refine ⟨70797970342204533808252283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188794587579212090155339421 70797970342204533808252283)
  ·
    refine ⟨106196955513306800712378425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70797970342204533808252283 106196955513306800712378425)
    ·
      refine ⟨79647716634980100534283819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106196955513306800712378425 79647716634980100534283819)
      ·
        refine ⟨119471574952470150801425729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79647716634980100534283819 119471574952470150801425729)
        ·
          refine ⟨89603681214352613101069297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119471574952470150801425729 89603681214352613101069297)
          ·
            refine ⟨67202760910764459825801973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89603681214352613101069297 67202760910764459825801973)
            ·
              refine ⟨6300258835384168108668935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67202760910764459825801973 6300258835384168108668935)
              ·
                refine ⟨9450388253076252163003403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6300258835384168108668935 9450388253076252163003403)
                ·
                  refine ⟨14175582379614378244505105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9450388253076252163003403 14175582379614378244505105)
                  ·
                    refine ⟨10631686784710783683378829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14175582379614378244505105 10631686784710783683378829)
                    ·
                      refine ⟨3986882544266543881267061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10631686784710783683378829 3986882544266543881267061)
                      ·
                        rfl

theorem cell23_7764426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_7764426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764426 prefixEnd_7764426 := by exact prefixLift 7764426
  have htrace : WordTrace (prefixWord ++ tailWord_7764426) baseStart_7764426 baseEnd_7764426 := by
    simpa [prefixWord, tailWord_7764426, baseEnd_7764426] using wordTrace_append hprefix tailTrace_7764426
  have hstable : (prefixWord ++ tailWord_7764426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764426).length < 2 ^ (prefixWord ++ tailWord_7764426).sum := by decide
  have hdescent : baseEnd_7764426 < baseStart_7764426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764434 : List Nat := [3, 2, 2, 4, 2, 1, 2, 2, 1, 1, 3]
def baseStart_7764434 : Nat := 118140960795 + 7764434 * 2 ^ 59
def prefixEnd_7764434 : Nat := 4983230072969 + 3 ^ 40 * 7764434 * 2
def baseEnd_7764434 : Nat := 3986886652111779849967025

theorem tailTrace_7764434 : CollatzResearch.WordTrace tailWord_7764434 prefixEnd_7764434 3986886652111779849967025 := by
  unfold tailWord_7764434
  simp only [CollatzResearch.WordTrace]
  refine ⟨70798043288197288149825089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188794782101859435066200237 70798043288197288149825089)
  ·
    refine ⟨53098532466147966112368817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70798043288197288149825089 53098532466147966112368817)
    ·
      refine ⟨39823899349610974584276613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53098532466147966112368817 39823899349610974584276613)
      ·
        refine ⟨7466981128052057734551865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39823899349610974584276613 7466981128052057734551865)
        ·
          refine ⟨5600235846039043300913899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7466981128052057734551865 5600235846039043300913899)
          ·
            refine ⟨8400353769058564951370849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5600235846039043300913899 8400353769058564951370849)
            ·
              refine ⟨6300265326793923713528137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8400353769058564951370849 6300265326793923713528137)
              ·
                refine ⟨4725198995095442785146103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6300265326793923713528137 4725198995095442785146103)
                ·
                  refine ⟨7087798492643164177719155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4725198995095442785146103 7087798492643164177719155)
                  ·
                    refine ⟨10631697738964746266578733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7087798492643164177719155 10631697738964746266578733)
                    ·
                      refine ⟨3986886652111779849967025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10631697738964746266578733 3986886652111779849967025)
                      ·
                        rfl

theorem cell23_7764434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_7764434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764434 prefixEnd_7764434 := by exact prefixLift 7764434
  have htrace : WordTrace (prefixWord ++ tailWord_7764434) baseStart_7764434 baseEnd_7764434 := by
    simpa [prefixWord, tailWord_7764434, baseEnd_7764434] using wordTrace_append hprefix tailTrace_7764434
  have hstable : (prefixWord ++ tailWord_7764434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764434).length < 2 ^ (prefixWord ++ tailWord_7764434).sum := by decide
  have hdescent : baseEnd_7764434 < baseStart_7764434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764435 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 5]
def baseStart_7764435 : Nat := 118140960795 + 7764435 * 2 ^ 59
def prefixEnd_7764435 : Nat := 4983230072969 + 3 ^ 40 * 7764435 * 2
def baseEnd_7764435 : Nat := 3986887165592434346054519

theorem tailTrace_7764435 : CollatzResearch.WordTrace tailWord_7764435 prefixEnd_7764435 3986887165592434346054519 := by
  unfold tailWord_7764435
  simp only [CollatzResearch.WordTrace]
  refine ⟨283192209625785529770086759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188794806417190353180057839 283192209625785529770086759)
  ·
    refine ⟨424788314438678294655130139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283192209625785529770086759 424788314438678294655130139)
    ·
      refine ⟨637182471658017441982695209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424788314438678294655130139 637182471658017441982695209)
      ·
        refine ⟨477886853743513081487021407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 637182471658017441982695209 477886853743513081487021407)
        ·
          refine ⟨716830280615269622230532111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477886853743513081487021407 716830280615269622230532111)
          ·
            refine ⟨1075245420922904433345798167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716830280615269622230532111 1075245420922904433345798167)
            ·
              refine ⟨1612868131384356650018697251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075245420922904433345798167 1612868131384356650018697251)
              ·
                refine ⟨2419302197076534975028045877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1612868131384356650018697251 2419302197076534975028045877)
                ·
                  refine ⟨226809580975925153908879301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2419302197076534975028045877 226809580975925153908879301)
                  ·
                    refine ⟨42526796432985966357914869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 226809580975925153908879301 42526796432985966357914869)
                    ·
                      refine ⟨3986887165592434346054519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42526796432985966357914869 3986887165592434346054519)
                      ·
                        rfl

theorem cell23_7764435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_7764435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764435 prefixEnd_7764435 := by exact prefixLift 7764435
  have htrace : WordTrace (prefixWord ++ tailWord_7764435) baseStart_7764435 baseEnd_7764435 := by
    simpa [prefixWord, tailWord_7764435, baseEnd_7764435] using wordTrace_append hprefix tailTrace_7764435
  have hstable : (prefixWord ++ tailWord_7764435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764435).length < 2 ^ (prefixWord ++ tailWord_7764435).sum := by decide
  have hdescent : baseEnd_7764435 < baseStart_7764435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
